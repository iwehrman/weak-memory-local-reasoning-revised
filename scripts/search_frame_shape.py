#!/usr/bin/env python3
"""Bounded checkpoint-3 search. Rocq remains the authority for any witness.

Mirrors Machine, Separation, StableCompatibility, OrderedBuffers and
GeneralizedFlushing. The exact family and quantifiers are in
review/checkpoint-3-statement.md. No solver/library dependencies.
"""
from collections import Counter, deque
from dataclasses import dataclass, replace, asdict
from functools import lru_cache
from itertools import product
import json


@dataclass(frozen=True)
class Resource:
    heap: tuple
    buffers: tuple
    blocked: int = 0
    marks: int = 0

    def domain(self):
        return frozenset(i + 1 for i, v in enumerate(self.heap) if v is not None) | frozenset(
            a for buf in self.buffers for a, _ in buf)

    def well_formed(self):
        return not (self.blocked & ~3 or self.marks & ~3) and (
            self.marks != 0 or all(v is None for v in self.heap))


EMPTY = Resource((None, None, None), ((), ()))


@lru_cache(None)
def shuffles(left, right, ordered):
    if not left and not right:
        return ((),)
    out = set()
    if left:
        out.update((left[0],) + tail for tail in shuffles(left[1:], right, ordered))
    if right and (not ordered or all(w[0] != right[0][0] for w in left)):
        out.update((right[0],) + tail for tail in shuffles(left, right[1:], ordered))
    return tuple(sorted(out))


def stable(left, right):
    if left.blocked & right.blocked:
        return False
    right_heap = {i + 1 for i, v in enumerate(right.heap) if v is not None}
    for i in range(2):
        addresses = {a for a, _ in left.buffers[i]}
        if addresses & right_heap:
            return False
        if addresses & {a for a, _ in right.buffers[1 - i]}:
            return False
    return True


@lru_cache(None)
def compose(kind, left, right):
    if kind == "sp":
        if left.domain() & right.domain() or left.blocked & right.blocked:
            return ()
    elif not stable(left, right):
        return ()
    if kind == "tm" and any(right.marks & (1 << i) and left.buffers[i] for i in range(2)):
        return ()
    choices = [((left.buffers[i] + right.buffers[i],) if kind == "tm" else
                shuffles(left.buffers[i], right.buffers[i], kind == "ov")) for i in range(2)]
    heap = tuple(b if b is not None else a for a, b in zip(left.heap, right.heap))
    return tuple(Resource(heap, buffers, left.blocked | right.blocked, left.marks | right.marks)
                 for buffers in product(*choices))


def flushed(resource, processor):
    if resource.blocked & (1 << processor) or not resource.buffers[processor]:
        return None
    address, value = resource.buffers[processor][0]
    heap, buffers = list(resource.heap), list(resource.buffers)
    heap[address - 1], buffers[processor] = value, buffers[processor][1:]
    return Resource(tuple(heap), tuple(buffers), resource.blocked, resource.marks | (1 << processor))


@lru_cache(None)
def futures(resource):
    seen, queue = {resource}, deque([resource])
    while queue:
        current = queue.popleft()
        successors = [replace(current, marks=current.marks | (1 << i)) for i in range(2)]
        successors += [flushed(current, i) for i in range(2)]
        for successor in successors:
            if successor is not None and successor not in seen:
                seen.add(successor)
                queue.append(successor)
    return tuple(sorted(seen, key=repr))


@lru_cache(None)
def subsequences(buffer):
    if not buffer:
        return ((),)
    tails = subsequences(buffer[1:])
    return tuple(sorted(set(tails) | {(buffer[0],) + tail for tail in tails}))


def residuals(world, local, acquired, actor):
    allowed = local.domain() | ({3} if acquired else set())
    heap_choices = [(None, v) if v is not None and i + 1 in allowed else (None,)
                    for i, v in enumerate(world.heap)]
    buffer_choices = [tuple(b for b in subsequences(buf) if all(a in allowed for a, _ in b))
                      for buf in world.buffers]
    marks = local.marks | ((1 << actor) if acquired else 0)
    for heap in product(*heap_choices):
        for buffers in product(*buffer_choices):
            candidate = Resource(heap, buffers, world.blocked, marks)
            if candidate.well_formed():
                yield candidate


@lru_cache(None)
def reframe(kind, frame, retained, grouped_after, local_after, whole_after):
    for frame_after in futures(frame):
        for retained_after in futures(retained):
            if grouped_after not in compose(kind, frame_after, retained_after):
                continue
            for local_framed in compose("tm", retained_after, local_after):
                if whole_after in compose(kind, frame_after, local_framed):
                    return True
    return False


def family():
    for proc, x, values, fm, rm, pm in product(range(2), (1, 2), product((0, 1), repeat=4),
                                             (1, 2, 3), range(4), range(4)):
        h, fw, rw, pw = values
        y = 3 - x
        def pending(address, value, marks):
            buffers = [(), ()]
            buffers[proc] = ((address, value),)
            return Resource((None, None, None), tuple(buffers), marks=marks)
        frame = pending(x, fw, fm)
        heap = list(frame.heap)
        heap[x - 1] = h
        yield proc, x, replace(frame, heap=tuple(heap)), pending(y, rw, rm), pending(x, pw, pm)


def actions(whole, proc, x):
    # Assume true is a genuine primitive step (skip itself has no step).
    yield "assume", whole, False, proc
    for v in (0, 1):
        buffers = list(whole.buffers)
        buffers[proc] += ((x, v),)
        yield "store", replace(whole, buffers=tuple(buffers)), False, proc
    result = flushed(whole, proc)
    if result is not None:
        yield "flush", result, False, proc
    # Initially full shared cell at fresh address 3; no footprint overlap.
    actor = 1 - proc
    assert not whole.buffers[actor] and whole.blocked == 0 and 3 not in whole.domain()
    pool = Resource((None, None, 0), ((), ()), marks=3)
    machines = compose("sp", pool, whole)
    assert len(machines) == 1
    machine = machines[0]
    yield "acquire", replace(machine, blocked=3 ^ (1 << actor)), True, actor


def search(kind, stop_each_action=False):
    counts, failures = Counter(), {}
    for proc, x, frame, retained, local in family():
        for inner in compose("tm", retained, local):
            for whole in compose(kind, frame, inner):
                for grouped in compose(kind, frame, retained):
                    if whole not in compose(kind, grouped, local):
                        continue
                    counts["initial_decompositions"] += 1
                    for action, physical_after, acquired, actor in actions(whole, proc, x):
                        if stop_each_action and action in failures:
                            continue
                        counts["steps_" + action] += 1
                        for grouped_after in futures(grouped):
                            for local_after in residuals(physical_after, local, acquired, actor):
                                whole_after = replace(physical_after, marks=grouped_after.marks | local_after.marks)
                                if whole_after not in compose(kind, grouped_after, local_after):
                                    continue
                                counts["residuals_" + action] += 1
                                if reframe(kind, frame, retained, grouped_after, local_after, whole_after):
                                    continue
                                witness = dict(kind=kind, action=action, actor=actor + 1,
                                    frame=asdict(frame), retained=asdict(retained), local=asdict(local),
                                    inner=asdict(inner), whole=asdict(whole), grouped=asdict(grouped),
                                    grouped_after=asdict(grouped_after), local_after=asdict(local_after),
                                    whole_after=asdict(whole_after))
                                failures.setdefault(action, witness)
                                if kind == "tm":
                                    return dict(counts=counts, failures=failures)
                                break
                            if action in failures:
                                break
                        if len(failures) == 4:
                            return dict(counts=counts, failures=failures)
    return dict(counts=counts, failures=failures)


if __name__ == "__main__":
    for kind in ("tm", "ov"):
        result = search(kind, stop_each_action=kind == "ov")
        print(json.dumps(dict(outer=kind, **result), sort_keys=True), flush=True)
