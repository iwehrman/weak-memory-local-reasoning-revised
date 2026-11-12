#!/usr/bin/env python3
"""Checkpoint-7 bounded frame reconstruction search; Rocq is authoritative.

The statements, finite bounds, and sampling limits are recorded before the
proof attempt in review/checkpoint-7-statement.md. No third-party packages.
"""
from collections import Counter
from dataclasses import asdict, replace
from itertools import product
import json
import random

from search_frame_shape import Resource, EMPTY, compose, flushed, futures


POOLS = (replace(EMPTY, marks=3),) + tuple(
    Resource(tuple(v if j == a else None for j in range(3)), ((), ()), marks=3)
    for a, v in product(range(3), (0, 1)))


def physical(r):
    return r.heap, r.buffers, r.blocked


def phase(r):
    return {0: "free", 2: 0, 1: 1}.get(r.blocked, "invalid")


def matches(pool, frame, local, world, mode):
    if mode == "dj" and frame.domain() & local.domain():
        return False
    if phase(world) == "invalid" or (phase(world) != "free" and pool.domain()):
        return False
    return any(physical(w) == physical(world)
               for c in compose("ov", frame, local) for w in compose("sp", pool, c))


def actions(w):
    yield "ordinary", None, w
    for actor in range(2):
        for address, value in product((1, 2, 3), (0, 1)):
            readable = w.heap[address - 1] is not None or any(a == address for a, _ in w.buffers[actor])
            if readable:
                buffers = list(w.buffers)
                buffers[actor] += ((address, value),)
                yield "store", actor, replace(w, buffers=tuple(buffers))
        if not w.buffers[actor]:
            yield "fence", actor, w
            if phase(w) == "free":
                yield "acquire", actor, replace(w, blocked=3 ^ (1 << actor))
            if phase(w) == actor:
                yield "release", actor, replace(w, blocked=0)


def residual_buffer(frame, whole):
    left, local = list(frame), []
    for write in whole:
        if any(a == write[0] for a, _ in left):
            if not left or left[0] != write:
                return None
            left.pop(0)
        else:
            local.append(write)
    return None if left else tuple(local)


def update_ok(before, after, pool, returned, old_phase, new_phase, action, actor):
    earned = (1 << actor) if action in ("fence", "acquire", "release") else 0
    if after.marks & ~(before.marks | earned):
        return False
    if (after.domain() | returned.domain()) - (before.domain() | pool.domain()):
        return False
    if action == "acquire":
        return old_phase == "free" and new_phase == actor and not returned.domain() and after.blocked == 3 ^ (1 << actor)
    if action == "release":
        return old_phase == actor and new_phase == "free" and before.blocked == 3 ^ (1 << actor) and after.blocked == 0
    return old_phase == new_phase and physical(pool) == physical(returned) and before.blocked == after.blocked


def residuals(grouped, local, pool, world, after, action, actor):
    buffers = tuple(residual_buffer(f, w) for f, w in zip(grouped.buffers, after.buffers))
    if None in buffers:
        return
    allowed = local.domain() | pool.domain()
    heaps = tuple((None, v) if v is not None and a + 1 in allowed else (None,)
                  for a, v in enumerate(after.heap))
    returned_pools = (POOLS[0],) if action == "acquire" else POOLS if action == "release" else (pool,)
    blocks = 3 ^ (1 << actor) if action == "acquire" else 0 if action == "release" else local.blocked
    for heap, marks, returned in product(product(*heaps), range(4), returned_pools):
        candidate = Resource(heap, buffers, blocks, marks)
        if candidate.well_formed() and update_ok(local, candidate, pool, returned,
                phase(world), phase(after), action, actor):
            yield candidate, returned


def overlapping_family():
    for actor, x, values, marks in product(range(2), (1, 2),
            product((0, 1), repeat=4), product(range(4), repeat=3)):
        old, fv, rv, pv = values
        def component(address, value, mark, heap=False):
            buffers = [(), ()]
            buffers[actor] = ((address, value),)
            return Resource(tuple(old if heap and a == x else None for a in (1, 2, 3)),
                            tuple(buffers), marks=mark)
        f = component(x, fv, marks[0], True)
        r = component(3-x, rv, marks[1])
        p = component(x, pv, marks[2])
        if all(v.well_formed() for v in (f, r, p)):
            yield f, r, p, POOLS[0]


def sampled_family(draws=4000):
    rng = random.Random(7)
    for _ in range(draws):
        buffers = [[[], []] for _ in range(3)]
        for _ in range(rng.randrange(4)):
            buffers[rng.randrange(3)][rng.randrange(2)].append((rng.randrange(1, 4), rng.randrange(2)))
        roles = []
        for role in range(3):
            heap = [None] * 3
            if rng.randrange(3) == 0:
                heap[rng.randrange(3)] = rng.randrange(2)
            roles.append(Resource(tuple(heap), tuple(tuple(b) for b in buffers[role]), marks=rng.randrange(4)))
        state = rng.randrange(3)
        if state:
            role = rng.randrange(3)
            roles[role] = replace(roles[role], blocked=state)
        pool = POOLS[0] if state else rng.choice(POOLS)
        if all(r.well_formed() for r in roles):
            yield *roles, pool


def search(kind, mode):
    counts = Counter()
    for family, inputs in (("overlap", overlapping_family()), ("sample", sampled_family())):
        for f, r, p, pool in inputs:
            counts[family + "_inputs"] += 1
            compose.cache_clear()
            futures.cache_clear()
            for local in compose(kind, r, p):
                # Every immediate local future must have a future split.
                immediate = [replace(local, marks=local.marks | (1 << i)) for i in range(2)]
                immediate += [w for i in range(2) if (w := flushed(local, i)) is not None]
                for later in immediate:
                    counts["local_future_checks"] += 1
                    if not any(later in compose(kind, rr, pp) for rr in futures(r) for pp in futures(p)):
                        return dict(counts=counts, counterexample=dict(reason="future split", retained=asdict(r), local=asdict(p), after=asdict(later)))
                for combined in compose("ov", f, local):
                    for world in compose("sp", pool, combined):
                        if not matches(pool, f, local, world, mode):
                            continue
                        counts["input_environments"] += 1
                        groups = [g for g in compose("ov", f, r) if matches(pool, g, p, world, mode)]
                        if not groups:
                            return dict(counts=counts, counterexample=dict(reason="unframe", frame=asdict(f), retained=asdict(r), local=asdict(p)))
                        for grouped in groups:
                            for action, actor, after in actions(world):
                                counts["steps_" + action] += 1
                                for pp, returned in residuals(grouped, p, pool, world, after, action, actor):
                                    if not matches(returned, grouped, pp, after, mode):
                                        continue
                                    counts["successors_" + action] += 1
                                    found = any(matches(returned, f, big, after, mode) and
                                        update_ok(local, big, pool, returned, phase(world), phase(after), action, actor)
                                        for big in compose(kind, r, pp))
                                    if not found:
                                        return dict(counts=counts, counterexample=dict(reason="reframe", action=action,
                                            actor=actor, frame=asdict(f), retained=asdict(r), local=asdict(p),
                                            grouped=asdict(grouped), pool=asdict(pool), whole=asdict(world),
                                            local_after=asdict(pp), pool_after=asdict(returned), whole_after=asdict(after)))
    return dict(counts=counts, counterexample=None)


if __name__ == "__main__":
    for kind, mode in (("sp", "ov"), ("sp", "dj"), ("tm", "ov")):
        print(json.dumps(dict(rule=kind, mode=mode, seed=7, draws=4000, **search(kind, mode)), sort_keys=True), flush=True)
