#!/usr/bin/env python3
"""Checkpoint-9 finite heap-rule obligations; the Rocq proofs are authoritative."""
from collections import Counter
from dataclasses import asdict, replace
from itertools import product
import json
import random

from search_frame_shape import Resource, EMPTY, compose
from search_owned_frames import POOLS, matches, phase, update_ok
from search_owned_parallel import read


def pending(actor, address, value, marks=0, blocked=0, copies=1):
    buffers = [(), ()]
    buffers[actor] = ((address, value),) * copies
    return replace(EMPTY, buffers=tuple(buffers), marks=marks, blocked=blocked)


def cell(address, value, marks):
    heap = [None] * 3
    heap[address - 1] = value
    return replace(EMPTY, heap=tuple(heap), marks=marks)


def atoms(kind, actor, address, value):
    if kind == "printed":
        for marks, blocked in product(range(4), (0, 1 << actor)):
            yield pending(actor, address, value, marks, blocked)
        for marks in range(4):
            if marks & (1 << actor):
                yield cell(address, value, marks)
    else:
        for marks in (1, 2, 3):
            yield cell(address, value, marks)


def focused(kind):
    for actor, old in product(range(2), (0, 1)):
        frames = [EMPTY, cell(1, old, 3), cell(1, 1-old, 3),
                  pending(actor, 1, old), pending(actor, 1, 1-old),
                  pending(actor, 1, old, copies=2), pending(1-actor, 1, old)]
        retained = [EMPTY, cell(2, 0, 3), cell(2, 1, 3),
                    pending(actor, 2, 0), pending(1-actor, 2, 1)]
        for atom, frame, rest, fm, rm, fb, rb in product(
                atoms(kind, actor, 1, old), frames, retained, range(4), range(4), (0, 1, 2), (0, 1, 2)):
            frame, rest = replace(frame, marks=fm, blocked=fb), replace(rest, marks=rm, blocked=rb)
            if frame.well_formed() and rest.well_formed():
                for pool in (POOLS[0], cell(3, 0, 3)):
                    yield actor, 1, old, atom, rest, frame, pool


def sampled(kind, draws=4000):
    rng = random.Random(9)
    for _ in range(draws):
        actor, address, old = rng.randrange(2), rng.randrange(1, 4), rng.randrange(2)
        atom = rng.choice(tuple(atoms(kind, actor, address, old)))
        buffers = [[[], []] for _ in range(2)]
        for _ in range(rng.randrange(4)):
            buffers[rng.randrange(2)][rng.randrange(2)].append((rng.randrange(1, 4), rng.randrange(2)))
        resources = []
        for role in range(2):
            heap = [None] * 3
            if rng.randrange(3) == 0:
                heap[rng.randrange(3)] = rng.randrange(2)
            resources.append(Resource(tuple(heap), tuple(tuple(b) for b in buffers[role]),
                                      rng.randrange(3), rng.randrange(4)))
        if all(r.well_formed() for r in resources):
            yield actor, address, old, atom, *resources, rng.choice(POOLS)


def search(kind, mode):
    counts = Counter()
    for family, inputs in (("focused", focused(kind)), ("sampled", sampled(kind))):
        for actor, address, old, atom, rest, frame, pool in inputs:
            counts[family + "_inputs"] += 1
            compose.cache_clear()
            for local in compose("sp", atom, rest):
                for combined in compose("ov", frame, local):
                    for world in compose("sp", pool, combined):
                        if not matches(pool, frame, local, world, mode):
                            continue
                        counts["environments"] += 1
                        if read(world, actor, address) != old:
                            return dict(counts=counts, counterexample=dict(reason="wrong read", kind=kind,
                                actor=actor, address=address, old=old, world=asdict(world), local=asdict(local)))
                        counts["blocked_loads" if world.blocked & (1 << actor) else "enabled_loads"] += 1
                        if kind == "any_writer" and not atom.marks & (1 << actor):
                            counts["cell_without_loader_mark"] += 1
                        for value in (0, 1):
                            buffers = list(local.buffers)
                            buffers[actor] += ((address, value),)
                            successor = replace(local, buffers=tuple(buffers))
                            buffers = list(world.buffers)
                            buffers[actor] += ((address, value),)
                            after = replace(world, buffers=tuple(buffers))
                            okay = (matches(pool, frame, successor, after, mode)
                                    and update_ok(local, successor, pool, pool, phase(world), phase(after), "store", actor)
                                    and successor in compose("tm", local, pending(actor, address, value)))
                            if not okay:
                                return dict(counts=counts, counterexample=dict(reason="enqueue or temporal post",
                                    actor=actor, address=address, value=value, atom=asdict(atom), rest=asdict(rest),
                                    frame=asdict(frame), pool=asdict(pool), local=asdict(local), world=asdict(world)))
                            counts["stores"] += 1
    return dict(counts=counts, counterexample=None)


if __name__ == "__main__":
    for kind, mode in product(("printed", "any_writer"), ("ov", "dj")):
        result = dict(family=kind, mode=mode, seed=9, draws=4000, **search(kind, mode))
        print(json.dumps(result, sort_keys=True), flush=True)
        if result["counterexample"] is not None:
            raise SystemExit(1)
