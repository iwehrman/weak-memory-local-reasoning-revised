#!/usr/bin/env python3
"""Common-split resource framing search. Statement: review/paper-common-split-statement.md."""
from collections import Counter
from dataclasses import asdict, replace
from itertools import product
import json
from search_frame_shape import Resource, EMPTY, compose, flushed, futures
from search_owned_frames import (POOLS, matches, phase, actions, residuals,
                                update_ok, overlapping_family, sampled_family)


def common(left, right):
    return tuple(out for out in compose("tm", left, right) if out in compose("sp", left, right))


def release_family():
    for actor, rv, pv, marks in product(range(2), (0, 1), (0, 1), product(range(4), repeat=2)):
        foreign = 1 - actor
        rb, pb = [(), ()], [(), ()]
        rb[foreign], pb[foreign] = ((2, rv),), ((1, pv),)
        r = replace(EMPTY, buffers=tuple(rb), marks=marks[0])
        p = Resource((None, None, 0), tuple(pb), 3 ^ (1 << actor), marks[1])
        if r.well_formed() and p.well_formed():
            yield EMPTY, r, p, POOLS[0]


def search(mode):
    counts = Counter()
    for family, inputs in (("focused", overlapping_family()), ("release", release_family()), ("sample", sampled_family())):
        for f, r, p, pool in inputs:
            counts[family + "_inputs"] += 1
            compose.cache_clear()
            futures.cache_clear()
            for local in common( r, p):
                # Every immediate local future must have a future split.
                immediate = [replace(local, marks=local.marks | (1 << i)) for i in range(2)]
                immediate += [w for i in range(2) if (w := flushed(local, i)) is not None]
                for later in immediate:
                    counts["local_future_checks"] += 1
                    if not any(later in common( rr, pp) for rr in futures(r) for pp in futures(p)):
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
                                        for big in common( r, pp))
                                    if not found:
                                        return dict(counts=counts, counterexample=dict(reason="reframe", action=action,
                                            actor=actor, frame=asdict(f), retained=asdict(r), local=asdict(p),
                                            grouped=asdict(grouped), pool=asdict(pool), whole=asdict(world),
                                            local_after=asdict(pp), pool_after=asdict(returned), whole_after=asdict(after)))
    return dict(counts=counts, counterexample=None)


if __name__ == "__main__":
    for mode in ("ov", "dj"):
        result = dict(mode=mode, seed=7, draws=4000, **search(mode))
        print(json.dumps(result, sort_keys=True), flush=True)
        if result["counterexample"] is not None:
            raise SystemExit(1)
