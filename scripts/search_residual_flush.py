#!/usr/bin/env python3
"""Checkpoint-4 finite searches; no search result is trusted by Rocq.

Reuses the executable relations from checkpoint 3. Bounds and intended
statements are in review/checkpoint-4-statement.md.
"""
from collections import Counter
from dataclasses import asdict
from itertools import product
import json

from search_frame_shape import Resource, EMPTY, shuffles, compose, flushed


ALPHABET = tuple(product((1, 2), (0, 1)))


def words(length):
    return tuple(product(ALPHABET, repeat=length))


def uniqueness_search():
    buffers = tuple(w for n in range(4) for w in words(n))
    seen, counts = {}, Counter()
    for frame, local in product(buffers, repeat=2):
        counts["input_pairs"] += 1
        for whole in shuffles(frame, local, True):
            counts["ordered_merges"] += 1
            previous = seen.setdefault((frame, whole), local)
            if previous != local:
                return dict(counts=counts, counterexample=dict(
                    frame=frame, whole=whole, local=previous, other_local=local))
    counts["frame_output_pairs"] = len(seen)
    return dict(counts=counts, counterexample=None)


def layouts():
    for sizes in product(range(4), repeat=4):
        if sum(sizes) <= 3:
            yield from product(*(words(n) for n in sizes))


def flush_search():
    heaps = tuple(h + (None,) for h in product((None, 0, 1), repeat=2))
    blocking = tuple((f, l) for f, l in product(range(4), repeat=2)
                     if not f & l and f | l != 3)
    pools = [Resource(EMPTY.heap, EMPTY.buffers, marks=3)]
    for address, value in product((1, 2, 3), (0, 1)):
        heap = [None, None, None]
        heap[address - 1] = value
        pools.append(Resource(tuple(heap), EMPTY.buffers, marks=3))
    counts = Counter()
    for f1, f2, l1, l2 in layouts():
        counts["buffer_layouts"] += 1
        # Bound memory used by the shared relation cache during this search.
        compose.cache_clear()
        for fh, lh, (fb, lb) in product(heaps, heaps, blocking):
            frame = Resource(fh, (f1, f2), fb, 3)
            local = Resource(lh, (l1, l2), lb, 3)
            for combined in compose("ov", frame, local):
                counts["frame_local_compositions"] += 1
                for pool in pools:
                    for whole in compose("sp", pool, combined):
                        counts["pool_compositions"] += 1
                        for processor in range(2):
                            after = flushed(whole, processor)
                            if after is None:
                                continue
                            counts["machine_flushes"] += 1
                            duplicate = bool(frame.buffers[processor] and local.buffers[processor]
                                and frame.buffers[processor][0] == local.buffers[processor][0])
                            if duplicate:
                                counts["identical_source_heads"] += 1
                            choices = []
                            for label, left, right in (
                                ("frame", flushed(frame, processor), local),
                                ("local", frame, flushed(local, processor))):
                                if left is None or right is None:
                                    continue
                                found = any(after in compose("sp", pool, out)
                                            for out in compose("ov", left, right))
                                if found:
                                    source = frame if label == "frame" else local
                                    if source.buffers[processor][0] != whole.buffers[processor][0]:
                                        return dict(counts=counts, counterexample=dict(
                                            reason="attributed a different write", label=label,
                                            frame=asdict(frame), local=asdict(local),
                                            pool=asdict(pool), whole=asdict(whole), after=asdict(after)))
                                    choices.append(label)
                            if not choices:
                                return dict(counts=counts, counterexample=dict(
                                    reason="no attribution", frame=asdict(frame), local=asdict(local),
                                    pool=asdict(pool), whole=asdict(whole), after=asdict(after)))
                            if len(choices) > 1:
                                return dict(counts=counts, counterexample=dict(
                                    reason="ambiguous attribution", frame=asdict(frame), local=asdict(local),
                                    pool=asdict(pool), whole=asdict(whole), after=asdict(after)))
                            counts[choices[0] + "_flushes"] += 1
                            if duplicate:
                                counts["duplicate_" + choices[0] + "_flushes"] += 1
    return dict(counts=counts, counterexample=None)


if __name__ == "__main__":
    print(json.dumps(dict(search="residual_uniqueness", **uniqueness_search()), sort_keys=True), flush=True)
    print(json.dumps(dict(search="flush_attribution", **flush_search()), sort_keys=True), flush=True)
