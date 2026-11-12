#!/usr/bin/env python3
"""Screen E12 on exact write/barrier atoms for two active processors.

One address, old/new values 0 and 1, all mark subsets and permitted blocked
bits. Intermediate compositions are retained, including two pending writes.
The general, expression-valued Rocq theorem remains the authority.
"""
from itertools import product
import json
from search_frame_shape import Resource, compose


def writes(actor, value):
    out = set()
    for marks in range(4):
        for blocked in (0, 1 << actor):
            buffers = [(), ()]
            buffers[actor] = ((1, value),)
            out.add(Resource((None, None, None), tuple(buffers), blocked, marks))
        if marks & (1 << actor):
            out.add(Resource((value, None, None), ((), ()), 0, marks))
    return out


def tm(left, right):
    return {out for a in left for b in right for out in compose("tm", a, b)}


if __name__ == "__main__":
    checks = 0
    for actor, old, new in product(range(2), (0, 1), (0, 1)):
        bar = {Resource((None, None, None), ((), ()), 0, marks)
               for marks in range(4) if marks & (1 << actor)}
        left = tm(tm(writes(actor, old), writes(actor, new)), bar)
        right = tm(writes(actor, new), bar)
        assert left == right, (actor, old, new, left ^ right)
        checks += 1
    print(json.dumps({"law": "E12", "instances_checked": checks,
                      "counterexample": None, "scope": __doc__}, sort_keys=True))
