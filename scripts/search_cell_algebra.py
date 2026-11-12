#!/usr/bin/env python3
"""Exact-atom screening of the two proposed flushed-cell laws for 4B.

Two active processors, addresses 1 and 2, values 0 and 1, every nonempty
mark subset, empty buffers and free locks. All compositions are retained.
This is evidence about these finite instances, not a general proof.
"""
from itertools import product
import json
from search_frame_shape import Resource, compose


def cells(address, value):
    heap = tuple(value if loc == address else None for loc in (1, 2, 3))
    return {Resource(heap, ((), ()), 0, marks) for marks in (1, 2, 3)}


def combine(kind, left, right):
    return {out for a in left for b in right for out in compose(kind, a, b)}


def main():
    distinct_checks = overwrite_checks = 0
    for address, other, old, new in product((1, 2), (1, 2), (0, 1), (0, 1)):
        left, right = cells(address, old), cells(other, new)
        temporal = combine("tm", left, right)
        if address != other:
            spatial = combine("sp", left, right)
            assert temporal == spatial, (address, other, old, new, temporal ^ spatial)
            distinct_checks += 1
        else:
            assert temporal <= right, (address, old, new, temporal - right)
            overwrite_checks += 1
    print(json.dumps({"scope": __doc__, "distinct_cell_instances": distinct_checks,
                      "overwrite_instances": overwrite_checks, "counterexample": None}, sort_keys=True))


if __name__ == "__main__":
    main()
