#!/usr/bin/env python3
"""Buffered named-lock contract screen: two actors, four addresses, all
mark choices, own/foreign pending or flushed retained writes, and both
named-flag branches. All compositions in this finite family are retained.
"""
from dataclasses import replace
import json
from search_frame_shape import Resource
from search_cell_algebra import combine

EMPTY = Resource((None,) * 4, ((), ()))


def cells(loc, value):
    return {replace(EMPTY, heap=tuple(value if a == loc else None for a in range(1, 5)), marks=m)
            for m in (1, 2, 3)}


def writes(actor, loc, value):
    buf = [(), ()]
    buf[actor] = ((loc, value),)
    return {replace(EMPTY, buffers=tuple(buf), marks=m, blocked=b)
            for m in range(4) for b in (0, 1 << actor)} | \
           {c for c in cells(loc, value) if c.marks & (1 << actor)}


def main():
    emp = {replace(EMPTY, marks=m) for m in range(4)}
    inv = cells(2, 7)
    flags = [cells(1, v) for v in (0, 1)]
    rest = cells(3, 0) | cells(3, 1)
    pool = combine("sp", combine("sp", flags[0], inv) | flags[1], rest)
    checks = {}

    def entails(name, before, after, inhabited=True):
        assert before <= after and (before or not inhabited), (name, before - after)
        checks[name] = len(before)

    for actor in range(2):
        bars = {replace(EMPTY, marks=m) for m in range(4) if m & (1 << actor)}
        for writer in range(2):
            retained = writes(writer, 4, 9)
            marked = combine("tm", retained, bars)
            changed_flag = combine("tm", flags[0], writes(actor, 1, 1))
            payload = combine("sp", changed_flag, combine("sp", inv, combine("sp", retained, rest)))
            entails(f"actor_{actor+1}_writer_{writer+1}_acquire_donation", combine("tm", payload, bars),
                    combine("sp", pool, combine("sp", inv, marked)))
            payload = combine("sp", flags[1], combine("sp", retained, rest))
            entails(f"actor_{actor+1}_writer_{writer+1}_retry_donation", combine("tm", payload, bars),
                    combine("sp", pool, retained))
        buffered = combine("tm", cells(2, 0), writes(actor, 2, 7))
        entails(f"actor_{actor+1}_completion", combine("tm", buffered, bars), inv)
        for old in (0, 1):
            flag_history = combine("tm", flags[old], writes(actor, 1, 0))
            tail = combine("sp", buffered, rest) if old else combine("sp", inv, combine("sp", buffered, rest))
            payload = combine("sp", flag_history, tail)
            entails(f"actor_{actor+1}_release_branch_{old}", combine("tm", payload, bars),
                    combine("sp", pool, emp), inhabited=bool(old))
    print(json.dumps({"scope": __doc__, "checks": checks, "counterexample": None}, sort_keys=True))


if __name__ == "__main__":
    main()
