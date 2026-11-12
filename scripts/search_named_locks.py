#!/usr/bin/env python3
"""Priority-2A assertion screen before general proofs.

Two actors, three addresses, every cell and empty-resource mark set,
one selected cell invariant, either no other lock or a second flag with
emp invariant, and pending/flushed flag writes. The selected invariant is
exclusive; the second component is only returned, not released by its
own named-lock rule. These are finite instances, not an all-frame proof.
"""
from dataclasses import replace
import json
from search_frame_shape import EMPTY
from search_cell_algebra import cells, combine
from search_owned_heap import atoms


def main():
    emp = {replace(EMPTY, marks=m) for m in range(4)}
    invariant = cells(2, 7)
    flag = [cells(1, v) for v in (0, 1)]
    component = combine("sp", flag[0], invariant) | flag[1]
    remainders = {"one_lock": emp, "two_locks": cells(3, 0) | cells(3, 1)}
    checks = {}

    def entails(name, before, after):
        assert before and before <= after, (name, before - after)
        checks[name] = len(before)

    for family, rest in remainders.items():
        pool = combine("sp", component, rest)
        for actor in range(2):
            label = f"{family}_actor_{actor+1}"
            locks = {replace(EMPTY, marks=m, blocked=3 ^ (1 << actor)) for m in range(4)}
            bars = {replace(EMPTY, marks=m) for m in range(4) if m & (1 << actor)}
            acquired = combine("tm", combine("sp", locks, pool), bars)
            cases = combine("sp", locks, combine("sp", flag[0], combine("sp", invariant, rest))) | \
                    combine("sp", locks, combine("sp", flag[1], rest))
            entails(label+"_acquire_cases", acquired, cases)
            for old, new, payload, retained, branch in ((0, 1, combine("sp", invariant, rest), invariant, "take"),
                                                       (1, 0, combine("sp", invariant, rest), emp, "return")):
                history = combine("tm", flag[old], set(atoms("printed", actor, 1, new)))
                checks[label+"_"+branch+"_pending"] = sum(bool(h.buffers[actor]) for h in history)
                entails(label+"_"+branch+"_donation",
                        combine("tm", combine("sp", history, payload), bars),
                        combine("sp", pool, retained))
            entails(label+"_retry_donation", combine("tm", combine("sp", flag[1], rest), bars),
                    combine("sp", pool, emp))
            entails(label+"_release_excludes_free", combine("sp", invariant, acquired),
                    combine("sp", locks, combine("sp", flag[1], combine("sp", invariant, rest))))
    print(json.dumps({"scope": __doc__, "checks": checks, "counterexample": None}, sort_keys=True))


if __name__ == "__main__":
    main()
