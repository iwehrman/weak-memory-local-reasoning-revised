#!/usr/bin/env python3
"""Priority-1 finite assertion screen, before the general Rocq proofs.

Two processors, data/token addresses 1/2/3, values 0/1/2, every cell mark
subset, every empty/lock mark subset, and pending/flushed write atoms.
This checks finite instances, not arbitrary environments or executions.
"""
from dataclasses import replace
from itertools import product
import json
from search_frame_shape import EMPTY, compose
from search_cell_algebra import cells, combine
from search_owned_heap import atoms


def main():
    emp = {replace(EMPTY, marks=m) for m in range(4)}
    data = [cells(1, v) for v in range(3)]
    token, receipt = cells(2, 0), cells(3, 0)
    invariant = data[0] | combine("sp", data[1], token) | combine("sp", token, receipt)
    checks = {}

    def entails(name, pre, post):
        bad = pre - post
        assert not bad, (name, bad)
        checks[name] = len(pre)

    for actor in range(2):
        locks = {replace(EMPTY, marks=m, blocked=3 ^ (1 << actor)) for m in range(4)}
        bars = {replace(EMPTY, marks=m) for m in range(4) if m & (1 << actor)}
        acquired = combine("tm", combine("sp", locks, invariant), bars)
        if actor == 0:
            entails("sender_acquire", combine("sp", token, acquired),
                    combine("sp", locks, combine("sp", data[0], token)))
        else:
            entails("receiver_acquire", combine("sp", receipt, acquired),
                    combine("sp", locks, combine("sp", data[0], receipt)) |
                    combine("sp", locks, combine("sp", data[1], combine("sp", token, receipt))))

        new = 1 if actor == 0 else 2
        history = combine("tm", data[actor], set(atoms("printed", actor, 1, new)))
        checks[f"actor_{actor+1}_pending_histories"] = sum(bool(h.buffers[actor]) for h in history)
        entails(f"actor_{actor+1}_drained_store", combine("tm", history, bars), data[new])
        if actor == 0:
            entails("sender_release", combine("tm", combine("sp", history, token), bars),
                    combine("sp", invariant, emp))
        else:
            entails("receiver_release_zero", combine("tm", combine("sp", data[0], receipt), bars),
                    combine("sp", invariant, receipt))
            entails("receiver_release_one", combine("tm", combine("sp", data[1], combine("sp", token, receipt)), bars),
                    combine("sp", invariant, data[1]))

    for loaded, local in ((0, receipt), (1, data[2])):
        finals = {out for out in combine("sp", invariant, local) if out.domain() == {1, 2, 3}}
        assert finals and all(out.heap[0] == loaded + 1 and not any(out.buffers) and out.blocked == 0 for out in finals)
        checks[f"terminal_{loaded}_with_preserved_domain"] = len(finals)
    print(json.dumps({"scope": __doc__, "checks": checks, "counterexample": None}, sort_keys=True))


if __name__ == "__main__":
    main()
