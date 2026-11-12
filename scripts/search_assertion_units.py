#!/usr/bin/env python3
"""Finite screening of emp units, including future-aware wands.

This is a bounded interpretation, not a proof about unbounded resources.
Two processors, one address, values 0/1, at most one pending write per
processor, all blocked sets and marks. Compositions leaving the universe
are omitted. The Rocq theorems are the authoritative general results.
"""
from itertools import product
import json

from search_frame_shape import Resource, compose, futures


def main():
    buffers = ((), ((1, 0),), ((1, 1),))
    universe = tuple(r for h, b0, b1, blocked, marks in product(
        (None, 0, 1), buffers, buffers, range(4), range(4))
        if (r := Resource((h, None, None), (b0, b1), blocked, marks)).well_formed())
    index = {r: i for i, r in enumerate(universe)}
    relations = {}
    for kind in ("sp", "tm"):
        relations[kind] = tuple((i, j, index[out]) for i, a in enumerate(universe)
                                for j, b in enumerate(universe)
                                for out in compose(kind, a, b) if out in index)
    future_indices = [tuple(index[f] for f in futures(r)) for r in universe]

    def sat(predicate):
        return frozenset(i for i, r in enumerate(universe) if predicate(r))

    def empty(r):
        return r.heap == (None, None, None) and r.buffers == ((), ()) and r.blocked == 0

    def conjunction(kind, left, right):
        if kind == "stm":
            return conjunction("sp", left, right) & conjunction("tm", left, right)
        return frozenset(out for a, b, out in relations[kind] if a in left and b in right)

    def wand(kind, antecedent, consequent, right=False):
        bad = set()
        for a, b, out in relations[kind]:
            extension, current = (b, a) if right else (a, b)
            if extension in antecedent and out not in consequent:
                bad.add(current)
        return frozenset(i for i, fs in enumerate(future_indices) if not any(f in bad for f in fs))

    formulas = {"true": frozenset(index.values()), "false": frozenset(), "emp": sat(empty)}
    for i in range(2):
        formulas[f"bar{i+1}"] = sat(lambda r: empty(r) and r.marks & (1 << i))
        formulas[f"lock{i+1}"] = sat(lambda r: r.heap == (None, None, None)
            and r.buffers == ((), ()) and r.blocked == (3 ^ (1 << i)))
        for v in (0, 1):
            formulas[f"write{i+1}:{v}"] = sat(lambda r:
                r.blocked == 0 and ((r.heap == (None, None, None)
                    and r.buffers[i] == ((1, v),) and not r.buffers[1-i])
                or (r.heap == (v, None, None) and r.buffers == ((), ()) and r.marks & (1 << i))))
    for v in (0, 1):
        formulas[f"cell{v}"] = sat(lambda r: r.heap == (v, None, None)
            and r.buffers == ((), ()) and r.blocked == 0 and r.marks != 0)
    atoms = tuple(formulas.items())
    for name_p, p in atoms:
        for name_q, q in atoms:
            for kind in ("sp", "tm", "stm"):
                formulas[f"({name_p} {kind} {name_q})"] = conjunction(kind, p, q)
            for kind, right in (("sp", False), ("tm", False), ("tm", True)):
                formulas[f"wand:{kind}:{right}({name_p},{name_q})"] = wand(kind, p, q, right)
    first_level = tuple(formulas.items())
    for name, p in first_level:
        if name.startswith("wand:"):
            for kind, right in (("sp", False), ("tm", False), ("tm", True)):
                formulas[f"nested:{kind}:{right}({name})"] = wand(kind, formulas["emp"], p, right)
    emp = formulas["emp"]
    checks = 0
    for name, p in formulas.items():
        for kind in ("sp", "tm", "stm"):
            for side in ("left", "right"):
                result = conjunction(kind, emp, p) if side == "left" else conjunction(kind, p, emp)
                checks += len(universe)
                if result != p:
                    witness = min(result ^ p)
                    raise AssertionError((name, kind, side, universe[witness], witness in p, witness in result))
    print(json.dumps({"resources": len(universe), "formulas": len(formulas),
                      "resource_formula_unit_checks": checks,
                      "spatial_compositions": len(relations["sp"]),
                      "temporal_compositions": len(relations["tm"]),
                      "counterexample": None, "scope": "bounded interpretation; not a proof"}, sort_keys=True))


if __name__ == "__main__":
    main()
