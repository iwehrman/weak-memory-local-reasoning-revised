#!/usr/bin/env python3
"""Bounded screening for the paper algebra audit, not a semantic proof.

Two processors; up to two addresses; value 0; up to one pending write per
processor; arbitrary marks; lock tokens included. Compositions outside the
finite universe are omitted. Every reported failure needs a Rocq witness.
"""
from dataclasses import asdict
from functools import lru_cache
from itertools import combinations, product
import json

from search_frame_shape import Resource, compose


def main():
    buffers = ((), ((1, 0),), ((2, 0),))
    universe = tuple(r for heap, b0, b1, blocked, marks in product(
        product((None, 0), repeat=2), buffers, buffers, range(4), range(4))
        if (r := Resource((*heap, None), (b0, b1), blocked, marks)).well_formed())
    index = {r: i for i, r in enumerate(universe)}
    relations = {}
    for kind in ("sp", "tm"):
        rows = [[] for r in universe]
        for i, a in enumerate(universe):
            for j, b in enumerate(universe):
                outputs = sum(1 << index[out] for out in compose(kind, a, b) if out in index)
                if outputs:
                    rows[i].append((1 << j, outputs))
        relations[kind] = rows

    def sat(predicate):
        return sum(1 << i for i, r in enumerate(universe) if predicate(r))

    def empty(r):
        return not r.domain() and r.blocked == 0

    @lru_cache(maxsize=50000)
    def conj(kind, left, right):
        if kind == "stm":
            return conj("sp", left, right) & conj("tm", left, right)
        out = 0
        while left:
            bit = left & -left
            for b, result in relations[kind][bit.bit_length()-1]:
                if right & b:
                    out |= result
            left ^= bit
        return out

    atoms = {"emp": sat(empty), "true": (1 << len(universe))-1}
    for i in range(2):
        atoms[f"bar{i+1}"] = sat(lambda r: empty(r) and r.marks & (1 << i))
        atoms[f"lock{i+1}"] = sat(lambda r: not r.domain() and r.blocked == (3 ^ (1 << i)))
        for loc in (1, 2):
            heap = tuple(0 if j == loc else None for j in range(1, 4))
            atoms[f"W({loc},{i+1},0)"] = sat(lambda r:
                (r.heap == (None, None, None) and not (r.blocked & ~(1 << i))
                 and r.buffers[i] == ((loc, 0),) and not r.buffers[1-i])
                or (r.heap == heap and r.buffers == ((), ()) and r.blocked == 0
                    and r.marks & (1 << i)))
    for loc in (1, 2):
        heap = tuple(0 if j == loc else None for j in range(1, 4))
        atoms[f"C({loc},0)"] = sat(lambda r: r.heap == heap and r.buffers == ((), ())
            and r.blocked == 0 and r.marks != 0)
    formulas = dict(atoms)
    for (a, x), (b, y) in combinations(atoms.items(), 2):
        formulas[f"({a} or {b})"] = x | y
    # Deduplicate denotations and preserve short names for readable witnesses.
    names = {}
    for name, value in formulas.items():
        names.setdefault(value, name)
    fs = list((name, value) for value, name in names.items())
    print(json.dumps({"scope": "bounded interpretation; not a proof", "resources": len(universe),
                      "formulas": len(fs), "bounds": __doc__}, sort_keys=True), flush=True)

    def result(law, assignments, lhs, rhs):
        diff = lhs & ~rhs
        if not diff:
            return False
        bit = diff & -diff
        print(json.dumps({"law": law, "formulas": assignments,
            "witness": asdict(universe[bit.bit_length()-1])}, sort_keys=True), flush=True)
        return True

    for kind in ("sp", "tm", "stm"):
        for i, j in product((1, 2), repeat=2):
            result("E6:"+kind, {"i": i, "j": j}, conj(kind, atoms[f"lock{i}"], atoms[f"lock{j}"]), 0)

    # Search atoms first, then disjunctive formulas, for a failure of either
    # direction of strong-temporal associativity.
    found = set()
    checked = 0
    for family in (list(atoms.items()), fs):
        for (np, p), (nq, q), (nr, r) in product(family, repeat=3):
            left = conj("stm", conj("stm", p, q), r)
            right = conj("stm", p, conj("stm", q, r))
            checked += 1
            if "left-to-right" not in found and result("E3:stm:left-to-right",
                    {"P": np, "Q": nq, "R": nr}, left, right):
                found.add("left-to-right")
            if "right-to-left" not in found and result("E3:stm:right-to-left",
                    {"P": np, "Q": nq, "R": nr}, right, left):
                found.add("right-to-left")
            if len(found) == 2:
                break
        if len(found) == 2:
            break
    print(json.dumps({"law": "E3:stm", "triples_checked": checked,
                      "counterexample_directions": sorted(found)}), flush=True)


if __name__ == "__main__":
    main()
