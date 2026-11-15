#!/usr/bin/env python3
"""Bounded test of review/daring-withdrawal-budget-proposal.md.

This checks proposed update reconstruction, not buffered_safe. The approved
budget is not modified. Each frame is fixed and every composed memory is
spatial; all enumerated resources satisfy the mark/heap well-formedness rule.
"""
from dataclasses import dataclass
from itertools import product
import json

ACTORS = (1, 2)
ADDRESSES = (1, 2)
VALUES = (0, 1)
MARKS = (frozenset(), frozenset((1,)), frozenset((2,)), frozenset(ACTORS))

@dataclass(frozen=True)
class Resource:
    heap: tuple = ()
    writes: tuple = ()  # (processor, address, value), at most one per frame
    marks: frozenset = frozenset()

    def domain(self):
        return {a for a, _ in self.heap} | {a for _, a, _ in self.writes}

    def well_formed(self):
        return (not self.heap or bool(self.marks)) and self.marks <= set(ACTORS)

    def empty_buffer(self, actor):
        return not any(i == actor for i, _, _ in self.writes)

    def memory(self):
        return (self.heap, self.writes)

    def describe(self):
        return dict(heap=self.heap, writes=self.writes, marks=sorted(self.marks))


def spatial(a, b):
    assert not (a.domain() & b.domain())
    out = Resource(tuple(sorted(a.heap + b.heap)), a.writes + b.writes, a.marks | b.marks)
    assert a.well_formed() and b.well_formed() and out.well_formed()
    return out


def received(old, pool, new, pool_new):
    old_heap, new_heap, pool_new_heap = map(dict, (old.heap, new.heap, pool_new.heap))
    return any(a not in old_heap and new_heap.get(a) == v and a not in pool_new_heap
               for a, v in pool.heap)


def proposed(old, pool, new, pool_new, when):
    if not (new.domain() | pool_new.domain()) <= (old.domain() | pool.domain()):
        return False
    transfer = received(old, pool, new, pool_new)
    # OrdinaryAction earns no mark. Resource well-formedness restricts to active actors.
    for actor in new.marks - old.marks:
        empty_before = old.empty_buffer(actor)
        empty_after = new.empty_buffer(actor)
        empty = {"before": empty_before, "after": empty_after,
                 "both": empty_before and empty_after}[when]
        if not (transfer and empty):
            return False
    return True


def main():
    counts = {when: dict(cases=0, failures=0) for when in ("before", "after", "both")}
    witnesses = {}
    for x, value, old_marks, earned in product(ADDRESSES, VALUES, MARKS, ACTORS):
        old = Resource(marks=old_marks)
        new = Resource(((x, value),), marks=old_marks | {earned})
        pool, pool_new = Resource(((x, value),), marks=frozenset(ACTORS)), Resource(marks=frozenset(ACTORS))
        y = 3 - x
        for heap_value in (None,) + VALUES:
            for pending in (None,) + tuple(product(ACTORS, VALUES)):
                for frame_marks in MARKS:
                    frame = Resource(() if heap_value is None else ((y, heap_value),),
                                     () if pending is None else ((pending[0], y, pending[1]),), frame_marks)
                    if not frame.well_formed():
                        continue
                    before, after = spatial(frame, old), spatial(frame, new)
                    assert spatial(pool, before).memory() == spatial(pool_new, after).memory()
                    assert received(old, pool, new, pool_new)
                    for when, stats in counts.items():
                        assert proposed(old, pool, new, pool_new, when)
                        stats["cases"] += 1
                        if proposed(before, pool, after, pool_new, when):
                            continue
                        stats["failures"] += 1
                        # Prefer a heap-backed pending write, for an ordinary concrete memory.
                        if when not in witnesses or (not witnesses[when]["frame"]["heap"] and frame.heap):
                            witnesses[when] = dict(old=old.describe(), pool=pool.describe(), new=new.describe(),
                                                   pool_new=pool_new.describe(), frame=frame.describe(),
                                                   combined_before=before.describe(), combined_after=after.describe(),
                                                   requested_mark=earned, whole_memory_unchanged=True)
    result = dict(property="fixed spatial frame reconstruction for proposed withdrawal budget",
                  bounds=dict(processors=ACTORS, addresses=ADDRESSES, values=VALUES,
                              local_cells_before=0, received_cells=1, max_frame_pending_writes=1),
                  results=counts, witnesses=witnesses,
                  conclusion="All three proposed readings fail update reconstruction; approved definitions unchanged.")
    print(json.dumps(result, indent=2))
    assert all(stats["failures"] > 0 for stats in counts.values())


if __name__ == "__main__":
    main()
