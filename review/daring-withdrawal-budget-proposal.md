# Conditional addendum 6: proposed budget, before search

The exact addendum-5 load triple is false because its invariant admits an
empty pool. Initial barriers nevertheless remove its separate mark obstacle:
`BufferedPoolBarriers.v` proves a successor construction on the allocated
branch, a guarded allocation protocol as an atomic premise and derivation,
and two-thread initial-barrier adequacy. The guarded example is single-thread:
its load changes a variable free in the invariant, so it does not meet CONC's
invariant-preservation condition. This does not make unrestricted withdrawal
merely a precondition convention.

To test the conditional alternative, take the following *proposal only*;
`buffered_mark_budget` and every approved definition remain unchanged.

A transfer `receives(nu, pool, nu', pool')` means that some address has a
heap cell in `pool`, no heap cell in `nu`, the same heap cell in `nu'`, and
no heap cell in `pool'`. Retain the approved joint-footprint condition and
replace its mark budget by

```
mark(nu', i) -> mark(nu, i) or action_earns(action, i)
                 or (receives(nu, pool, nu', pool') and buffer(nu, i) = [])
```

Also test the version that requires the private buffer to be empty *after*
the step, and the version that requires both. This is a narrow reading of
"receiving a heap cell": the cell actually leaves the pool and keeps its
value. A counterexample here also rejects a weaker receiving condition.

The first proposed reconstruction property is the counterpart of
`buffered_update_frame`: if the proposal permits a local update, and a fixed
spatial resource R composes with its input and output, it must permit the
same update with R included in the private resource. The same reconstruction
is used to combine a running thread with a sibling. The bounded search checks
this property, not a newly defined safety predicate or a general soundness
proof.

Search bounds: two processors, two addresses, values 0 and 1, one received
cell, an initially empty local memory, all four initial local mark sets, one
newly requested processor mark, and a fixed frame with either no write or
one pending write at the other address. Frames include empty and nonempty
heaps and every well-formed mark set. All selected before/after compositions
are spatial and the whole memory is unchanged, as for an ordinary assignment.
