# Checkpoint 8 — parallel rule before the bounded search

The target is a semantic two-thread rule for the existing `owned_valid`:

```text
valid^k J {P1} c1 {Q1}       valid^k J {P2} c2 {Q2}
mod(c1) disjoint fv(P2,c2,Q2)
mod(c2) disjoint fv(P1,c1,Q1)
mod(c1) disjoint fv(J)       mod(c2) disjoint fv(J)
------------------------------------------------------------
valid^k J {P1 * P2} (c1 || c2) {Q1 * Q2}
```

Here `k` is the same ownership mode in both premises and the conclusion.
The first two interference conditions are the dissertation's existing
`parallel_variable_condition`. The invariant freshness conditions are
stated explicitly up front, as accepted in the checkpoint-7 response.
They allow the inactive thread's safety, including its invariant-dependent
environments, to be transported to the new stack after its sibling steps.
This does not prohibit private assignments or loads.

No new safety predicate, thread certificate, assertion constructor, or
ownership compartment is proposed. The proof should use spatial splitting
of local futures, exact-frame reconstruction for the executing component,
stack agreement for the inactive component, and FRAME-SP when either
component finishes. It should cover both modes if the existing lemmas
suffice. No additional processor-domain assumption is anticipated.

## Search obligations

The memory search extends checkpoint 7's finite families and executable
relations. For each admissible `pool ⊎ (F # (L * R))`, let either component
take each enabled unchanged-memory, store, fence, acquire, or release step.
For every bounded successor satisfying that component's safety-update
constraints with its grouped frame fixed, require all of:

1. Reconstruct the composite with the sibling resource exactly unchanged.
2. Preserve the original external frame, mode, and composite update bounds.
3. Obtain the sibling's fresh environment using the new acting resource
   in its frame, with the same successor pool and physical machine.

Bounds: two active processors, three addresses, values 0/1, all mark sets,
up to one heap cell per input component, and at most three input pending
writes (a store may add one). The overlapping-buffer family is enumerated;
the remaining inputs use the same reproducible seed-7, 4,000-draw sample
as checkpoint 7. This is a search of reconstruction obligations, not an
exhaustive search of assertions or semantic validity.

A separate two-step family explicitly acquires on one processor and then
stores on the other while that processor is blocked. Both resource views
must remain admissible after each step, with ownership and marks assigned
only as permitted by the actual action. Test both processor roles and
both modes.

The stack search checks primitive-step and abort agreement on finite stacks
that agree on a primitive's free variables and a chosen larger support set.
It includes assignment, load, store, assume, assert, fence, lock and unlock,
with processor annotations that may be register expressions. The Rocq proof
must then lift this to arbitrary commands, assertions, stacks and indices.

Run `PYTHONDONTWRITEBYTECODE=1 python3 scripts/search_owned_parallel.py`.
Record the output in `review/checkpoint-8-search.jsonl` before beginning the
general proof. Any failing obligation requires a checked counterexample or
an explicit correction to the attempted lemma before building downstream.
