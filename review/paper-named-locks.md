# Priority 2A: named locks derived inside the calculus

**The named-lock rules are proved for any member of a finite family of
locks, using the unchanged assertion and program calculi.** The
[design](paper-named-locks-design.md) and
[bounded search](paper-named-locks-search.jsonl) preceded the general proofs.
The release condition is exactly the anticipated exclusivity proof; no
additional restriction was needed. These results await independent review.

## The rules

For a list of flag/invariant pairs, let

```text
F(l,I) = (C(l,0) * I) ∨ C(l,1)
J = spatial product of the family's components, with unit emp.

attempt(l,i,x) = acquire(i); x := [l]_i;
                if x=0 then ([l] := 1_i; release(i)) else release(i)
acquire_named(l,i,x) = x := 1; while x=1 do attempt(l,i,x)
release_named(l,i)   = acquire(i); [l] := 0_i; release(i)

J ⊢ᴰᴶ {emp} acquire_named(l,i,x) {I}
J ⊢ᴰᴶ {I}   release_named(l,i)   {emp}
```

`named_lock_acquire_family` and `named_lock_release_family` in
[NamedLockRules.v](../theories/NamedLockRules.v) are actual
`owned_derivation` trees. They require membership of `(l,I)` in the family.
Acquisition also requires the scratch variable absent from `fv(J)`.
Release requires an assertion derivation `I * I ⊢ₐ false`; acquisition does
not require that certificate. Thus emp and other nonexclusive invariants
are allowed by acquisition, while this release theorem does not cover
them. Exclusivity is a sufficient condition here, not claimed necessary
for every possible invariant.

`named_lock_family_valid` in
[NamedLockExamples.v](../theories/NamedLockExamples.v) applies the existing
soundness theorem with exactly its standing hypotheses: all family
invariants belong to the fragment and two distinct active processors exist.
There is no new finite-processor assumption. The *family* is finite because
its assertion is a finite Rocq fold. The code has constant flag and actor
annotations; the scratch register remains visible to the existing frame
and parallel side conditions.

As in the design, a semantic exclusivity assumption is represented by an
assertion proof certificate. No completeness theorem claiming that every
semantically exclusive formula has such a certificate is intended. Concrete
cell and nonempty cell-family certificates are derived in the existing basis.

## Proof structure

`nl_pool_focus` exposes a chosen component and the product of all remaining
components using spatial associativity and commutativity. It also carries
the needed free-variable inclusion. This does not change the invariant in
the program judgment or assume an ATOMIC/SHARE rule.

The physical acquire temporarily transfers the entire family. A zero
flag leads to storing 1, returning every other component and retaining
the selected `I`; a one flag returns the entire family and retries.
The loop invariant is `(I ∧ x=0) ∨ (emp ∧ x=1)`. It allows an arbitrary
number of failures, not just a selected successful branch.

Release begins with private `I`. After physical acquisition, the component
containing another `I` is excluded by the certificate. Storing zero and
releasing returns the invariant together with its flag. The existing UNLOCK
barrier premise completes the flag store; no fence is inserted.

Every CONS and UNLOCK obligation is an assertion derivation. The added
general loop/assignment interfaces in
[OwnedLoopRules.v](../theories/OwnedLoopRules.v) also use proof trees,
including the assumptions selecting a while branch. The basis remains
**47 assertion constructors and 21 program constructors**. No new grammar,
interpretation, safety predicate or machine instruction was added.

## Concrete evidence

The two-lock instance owns flags 1 and 3, protecting cells 2 and 4 with
values 7 and 9. `named_lock_two_initial_inhabited` exhibits its full
invariant model in an actual four-cell heap, with empty buffers/free lock.
`named_lock_nested_derived` acquires both logical locks and releases them
in reverse order. `named_lock_nested_all_runs` establishes no abort for
every finite execution and a restored invariant pool on termination.

`named_lock_nested_trace` is a **59-step** complete run. In its intermediate
`nl_two_both` state both named flags are 1 while the physical global lock
is free. `named_lock_nested_state` checks that the final named flags are
both 0, protected values remain 7 and 9, all buffers are empty and the
global lock is free. Named locks are therefore not being represented by
keeping the physical global lock held throughout their critical sections.

The general trace lemmas in
[NamedLockTrace.v](../theories/NamedLockTrace.v) cover:

- a successful named acquisition, 22 steps;
- a failed attempt, 8 steps, returning the physical lock;
- an entire failed retry iteration, 13 steps, returning to the same loop;
- a named release, 6 steps.

They allow arbitrary untouched heap contents and other processors' buffers.
Only the acting buffer must initially be empty. These are witness-trace
conditions, not extra hypotheses of the derived safety rules. The
successful-operation traces explicitly flush the flag write before release.

[CellFamilies.v](../theories/CellFamilies.v) supplies finite cell products,
their inhabited concrete memories under distinct-address conditions, their
fragment membership and a derived exclusivity certificate for nonempty
products. This also prepares the arbitrary-size region client. It adds no
recursive predicate to the assertion grammar.

The finite search covers one/two components, both actors, all mark sets
and pending/flushed flag writes. No counterexample was found. The full
proofs, not the search, establish validity over all admissible environments.

## Validation and next work

The seven new theory files contain **699 physical lines and 50 audited
declarations**. The full project has **173 theory files, 27,816 physical
lines and 1,157 audited declarations**. `make check` passes, including the independent `rocq check`, with all
1,157 audited declarations closed and no axioms or admitted proofs.

Next is the region mailbox client from part B. Its buffered stores will
need completion exposed in the derived lock contracts. The current plain
`{emp}/{I}` interfaces intentionally forget that information. The planned
route is to put a retained resource inside each physical UNLOCK premise,
so its existing `A ; bar(i)` clause can complete the acting processor's
writes. This is a derived-contract task, not a proposal for another fence
or a new program constructor. Any failure or additional semantic condition
will be reported before building the client around it.

Partial correctness remains the scope: neither the loop proof nor these
traces establish fairness, termination or deadlock freedom.
