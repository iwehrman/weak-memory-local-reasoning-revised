# Paper checkpoint 4C: container through assertion derivations

**The selected-branch one-item container is now derived with assertion
proof trees for every CONS and UNLOCK premise.** This includes the cell
LOAD/STORE helpers, so no semantic entailment proof is hidden in a helper
used by the container. No missing assertion law was found. The basis
remains **47 assertion constructors and 21 program constructors**.

This follows [assertion soundness](paper-assertion-soundness.md) at `b196efd`
and is the next checkpoint in
[the latest reviewer guidance](reviewer-guidance-after-independent-batch.md).
Ian authorized proceeding while the reviewer was offline. Both batches are
ready for review; the previous soundness batch has not been relabelled as
independently accepted.

## Exact scope and result

The program, invariant, precondition and postcondition are exactly those
of the existing selected-branch container. Its theorem is still
`owned_container_derived` in
[OwnedContainerDerivation.v](../theories/OwnedContainerDerivation.v):

```text
J = C(f,0) ∨ (C(f,1) * ∃u.C(x,u))
R = W(y,2,17)

J ⊢ᴰᴶ {R}
  acquire(1);
  r := [f]₁; assume(r=1); [f] := 0₁; release(1);
  [x] := 9₁;
  acquire(1);
  r := [f]₁; assume(r=0); [f] := 1₁; release(1)
{R}
```

Addresses `f,x,y` are 1,2,3 and register `r` is 0. The core remains
`container_core_derived : J ⊢ᴰᴶ {emp} container_program {emp}`.
The old derivation bodies were replaced in place; all 12 declaration
statements in that module are unchanged. No alternative program or new
validity predicate was introduced.

Every consequence application now uses `owned_assertion_consequence`;
both release applications use `owned_assertion_unlock`. The pre/post
proofs supplied to those wrappers have type `assertion_derivation`.
`owned_derive_load_cell` and `owned_derive_store_cell` were also rewritten
to use assertion proofs for their strong-temporal unit steps, preserving
their original statements. These are the only program helper dependencies
that previously concealed semantic entailment reasoning.

The old `container_expression_cell_some` entailment is retained as an API
compatibility corollary, now proved by `assertion_derivation_sound` from
`container_assert_cell_some`. The container proof uses the assertion
derivation directly and does not call this corollary. Earlier semantic
container proofs remain available for historical comparison.

## Assertion obligations and reusable work

[OwnedContainerAssertions.v](../theories/OwnedContainerAssertions.v)
contains 13 named assertion derivations. They use the approved constructors,
the four derived cell rules, and eight general proof-tree helpers in
[AssertionRearrangements.v](../theories/AssertionRearrangements.v).

| Obligation | Derivation / ingredients |
| --- | --- |
| Move a cell out from under the lock and retained spatial tail; put it back | `container_assert_held_swap`, `container_assert_held_restore`; spatial associativity and commutativity |
| Extract a load's register equality | `container_assert_spatial_pure`; pure-through-spatial distribution |
| Introduce the unknown old cell value | `container_assert_cell_some`; the derived capture-avoiding value-hiding rule |
| Complete a drained store history | `container_assert_history_complete`; the derived drained-history rule |
| Normalize the first acquisition | `container_assert_first_acquire`; barrier elimination, disjunction distribution and the spatial unit |
| Restore the pool at the first release | `container_assert_remove_unlock`; spatial barrier distribution, history completion, invariant injection |
| Donate the item at the final release | `container_assert_return_unlock`; the same ingredients plus value hiding |
| Normalize the overlapping history at reacquisition | `container_assert_reacquire`, with `container_assert_full_cell_overwrite` and `container_assert_full_overwrite`; detailed below |
| Select the branch following the load | `container_assert_select_one`, `container_assert_select_zero`; disjunction elimination and pure boolean implications |
| Cell-only LOAD/STORE and the outer foreign frame | `assert_derive_strong_emp_right`, the ordinary unit constructors and separating monotonicity |

There are **zero remaining semantic resource-entailment obligations in
this container derivation**. Boolean implications and syntactic freshness
remain the permitted side conditions. The helper for distinct cells uses
the existing pure rule to discharge the guarded address disequality; the
container instances use the literal fact `1 ≠ 2`.

The 13-plus-eight count describes proof factoring, not a new count of the
16 nonidentity rule-premise obligations (28 expanded instances) recorded
at checkpoint 10. No completeness or proof-automation result is claimed.

## The difficult step: reacquisition

Let `H = (∃u.C(x,u)) ; W(x,1,9)`, `L = lock(1)` and `B = bar(1)`.
The second acquisition still uses FRAME-TM in overlap mode, producing

```text
H ; ((L * J) ; B).
```

Ordinary temporal associativity and barrier distribution give
`(H ; B) ; ((L * J) ; B)`. History completion and barrier elimination
give `C(x,9) ; (L * J)`. The derived lock rearrangement moves this to
`L * (C(x,9) ; J)`, using only the approved lock conversions and ordinary
associativity.

Distributing through the invariant preserves both branches:

```text
C(x,9) ; C(f,0)                ⊢ₐ C(f,0) * C(x,9)
C(x,9) ; (C(f,1) * ∃u.C(x,u)) ⊢ₐ C(f,1) * ∃u.C(x,u).
```

The first uses distinct-cell separation. The second opens the value
existential, changes separator only between the distinct flag and item
cells, brings the two item cells together, and applies the one-way
overwrite rule `C(x,9) ; C(x,u) ⊢ₐ C(x,u)`. It then hides the value again.
Thus the full-pool branch keeps the later unknown value; the proof does
not infer that the old private value survives arbitrary overlap. The
subsequent load and `assume(r=0)` select the empty-pool branch.

No strong-temporal associativity, exchange, FRAME-STM or common-split
connective is used. The unrelated foreign write is still carried by one
spatial frame around the whole core program, including both releases.

## Execution evidence and practical limit

`owned_container_all_runs_safe` in
[OwnedContainerTrace.v](../theories/OwnedContainerTrace.v) now applies
`owned_derivation_adequacy` to the reconstructed `owned_container_derived`.
It no longer obtains validity from the earlier semantic container proof.
Its statement is unchanged. The completed-run restoration theorem
`owned_container_completed_restores` already uses `container_core_derived`
and therefore now uses this reconstruction too.

The existing inhabited initial state and 24-step trace are unchanged:
the lock starts free, the pool contains the item, and the unrelated
processor-2 write remains pending throughout. The checked trace ends with
the item returned holding 9 and the lock free. The general result covers
all finite executions, with postcondition/restoration on termination;
it does not establish termination or fairness.

**The separate retrying container has not been fully reconstructed in the
assertion system.** It still compiles, and its shared cell-access helpers
and selected-branch subproofs now benefit from this work, but its retry
register and additional ownership entailments remain semantic. The 4B
proposal explicitly selected the original branch-selected container as
the initial 4C target. No claim about the retrying variant is broadened here.

## Validation and next work

`make check` passes, including the independent `rocq check`, with
**1,028 audited declarations closed** and no axioms or admitted proofs.
All 21 new lemmas are audited. The two new files contain 239 physical
lines; the full checked development has 157 theory files and 25,931
physical lines, including historical experiments and audit commands.
The theorem statements in all three modified existing modules were
compared with their prior versions and are unchanged.

This is the requested checkpoint after 4C. Next is priority 1, the
dissertation's message-passing example. Its deferred token-based design
should be restated against the completed assertion system, including the
remaining token-erasure obligation. The exact domain-preservation theorem
needed by that design is already proved. Named locks/client follow;
restricted SHARE remains deferred in the agreed order.
