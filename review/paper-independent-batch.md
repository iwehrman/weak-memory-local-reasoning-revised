# Independent paper queue: batched results after the 4B statement

This batch follows `26af676`. The 21-constructor program calculus, assertion
interpretation, machine, and checkpoint-5 safety predicate are unchanged.
The proposed 47-constructor assertion system remains at its statement
checkpoint: this batch neither changes it nor claims its soundness.

Completed here: priority 3.3–7 and 5.3–4, together with the negative part of
3.1. Priority 3.1's general restricted SHARE theorem remains open. The
[writer's index](../notes/paper-theorem-index.md) consolidates the results,
including the earlier completed items. The reviewer-owned queue and paper
sources have not been edited.

## 1. The review counterexamples now use the printed points-to

[PrintedPointsToDerivations.v](../theories/PrintedPointsToDerivations.v)
repeats both bad derivations using exactly
`A.points_to`, the dissertation's existential-writer/all-processor-barrier
abbreviation, under the **original `models` interpretation**:

- `printed_points_stale_value_unsound`: with invariant `emp ∨ x ↦ 7`,
  derive `{x ↦ 7 * lock₁} skip₁ {x ↦ 5 * lock₁}`.
- `printed_points_foreign_barrier_unsound`: with invariant `x ↦ 7`,
  derive a foreign `bar(2)` after a pending processor-2 write and the held
  processor-1 lock, without executing a fence or changing the machine.

Each theorem includes the derivation, an inhabited full-state precondition,
failure of the postcondition on that same state, and invalidity for the
printed `valid_specification`. The first changes no value physically; the
second leaves the foreign write pending. The conclusions rule out every
postcondition decomposition. No weaker cell abbreviation is used in these
two invariant/pre/post schemas.

The four-rule subset is still SKIP, CONS, INV and FRAME-TM, including the
printed variable condition. INV is parenthesized `J * (P * lock_i)` as in
the accepted checkpoint-1 response.

[PrintedDerivations.v](../theories/PrintedDerivations.v) and
[ReviewObstructions.v](../theories/ReviewObstructions.v) are audited copies
of the historical review files. Their proof text is preserved, except for a
provenance comment, trailing-blank-line normalization, and moving their
`Print Assumptions` commands to
`Audit.v`. The originals remain unchanged. The abstract trilemma is still a
conditional theorem with explicit hypotheses; the retirement result is
still about an abandoned interpretation, not the active calculus.

## 2. Derived and alternative program rules

I checked the author's [original source, lines 2129–2175](https://github.com/iwehrman/Weak-Memory-Local-Reasoning/blob/master/dissertation.tex#L2129-L2175),
blob `ac4c24370dc22b3ca0892294206c2c6ac138d993`. In the table, `C` is the
weakened writer-existential cell, `↦` is the original all-processor cell,
`W_i` is a write atom, and `Q / T` abbreviates the existing right temporal
wand, `TemporalWandRight Q T`. All positive entries below are actual
`owned_derivation` trees. Their consequence steps still use semantic
entailments; replacing those with assertion derivations belongs to 4B/4C.

| Source rule | Checked classification and scope |
| --- | --- |
| LOAD-P | **Derived**, with the original `↦` and `⋉`: `{(a ↦ v) ⋉ P} r := [a]_i {((a ↦ v) ⋉ P) ∧ r=v}`. `owned_derive_load_points_to`, both modes. Requires the accepted destination freshness in `J`, address, value and `P`. No actor mark is manufactured: the precondition already contains every active mark. |
| STORE-P, literally displayed | **Refuted instance** in the final interpretation: the source displays a load command and a strong-temporal suffix. `owned_literal_store_p_invalid` uses an inhabited one-cell precondition and a real load step. `literal_store_p_post_false` shows the displayed suffix is impossible: it requires spatial separation of two resources owning the same address. Changing only the command to a store would not fix that postcondition. |
| STORE-P, corrected form | **Derived modified form**: `{(a ↦ u) ⋉ P} [a] := v_i {((a ↦ u) ⋉ P) ; W_i(a,v)}`. `owned_derive_store_points_to`, both modes. This matches the temporal suffix of primitive STORE; it is not a claim that the literal displayed STORE-P was sound. |
| Strengthened LOCK | **Modified for transfer**: existing `OwnedLock` returns `(lock_i * J) ; bar(i)`. With `J=emp`, the exact strengthened `lock_i * bar(i)` postcondition is derived by `owned_derive_lock_empty_strong`, both modes. The arbitrary-invariant rule must account for the acquired cells. |
| Strengthened UNLOCK | **Modified for restoration**: existing `OwnedUnlock` requires `A ; bar(i) ⊨ J * B`. With `J=emp`, `{lock_i} release_i {bar(i)}` is derived by `owned_derive_unlock_empty_strong`, DJ. |
| FENCE-G | **Derived in its displayed form**, both modes: `owned_derive_fence_after`. |
| LOCK-G | **Derived modified form**, both modes: `{P} acquire_i {P ; ((lock_i * J) ; bar(i))}`. `owned_derive_lock_after` retains the transferred invariant explicitly and uses FRAME-TM. |
| UNLOCK-G | **Derived with the empty-invariant restriction**, DJ: `{P * lock_i} release_i {P ; bar(i)}`, `owned_derive_unlock_after_empty`. For general `J`, use the restoration/donation premise of `OwnedUnlock`; the whole retained `P` cannot simply be promised unchanged after donating part of it. |
| FENCE-B | **Derived intended fence form**, both modes: `{Q / bar(i)} fence_i {Q}`, `owned_derive_fence_backward`. The source's displayed command is `lock_i`, an apparent transcription error; the theorem deliberately uses `fence_i`. This batch does not classify every instance of that literal lock-command schema. |
| LOCK-B | **Derived modified form**, both modes: `{Q / ((lock_i * J) ; bar(i))} acquire_i {Q}`, `owned_derive_lock_backward`. The transferred invariant appears in the wand. This is a useful backward rule, not an identification with the source's differently nested wand formula. |
| UNLOCK-B | **Derived with the empty-invariant restriction**, DJ: `{(Q / bar(i)) * lock_i} release_i {Q}`, `owned_derive_unlock_backward_empty`. General invariants retain the restoration obligation. |
| LOCKED and ATOMIC | **Derived modified wrapper**, `owned_derive_locked_wrapper`: acquire under `J`, prove the body under the **same `J`**, then use the existing release entailment. It permits restoration after draining, so a buffered store in the body is allowed. The source's rule importing an arbitrary body derivation under invariant `emp` is not recovered. This does not classify every specific source LOCKED/ATOMIC application as false. |
| Daring shared LOAD/STORE | **Unavailable as rules**. The calculus has no rule that borrows a pool cell for access without acquisition. Existing heap axioms require a local write/cell assertion. This is a statement of proof-system scope, not a theorem that every coincidentally matching instance is invalid. |

The exact LOAD-P derivation and corrected STORE-P derivation are in
[OwnedPointsToRules.v](../theories/OwnedPointsToRules.v). Their common
entailment is useful: a strong-temporal all-processor cell assertion is
equivalent to the weakened-cell version with `∀k. bar(k)` as an empty
**spatial** frame. LOAD preserves that frame. STORE moves it onto the
earlier history component, retaining the old cell's completeness without
claiming that the newly issued write has drained. This proof does not use
strong-temporal associativity or FRAME-STM.

The other new derived rules are in
[OwnedAlternativeRules.v](../theories/OwnedAlternativeRules.v). No program
constructor, invariant condition, or processor-count condition was added.
The lock schemas remain restricted to constant positive owner identifiers,
as in the existing calculus; the fence and heap rules accept expressions.

## 3. Common-split framing succeeds, including release

The [statement](paper-common-split-statement.md) was recorded before the
search and proof. [The finite search](paper-common-split-search.jsonl) found
no counterexample in either mode. It checked 9,951 local-future cases per
mode. There were 4,883 overlap and 1,605 disjoint input environments;
admissible release successors numbered 983 and 900 respectively. Acquisition,
store, fence, unchanged-buffer actions, mark-only futures and local flushes
were included. These numbers describe bounded screening, not a proof.

[OwnedCommonSplit.v](../theories/OwnedCommonSplit.v) proves the general result:

- `resource_common_future_split` supplies **one pair** of future resources
  that simultaneously satisfies both composition relations.
- `owned_common_reconstruction` fixes the retained resource through the
  actual program step and proves both successor relations on the same
  `retained`, `local'`, `big'` triple.
- `owned_safe_common_frame` gives same-index framing in **both modes**,
  for arbitrary commands/assertions, with the fragment invariant and usual
  variable condition. There is no two-processor hypothesis and no
  restriction excluding release.

The proof combines spatial footprint preservation with fixed-frame temporal
cancellation. It does not choose one successor for the spatial obligation
and another for the temporal obligation.

[OwnedCommonSplitExamples.v](../theories/OwnedCommonSplitExamples.v) provides
a concrete disjoint-mode release. Processor 1 holds the lock and the donated
cell. Processor 2's retained write precedes its local write in the same
buffer; both stay pending through release. `owned_common_release_safe`
proves safety at every index and `owned_common_release_enabled` supplies the
inhabited precondition, actual environment and enabled step.

This **does not reinstate FRAME-STM**: `(R * P) ∧ (R ; P)` still need not
have a common split. No assertion constructor or semantic validity layer
was introduced. Exposing this resource theorem through a new connective
would be a separate design decision, and has not been attempted.

## 4. The witness mismatch also yields a printed-calculus counterexample

[PrintedStrongFrame.v](../theories/PrintedStrongFrame.v) extends the reviewed
printed-rule subset only by the displayed FRAME-STM rule. It proves
`printed_strong_frame_counterexample` under original `models`:

```text
J = emp ∨ x ↦ 7       R = emp ∨ x ↦ 5
P = x ↦ 7 * lock₁    Q = emp * lock₁
J ⊢ {R ⋉ P} skip₁ {R ⋉ Q}
```

On the held-lock state with the actual cell value 7, the spatial precondition
uses `R=emp`; the temporal precondition uses the stale `R=x ↦ 5`, overridden
by the later cell containing 7. INV donates the current cell in the base
derivation. After that donation the framed postcondition has no satisfying
decomposition on the unchanged state. The theorem packages the derivation,
inhabited precondition, postcondition failure, and printed-safety invalidity.
The derivation uses no FRAME-TM application.

This transfers the **independent-witness mechanism**, with a smaller witness;
it is not the identical checkpoint-6 release program. The stale 5/7 values
make the error visible in the original full-memory postcondition, where
the invariant cell remains physically present. Nor does this isolate
FRAME-STM as the sole source of unsoundness: INV donation is also used,
and already participates in the earlier bad derivations. The positive
common-split theorem and negative abbreviation theorem have different
hypotheses and do not conflict.

## 5. SHARE: two negative results, and a precise open target

`owned_printed_share_lock_counterexample` in
[OwnedAlternativeCounterexamples.v](../theories/OwnedAlternativeCounterexamples.v)
checks the requested example in both modes. Apply printed SHARE to
acquisition with a one-cell invariant. The conclusion requires that cell
once as the exposed invariant and again as acquired ownership. The
precondition is inhabited and acquisition executes, but every successor
postcondition is impossible. Unrestricted SHARE is therefore incompatible
with these transferring lock rules.

There is a qualification for the proposed restricted rule:
**absence of the `Lock` constructor is insufficient**. The additional
`owned_syntactic_lock_free_share_counterexample` has precondition `emp` and
postcondition `C(x,7) * true`, neither of which contains `Lock`. Acquisition
derives this postcondition because `true` can absorb the token. SHARE again
demands two copies of the cell and fails in both modes. It is a counterexample
to the syntactic reading, not to the stronger semantic reading below.

Before attempting the general restricted theorem, I propose making its
intended premise explicit, without adding an assertion atom or validity
predicate:

```text
invariant_fragment J; two_active_processors active
∀s,r. r ⊨ P → lock_free(memory(r))
∀s,r. r ⊨ Q → lock_free(memory(r))
owned_valid active DJ J P c Q
-------------------------------------------------------
owned_valid active DJ emp (J * P) c (J * Q)
```

This is an **open theorem statement**, not an axiom, admitted theorem, or
claimed result. Whether it holds, and whether an overlap-mode counterpart
holds, remains unsettled. The new counterexample establishes the needed
distinction between syntactically and semantically lock-free assertions;
it does not justify predicting the answer for the semantic statement.

## 6. Fenced Dekker: scope, not a machine counterexample

The present calculus does not provide the rule needed for the dissertation's
fenced Dekker proof: one thread reads a flag that another thread can update,
without acquiring the global lock. LOAD and LOAD-ANY require private write
or cell ownership. Spatial concurrency cannot give the same flag to both
threads, and putting it in `J` makes its ownership available only through
acquisition. A fence drains a buffer; it does not transfer ownership or
grant a shared-read permission. The missing ingredient is a shared-access
rule or protocol, such as a justified daring rule, not another fence lemma.
This is a limitation of the available proof rules, not a claim that fenced
Dekker is incorrect on the machine, nor a formal theorem excluding every
possible encoding or specialized derivation.

## 7. Review decisions and verification

The batch is ready for review alongside the earlier 4B statement. The next
inputs that affect development are:

1. Assess the unchanged 47-constructor assertion-rule proposal before its
   soundness proof, as agreed. Then proceed to 4C and the parked examples.
2. Confirm that restricted SHARE is intended to use the explicit semantic
   token-freedom premises above. The syntactic reading has now failed.

There is no proposal here to add a common-split connective or a new program
rule. Review reports and counterexamples can be consumed together; no
changes have been made to the reviewer's prose or queue.

`make check` passes with **947 audited declarations closed**, no axioms or
admitted proofs. This adds 84 declarations to the audit: 32 historical
review lemmas/theorems and 52 new results. All named proof declarations in
the nine new theory modules are audited. The bounded search is reproducible
with `python3 scripts/search_common_split.py`; its output is checked in.
