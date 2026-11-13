# Request: check two new appendix figures against the Rocq statements

**Draft to check:** `3585af5` (paper only; proof reference is still
`2b53266`). No new proof work is requested. Please do not edit the paper;
report corrections and I will apply them.

I added two figures to `paper/sections/appendix.tex` and rewrote one
paragraph in `paper/sections/calculus.tex`. I transcribed the rules by hand
from the Rocq sources, so the risk is a wrong bracket, direction, operand
order or side condition.

## 1. Figure "Assertion rules particular to this logic" (`app:assertion-rules`)

Source: `theories/AssertionDerivation.v`. Please check each displayed rule
against its constructor, in particular:

- The bullet stands for `*` or `⊲`, the same one throughout a rule. Confirm
  every rule displayed with a bullet really has a `kind` parameter
  (units, associativity, monotonicity, pure conjunct, barrier duplicate,
  barrier distribute).
- The pure-conjunct rule is displayed only in its left form,
  `(b ∧ P) • Q ⊣⊢ b ∧ (P • Q)` (`AssertPureSeparateLeft`).
- The three adjunctions, and my reading of the wand notation:
  `P -* R` for `SpatialWand p r`, `P -⊲ R` for `TemporalWandLeft p r`,
  and `R ⊲- P` for `TemporalWandRight r p`. The caption says each is
  invertible and only the introduction direction is shown.
- `P ⊲ bar ⊢ P * bar` is one direction only (`AssertBarrierSpatial`).
- Lock exclusivity is displayed with constant processors `i`, `j` and the
  premise "k active, k ≠ i, k ≠ j".
- Write collapse is bracketed `(W(e,f,e') ⊲ W(e,f,e'')) ⊲ bar_f`.
- Points-to to write has the premise "f denotes an active processor".
- The two cell rules: the disequality guard appears on both sides of the
  first; the second is one direction only.

Also check the two sentences of prose around the figure:

- the list of what is omitted (rules for `∧`, `∨`, quantifiers,
  substitution, equality, and distribution of `*` and `⊲` over `∨` and
  `∃`). Is anything else omitted that is not standard? I count the boolean
  oracle `AssertPure`, `AssertPureCases` and the right-hand pure-conjunct
  rule as omitted without mention.
- the closing paragraph's informal glosses of the barrier, lock, collapse
  and cell rules.

## 2. Figure "The dissertation's derived rules in the form derived in the repaired calculus" (`app:derived`)

Sources: `OwnedPointsToRules.v`, `OwnedFenceExamples.v`,
`OwnedAlternativeRules.v`. The figure uses the single judgment of the main
text, which is the disjoint mode.

| Displayed rule | Theorem |
| --- | --- |
| LOAD-P | `owned_derive_load_points_to` |
| STORE-P | `owned_derive_store_points_to` |
| FENCE-G | `owned_derive_fence_after` |
| FENCE-B | `owned_derive_fence_backward` |
| LOCK-G | `owned_derive_lock_after` |
| LOCK-B | `owned_derive_lock_backward` |
| UNLOCK-G (invariant `emp`) | `owned_derive_unlock_after_empty` |
| UNLOCK-B (invariant `emp`) | `owned_derive_unlock_backward_empty` |
| LOCKED | `owned_derive_locked_wrapper` |

Please confirm for each: the pre- and postcondition, the bracketing of
`P ⊲ ((lock_i * J) ⊲ bar_i)`, the operand order of `P * lock_i` in the
unlock rules, and the side conditions. For LOAD-P I display the single side
condition `x ∉ fv(J, e, e', P)`. LOCKED's second premise is displayed as a
semantic entailment `A ⊲ bar_i ⊨ J * Q`.

## 3. The rewritten paragraph in `calculus.tex` ("What became of the derived rules")

It now describes the rule families informally before giving their status:

- LOAD-P and STORE-P are the load and store axioms restated for the
  all-processor points-to.
- Rules ending in -G take an arbitrary precondition and append the
  command's effect; rules ending in -B are the backward forms from an
  arbitrary postcondition.
- LOCKED and ATOMIC give a specification to a body run between acquiring
  and releasing the lock.

Please check these against the dissertation's own section "Derived and
Alternative Axioms and Inference Rules". Two specific questions:

1. Is the description of ATOMIC fair, given how the original differs from
   LOCKED? The figure displays only LOCKED.
2. The paragraph says LOAD-P and FENCE-G are derived "exactly as the
   dissertation displays them". That was in the previous draft and you
   passed it; I repeat it only because the surrounding text changed.

## Report

A short file in `review/` listing each discrepancy with its location and a
suggested replacement, or a statement that the figures agree.
