# Necessity targets, before proofs

A and B pass at `50f1dbb`. This is the next independent batch from
`paper-strengthening-requests.md`. No semantics or calculus change is
proposed.

1. **C1 diagnostic/refutation.** On exactly two active processors,
   `lock(1) * lock(2)` has resource models: its two blocked sets are
   disjoint. Their union blocks both processors, so no owned environment
   can contain such a local resource. Test that, with the one-cell fragment
   invariant `C(2,7)`, the overlap specification
   `{lock(1) * lock(2)} unlock(1) {false}` is nevertheless valid. This would
   refute the requested universal claim even with two processors, a
   fragment invariant, and a satisfiable precondition. It would show why
   any replacement needs an admissible, enabled release environment, not
   just assertion satisfiability.
2. **C2.** Reuse the inhabited, enabled release instance from
   `StrongTemporalCounterexample.v`, but retain only its temporal
   precondition and temporal postcondition. Prove that the unframed
   specification is DJ-valid and the temporally framed specification is
   not, with the variable condition satisfied.
3. **C3.** Let `J` be the printed all-processor `2 ↦ 7`. Prove that the
   `OwnedLock` derivation from emp is invalid in either mode: the acting
   processor is 1, and its postcondition requires processor 2's mark.
   Exhibit a free-lock start with the nonempty pool. This is already a
   counterexample to soundness without the fragment hypothesis; the
   longer acquire/release example is unnecessary.
4. **C4.** On the singleton domain `{1}`, with the fragment invariant
   `C(2,7)`, derive `lock(1); lock(1)` by spatially retaining the first
   acquisition's postcondition around the second. Exhibit a concrete
   free-lock start with that one-cell pool and show the specification is
   invalid. The second acquire remains physically enabled while its input
   environment has held phase, contrary to the action-transfer obligation.

For C3 and C4 the result will pair an `owned_derivation` with the negation
of its `owned_valid` conclusion, keeping the other standing hypothesis.
These establish necessity for the existing transfer rule and safety
definition. They do not establish that the chosen invariant fragment or
the weakened cell is the unique possible repair among different logics.

## Optional D1 target

Test INV alone with `J = false`, `P = emp`, `Q = false`, processor 1, and
`c = skip`. Its premise under the empty invariant has an unsatisfiable
precondition `false * (emp * lock(1))`, hence is valid. The conclusion
under invariant `false` has the inhabited precondition `emp * lock(1)`
and the impossible postcondition `false * lock(1)`. This is deliberately
a minimal logical counterexample; no inhabited premise is claimed. It
uses only the printed `valid_specification` and the exact INV schema.
