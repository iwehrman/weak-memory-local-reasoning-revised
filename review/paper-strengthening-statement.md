# Strengthening targets, before proofs

Responds to `paper-strengthening-requests.md` at `1aad6bb`.
The current calculus, assertion interpretation, and safety predicate are
unchanged. The paper remains the reviewer's file to edit.

## A. Original local counterexamples

1. Reuse the pending-write/barrier witness, but state satisfaction with
   `ConcreteAssertions.models` and composition with `Separation.temporal`.
   Transcribe the indexed generalized flush and its reflexive transitive
   closure from Definition 6, without the extra mark-only steps of the
   repaired future relation. Prove an actual one-flush counterexample and
   hence refute closure under that original order.
2. Under invariant `Pure false`, prove
   `~ valid_specification two_processors false (lock 1) (unlock 1) emp`.
   Supply the concrete held-lock precondition, an admissible printed
   environment, and an enabled release; rule out every successor
   environment. No new safety predicate is involved.

Definition 6 was rechecked in the original `dissertation.tex`, blob
`ac4c24370dc22b3ca0892294206c2c6ac138d993`, lines 1984–1991. Its indexed
step grows the mark set, includes the flushing processor, and performs an
actual indexed machine flush. Its order is the reflexive transitive
closure. The direction below is written `before -> after`.

## B. Eliminate the judgment's mode for unlock-free commands

Define `unlock_free` recursively: false for a primitive unlock, true for
the other primitives, conjunction over sequence/choice/parallel, and
recursive inspection of a loop body.

Targets, with arbitrary active domain and invariant:

```text
owned_derivation mode P c Q -> unlock_free c -> owned_derivation OV P c Q

owned_derivation OV P c Q -> unlock_free c

owned_derivation DJ P c Q -> unlock_free c -> frame_variable_condition c R
  -> owned_derivation DJ (R ; P) c (R ; Q)
```

The second target would explain the exact strength of the syntactic guard
for replaying derivations in this existing calculus. It is not a claim
that semantic overlap validity is equivalent to absence of unlock.
Soundness of the derived DJ frame rule then uses the existing fragment and
two-active-processor hypotheses, through `owned_calculus_sound`.

## Later targets

After reporting A and B, test C's proposed necessity statements in the
requested order. In C1, mere satisfiability of an assertion must be checked
against existence of an admissible environment: these are different
conditions in `owned_safe`. A counterexample to the proposed universal
statement is an acceptable result. C2–C4 will each pair the requested
validity or derivation with an explicit invalidity theorem. D remains
optional if premise validity in the printed model requires substantial
additional infrastructure.
