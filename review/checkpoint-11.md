# Checkpoint 11 — derivation soundness and retrying container

**The mode-indexed repaired calculus is proved sound, with operational
adequacy from derivations. Both container programs are derived inside it.**
This implements the four checkpoint-10 recommendations: omit SHARE, prove
EX with invariant freshness, track modes in the judgment, and state the
fragment and two-processor assumptions once on the soundness/adequacy
theorems. It also completes the requested retrying example and consolidated
comparison with the dissertation.

The starting point was `4fba0b3`. `OwnedSafety.v`, the invariant fragment,
assertion interpretation, operational semantics and previously proved rule
statements are unchanged. No new validity predicate, unapproved side
condition, assertion atom, FRAME-STM rule, or fence instruction was needed.

## EX and the judgment

[`owned_exists_valid`](../theories/OwnedExists.v) proves:

```text
J ⊨ᵐ {P} c {Q}       x ∉ fv(J,c,Q)
----------------------------------- EX
J ⊨ᵐ {∃x.P} c {Q}
```

It unpacks the witness and transports safety from the witness-updated stack
using `owned_safe_stack_agrees`. The extra `fv(J)` condition is exactly the
one proposed and accepted at checkpoint 10. There is no restriction on the
bound variable occurring in `P`, and no processor or invariant-fragment
hypothesis on this semantic rule.

[`owned_derivation`](../theories/OwnedCalculus.v) has 21 constructors:
SKIP, ASSIGN, ASSUME, ASSERT, LOAD, STORE, LOAD-ANY, STORE-ANY, FENCE, LOCK,
UNLOCK, SEQ, CONS, DISJ, CHOICE, LOOP, EX, FRAME-SP, FRAME-TM, CONC and mode
weakening. Ordinary rules work at either mode, UNLOCK at DJ only, FRAME-TM
at OV only, and weakening goes OV → DJ. There are no INV, SHARE or FRAME-STM
constructors.

No constructor takes semantic command validity or safety as a premise.
Semantic entailments remain in CONS and UNLOCK. LOCK and UNLOCK currently
use constant positive processor identifiers, as the existing transfer
theorems do; expression-valued lock schemas are an explicit remaining scope
limit rather than an unproved constructor.

## Soundness and adequacy

The principal theorems in `OwnedCalculus.v` are:

```text
owned_calculus_sound:
  invariant_fragment J → two_active_processors active →
  owned_derivation active J mode P c Q → owned_valid active mode J P c Q

owned_derivation_adequacy:
  invariant_fragment J → two_active_processors active →
  owned_derivation active J mode P c Q →
  [concrete free-lock start with pool ⊨ J and local ⊨ P] →
  execution ... → no abort ∧ [terminal postcondition/ownership decomposition]
```

The first is induction on the derivation tree, using the proved semantic
rules. The second instantiates the existing operational adequacy theorem.
There is no residual external-frame or mode condition and no finite-domain
hypothesis. Standing hypotheses occur once on each theorem, not in the rule
constructors.

One clarification to the checkpoint-10 assessment: no-abort for every finite
execution does **not** mean every prefix restores `J`. A prefix can stop
with the lock held, and a general terminal postcondition may retain it.
[`OwnedExecution.v`](../theories/OwnedExecution.v) now proves the stronger
client property where justified:

- `owned_execution_frame` follows a chosen initial external frame through an
  actual execution. It changes only by its own futures, without weakening
  safety's fresh-environment quantification.
- `owned_emp_derivation_restores` takes an `emp`-to-`emp` derivation and an
  initially lock-free frame. On termination it gives a free lock and a
  **spatial decomposition of the actual final memory** into a pool satisfying
  `J` and a future of that frame. This is not an unrelated existential heap.
- `owned_container_completed_restores` and
  `owned_retrying_container_completed_restores` instantiate this result for
  the concrete free-pool start with the foreign write.

The initial-frame condition is a premise of this more specific execution
corollary, not an added rule or soundness side condition. The ordinary
top-level adequacy theorem remains unchanged in shape.

## Deriving the examples inside the calculus

[`OwnedContainerDerivation.v`](../theories/OwnedContainerDerivation.v)
reconstructs checkpoint 10's program as an actual derivation tree. Its
`container_store_some_derived` uses EX to open the item's existential value;
there is no manual invocation of semantic validity under an existential.
`container_return_derived` uses FRAME-TM and then mode weakening. One outer
FRAME-SP carries the unrelated foreign write through the entire program.

[`OwnedDerivedRules.v`](../theories/OwnedDerivedRules.v) packages cell-only
LOAD/STORE, assignment from an entailment about the updated stack, a standard
while rule, and release from an impossible precondition. These are derived
from constructors, with no extra operational assumptions.

[`OwnedRetryContainer.v`](../theories/OwnedRetryContainer.v) adds a done
register separate from the loaded flag and derives this program:

```text
done := 0;
while done = 0:
  acquire(1);
  r := [f]₁;
  if r = 1:
    [f] := 0₁; release(1); done := 1
  else:
    release(1); done := 0

[x] := 9₁;

done := 0;
while done = 0:
  acquire(1);
  r := [f]₁;
  if r = 0:
    [f] := 1₁; release(1); done := 1
  else:
    release(1); done := 0
```

The invariant and foreign frame are unchanged:

```text
J = C(f,0) ∨ (C(f,1) * ∃v.C(x,v))
R = y ↦₂ 17
owned_retrying_container_derived: J ⊢ᴰᴶ {R} retrying_container_program {R}
```

The loop invariant is `(pre ∧ done=0) ∨ (post ∧ done=1)`. The take's failure
branch restores the empty-container invariant and releases before retrying.

The return proof uses spatial framing at acquisition: it retains the
private resource containing the history of `x`. A pool also owning `x` would
conflict with that resource, so the acquired pool must be in its empty
branch. Consequently the return's failure branch is unreachable; it is
derived from false. The successful return releases only after the actor's
buffer has drained, and its entailment completes both the flag and item
histories. No new invariant condition is involved. The original example
still exercises FRAME-TM; the retrying example demonstrates that spatial
ownership can give a stronger branch fact when that is useful.

The old 16 named entailment obligations are reused. New substantive
ownership entailments are `container_retry_acquire_entails` and
`container_retry_return_unlock_entails`, supported by two heap/domain
lemmas. Register-update and guard entailments remain short semantic proofs.
This is progress toward reusable derived rules, not a claim that assertion
entailment has become automatic.

## Non-vacuity and traces

[`OwnedRetryTrace.v`](../theories/OwnedRetryTrace.v) checks:

| Result | Exact scope |
| --- | --- |
| `owned_retrying_container_trace` | Complete 52-step successful execution from checkpoint 10's free, nonempty pool to the same final memory: `f=1`, `x=9`, actor buffer empty, foreign write pending, lock free. |
| `container_retry_empty_environment` | An admissible free-pool start with the empty container (`f=0`), empty local ownership, and the foreign pending write in the frame. |
| `container_take_failure_trace` | Ten-step failed take, including release and resetting done to zero. |
| `container_failed_iteration_retries` | Fifteen-step loop iteration returning to the same loop with a free lock and done zero. |
| `container_two_failed_iterations` | Thirty-step execution of two such iterations; foreign write remains pending and the lock is free at the iteration boundary. |
| `owned_retrying_container_all_runs_safe` | Every finite execution from the full-pool start is non-aborting; terminal executions have the postcondition/ownership decomposition, by adequacy from the derivation. |
| Both `*_completed_restores` theorems | Every completed execution from that start has a free lock and an actual restored invariant pool, with only a future of the original foreign frame left over. |

The successful trace uses the same eleven memory states as the old trace;
the additional assignment, guard, choice and loop steps do not change memory.
`owned_container_foreign_pending_throughout` checks the foreign buffer in all
eleven states. The failed trace adds only the empty-container memory and its
acquired version, whose foreign buffer is unchanged.

This remains safety and partial correctness. There is no termination or
fairness theorem; in particular, no producer is present in the two-failure
trace. The guarded-choice encoding inherited from the command language can
also select a false assumption and wait. The return failure branch is not
presented as an inhabited test.

## Consolidation and review boundary

[`notes/current-calculus.md`](../notes/current-calculus.md) records the
standing hypotheses, all rule differences, resource/compatibility/wand
repairs, mark interpretation, invariant restriction, unchanged machine,
remaining expression-valued-lock scope, and omitted rules in one place.
The README now leads with the current result. Earlier alternative safety and
calculus reports are explicitly historical; their original statements and
counterexamples remain available.

The meaningful remaining review is of this calculus and theorem scope,
especially EX, the absence of semantic-validity premises in constructors,
the loop derivations, and the final-memory relation in the restoration
corollaries. No unproved rule is hidden in the induction. Assertion
automation, expression-valued lock schemas, recursive predicates and the
Chapter 5 extensions are subsequent work, not outstanding cases of this
soundness theorem.

Validation: `make check` compiles the project and checks `WMLR.Audit` with
Rocq 9.3.0. The audit contains **683 declarations**, all closed under the
global context, including all **57** new named lemmas/theorems. There are no
admitted proofs or declared axioms in the new development.
