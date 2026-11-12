# Checkpoint 5 implementation — safety, adequacy, and acceptance tests checked

**Subsequent status:** [checkpoint 6](checkpoint-6.md) proves general LOCK
and UNLOCK, but refutes unrestricted FRAME-STM in disjoint mode. The
checkpoint-5 definition and results below are unchanged; its remaining-work
section records the state at that checkpoint.

**The approved definition is implemented, and all three fixed acceptance
tests pass.** The mark-only and externally blocked local futures remain in
the closure clause. No definition change was needed to pass the tests.
The two-processor assumption is the one approved after the proposal; no
finiteness assumption, new assertion atom, or changed entailment was added.

`make check` passed, including the independent proof-object check. All
**438** audited declarations reported `Closed under the global context`;
there are no added axioms or admitted proofs. This includes 27 newly
audited declarations. It is not a proof of full calculus soundness.

## The active target

[`OwnedSafety.v`](../theories/OwnedSafety.v) defines `owned_safe` and
`owned_valid` as the single active soundness target replacing the separated
protected/private path. The old predicates retain their historical meanings.
The assertion interpretation is still `persistent_models`.

The implementation follows the [approved proposal](checkpoint-5.md):

- One owned marked resource, a separate invariant pool, and `OverlapMode`
  or `DisjointMode`.
- Pool free with `J` established, or pool empty while the physical lock is
  held. Local, external, and split-token contexts are all admitted.
- A complete local lock token is required to release; it is not required
  just to be an admissible resource.
- Every recursive safety obligation quantifies fresh frames, pools, and
  phases. A particular program step keeps its exact input frame unchanged.
- The action determines when the pool can change and which marks the local
  successor may gain. Ordinary and structural steps cannot add marks;
  fence, acquire, and release can add only their actor's mark.
- The pool/local footprint cannot grow. Successor disjointness is checked
  in disjoint mode and follows from this bound and input separation.
- Every generalized local future is covered, including the reflexive
  future. The terminal postcondition is independent of whether an
  environment happens to exist.

[`ProgramSteps.v`](../theories/ProgramSteps.v) labels non-flush program
steps without changing the machine. `program_step_erases` and
`step_program_or_flush` prove the connection in both directions. A flush
nested under sequence or parallel composition is still a flush; an
assumption or fence that leaves physical memory unchanged is still a
program step.

## Closure, modes, and adequacy

| Obligation | Checked result |
| --- | --- |
| Same-index closure under every existing resource future | `owned_safe_future` |
| Mark-only extension, with no physical flush | `owned_safe_mark_extension` |
| Safe weakening of the step index | `owned_safe_index_mono` |
| Actual flush attributed with the pool and other component fixed | `owned_environment_flush_attribution` |
| Exact empty frame preserved through actual execution | `owned_empty_frame_flush`, `owned_execution_empty_frame` |
| Disjointness preserved by the successor footprint bound | `owned_update_preserves_disjoint` |
| Overlap-mode validity implies disjoint-mode validity | `owned_valid_overlap_disjoint` |
| Partial correctness with no leftover mode/frame premise | `owned_valid_adequacy` |

The adequacy theorem in [`OwnedAdequacy.v`](../theories/OwnedAdequacy.v)
starts with a concrete free-lock memory spatially composed from a pool
satisfying `J` and an owned resource satisfying `P`. It instantiates the
external frame to `empty_resource_value` internally. For every finite
actual execution, the last state cannot abort. If terminal, the actual
memory splits into a returned pool and an owned resource satisfying `Q`.
The pool satisfies `J` when free; otherwise the complete lock token is
local and the pool is empty. Neither mode leaves a frame condition for the
client to discharge.

`invariant_fragment J` is explicit on the execution/adequacy results,
because flush attribution requires a buffer-free pool. The client theorem
also states `two_active_processors active`. This is an ordinary hypothesis
(`exists i j, active i /\ active j /\ i <> j`), not an axiom or an additional
resource-validity filter. The foundational closure and mode lemmas do not
need it. The underlying empty-frame simulation is in fact more general.

One placement detail: the release-recomposition helper also uses that same
approved processor hypothesis to distinguish a locally held token from a
free machine. This is exactly the singleton ambiguity already diagnosed,
not an additional restriction on the model. The fixed two-processor
donation acceptance theorem has no extra premise.

The execution proof uses the total finite trace length as a sufficient
bound on program steps. Flushes are handled by closure and index weakening,
not by an existential reallocation of pending writes. No fairness or
termination theorem is claimed.

## The three fixed acceptance tests

All statements and witnesses are in
[`OwnedAcceptance.v`](../theories/OwnedAcceptance.v). The original
[acceptance requirements](checkpoint-5-acceptance.md) remain the reference.

### 1. Donation distinguishes the modes

For `J = emp or C(x,7)`, the ordinary contract

```text
{lock(1) * C(x,7)} release(1) {emp}
```

is proved valid in disjoint mode by `owned_disjoint_donation_valid`, and
invalid in overlap mode by `owned_overlap_donation_invalid`.

The positive theorem quantifies over all disjoint external frames and all
generalized local futures. The negative proof supplies the fixed frame
`C(x,5)` and a real release from a local `x = 7` cell. Any local `emp`
successor would expose the frame's value 5 in the recomposed machine,
contradicting its actual value 7. The proof excludes all possible successor
pool/resource witnesses. It does not accept the forged stale-value
specification in either mode.

### 2. Foreign completeness is rejected in both modes

`owned_foreign_barrier_invalid` quantifies over the mode and proves

```text
not valid {emp} acquire(1); release(1) {bar(2)}
```

under the nonempty invariant `C(x,7)`. Its initial local resource has no
marks, and the external frame has a pending processor-2 write to a
different address. The proof follows the actual acquire, structural
sequence, and release steps without flushing. The three successor mark
budgets exclude mark 2 in every allowed final local resource.

Choosing the reflexive future at these obligations is legitimate because
safety universally quantifies over all futures. Adding mark-only futures
does not allow the implementation to choose a more convenient future and
escape this execution.

### 3. The other thread's lock does not prohibit a private store

`owned_holder_skip_valid` and `owned_private_store_valid` prove the two
component specifications. They actually hold in both modes, although the
acceptance target only required disjoint mode.

`owned_foreign_holder_store_witness` supplies one common machine with a
nonempty protected cell owned by processor 1 and a separate private cell
owned by processor 2. The pool is empty and processor 2 is physically
blocked. Both thread views are admissible. Its store nevertheless issues,
as specified by `PrimitiveStore`, and both successor views are admissible
with the owner resource exactly unchanged.

`owned_foreign_holder_both_safe` proves safety for every index, including
the storing thread's postcondition after the step. This establishes the
requested component safety and concrete interaction. It does not assume or
prove the general parallel-composition rule.

## The three additional regressions

- **Externally blocked local flush:** `owned_blocked_local_future_regression`
  constructs an actual generalized future that flushes the private
  processor-2 write. Safety covers that future. The theorem also proves
  that the corresponding processor-2 machine flush is impossible while
  processor 1's token remains in the frame. The approved over-approximation
  therefore survives the concrete test unchanged.
- **Double acquisition:** `double_acquire_stuck` gives a real two-step
  execution of `acquire(i); acquire(i)` to the second acquire, starting
  free with the actor's buffer empty. With two distinct active processors,
  that residual instruction cannot abort and has no machine successor,
  including no flush successor. `owned_held_reacquire_safe` proves its
  safety for every index and any postcondition when the complete token is
  local. This is the expected partial-correctness treatment of waiting;
  a second invariant transfer cannot occur.
- **Split token:** `owned_split_token_not_vacuous` admits the checked
  three-processor context whose two components block `{2}` and `{3}`.
  An `assert false` on processor 1 is proved unsafe in that context.
  Incomplete local tokens do not hide real faults through vacuity.

## Remaining work

No new derivation calculus has been introduced. The concrete contract
proofs above are the required acceptance tests. General acquisition and
release rules for arbitrary fragment invariants remain to be proved,
followed by the frame reconstruction argument using fixed program-step
frames, the mark budget, and the footprint bound. The general FRAME-TM,
spatial/strong-temporal frame, and concurrency theorems are still open for
`owned_safe`, as is the full container derivation.

This is a useful review boundary: the definition now has operational
adequacy and passes its agreed positive and negative tests, without
weakening either closure case flagged by the reviewer. The next risk is
the general reconstruction theorem, not the existence of these examples.
