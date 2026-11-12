# Flushing closure, primitive rules, and release obligations

> **Historical checkpoint.** This report describes an earlier development
> stage. Its alternative safety/calculus design is superseded by
> `OwnedSafety.v` and `OwnedCalculus.v`; any statements about remaining
> soundness work belong to that stage. Reused resource lemmas and checked
> counterexamples retain their meanings. See the
> [current calculus and complete comparison](current-calculus.md).

The full dissertation soundness theorem remains open. The current checkpoint
proves flushing closure for the entire assertion grammar under an explicit
change to wand semantics, and soundness of a bounded calculus containing
heap operations and lock operations. The original transcription and the
earlier repaired pointwise interpretation remain available unchanged.

## Exact changes and side conditions

| Area | Current checked treatment |
| --- | --- |
| Assertion syntax | Unchanged, including all three wands and both quantifiers. |
| Wand semantics | A wand must hold at every future resource obtained by generalized flushing or growth of completeness information. |
| Assertions without wands | Exactly the same meaning as in `repaired_interpretation`; this equivalence is proved. |
| Temporal compatibility | Retains the previous repair: conflicts are checked even for blocked processors. |
| Buffer overriding | Retains event-ordered overriding for the spatiotemporal frame relation. |
| Safety witnesses | Retains the previous requirement that private/shared residual domains stay within their old combined ownership region. |
| Assignment | Assigned variable must be absent from the invariant's free variables. The proved rule still has a pure postcondition; arbitrary assertion substitution is not implemented. The invariant can now be any assertion. |
| Load | Destination must be absent from the invariant's free variables. The proved base rule uses a constant address and value; freshness for general address/value expressions is still to be checked. |
| Store | A constant-cell base rule is proved, producing `Temporal (old points-to) (new leads-to)`. The general placeholder/frame forms remain open. |
| Skip, assume, assert, fence, lock acquisition | Checked with arbitrary invariants under the future-aware interpretation; no new syntactic side conditions. |
| Unlock | The arbitrary-invariant `{lock} unlock {emp}` contract fails. The proved replacement is restricted to a pure invariant `b` and requires `{lock AND b}` before release. |
| Consequence, disjunction, sequencing | Proved under the new interpretation with their usual premises. |

There is no new condition restricting users to wand-free assertions: the new
semantics has flushing closure for every formula. In the code, `persistent`
means preservation under generalized flushing, not permission to duplicate
an owned resource. The operational machine is unchanged. No finiteness
assumption on processors, choice axiom, or extensionality axiom is used.

## Why the pointwise wand failed

`FlushingCounterexample.v` uses exactly two processors and the formula

```text
TemporalWandRight (Pure false) (Barrier 1)
```

Initially processor 1 has a pending write. The temporal completeness condition
prevents that resource from preceding a barrier for processor 1. The pointwise
wand therefore holds vacuously. After an actual flush, the buffer is empty,
composition with the barrier becomes possible, and the wand requires false.
`pointwise_temporal_wand_not_flush_closed` checks this loss of satisfaction.
The issue comes from temporal completeness, independently of the stronger
compatibility guard.

`future_satisfies` changes only the wand clauses: before considering an
extension, quantify over every future of the current resource. The old
unstable witness is then rejected already before it flushes. The comparison
theorem `persistent_wand_free_unchanged` proves that atoms, conjunctions,
disjunctions, and quantified formulas without wands retain their meaning.

The three `persistent_*_wand_*adjoint` theorems prove the usual separating
implication adjunctions. Introduction uses flushing closure of the assertion
on the current resource; elimination uses the reflexive future. Thus the
new interpretation still supports the expected logical role of wands.

## What makes the closure proof work

`GeneralizedFlushing.v` keeps the identity of the processor that flushed.
A generalized flush grows the completeness set and marks that processor
complete, as in Definition 6. A separate marking step grows completeness
without changing the operational memory. This exposes the monotonicity
needed when distributing additional completeness information between parts.

The spatial and temporal decomposition theorems produce actual component
flushes, preserve the compatibility and completeness conditions, and construct
valid generalized-resource witnesses. When the future temporal component
flushes processor `i`, concatenation proves that the past buffer for `i` was
already empty; adding `i` to the future's completeness set is therefore valid.

`AssertionFlushing.v` proves preservation of every atomic assertion.
`repaired_future_model_laws` supplies all atomic and decomposition obligations
to the generic induction on formulas. These obligations are proved, not
postulated. `persistent_assertion_flushing_closed` handles generalized
resources, and `persistent_full_flushing_closed` supplies the closure needed
by safety under ordinary machine flush sequences.

## Checked calculus and concrete examples

`PersistentCalculus.v` defines derivations and proves `persistent_calculus_sound`.
Its constructors cover the rules listed above and have no program-validity
or safety premises. `persistent_derivation_no_abort` combines this soundness
theorem with operational adequacy, so its input is a derivation and a valid
initial environment rather than an assumed safety fact.

`PersistentExamples.v` checks the repaired wand, derives constant-cell load
and store specifications, and proves that a store's temporal postcondition
survives an actual flush overwriting the old heap value. It also derives a
lock/unlock round trip, exhibits its execution, and proves absence of faults
for all its finite executions from the supplied initial environment.

These results exercise the stronger compatibility guard for the base heap
and lock rules. A complete framed critical-section specification is not yet
proved, and the general frame and parallel rules remain open.

## Why general unlock still needs a design repair

`UnlockCounterexample.v` also uses exactly two processors. Let the invariant
be `false`, let processor 1 hold the lock, and let all memories be empty apart
from the blocking fact for processor 2. The precondition `Lock 1` holds and
the environment permits the invariant to be false while the lock is held.
Unlock is enabled. Afterwards the lock is free, and no decomposition can
make the false invariant hold. `arbitrary_invariant_unlock_invalid` proves
the contract invalid under the current safety semantics.

For a pure invariant `b`, the extra precondition `b` repairs this: the stack
is unchanged by release, so the invariant can be re-established over the
shared component. `persistent_unlock_pure_valid` proves the full rule,
including arbitrary admissible frames and intervening flushes.

For a heap invariant, merely writing `J * Lock` in the precondition is not
yet a repair theorem. The current environment still allows an unconstrained
shared region while locked; the proof must account for that region as well
as the private resource asserting `J`. The next design step is to make
protected-memory ownership explicit during lock acquisition and release,
and prove the corresponding transfers. A protocol in which protected state
is either shared with `J` established or owned by the lock holder is a
candidate. Its environment definition, contracts, and relation to the
dissertation's invariant rule remain to be worked out and checked.

A subsequent, separate [ownership protocol](ownership-protocol.md) now checks
acquisition and release for arbitrary assertions, without extending assertion
syntax or changing `persistent_models`. It proves a bounded calculus and a
heap-restoring critical section for all executions, using spatial external
frames and explicit open/closed judgment indices. General private payloads,
temporal frames, and the full invariant/concurrency rules remain open. The
counterexample and restricted release result above still describe
`persistent_valid`; that older validity definition has not been changed.
