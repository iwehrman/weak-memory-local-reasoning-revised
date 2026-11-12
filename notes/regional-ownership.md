# Ownership regions, temporal history, and completeness import

> **Historical checkpoint.** This report describes an earlier development
> stage. Its alternative safety/calculus design is superseded by
> `OwnedSafety.v` and `OwnedCalculus.v`; any statements about remaining
> soundness work belong to that stage. Reused resource lemmas and checked
> counterexamples retain their meanings. See the
> [current calculus and complete comparison](current-calculus.md).

**Subsequent result:** [separated-temporal-framing.md](separated-temporal-framing.md)
recovers private FRAME-TM in a new model that keeps protected assertions
separate throughout acquisition/release. The counterexample below remains
valid for the regional model; the separated model rejects its source specification.
The new result has an explicit ownership-transfer limitation.

The generalized ownership model now has checked flushing preservation,
acquire/release validity, consequence and sequencing, operational adequacy,
and a sound bounded calculus. It supports a temporal history rule around the
**whole shared/private region**. The unrestricted temporal frame rule around
only the private assertions is false in this model, even for a closed-to-closed
specification with an actual derivation.

This is a substantive limit of the proposed repair, not an unfilled proof
hole. Full corrected soundness and a combined spatial/temporal/concurrent
calculus remain open.

## Generalized ownership throughout both phases

`marked_region` in `RegionalResources.v` retains generalized resources and
their completeness sets throughout the protocol:

- Closed: the region is a spatial composition of a pool satisfying `J` and
  the private resource satisfying the local assertion.
- Open: the owner holds the entire region. The local assertion describes
  that region, including the lock token and protected/private payload.

An external temporal history precedes the combined region. It is lock-free,
may have historical heap cells overlapping the region, and evolves only by
generalized futures. The underlying histories follow actual buffer flushes.
There is no separate shared pool outside this temporal composition.

`regional_environment_flush` splits actual machine flushes through the
history, region, and closed pool/private decomposition. Assertion truth and
completeness survive through the existing generalized-future lemmas. The
owned region's domain still cannot grow.

`regional_acquire_valid` and `regional_release_valid` establish, for arbitrary
invariant and private assertions, all safety indices, all admissible temporal
histories, and intervening flushes:

```text
Closed {P} lock(i)   Open   {lock(i) * (J * P)}
Open   {lock(i) * (J * Q)} unlock(i) Closed {Q}
```

Acquisition preserves the region's completeness marks. Release extracts and
redistributes the marked payload; neither rule unconditionally promotes a
local resource to full completeness. The machine semantics is unchanged:
lock and unlock require the issuing processor's buffer to be empty.

`RegionalSafety.v` proves skip, consequence, sequence, and execution adequacy.
`RegionalCalculus.v` defines the corresponding derivation system and proves
`regional_calculus_sound`. No constructor has a program-safety premise. Its
consequence rule uses assertion entailments over all valid generalized
resources. There are no frame, load/store, loop, or parallel constructors yet.

## A temporal rule that does compose with ownership

`regional_history_frame_rule` proves the following boundary rule:

```text
J; Closed ⊢ {P} c {Q}; Closed
mod(c) ∩ FV(R) = ∅
initial whole memory is lock-free
------------------------------------------------------
{ R ; (J * P) } c { R ; (J * Q) }
```

The conclusion is an operational theorem: every finite execution is
non-aborting; every terminating execution has a free lock and satisfies the
displayed whole-memory postcondition. The premise is ordinary `regional_valid`,
so the theorem is not restricted to a special derivation. It keeps the
original marked witnesses until the final whole-memory interpretation.

The location of `J` matters. This does not prove the private rule
`J ⊢ {R ; P} c {R ; Q}`. In particular, when `J` is a points-to assertion,
its completeness forces any history *before the whole region* to have empty
buffers. Pending private writes may still occur inside `P` and `Q`.

The checked example combines:

- an external historical cell `1 -> 5`;
- the current invariant cell `1 -> 7`;
- a private pending write of 17 to address 3 on processor 2;
- acquisition and release on processor 1.

The historical and current cells overlap temporally. The pending write is
inside the private assertion `pending(2, 3, 17) ; emp`. The three-step run
acquires, advances the sequence, and releases without flushing that write.
`regional_overlap_pending_all_runs` proves safety and the full boundary
postcondition for all executions/terminating executions, including schedules
that do flush it. Thus the model handles the previous overlapping-history
release problem and preserves a pending private write in the same example.

## Why the unrestricted private temporal rule fails

The current points-to abbreviation implies completeness for every active
processor. Spatial composition unions completeness sets and permits the
same mark in both components. Consequently the following is a genuine
assertion entailment in the existing interpretation:

```text
cell(1, 7) * emp  entails  cell(1, 7) * barrier(2)
```

`cell_emp_entails_barrier` proves it without changing the underlying memory.
Acquiring the invariant exposes this marked cell. Consequence can assign its
processor-2 completeness mark to the empty private component, and release can
return that private barrier. `regional_roundtrip_barrier_derivable` therefore
constructs an actual derivation:

```text
J = cell(1, 7)
J; Closed ⊢ {emp} lock(1); unlock(1) {barrier(2)}; Closed
```

The source precondition has a concrete model (`regional_empty_private_initial`).
The derivation is valid in this candidate's environments. It does not claim
that processor 1 physically flushes processor 2: those source environments
already exclude a processor-2 pending prefix before the complete invariant.

Now apply the proposed private temporal frame rule with
`R = pending(2, 3, 17)`. The framed precondition `R ; emp` is satisfiable with
the invariant in a disjoint shared cell. A concrete three-step execution
leaves the processor-2 write pending. Its proposed postcondition
`R ; barrier(2)` requires that buffer to be empty. No admissible final
decomposition can hide the remaining write: the invariant's cell has empty
buffers, and the initially empty external history can only flush.

`regional_temporal_frame_counterexample` proves all three facts together:
the source derivation, the usual variable side condition, and invalidity of
the framed conclusion. Restricting the rule to closed entry *and closed exit*
does not avoid the counterexample. The machine has only two processors, so a
finite-processor assumption does not help either.

This refutes adding the unrestricted rule to this **repaired ownership
calculus**. It is not a claim that this particular derivation has already
been reproduced using only the dissertation's printed rules.

## Practical interpretation and next choices

Ordinary protected-resource transfer and retention of a private temporal
assertion still work: `regional_pending_roundtrip_derivable` returns
`R ; emp` unchanged, even with the other processor's write pending. The
problem is transporting synchronization information imported from `J`
across an arbitrary private temporal frame.

The boundary rule is a checked replacement with an explicit cost: it places
the invariant inside the framed region. It does not provide all uses of the
original hidden-invariant private frame rule. For a points-to invariant, its
outer history is already drained, as explained above.

The next repair to investigate is keeping protected completeness distinct
from private barrier claims, for example by retaining a separate protected
assertion in the open judgment instead of merging it into the private
assertion. A useful test is whether acquire/release can preserve arbitrary
private temporal frames while rejecting the derivation that exports
`barrier(2)` from this invariant. That is a proposed design direction, not
another proved theorem.

A processor-local restriction on pending frames would exclude this particular
counterexample, but its sufficiency has not been proved; overlapping history
and transfers of heap ownership are separate constraints. No such restriction
has been silently added. General spatial framing in the regional model,
spatiotemporal external contexts, heap operations, and concurrency still need
proofs. The earlier private spatial and parallel theorems retain their own
unchanged semantics.

The new files use the existing assertion grammar and interpretation, the
existing machine steps, and no axioms or admitted proofs. All principal
positive and negative results are in `Audit.v`.
