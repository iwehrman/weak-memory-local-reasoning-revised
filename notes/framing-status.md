# Spatial framing and the temporal repair

> **Historical checkpoint.** This report describes an earlier development
> stage. Its alternative safety/calculus design is superseded by
> `OwnedSafety.v` and `OwnedCalculus.v`; any statements about remaining
> soundness work belong to that stage. Reused resource lemmas and checked
> counterexamples retain their meanings. See the
> [current calculus and complete comparison](current-calculus.md).

The general semantic spatial frame rule is proved for `private_valid` with
closed entry. The work below proves temporal framing in a separate semantics
retaining completeness marks and identifies two transfer obstacles. The
subsequent [generalized regional model](regional-ownership.md) now proves
flushing, acquire/release, bounded calculus soundness, and temporal history
framing around the whole shared/private region. It also finds a stronger
counterexample: the unrestricted private temporal rule fails even for an
actually derivable closed-to-closed specification. Full corrected soundness
and frame/concurrency integration remain open.

## Spatial framing

`private_spatial_frame_valid` proves:

```text
J; Closed ⊢ {P} c {Q}; finish
mod(c) ∩ FV(R) = ∅
---------------------------------------
J; Closed ⊢ {P * R} c {Q * R}; finish
```

The source premise is ordinary semantic validity, not a special derivation
or a premise already containing the framed conclusion. The assertion `R`
can be arbitrary, including wands and pending writes. Closed entry makes its
resource lock-free; no separate purity, precision, empty-buffer, or
register-preservation condition is imposed. The command can acquire and
release the lock, and the final phase can be open or closed. Spatial
commutativity gives the displayed dissertation rule's left-frame orientation.

The proof moves the retained resource into the source specification's spatial
external frame. Each step splits that external frame's **actual** finite
flushing history, transports `R` across unmodified registers, and rebuilds the
larger ownership region. Region domains remain bounded. It works at every
safety index and for every admissible external spatial frame.

`SpatialFramingExamples.v` reuses the existing critical section followed by a
private load. Its added resource has a pending processor-2 write of 17 to
address 3. The checked specification preserves that write assertion and the
load result 11 for every terminating execution. A 14-step concrete run flushes
the added write, restores the protected cell, releases the lock, and loads the
private cell.

## First temporal obstruction: lost completeness

At full resource completeness, `emp` implies a barrier assertion for an
active processor. Consequently the current `private_valid` validates
`{emp} skip {barrier(1)}`. This is a semantic specification; we do not claim
that it is derivable in `private_derivation`.

Let `R` describe a pending write on processor 1. Then `R ; emp` can hold: the
past component supplies the complete marks, while the empty future component
has no marks. But `R ; barrier(1)` cannot hold while the write remains pending.
The barrier's completeness requires the past buffer to be empty. `skip` is
already terminal and need not flush. `private_temporal_frame_counterexample`
checks the valid source specification, the ordinary variable side condition,
and the invalid framed specification.

Promoting each separated component to full completeness was sufficient for
spatial framing. It loses information needed to reconstruct a temporal split.
The assertion syntax and temporal connective are not the cause of this loss.

## A checked semantics retaining completeness

`TemporalSafety.v` defines `prefix_safe` and `prefix_valid`. Local resources
and external prefixes retain their generalized-memory completeness sets.
Validity ranges over every such well-formed local resource, including ones
without all completeness marks. The assertion interpretation is still
`persistent_models`; the machine steps are unchanged.

In this prototype, an environment decomposes as:

```text
shared * (external prefix ; local)
```

External prefixes evolve by generalized futures whose underlying memories
follow actual flushes. The ownership-domain bound and the invariant-or-locked
obligation are retained. The external relation is temporal, not the full
spatiotemporal relation. No equivalence with either older validity predicate
is claimed.

`prefix_temporal_frame_valid` proves the general left temporal frame rule
under only `mod(c) ∩ FV(R) = ∅` in this semantics. The proof uses temporal
associativity and future splitting, preserving the actual completeness sets.
Operational adequacy establishes no abort for every finite execution and the
marked local postcondition on termination.

The revised validity rejects `{emp} skip {barrier(1)}`.
`prefix_fence_valid` instead obtains the barrier from a real fence, using its
empty-buffer guard. `prefix_framed_fence_valid` permits an arbitrary past
assertion, including pending writes. The two-step pending-write example first
flushes and then fences; its safety and postcondition also hold for every
execution/terminating execution, respectively. No restriction to already
drained past assertions was introduced.

## Second temporal obstruction: history at a released address

Retaining marks alone does not repair shared ownership transfer.
`prefix_ownership_release_invalid` checks the proposed restored-invariant
release contract in the prototype above:

```text
J = cell(1, 7)
{lock(1) * J} unlock(1) {emp}
```

The lock is held and `J` is already true. An external temporal prefix contains
a historical copy of `cell(1, 7)`, overlapping the current owned cell. This is
a valid temporal composition, and unlock is enabled. After unlock, `J` must
move to the shared pool. Its cell would then have to be spatially disjoint from
the same cell in the retained history, which is impossible. The past has empty
buffers, so flushing cannot erase it. This is a decomposition failure even
when the invariant is restored, distinct from the earlier unrestricted
`{lock} unlock {emp}` counterexample.

## Checked transfer lemma for an alternative arrangement

The candidate arrangement puts temporal history before the combined ownership
region:

```text
history ; (shared * private)
```

The shared and private resources still separate spatially. Historical heap
values can overlap that region without being treated as another current
owner of its cells.

`release_marked_invariant` extracts a restored invariant resource while
retaining the owned region's completeness, without promoting it to full.
`temporal_history_release_transfer` proves an actual enabled unlock and
reconstructs the **same** temporal history before the restored pool. Its
premises are a lock-free past, the owned lock/invariant assertion, valid
temporal composition, and the operational empty-buffer guard for unlock.
It does not require disjoint history/protected heap domains or that all past
buffers be empty.

`overlapping_history_release_recomposes` applies this lemma to the exact
overlapping-cell example that the prototype's release rule rejects. This is a
positive transfer lemma, not yet an all-step release rule or a sound calculus
for the new arrangement.

## Next proof obligations

1. The generalized region definition, silent-flush preservation, acquire/release,
   and adequacy are now proved in `RegionalResources.v` and `RegionalSafety.v`.
   The checked temporal rule frames the whole region, explicitly including `J`.
2. Resolve the newly checked completeness-import obstruction. The unrestricted
   private temporal rule is false with the current transfer and consequence
   rules, so mixed rearrangement lemmas alone cannot establish it. Investigate
   separating protected completeness from private barrier claims; see
   [the new result and counterexample](regional-ownership.md).
3. Integrate spatial framing and heap operations in the chosen regional model,
   then port the critical-section/private-load and two-thread ownership examples.
4. Address general spatiotemporal environments and strong temporal framing,
   which are not established by the ordinary temporal frame theorem.

The current phase adds no assertion constructors, processor-finiteness
assumption, admitted facts, or axioms. All principal results, including the
negative ones, are included in `Audit.v`. The existing private and parallel
results keep their original, explicitly spatial semantics.
