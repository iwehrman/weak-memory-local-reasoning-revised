# Recovering FRAME-TM with separate protected assertions

**Transfer extension:** [ownership-transfer.md](ownership-transfer.md) now
proves withdrawal of protected cells into private ownership at an owner
fence or unlock, and identifies a checked obstruction to unrestricted
donation in the reverse direction. FRAME-TM still checks with the relaxed
combined-footprint bound.

`separated_FRAME_TM` recovers the printed form of the private temporal frame
rule in a new, explicitly separated ownership model:

```text
J |- {P} c {Q}       mod(c) intersect FV(R) = empty
-------------------------------------------------
J |- {R ; P} c {R ; Q}
```

Here `;` is the dissertation's left-to-right temporal assertion connective
(`triangleleft` in FRAME-TM), not command sequencing. There is no new
restriction on `R`, no requirement that its buffers be empty, and no
finite-processor hypothesis. The invariant remains outside the private frame.

This is a semantic frame theorem for arbitrary `separated_closed_valid`
premises, not just for the examples or the bounded derivation system.
`separated_temporal_frame_valid` also holds across arbitrary open/closed
phase boundaries, with the protected assertions unchanged by framing.

The result is not soundness of the dissertation's entire calculus. The
ownership discipline has changed: protected and private assertions are kept
in separate proof compartments, including while the lock is held. Spatial
framing and concurrency have not yet been integrated into this model.
Protected-to-private withdrawal is now supported; general donation remains
open. Existing results under the older
validity predicates keep their original meanings.

## What changes in judgments

The assertion grammar and `persistent_models` are unchanged. Open judgments
now have two assertion positions. Schematically, write `{S | P}`, where `S`
describes the protected compartment and `P` the private compartment:

```text
Closed {emp       | P} lock(i)   Open   {lock(i) * J | P}
Open   {lock(i)*J | Q} unlock(i) Closed {emp        | Q}
```

Closed judgments hide the protected pool behind `J`, just as before. Their
protected assertion is interpreted on the empty visible view. Open judgments
interpret the protected assertion on the held pool. These are the existing
`protocol_region` and `protocol_assertion` definitions. The protected
interpretation uses full resources; private assertions are always evaluated
on generalized resources with their actual completeness marks.

`S | P` is a pair of judgment positions, **not** an abbreviation for `S * P`.
Consequence operates on each position separately. In particular, an
entailment from `J * emp` to `J * barrier(2)` cannot move completeness from
the protected position into the private position. Completeness within the
protected compartment can still be used by protected heap proofs.

The lock token remains in the protected compartment; private resources and
their external temporal histories are lock-free. The machine's lock,
unlock, load, store, and flush transitions have not changed.

## Why framing now works

Both phases use the same decomposition of the physical machine:

```text
(external history ; private) * protected
```

Acquisition and release change the protected phase and view without moving
the protected heap into the private temporal chain. Framing changes a local
`P` to `R ; P`; temporal associativity moves `R` into the external history
when applying the source safety proof. Generalized-future splitting recovers
the retained `R` afterward. Assertion flushing closure and register agreement
preserve its meaning through all intervening steps.

The protected component supplies no completeness marks to that temporal
composition. Conversely, a private barrier earned by a real fence requires
the issuing buffer to be empty in the whole machine. This includes any
earlier private history on that processor. Hence pending temporal frames are
allowed, but their writes must actually flush before such a fence completes.

`separated_execution_no_abort` and `separated_execution_post` connect this
safety predicate to all finite executions of the existing machine. Safety
does not imply termination or fairness.

## Checked positive and negative examples

1. **Pending foreign write across a protected update.** The invariant is
   `x -> 7`; processor 2 has `y := 17` buffered at a disjoint location.
   Processor 1 acquires, writes 9 to `x`, fences, restores 7, and releases.
   `separated_restore_derivable` uses FRAME-TM itself to retain the pending
   private history. `separated_restore_all_runs` proves safety and the
   restored invariant/private postcondition for all executions. The checked
   eleven-step `separated_restore_pending_trace` leaves processor 2's write
   pending. Other executions may legitimately flush that write.

2. **A real fence earns the stronger postcondition.** With the same initial
   write pending on processor 2, FRAME-TM gives
   `{R ; emp} fence(2) {R ; barrier(2)}`. The two-step example flushes the
   write and then fences. `separated_pending_fence_all_runs` checks all
   executions and terminating postconditions.

3. **The false source specification is rejected.**
   `separated_roundtrip_cannot_import_barrier` proves
   `not {emp} lock(1); unlock(1) {barrier(2)}` under the nonempty invariant.
   A pending external processor-2 history supplies a concrete countermodel.
   This is the source specification that was derivable in the regional
   model. It is now semantically invalid and, by calculus soundness, not
   derivable. The repair does not suppress its pending-write frame.

4. **Overlapping private history and a register-changing load.** A private
   location has historical value 5 and current value 11; the protected
   invariant occupies another location. FRAME-TM retains the older value
   while the load reads 11 into a register. A concrete initial model and
   all-execution safety/postconditions are checked. The load rule has the
   ordinary freshness conditions for the invariant and protected assertion;
   framing additionally checks the displayed `mod/FV` condition.

`separated_calculus_sound` proves soundness of a bounded calculus with
protected derivations, private fence/load, sequencing, componentwise
consequence, and FRAME-TM. The protected constructor requires an actual
derivation in the existing bounded ownership calculus. No constructor takes
program safety or validity as a premise.

## Cost and remaining work

The private temporal history must be spatially disjoint from the protected
compartment throughout the proof. It may overlap newer private heap values,
as the load example demonstrates. Historical assertions about protected
memory belong in the protected assertion, not in a private frame carried out
of the critical section.

The initial checkpoint prevented either compartment's footprint from
growing. The transfer extension replaces that restriction with a bound on
their combined footprint and reproves framing. A known protected cell can
now be retained privately on release, using an owner-specific flushed-cell
assertion. There is still no joint consequence rule that merges the two
assertion positions. A general return of private cells to the protected
pool conflicts with retained overlapping history; see the positive transfer
rules and negative result in [ownership-transfer.md](ownership-transfer.md).

The regional theorem allowing external history to overlap the shared pool
still belongs to the earlier model. We have not combined that capability
with the recovered private FRAME-TM theorem. Likewise, the existing spatial
and parallel results have not been silently imported into separated validity.

Next work should resolve donation's overlapping-history obstruction and
integrate spatial framing/concurrency while preserving the rejection of
foreign-barrier import. General heap expressions, assignment, loops, and full corrected
soundness also remain open. All new principal results are audited in
`Audit.v`; there are no added axioms or admitted proofs.
