# Ownership withdrawal, temporal framing, and the donation obstruction

**Subsequent experiment:** [retired-ownership.md](retired-ownership.md) resolves
the overlapping-heap case in a separate buffer-free interpretation, with
bidirectional transfer and FRAME-TM. It changes the meaning of temporal
`emp`; it does not invalidate the obstruction below in the previous model.
A flush-simulation bridge is checked, but the combined buffered retirement
model is still open.

The separated calculus now supports taking a protected cell into private
ownership, including at unlock without an added fence instruction. Its
general FRAME-TM theorem still has only the original variable condition.
The proof system and safety semantics both changed; this is not merely a
new interpretation of unchanged ownership rules.

The reverse direction has a checked structural obstruction. An earlier
private heap value can overlap the cell being donated to the protected
pool. Even with all buffers empty, the current spatial pool cannot coexist
with that retained history. A positive reassembly lemma covers histories
disjoint from the donated cell, but it is not a general donation rule.

## The returned cell assertion

Ordinary points-to includes completeness for all active processors. Returning
that assertion on a transferred cell would falsely constrain unrelated
pending temporal history. `withdrawal_as_all_processor_cell_invalid` checks
this failure even if processor 1 executes an actual fence during transfer.

The withdrawal rule instead returns this abbreviation in the existing
assertion grammar:

```text
processor_cell(i, x, v) = write(i, x, v) ; barrier(i)
```

It describes exactly one flushed heap cell, with value `v` at `x`, empty
buffers and a free local lock component. It requires completeness only for
processor `i`; any additional marks must already be justified by the private
resource. `processor_cell_shape` proves the physical shape and required mark.
The rule constructs a resource marked only by the previously private marks
plus `i`, copying no protected completeness.

This changes the ownership-transfer contract: the private cell is not
returned as ordinary all-processor points-to. It remains readable after
release, as `separated_load_processor_cell_valid` and the examples prove.
`processor_cell_does_not_imply_all_processor_cell` gives a checked witness
that the synchronization difference is real. No assertion constructor was
added; the new notation is an abbreviation.

## The proved transfer rules

Using the separate protected/private judgment positions from
[separated-temporal-framing.md](separated-temporal-framing.md), the rules are:

```text
Open {lock(i) * (S * (x -> v)) | emp}
    fence(i)
Open {lock(i) * S             | processor_cell(i,x,v)}

Open {lock(i) * (J * (x -> v)) | emp}
    unlock(i)
Closed {emp                  | processor_cell(i,x,v)}
```

The first leaves the lock held and the protected remainder satisfying `S`.
The second restores invariant `J`, releases the lock, and retains the cell
privately. It uses unlock's existing issuing-buffer guard, so an extra fence
instruction is unnecessary. Both rules admit arbitrary private temporal
frames via FRAME-TM. In particular the rule does not require other
processors' histories to have drained.

The safety definition now bounds the **combined** private/protected
footprint: either output compartment may contain locations from either
input compartment, while no new locations may appear. Each machine step
must still recompose with every external temporal history. The FRAME-TM,
adequacy, calculus-soundness and prior counterexample-rejection proofs all
check with the relaxed bounds.

For withdrawal, the cell was spatially disjoint from the external history
before the move. The physical repartition is therefore possible. The
issuing-buffer guard ensures that adding the issuing processor's
completeness mark to private state imposes no false ordering claim.

## A nonempty withdrawal and subsequent private read

`release_take_and_read_all_runs` checks this example:

- The lock is held by processor 1. A known protected cell contains 7.
- The invariant permits either an empty pool or that cell.
- Processor 2 has a write of 17 to a different address still pending.
- Processor 1 releases the lock while retaining the cell privately, then
  loads the cell into register 0.

All finite executions are non-aborting. Every terminating execution has a
free lock, register 0 equal to 7, the retained private assertion and an empty
protected pool. The three-step trace leaves processor 2's write pending.
The variant transferring at an explicit fence before release also checks.

The precondition is an **open, known-present branch**. This is not yet a
complete concurrent container-removal proof: the program that acquires the
lock and discovers which invariant branch holds has not been verified here.
The initial held state has a concrete machine model, and the transfer
proof does not assume its desired safety conclusion.

## Why unrestricted donation still fails

Consider a private cell currently holding 7 with an older value 5 in its
external temporal history. Initially this is a valid temporal composition:
the current value overrides the past value. The protected compartment holds
only the lock token. All buffers are empty.

If the current cell is moved into the protected compartment and private
state becomes `emp`, the old value 5 must remain in the history. The resulting
decomposition would require:

```text
(history containing x -> 5 ; emp) * protected cell x -> 7
```

Both spatial sides contain `x`, which is impossible. Fences cannot erase a
retained heap history. `retained_history_prevents_donation` proves this as
an environment-level impossibility, independently of the particular command
or the footprint bounds. `owner_fenced_donation_invalid` supplies a concrete
enabled fence and rejects the proposed donation specification under the
relaxed safety semantics. This is not simply a missing derivation rule.

There is also a positive replacement:
`history_disjoint_donation_recomposes` transfers a private points-to cell
into the protected assertion if the external history is spatially disjoint
from it. `donation_without_history_recomposes` supplies a concrete nonempty
instance. This is a reassembly lemma, not `separated_valid`, whose universal
history quantification also includes overlapping histories. No extra history
restriction has been silently added to FRAME-TM or to the general validity
predicate.

## Remaining design choice

Full bidirectional ownership transfer remains open. Preserving unrestricted
FRAME-TM while supporting donation appears to require distinguishing
remembered historical values from current ownership in the resource model.
Alternatively, a separate donation discipline could explicitly restrict
which histories may be retained. The reassembly lemma identifies a sufficient
condition for that restricted approach, but neither design has yet been
integrated into a complete calculus.

Spatial framing, concurrency, general expression-based heap operations,
loops, and full corrected soundness also remain open. This checkpoint adds
no axioms, admitted proofs, or finite-processor assumption.
