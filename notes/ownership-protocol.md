# Ownership protocol for release

> **Historical checkpoint.** This report describes an earlier development
> stage. Its alternative safety/calculus design is superseded by
> `OwnedSafety.v` and `OwnedCalculus.v`; any statements about remaining
> soundness work belong to that stage. Reused resource lemmas and checked
> counterexamples retain their meanings. See the
> [current calculus and complete comparison](current-calculus.md).

This is a checked, bounded implementation of the ownership-transfer repair.
It is separate from `persistent_valid` and the printed safety predicate.
It does not establish the full dissertation soundness theorem.

The subsequent [private-resource extension](private-ownership.md) now carries
separate private resources through acquisition/release and proves a
post-release private load. The limits below describe this original prototype;
the extension still leaves concurrency and temporal external frames open.

## What changes

The assertion grammar in `Assertions.v` and the entire interpretation
`persistent_models` are reused exactly. In particular, there is no new
`held_J` assertion and no reinterpretation of the existing `Lock` atom.
The machine's ordinary transitions, aborts, and buffer flushing are also
reused exactly.

The change is in the safety semantics and the judgments. A specification
has an owning processor and an initial/final ownership phase:

```
J |- {Closed; emp}          lock_i    {Open; lock_i * J}
J |- {Open; lock_i * J}     unlock_i  {Closed; emp}
```

These phase labels are specification indices, not assertion constructors.
Both primitive rules are proved for arbitrary assertions `J`, including
heap assertions and future-aware wands.

`protocol_environment` has one protected region and a spatial external
frame. In `Closed`, the region is the shared pool, its lock state is free,
and it satisfies `J`. The command's visible local memory is empty. In
`Open`, that same region is the owner's local memory and contains its lock
ownership; `J` need not currently hold. There is no additional unconstrained
shared fragment in the open state. The external frame is lock-free, spatially
disjoint from the region, and may contain buffered writes.

Acquisition exposes the existing region as `lock_i * J`. Release extracts
the `J` witness from that spatial assertion and returns it to shared ownership.
The lock atom has no heap or buffers, so removing it preserves exactly the
protected heap and buffers, up to pointwise equality. The spatial frame stays
disjoint. This eliminates the leftover-shared-fragment problem from the older
safety semantics.

The phase annotations do not filter machine execution. `protocol_safe`
quantifies over every ordinary operational step and requires a suitable
post-step environment. A proof cannot assume that a bad release is disabled.
Every residual protected domain must lie within its preceding domain;
the frame must evolve by an actual sequence of flushes.

## Checked proofs

- `protocol_environment_flush` splits every whole-machine flush into actual
  component flushes and preserves ownership and the closed invariant.
- `protocol_acquire_valid` and `protocol_release_valid` establish full
  step-indexed validity, including arbitrary intervening flushes and spatial
  external frames.
- `protocol_store_cell_valid` proves buffered writes while the region is
  owned. `protocol_fence_cell_valid` obtains the new points-to assertion only
  when the owner's buffer is empty.
- `protocol_release_buffered_cell_valid` uses unlock's existing empty-buffer
  execution premise to restore a single-cell invariant from its temporal
  buffered-write assertion. An extra fence immediately before unlock is not
  required for this rule.
- `ownership_calculus_sound` proves soundness by induction on a small
  derivation system containing skip, acquire, release, cell store/fence,
  buffered cell release, and sequencing. Its constructors have no safety
  or specification-validity premises.
- `protocol_execution_no_abort` and `protocol_execution_closed_post` connect
  the new safety predicate to ordinary machine executions. A closed terminal
  state contains a shared region satisfying `J` and has a free global lock.

The general transfer proofs do not assume finitely many processors, classical
logic, choice, or functional/propositional extensionality. The cell-construction
lemma uses processor-membership cases obtained from the preexisting points-to
model's universal barrier assertion, rather than adding a decidability axiom.

## Positive and negative examples

`OwnershipExamples.v` uses exactly two processors and the heap invariant
`1 |-> 7`. It derives:

```
lock_1;
[1] := 9; fence_1;
[1] := 7; fence_1;
unlock_1
```

`restore_program_trace` exhibits a 13-step execution, including both flushes.
`intermediate_invariant_broken` checks that the protected payload fails the
invariant after the first write has flushed. `restore_program_no_abort`
covers every execution from every admitted initial spatial frame, and
`restore_program_all_terminating_runs` proves that every terminating execution
ends with heap cell 1 equal to 7 and the lock free. These are partial-correctness
results; no fairness or termination assumption is introduced.

`restore_using_unlock_fence_derivable` derives the version omitting the last
explicit fence. `pending_restore_then_unlock` exhibits the final flush and
release when execution reaches unlock with the restoring write still pending.

`unrestored_release_invalid` checks the negative case: with a protected value
of 9 and target invariant `1 |-> 7`, release is operationally enabled but the
proposed open-to-closed specification is invalid. Thus restoration is an
actual proof obligation, not an assumption hidden in the execution model.

## Limits and next obligations

This is a single-owner protocol with **spatial external frames**. It does not
yet support temporal external frames, a separate private payload `P` carried
through the closed boundary, or a concurrent observer's view while another
processor owns the region. The assertion language still contains all its
temporal connectives; the restriction is on the external framing relation.

The next steps are to add a separate private component, prove the transfers
and rearrangements with it, and derive a general whole-critical-section rule.
Concurrency then needs compatible owner/non-owner views of the same region.
The printed invariant rule, general spatial/temporal frame inference rules,
and compatibility with the earlier `persistent_derivation` calculus remain
unproved. This file records a separate candidate semantics, not a theorem
that all earlier valid triples remain valid in it.

The new files and their principal theorems are imported by `Audit.v` and
checked by `make check`.
