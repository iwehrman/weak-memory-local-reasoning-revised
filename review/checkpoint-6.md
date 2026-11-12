# Checkpoint 6 — general lock rules proved; FRAME-STM in disjoint mode refuted

**Subsequent status:** the accepted review dropped FRAME-STM from the active
target. [Checkpoint 7](checkpoint-7.md) proves FRAME-SP in both modes and
semantic FRAME-TM from overlap-mode validity, without changing definitions.
The checkpoint-6 results and reasoning below remain unchanged.

**The general LOCK and UNLOCK rules are proved for the approved invariant
fragment. The proposed unrestricted FRAME-STM rule in disjoint mode is
false.** This is a counterexample to the semantic rule itself, not just to
an auxiliary regrouping lemma. Development stopped at this finding, before
the general frame proofs and before parallel composition.

No safety definition, assertion interpretation, machine rule, or entailment
was changed. `owned_safe` / `owned_valid` remain the single target from
checkpoint 5. The counterexample uses two processors, three distinct
addresses, one release, and two pending writes. It needs neither duplicate
writes nor equal-address buffer overlap.

## General transfer rules

[`OwnedRules.v`](../theories/OwnedRules.v) proves the following rules, using
the existing assumption that two distinct active processors exist and that
`J` is in `invariant_fragment`:

```text
LOCK, in either mode:
    J ⊨ {emp} acquire(i) {(lock(i) * J) ; bar(i)}

UNLOCK, in disjoint mode:
    A ; bar(i) ⊨ J * B
    -----------------------------------------
    J ⊨ {lock(i) * A} release(i) {B}
```

The principal theorems are `owned_lock_valid` and `owned_unlock_valid`.
They quantify over all stacks, satisfying resources, safety indices, local
futures, and admissible external environments. `A` and `B` are arbitrary
assertions; the rule does not require them to be buffer-free or wand-free.
The guarded-fragment restriction applies to `J` alone.

LOCK re-marks the acquired invariant with the old local marks plus `i`.
With an initially unmarked `emp`, the acquired cells therefore have only
`i`'s mark. The result establishes the displayed barrier suffix; it does
not import foreign marks from the pool's full-completeness representation.

UNLOCK uses its entailment to choose the returned invariant and retained
postcondition. The former becomes the spatially separate pool; the latter
keeps the remaining ownership, including foreign pending writes. The
processor assumption is also used by the release helper to distinguish a
complete local token from a free machine, as recorded at checkpoint 5.
There is no additional domain assumption or new rule side condition.

## The FRAME-STM counterexample

All statements and witnesses are checked in
[`StrongTemporalCounterexample.v`](../theories/StrongTemporalCounterexample.v).

Write `Wa` and `Wb` for processor 2's existing write assertions, respectively
to distinct addresses `a` and `b`, both with value 0. They may describe a
pending or flushed write. Let `C` be the weakened, buffer-free cell
assertion `writer_points_to(c,0)`, where `c` differs from both addresses.
The concrete instance uses `a=1`, `b=2`, and `c=3`.

Set:

```text
J = C
Q = Wa ∨ (Wa ; Wb)
P = lock(1) * (C * Q)
R = Wb ∨ C
command = release(1)
```

The existing strong-temporal abbreviation is exactly:

```text
R ⋉ P  :=  (R * P) ∧ (R ; P)
```

The two conjuncts have independent existential witnesses. Nothing in this
abbreviation requires their `R` components or their `P` components to be
the same resources.

### The unframed premise is valid

`stm_unframed_release_valid` proves:

```text
J ⊨dj {P} release(1) {Q}
```

It is an instance of the general UNLOCK theorem above with `A = C * Q`.
The entailment `(C * Q) ; bar(1) ⊨ C * Q` is proved in the unchanged
interpretation. The small auxiliary proof here concerns these wand-free
formulas; it is not a restriction added to the UNLOCK rule.

The frame-variable condition is vacuous because release modifies no
registers. Thus both premises of the proposed FRAME-STM instance hold.

### The framed precondition is inhabited

Take a whole owned resource with:

- heap consisting of `c = 0`;
- processor 2's buffer `[a:=0, b:=0]`;
- processor 1's buffer empty;
- the complete lock token for processor 1;
- completeness mark 1 only.

The invariant pool and external environment frame are empty. This is an
admissible held-lock environment, proved by `stm_initial_environment`.
The assertion frame `R` below is an internal part of the precondition; it
is distinct from that empty external frame.

`stm_framed_precondition` proves that this resource satisfies `R ⋉ P`,
using these two decompositions:

| Conjunct | Resource satisfying `R` | Resource satisfying `P` |
| --- | --- | --- |
| `R * P` | Pending `Wb`, no heap | The token, `C`, and pending `Wa`; choose the first branch of `Q` |
| `R ; P` | `C`, no pending writes | The token, `C`, and pending `Wa ; Wb`; choose the second branch of `Q` |

For the spatial split, interleaving `[b]` and `[a]` may produce `[a,b]`.
Their footprints are disjoint. For the temporal split, the earlier `C`
is overridden by the identical later `C`, while the earlier buffer is
empty. Its result is the same whole resource.

These are `stm_initial_spatial_split` and
`stm_initial_temporal_split`. Their different witnesses are essential.

### The real release cannot establish the postcondition

`stm_release_step` proves the actual release transition. Processor 1's
buffer is empty, so release is enabled. It does not drain processor 2's
buffer: the final machine still has heap `c=0` and buffer `[a:=0,b:=0]`.

The successor pool must satisfy `J=C`, hence own `c=0`. Because the pool
is spatially separate from the remaining owned resource, every allowed
owned successor has **empty heap** and the same buffer `[a:=0,b:=0]`.
`stm_returned_local_shape` proves this for every possible successor split.

Such a resource cannot satisfy `R ; Q`:

1. The `R=C` branch needs a heap cell, but no heap cell remains owned.
2. In the `R=Wb` branch, `Wb` cannot be flushed, since that also needs a
   heap cell. It must be pending. Temporal composition then puts `b:=0`
   first in processor 2's buffer, contradicting the actual first write
   `a:=0`.

`stm_temporal_post_impossible` proves the stronger fact that **no suffix
assertion at all** can follow this `R` on the remaining resource. Thus
choosing another postcondition witness, pool, or mark set cannot help.

`owned_disjoint_strong_temporal_frame_invalid` proves:

```text
not (J ⊨dj {R ⋉ P} release(1) {R ⋉ Q})
```

Finally, `owned_strong_temporal_counterexample` packages the two-processor
assumption, fragment invariant, variable condition, valid unframed premise,
and invalid framed conclusion in one theorem.

## What this changes, and what it does not establish

The review's argument that a spatially disjoint frame remains disjoint
through transfer applies to a fixed spatial split. It does not show that
the separate temporal witness survives. Requiring a common pair of
witnesses would describe a stronger connective than the existing
conjunction. It cannot be silently substituted in the proof.

The fixed-frame buffer-uniqueness and flush-attribution results remain
intact. The concrete external frame here is empty throughout. Neither
arbitrary frame futures nor reassignment of a buffered occurrence causes
this failure. Likewise, this example does not refute a resource regrouping
lemma whose hypotheses already give one common spatial/temporal split.

This result refutes **FRAME-STM in disjoint mode with arbitrary assertions**.
It does not refute FRAME-SP or semantic FRAME-TM from overlap-mode validity.
Those general theorems, FRAME-STM in overlap mode, parallel composition,
and the full container derivation remain unproved for `owned_safe`.
The unframed release premise used here is only proved in disjoint mode.

My recommendation is to retain the proved transfer rules and the current
safety definition. After review, the independent positive work is FRAME-SP
and overlap-mode FRAME-TM. For disjoint-mode strong temporal framing, the
next design question is whether to keep the existing conjunction and
restrict the rule, or require a common split explicitly. A common-split
repair would first need a precise rule statement and tests showing that
the intended examples still satisfy it. Neither repair has been implemented
or claimed sound here; no additional predicate was added.

## Validation

`make check` passes, including the independent `rocq check` verification of
compiled proof objects. All **467** audited declarations report
`Closed under the global context`, including all 29 new proved declarations
in these two modules. There are no added axioms or admitted proofs.

The historical review and checkpoint reports retain their original
findings. This report supersedes the general-transfer and FRAME-STM status
in the checkpoint-5 implementation report.
