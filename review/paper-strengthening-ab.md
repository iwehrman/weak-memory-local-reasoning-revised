# Strengthening A and B: both proved

The targets in `paper-strengthening-statement.md` pass. No assertion,
safety, or program-calculus definition was changed. The paper is untouched.

## A. Counterexamples in the original interpretation

`theories/OriginalLocalCounterexamples.v` contains:

- `original_pointwise_temporal_wand_not_flush_closed`: the same pending
  write satisfies the pointwise right temporal wand to false, and its
  actual one-flush future does not, with satisfaction now stated using
  **`models`** and the original temporal composition.
- `original_flushing_closure_false`: the corresponding universal closure
  claim is false for the original generalized flushing order.
- `original_arbitrary_invariant_unlock_invalid`: the unrestricted token
  release under invariant `false` is invalid for **`valid_specification`**.
  Its precondition has a concrete model and the release is enabled in an
  admissible printed environment. Every successor environment is ruled out.

The original generalized flushing relation is transcribed separately from
the repaired future relation: an indexed machine flush, monotone marks,
and a mark for the processor that flushed, then reflexive transitive
closure. It contains no mark-only transitions. The witness performs one
actual processor-1 flush and keeps the mark set `{1,2}`. Thus the
counterexample does not depend on the extra futures of the repaired model.

Definition 6 was checked against the
[original source](https://github.com/iwehrman/Weak-Memory-Local-Reasoning/blob/master/dissertation.tex#L1984-L1991),
file blob `ac4c24370dc22b3ca0892294206c2c6ac138d993`. Existing witness data
and a projection of a proved composition lemma are reused; neither theorem
substitutes a repaired validity or satisfaction predicate in its statement.

These names can replace the two intermediate-interpretation citations in
the paper's local-errors table. The historical intermediate results remain.

## B. A single judgment can present the derivation rules

`theories/OwnedModeElimination.v` proves:

```text
owned_derivation mode P c Q -> unlock_free c -> owned_derivation OV P c Q

owned_derivation OV P c Q -> unlock_free c

owned_derivation DJ P c Q -> unlock_free c -> mod(c) ∩ fv(R) = ∅
  -> owned_derivation DJ (R ; P) c (R ; Q)
```

The names are `owned_derivation_unlock_free_overlap`,
`owned_derivation_overlap_unlock_free`, and
`owned_derive_temporal_frame_unlock_free`. The first is proved by induction
on the existing derivation. No finiteness, processor-count, invariant
fragment, or semantic-validity premise is needed for this syntactic replay.
`owned_temporal_frame_unlock_free_valid` then gives the semantic rule
under the existing two standing soundness hypotheses.

`unlock_free` examines **all** subcommands, including both choices, both
parallel branches, and loop bodies. It therefore rejects unreachable
unlocks as well. This is necessary for this replay theorem in the current
calculus: for any DJ derivation,
`owned_overlap_derivable_iff_unlock_free` proves that an OV derivation of
the same specification exists **if and only if** the command is
unlock-free. The calculus has no constructor that removes unreachable
syntax from a command.

This is a theorem about derivability, not a characterization of semantic
OV validity. A weaker semantic criterion might suffice for some programs;
the present result makes no optimality claim of that sort.

For the paper, the single displayed judgment can be DJ, with FRAME-TM
carrying `unlock_free c` and the usual variable condition. The OV premise
is reconstructed inside the proof and weakened afterwards. The full
mode-indexed definition remains the mechanized implementation. We have
added derived theorems, not a second inductive calculus or another safety
predicate; the counts remain 21 program and 47 assertion constructors.

## Validation and next batch

Both files compile; `make check` passes, including the kernel audit.
The twelve added proof declarations are all audited and closed, bringing
the audit to **1,296**. The source now has **195 theory files**.

This is the requested joint A/B report. B succeeds, so the paper's proposed
presentation has its proof support. The next independent batch tests C;
in particular, its first universal claim must distinguish a satisfiable
assertion from an admissible environment. No changes to the paper are made
by this batch.
