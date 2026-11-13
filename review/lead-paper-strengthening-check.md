# Lead's check of the five rewritten sections

Responds to the last request in
`review/reviewer-response-to-strengthening.md`.

**Draft checked:** `e82fc1e34c513c07bd4d2988ba23041a1fce411e`.
**Proof artifact checked:** `2b53266aca3329c92c4bc04423e16c9270bde3f8`.
Line references below are to that draft. There is no difference in
`theories/`, `_CoqProject`, or `Makefile` between these commits.

The single-judgment presentation is supported, and the restated soundness
theorem is correct. Two sentences in the temporal-frame paragraph need
qualification. Neither correction requires new proof work or a change to
the calculus. I have changed neither the paper nor the theory sources.

## Two corrections in calculus.tex

### 1. The equivalence assumes a disjoint-mode derivation

**Location:** `paper/sections/calculus.tex:59–61`.

The sentence says that a specification has an overlap-mode derivation if
and only if its command contains no unlock. The actual theorem,
`owned_overlap_derivable_iff_unlock_free`
(`theories/OwnedModeElimination.v:37–39`), has an additional premise:
the same specification already has a disjoint-mode derivation.

Without that premise, being unlock-free would suffice to derive arbitrary
pre/postconditions. For a checked counterexample, the unfenced
cell-to-cell store has an unlock-free command but is not derivable in
either mode (`owned_plain_store_cell_not_derivable` in
`theories/OwnedFenceExamples.v`).

Suggested replacement:

> Among specifications derivable in disjoint mode, an overlap-mode
> derivation exists if and only if the command contains no unlock
> (`owned_overlap_derivable_iff_unlock_free`).

This is the exact syntactic replay result. It is not a characterization
of semantic overlap-mode validity or of the weakest sound frame guard.
The following sentence's counterexample to unrestricted temporal framing
is correctly supported by `owned_disjoint_temporal_frame_counterexample`.

### 2. Restrict the rule, not all release specifications

**Location:** `paper/sections/calculus.tex:51–53`.

“A release is valid only in disjoint mode” is too strong as a statement
about semantic validity. The C1 counterexample that the response accepts
is itself an overlap-valid release specification: its precondition
`lock(1) * lock(2)` is inhabited, but has no admissible environment.
`owned_inhabited_but_environmentless_unlock_valid`
(`theories/OwnedNecessity.v:69–70`) proves validity in either mode for any
invariant and postcondition. The stronger packaged statement at line 81
also supplies two active processors and a nonempty fragment invariant.

Suggested replacement for the relevant two clauses:

> Under the soundness hypotheses, every derivable specification whose
> command contains no unlock is valid in overlap mode. The general UNLOCK
> rule is provided only in disjoint mode.

This preserves the intended explanation and does not reopen C1. No
replacement universal donation theorem is needed.

## The restated soundness theorem passes

`paper/sections/results.tex:4–9` follows from two existing results:

1. Apply `owned_calculus_sound` to the disjoint-mode derivation.
2. If the command is unlock-free, replay the same derivation using
   `owned_derivation_unlock_free_overlap`, then apply soundness in overlap
   mode.

I compiled the following scratch corollary against the current artifact;
Rocq reports it closed under the global context:

```coq
Theorem paper_single_judgment_sound active invariant pre command post :
  invariant_fragment invariant -> two_active_processors active ->
  owned_derivation active invariant DisjointMode pre command post ->
  owned_valid active DisjointMode invariant pre command post /\
  (unlock_free command ->
    owned_valid active OverlapMode invariant pre command post).
```

The theorem's displayed citation to `owned_calculus_sound` is therefore
sound as a reference to its main ingredient. For precise attribution,
add the replay theorem to the citation or explain the extra replay step
in the proof paragraph. The standing hypotheses are exactly the fragment
and two distinct active processors; there is no additional finiteness or
register-preservation assumption.

## Results of the other checks

| Section | Assessment |
| --- | --- |
| `calculus.tex` | The displayed single-judgment rules agree with disjoint-mode derivations. FRAME-TM has the correct syntactic guard, including nested and unreachable subcommands. The counterexample establishes the need for some invariant restriction, without claiming the exact fragment is uniquely necessary. Apply the two qualifications above. |
| `results.tex` | Soundness and adequacy agree with the proofs. The necessity results each drop just the named standing hypothesis. The initially lock-free-frame qualification for emp-to-emp restoration is retained. The SHARE statement retains its semantic endpoint conditions. |
| `changes.tex` | The single-judgment frame restriction and singleton-processor counterexample are correctly described. The cell discussion explains why a general acquisition cannot promise all-processor completeness while preserving the original points-to as an assertion. This does not make the exact weakened-cell definition the only possible repair. |
| `wrong.tex` | The new flushing and unlock references really use original `models` / `valid_specification`; the intermediate-interpretation footnote can be removed. INV alone is refuted as stated. Its valid premise is vacuous, which is consistent with the limited claim made here. The trilemma's non-optimality qualification remains correct. |
| `proofs.tex` | Removing the mode annotations preserves the cited derivations. The fence, buffered-load, and acquisition applications of FRAME-TM all have unlock-free commands. Container, named-lock, and mailbox derivations are in disjoint mode. The freshness, address-distinctness, acquisition-draining, completion, and older-retrying-container qualifications from the previous review remain present. |

## Validation and scope

I reread all five sections, checked the changed claims against their
definitions and theorem statements, and checked the affected example
derivations. All **36 distinct Rocq references** in these sections resolve
uniquely to declarations in `_CoqProject`, and every one is included in
`Audit.v`.

The proof sources and build inputs are identical to the already checked
`2b53266` artifact. The counts remain **196 theory files**, **30,574 physical
theory lines**, and **1,316 audit entries**. I did not repeat the full build
for this paper-only change; the additional scratch check above compiled
successfully and introduced no repository declaration.

This is a paper-to-statement check, not a new line-by-line proof audit,
literature review, or layout review. The fixed proof reference remains
`2b53266`. C1 and optional D2 remain closed as requests, as the reviewer
specified; this report creates no further proof obligation.
