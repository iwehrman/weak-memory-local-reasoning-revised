# Request: rename "printed" to "original" in the proof sources

Ian finds "printed" confusing as terminology. The paper already says
"original" throughout, but it still cites Rocq names that begin with
`printed_`, and three theory files are named `Printed*.v`. Please rename
them so the artifact and the paper use one word.

This is a mechanical rename. No statement or proof should change.

## Scope

1. **Identifiers.** Every declaration in `theories/` whose name contains
   `printed` (about 50 distinct names), for example
   `printed_assignment_invalid` to `original_assignment_invalid`, and
   `stable_implies_printed_compatible` to
   `stable_implies_original_compatible`.
2. **Files and modules.** `PrintedDerivations.v`,
   `PrintedPointsToDerivations.v`, `PrintedStrongFrame.v`, with
   `_CoqProject`, `Audit.v` and every `Require` updated.
3. **Comments** in `theories/` that use "printed" in this sense.
4. **Living documentation:** `README`, `notes/current-calculus.md` and
   `notes/paper-theorem-index.md`.

Leave alone: the historical reports in `review/` (they describe past
commits and should keep the names that were true then), and
`review/Review.v` and `review/Derivations.v`.

## Things to watch

- **Collisions.** `original_*` names already exist, for example in
  `OriginalLocalCounterexamples.v` (`original_flushing_closure_false`,
  `original_arbitrary_invariant_unlock_invalid`,
  `original_inv_alone_counterexample`). If a rename would collide, pick a
  distinct name and list it.
- **Do not edit `paper/`.** I will update the cited names from your
  mapping. The paper currently cites these eight:
  `printed_assignment_invalid`,
  `printed_buffer_override_not_associative`, `printed_conjecture1_false`,
  `printed_points_foreign_barrier_unsound`,
  `printed_points_stale_value_unsound`,
  `owned_printed_share_lock_counterexample`,
  `printed_spatiotemporal_not_associative`,
  `printed_strong_frame_counterexample`.

## Report

A short file in `review/` with:

- the new commit hash;
- the full old-to-new mapping, with any name that is not a plain
  `printed` to `original` substitution marked;
- the `make check` result, with the count of audited declarations (it
  should still be 1,316) and the file and line counts for the paper's
  mechanization section.

I will rebuild from a clean clone and then move the paper's cited commit.
