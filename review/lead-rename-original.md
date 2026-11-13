# Rename handoff: original terminology

Responds to `review/reviewer-request-rename-printed.md`.

**New proof commit:** `1c66a282af874690ed3ef3bd45d9d1789d7b14e8`.
**Rename baseline:** `4c5d06b`.

This is a mechanical rename. Every changed file was compared with its
baseline after exactly the substitutions `printed` to `original`,
`Printed` to `Original`, and `PRINTED` to `ORIGINAL`. No other text,
statement, proof, or line break changed. There were no declaration-name
collisions and no exceptions to those substitutions.

The scope is `theories/*.v`, `_CoqProject`, `README.md`,
`notes/current-calculus.md`, and `notes/paper-theorem-index.md`. No old
spelling remains there. Historical `review/` files, including `Review.v`
and `Derivations.v`, all other notes, and the paper were left untouched.
The paper's eight citations therefore remain for the reviewer to update.

## The eight paper citations

| Old | New |
| --- | --- |
| `printed_assignment_invalid` | `original_assignment_invalid` |
| `printed_buffer_override_not_associative` | `original_buffer_override_not_associative` |
| `printed_conjecture1_false` | `original_conjecture1_false` |
| `printed_points_foreign_barrier_unsound` | `original_points_foreign_barrier_unsound` |
| `printed_points_stale_value_unsound` | `original_points_stale_value_unsound` |
| `owned_printed_share_lock_counterexample` | `owned_original_share_lock_counterexample` |
| `printed_spatiotemporal_not_associative` | `original_spatiotemporal_not_associative` |
| `printed_strong_frame_counterexample` | `original_strong_frame_counterexample` |

## Files and implicit modules

| Old file/module | New file/module |
| --- | --- |
| `theories/PrintedDerivations.v` / `WMLR.PrintedDerivations` | `theories/OriginalDerivations.v` / `WMLR.OriginalDerivations` |
| `theories/PrintedPointsToDerivations.v` / `WMLR.PrintedPointsToDerivations` | `theories/OriginalPointsToDerivations.v` / `WMLR.OriginalPointsToDerivations` |
| `theories/PrintedStrongFrame.v` / `WMLR.PrintedStrongFrame` | `theories/OriginalStrongFrame.v` / `WMLR.OriginalStrongFrame` |

All imports and the project/audit references use the new module names.

## Full declaration and constructor mapping

All 52 entries below use the plain substitution. Source locations are in
the new artifact; their line numbers are unchanged.

| Old | New | Source |
| --- | --- | --- |
| `PrintedCore` | `OriginalCore` | `theories/OriginalStrongFrame.v:11` |
| `PrintedFrameSTM` | `OriginalFrameSTM` | `theories/OriginalStrongFrame.v:12` |
| `PrintedFutureNext` | `OriginalFutureNext` | `theories/OriginalLocalCounterexamples.v:18` |
| `PrintedFutureRefl` | `OriginalFutureRefl` | `theories/OriginalLocalCounterexamples.v:17` |
| `PrintedPureAssign` | `OriginalPureAssign` | `theories/SafetyExamples.v:69` |
| `assertion_lock_multiplication_printed_model` | `assertion_lock_multiplication_original_model` | `theories/AssertionAlgebraCounterexamples.v:264` |
| `assertion_strong_associativity_printed_left_not_model` | `assertion_strong_associativity_original_left_not_model` | `theories/AssertionAlgebraCounterexamples.v:237` |
| `assertion_strong_associativity_printed_right_model` | `assertion_strong_associativity_original_right_model` | `theories/AssertionAlgebraCounterexamples.v:230` |
| `assertion_wand_free_in_printed` | `assertion_wand_free_in_original` | `theories/AssertionAlgebra.v:179` |
| `memory_repaired_in_printed` | `memory_repaired_in_original` | `theories/RepairedFlushing.v:94` |
| `ordered_in_printed` | `ordered_in_original` | `theories/OrderedSeparation.v:11` |
| `owned_printed_share_lock_counterexample` | `owned_original_share_lock_counterexample` | `theories/OwnedAlternativeCounterexamples.v:84` |
| `printed` | `original` | `theories/OriginalDerivations.v:269` |
| `printed_assignment_invalid` | `original_assignment_invalid` | `theories/SafetyExamples.v:41` |
| `printed_assignment_soundness_false` | `original_assignment_soundness_false` | `theories/SafetyExamples.v:75` |
| `printed_buffer_override_not_associative` | `original_buffer_override_not_associative` | `theories/OrderedBuffers.v:116` |
| `printed_calculus_foreign_barrier_unsound` | `original_calculus_foreign_barrier_unsound` | `theories/OriginalDerivations.v:444` |
| `printed_calculus_stale_value_unsound` | `original_calculus_stale_value_unsound` | `theories/OriginalDerivations.v:369` |
| `printed_cell` | `original_cell` | `theories/OriginalPointsToDerivations.v:10` |
| `printed_cell_elim` | `original_cell_elim` | `theories/OriginalPointsToDerivations.v:12` |
| `printed_cell_intro` | `original_cell_intro` | `theories/OriginalPointsToDerivations.v:31` |
| `printed_conjecture1` | `original_conjecture1` | `theories/SeparationExamples.v:154` |
| `printed_conjecture1_false` | `original_conjecture1_false` | `theories/SeparationExamples.v:163` |
| `printed_derives_foreign_barrier` | `original_derives_foreign_barrier` | `theories/OriginalDerivations.v:302` |
| `printed_derives_stale_value` | `original_derives_stale_value` | `theories/OriginalDerivations.v:290` |
| `printed_generalized_flush` | `original_generalized_flush` | `theories/OriginalLocalCounterexamples.v:11` |
| `printed_generalized_future` | `original_generalized_future` | `theories/OriginalLocalCounterexamples.v:16` |
| `printed_history_invention` | `original_history_invention` | `theories/ReviewObstructions.v:63` |
| `printed_memory_compatibility_not_associative` | `original_memory_compatibility_not_associative` | `theories/StableCompatibility.v:150` |
| `printed_points_derives_foreign_barrier` | `original_points_derives_foreign_barrier` | `theories/OriginalPointsToDerivations.v:235` |
| `printed_points_derives_stale_value` | `original_points_derives_stale_value` | `theories/OriginalPointsToDerivations.v:225` |
| `printed_points_donate` | `original_points_donate` | `theories/OriginalPointsToDerivations.v:140` |
| `printed_points_foreign_barrier_unsound` | `original_points_foreign_barrier_unsound` | `theories/OriginalPointsToDerivations.v:295` |
| `printed_points_held7_not_post` | `original_points_held7_not_post` | `theories/OriginalPointsToDerivations.v:266` |
| `printed_points_held7_pre` | `original_points_held7_pre` | `theories/OriginalPointsToDerivations.v:244` |
| `printed_points_import` | `original_points_import` | `theories/OriginalPointsToDerivations.v:196` |
| `printed_points_invent` | `original_points_invent` | `theories/OriginalPointsToDerivations.v:68` |
| `printed_points_stale_value_unsound` | `original_points_stale_value_unsound` | `theories/OriginalPointsToDerivations.v:280` |
| `printed_points_unit` | `original_points_unit` | `theories/OriginalPointsToDerivations.v:103` |
| `printed_pure_assignment` | `original_pure_assignment` | `theories/SafetyExamples.v:67` |
| `printed_spatiotemporal_not_associative` | `original_spatiotemporal_not_associative` | `theories/StableCompatibility.v:164` |
| `printed_stm_donation_derivation` | `original_stm_donation_derivation` | `theories/OriginalStrongFrame.v:21` |
| `printed_stm_final_impossible` | `original_stm_final_impossible` | `theories/OriginalStrongFrame.v:43` |
| `printed_stm_frame` | `original_stm_frame` | `theories/OriginalStrongFrame.v:17` |
| `printed_stm_initial_models` | `original_stm_initial_models` | `theories/OriginalStrongFrame.v:31` |
| `printed_stm_invariant` | `original_stm_invariant` | `theories/OriginalStrongFrame.v:16` |
| `printed_stm_post` | `original_stm_post` | `theories/OriginalStrongFrame.v:19` |
| `printed_stm_pre` | `original_stm_pre` | `theories/OriginalStrongFrame.v:18` |
| `printed_strong_frame_counterexample` | `original_strong_frame_counterexample` | `theories/OriginalStrongFrame.v:60` |
| `printed_with_stm` | `original_with_stm` | `theories/OriginalStrongFrame.v:10` |
| `repaired_in_printed` | `repaired_in_original` | `theories/RepairedSeparation.v:19` |
| `stable_implies_printed_compatible` | `stable_implies_original_compatible` | `theories/StableCompatibility.v:15` |

The only additional local code identifier changed is the proof binder
`Hprinted` to `Horiginal`. Together with the three implicit file/module
names, this accounts for all 56 changed code identifiers. Comment prose
and the requested living documents use the same terminology substitution.

## Validation and paper figures

`make clean` followed by `make check` passed, including the independent
kernel check of `WMLR.Audit`. The build printed exactly **1,316** reports
of declarations closed under the global context, with no error or axiom
reports. The source scan found no declared axioms or admitted proofs.

| Quantity | After rename |
| --- | ---: |
| Theory files in `_CoqProject` | 196 |
| Physical theory lines, including comments and blanks | 30,574 |
| Distinct audited declarations | 1,316 |
| Program-calculus constructors | 21 |
| Assertion-calculus constructors | 47 |

All counts are unchanged. The checked build started after removing the
old compiled artifacts; the three renamed theories were compiled under
their new module paths. The reviewer can clean-clone the new proof commit
above before updating the paper's reference.
