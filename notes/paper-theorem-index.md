# Writer's index: rules, repairs, counterexamples and scope

This is a source map, not another semantics or proof system. The active
program judgment is `owned_derivation`; its one semantic target is
`owned_safe` / `owned_valid`. Fully qualified names are used below where
historical modules have colliding names. The complete declaration audit is
[Audit.v](../theories/Audit.v); the full assertion-law instance table is
[the algebra audit](../review/paper-algebra-audit.md).

## Main theorem and standing hypotheses

| Result | Declaration and source | Scope |
| --- | --- | --- |
| Program calculus, 21 constructors | `owned_derivation`, [OwnedCalculus.v](../theories/OwnedCalculus.v) | Modes OV and DJ; no safety/validity premise in a constructor. CONS and UNLOCK have semantic assertion-entailment premises. |
| Assertion calculus, 47 constructors | `assertion_derivation`, [AssertionDerivation.v](../theories/AssertionDerivation.v); `assertion_derivation_sound`, [AssertionSoundness.v](../theories/AssertionSoundness.v) | Entire assertion grammar, including wands; no global processor-count, finiteness or invariant hypothesis. |
| CONS and UNLOCK from assertion proofs | `owned_assertion_consequence`, `owned_assertion_unlock`, [OwnedAssertionRules.v](../theories/OwnedAssertionRules.v) | Derived interfaces to the existing program constructors; no new program rule. |
| Soundness by induction | `owned_calculus_sound`, [OwnedCalculus.v](../theories/OwnedCalculus.v) | `invariant_fragment J` and `two_active_processors active`. No finiteness axiom. |
| Adequacy directly from a derivation | `owned_derivation_adequacy`, same file | Concrete free-lock start, disjoint invariant pool; empty external frame instantiated internally. Every finite run avoids abort; termination gives the postcondition and ownership decomposition. |
| Semantic adequacy | `owned_valid_adequacy`, [OwnedAdequacy.v](../theories/OwnedAdequacy.v) | Same standing hypotheses; takes semantic validity. |
| Final invariant restoration for emp-to-emp clients | `owned_emp_derivation_restores`, [OwnedExecution.v](../theories/OwnedExecution.v) | Also assumes a lock-free initial external frame. The final pool is a component of the actual final memory. |
| Exact address-domain preservation | `step_preserves_domain`, `steps_preserve_domain`, `execution_preserves_domain`, [ExecutionDomain.v](../theories/ExecutionDomain.v) | Union of heap and buffer addresses. No safety, processor-count, or invariant premise. |

These are partial-correctness results. They do not establish termination,
fairness, deadlock freedom, or restoration at every intermediate prefix.
A general terminating postcondition may retain the lock.

## Every program constructor and its semantic theorem

All constructors are in `OwnedCalculus.v`. Unless restricted below, they
are available at both modes. The semantic lemmas often need fewer
hypotheses than the combined soundness theorem.

| Constructor / rule | Semantic theorem | Source / extra premise |
| --- | --- | --- |
| `OwnedSkip` / SKIP | `owned_skip_valid` | [OwnedStructural.v](../theories/OwnedStructural.v) |
| `OwnedAssign` / ASSIGN | `owned_assignment_valid` | [OwnedPrimitives.v](../theories/OwnedPrimitives.v); destination absent from `fv(J)` |
| `OwnedAssume` / ASSUME | `owned_assume_valid` | Same file |
| `OwnedAssert` / ASSERT | `owned_assert_valid` | Same file |
| `OwnedLoad` / LOAD | `owned_load_valid` | [OwnedHeap.v](../theories/OwnedHeap.v); destination fresh for invariant, address, annotation, value and retained assertion |
| `OwnedStore` / STORE | `owned_store_valid` | Same file |
| `OwnedLoadAny` / LOAD-ANY | `owned_load_any_writer_valid` | Same file; destination fresh for invariant, address, value and retained assertion |
| `OwnedStoreAny` / STORE-ANY | `owned_store_any_writer_valid` | Same file |
| `OwnedFence` / FENCE | `owned_fence_valid` | [OwnedPrimitives.v](../theories/OwnedPrimitives.v) |
| `OwnedLock` / transferring LOCK | `OwnedRules.owned_lock_valid` | [OwnedRules.v](../theories/OwnedRules.v); fragment invariant, two active processors; constant positive owner |
| `OwnedUnlock` / transferring UNLOCK | `owned_unlock_valid` | Same file; fragment invariant, two active processors, restoration entailment; DJ only; constant positive owner |
| `OwnedSequence` / SEQ | `owned_sequence_valid` | [OwnedStructural.v](../theories/OwnedStructural.v) |
| `OwnedConsequence` / CONS | `owned_consequence_valid` | Same file |
| `OwnedDisjunction` / DISJ | `owned_disjunction_valid` | Same file |
| `OwnedChoice` / CHOICE | `owned_choice_valid` | Same file |
| `OwnedLoop` / LOOP | `owned_loop_valid` | Same file |
| `OwnedExists` / EX | `owned_exists_valid` | [OwnedExists.v](../theories/OwnedExists.v); binder fresh for command, postcondition and invariant |
| `OwnedFrameSP` / FRAME-SP | `owned_spatial_frame_valid` | [OwnedFraming.v](../theories/OwnedFraming.v); usual modified/free-variable condition |
| `OwnedFrameTM` / FRAME-TM | `owned_temporal_frame_valid` | Same file; fragment invariant, usual variable condition; OV only |
| `OwnedParallel` / CONC | `owned_parallel_valid` | [OwnedParallel.v](../theories/OwnedParallel.v); printed mutual interference condition and neither command modifies `fv(J)` |
| `OwnedWeaken` / OV → DJ | `owned_valid_overlap_disjoint` | [OwnedResources.v](../theories/OwnedResources.v) |

INV, FRAME-STM and SHARE are not hidden unproved constructors: they are
absent. There is no auxiliary-variable elimination rule. Expression-valued
lock schemas, recursive predicates and general shared-read permissions are
not implemented.

## Every assertion constructor and its semantic lemma

All 47 constructors are in `AssertionDerivation.v`; the induction is in
`AssertionSoundness.v`. Equivalence rules use
`assertion_equivalence_direction` to select the indicated direction.
The cell disequality is retained as a pure conjunct. Individual atomic
processor conditions stay on their constructors; no global hypothesis is
added by soundness.

| Constructor | Semantic lemma | Source / qualification |
| --- | --- | --- |
| `AssertRefl` | `assertion_rule_refl` | [AssertionLogicalRules.v](../theories/AssertionLogicalRules.v) |
| `AssertTrans` | `assertion_rule_trans` | Same file |
| `AssertTrue` | `assertion_rule_true` | Same file |
| `AssertFalse` | `assertion_rule_false` | Same file |
| `AssertAndIntro` | `assertion_rule_and_intro` | Same file |
| `AssertAndLeft` | `assertion_rule_and_left` | Same file |
| `AssertAndRight` | `assertion_rule_and_right` | Same file |
| `AssertOrLeft` | `assertion_rule_or_left` | Same file |
| `AssertOrRight` | `assertion_rule_or_right` | Same file |
| `AssertOrCases` | `assertion_rule_or_cases` | Same file; retains additive context |
| `AssertExistsIntro` | `assertion_rule_exists_intro` | Same file; capture-avoiding substitution |
| `AssertExistsElim` | `assertion_rule_exists_elim` | Same file; context and result freshness |
| `AssertForallIntro` | `assertion_rule_forall_intro` | Same file; antecedent freshness |
| `AssertForallElim` | `assertion_rule_forall_elim` | Same file |
| `AssertSubstitute` | `assertion_rule_substitute` | Same file |
| `AssertPure` | `assertion_rule_pure` | Same file; boolean-only implication premise |
| `AssertPureCases` | `assertion_rule_pure_cases` | Same file; decidable boolean case split |
| `AssertEquality` | `assertion_rule_equality` | Same file; equality of expression evaluations |
| `AssertSeparateMono` | `assertion_conjunction_mono` | [AssertionAlgebra.v](../theories/AssertionAlgebra.v), spatial/temporal instances |
| `AssertUnitLeft` | `assertion_conjunction_unit_left` | Same file, spatial/temporal instances |
| `AssertUnitRight` | `assertion_conjunction_unit_right` | Same file, spatial/temporal instances |
| `AssertAssociative` | `assertion_spatial_associative`, `assertion_temporal_associative` | Same file |
| `AssertSpatialComm` | `assertion_spatial_commutative` | Same file |
| `AssertOrSeparateLeft` | `assertion_rule_or_separate_left` | [AssertionLogicalRules.v](../theories/AssertionLogicalRules.v) |
| `AssertOrSeparateRight` | `assertion_rule_or_separate_right` | Same file |
| `AssertExistsSeparateLeft` | `assertion_rule_exists_separate_left` | Same file; right operand freshness |
| `AssertExistsSeparateRight` | `assertion_rule_exists_separate_right` | Same file; left operand freshness |
| `AssertPureSeparateLeft` | `assertion_rule_pure_separate_left` | Same file; all components use the same stack |
| `AssertPureSeparateRight` | `assertion_rule_pure_separate_right` | Same file; no buffer-freedom premise |
| `AssertSpatialWandIntro` | `persistent_spatial_wand_adjoint`, forward | [PersistentRules.v](../theories/PersistentRules.v) |
| `AssertSpatialWandElim` | `persistent_spatial_wand_adjoint`, backward | Same file |
| `AssertTemporalWandLeftIntro` | `persistent_temporal_wand_left_adjoint`, forward | Same file |
| `AssertTemporalWandLeftElim` | `persistent_temporal_wand_left_adjoint`, backward | Same file |
| `AssertTemporalWandRightIntro` | `persistent_temporal_wand_right_adjoint`, forward | Same file |
| `AssertTemporalWandRightElim` | `persistent_temporal_wand_right_adjoint`, backward | Same file |
| `AssertBarrierEmp` | `assertion_barrier_entails_emp` | [AssertionAlgebra.v](../theories/AssertionAlgebra.v) |
| `AssertBarrierDuplicate` | `assertion_barrier_idempotent` | Same file, spatial/temporal instances |
| `AssertBarrierDistribute` | `assertion_barrier_distributes_spatial`, `assertion_barrier_distributes_temporal` | [AssertionBarrierAlgebra.v](../theories/AssertionBarrierAlgebra.v) |
| `AssertBarrierSpatial` | `assertion_strong_barrier_temporal`, spatial projection | [AssertionAlgebra.v](../theories/AssertionAlgebra.v) |
| `AssertLockRight` | `assertion_temporal_lock_right_spatial` | [AssertionLockAlgebra.v](../theories/AssertionLockAlgebra.v) |
| `AssertLockLeft` | `assertion_temporal_lock_left_spatial` | Same file |
| `AssertLocksExclusive` | `assertion_lock_multiplication_common_blocker` | [AssertionAlgebra.v](../theories/AssertionAlgebra.v); explicit active common blocker |
| `AssertWritesExclusive` | `assertion_spatial_writes_exclusive`, forward | Same file |
| `AssertWritesCollapse` | `assertion_successive_writes_collapse` | [AssertionWriteAlgebra.v](../theories/AssertionWriteAlgebra.v) |
| `AssertPointsToWrite` | `assertion_points_to_write_active` | Same file; annotation always denotes an active processor |
| `AssertCellsSeparate` | `assertion_cells_separate` | [AssertionCellAlgebra.v](../theories/AssertionCellAlgebra.v); pure address disequality |
| `AssertCellOverwrite` | `assertion_cell_overwrite` | Same file; one-way, later value wins |

The four cell proof trees are `assert_derive_cells_exclusive`,
`assert_derive_drained_write_cell`, `assert_derive_cell_value_hiding` and
`assert_derive_drained_history` in
[AssertionDerivedRules.v](../theories/AssertionDerivedRules.v). They use
no semantic entailment premises. Syntactic substitution normalization and
bound-name regressions are in
[AssertionCellSubstitution.v](../theories/AssertionCellSubstitution.v) and
[AssertionDerivationExamples.v](../theories/AssertionDerivationExamples.v).
See [the checkpoint report](../review/paper-assertion-soundness.md) for
freshness details and the unchanged constructor counts.

## Derived rules and examples

| Result | Declaration and source |
| --- | --- |
| Exact all-processor LOAD-P | `owned_derive_load_points_to`, [OwnedPointsToRules.v](../theories/OwnedPointsToRules.v) |
| Corrected STORE-P, temporal write suffix | `owned_derive_store_points_to`, same file |
| Cell-only LOAD/STORE, assignment from an updated-stack entailment, while loop | `owned_derive_load_cell`, `owned_derive_store_cell`, `owned_derive_assign_from`, `owned_derive_while`, [OwnedDerivedRules.v](../theories/OwnedDerivedRules.v) |
| Own-buffered-write load, arbitrary history and spatial tail | `owned_derive_load_after_history_spatial`, `owned_derive_load_own_buffered_write`, [OwnedBufferedLoad.v](../theories/OwnedBufferedLoad.v) |
| Pending, flushed, and other-processor load witnesses | `buffered_load_pending_enabled`, `buffered_load_after_flush_enabled`, `buffered_load_other_processor_reads_old`, [OwnedBufferedLoadExamples.v](../theories/OwnedBufferedLoadExamples.v) |
| FENCE-G | `owned_derive_fence_after`, [OwnedFenceExamples.v](../theories/OwnedFenceExamples.v) |
| Fenced cell-store contract and complete trace | `owned_derive_store_fence_cell`, `owned_store_fence_cell_witness`, same file |
| FENCE-B; transferring LOCK-G and LOCK-B | `owned_derive_fence_backward`, `owned_derive_lock_after`, `owned_derive_lock_backward`, [OwnedAlternativeRules.v](../theories/OwnedAlternativeRules.v) |
| Empty-invariant strengthened LOCK/UNLOCK and UNLOCK-G/B | `owned_derive_lock_empty_strong`, `owned_derive_unlock_empty_strong`, `owned_derive_unlock_after_empty`, `owned_derive_unlock_backward_empty`, same file |
| Replacement locked wrapper, body under the same invariant | `owned_derive_locked_wrapper`, same file |
| Common-split future closure and program-step reconstruction | `resource_common_future_split`, `owned_common_reconstruction`, [OwnedCommonSplit.v](../theories/OwnedCommonSplit.v) |
| Resource-level common-split framing, both modes | `owned_safe_common_frame`, same file; fragment invariant and variable condition; **one common pair of witnesses**, not merely `R ⋉ P` |
| Enabled common-split release with foreign writes pending | `owned_common_release_safe`, `owned_common_release_enabled`, [OwnedCommonSplitExamples.v](../theories/OwnedCommonSplitExamples.v) |
| Selected-branch container, assertion derivations throughout | `owned_container_derived`, [OwnedContainerDerivation.v](../theories/OwnedContainerDerivation.v); all CONS/UNLOCK premises and cell-access helpers now use assertion proof trees |
| Container assertion obligations, including both releases and reacquisition | `container_assert_remove_unlock`, `container_assert_return_unlock`, `container_assert_reacquire`, [OwnedContainerAssertions.v](../theories/OwnedContainerAssertions.v); all 13 lemmas construct `assertion_derivation` |
| Reusable assertion rearrangements | `assert_derive_lock_temporal_out`, `assert_derive_strong_emp_right`, `assert_derive_distinct_cells`, [AssertionRearrangements.v](../theories/AssertionRearrangements.v); eight derived lemmas, no new constructor |
| Original container trace, pending foreign write and all-run safety | `owned_container_trace`, `owned_container_foreign_pending_throughout`, `owned_container_all_runs_safe`, [OwnedContainerTrace.v](../theories/OwnedContainerTrace.v) |
| Retrying container derivation | `owned_retrying_container_derived`, [OwnedRetryContainer.v](../theories/OwnedRetryContainer.v); retains some semantic entailment proofs, outside this 4C reconstruction |
| 52-step success and two failed retry iterations | `owned_retrying_container_trace`, `container_two_failed_iterations`, [OwnedRetryTrace.v](../theories/OwnedRetryTrace.v) |
| Both containers restore the invariant on completion | `owned_container_completed_restores`, `owned_retrying_container_completed_restores`, same file |
| Concurrency with register updates and an acquire beside a blocked store | `owned_parallel_registers_valid`, `owned_parallel_acquire_store_valid`, [OwnedParallelExamples.v](../theories/OwnedParallelExamples.v); enabled witnesses in the same file |

See the [derived-rule classification](../review/paper-independent-batch.md)
for the exact differences from the source's LOCKED/ATOMIC, backward rules
and apparently mistyped STORE-P/FENCE-B displays. A useful modified theorem
is not represented as proof of the source's literal formula.

## Repairs and design choices, with supporting theorems

| Repair or choice | Checked support | Status |
| --- | --- | --- |
| Preserve occurrence order in buffer overriding | `ordered_associative`, [OrderedBuffers.v](../theories/OrderedBuffers.v) | Repair of failed printed algebra |
| Compatibility must include blocked processors | `stable_compatibility_associative`, `stable_implies_printed_compatible`, [StableCompatibility.v](../theories/StableCompatibility.v) | Conservative repair; admits fewer compositions |
| Combine repaired merge and compatibility | `repaired_resource_associative`, `repaired_temporal_resource_associative`, [RepairedSeparation.v](../theories/RepairedSeparation.v) | Active resource algebra |
| Full flushing closure, including wands | `persistent_assertion_flushing_closed`, [PersistentAssertions.v](../theories/PersistentAssertions.v) | Future-quantified wand interpretation |
| Preserve all three wand adjunctions | `persistent_spatial_wand_adjoint`, `persistent_temporal_wand_left_adjoint`, `persistent_temporal_wand_right_adjoint`, [PersistentRules.v](../theories/PersistentRules.v) | Full assertion grammar |
| Preserve all six emp unit laws | `assertion_unit_spatial_left/right`, `assertion_unit_temporal_left/right`, `assertion_unit_strong_left/right`, [AssertionUnits.v](../theories/AssertionUnits.v) | Full grammar, including wands; no domain assumption |
| Preserve spatial/temporal associativity and spatial commutativity | `assertion_spatial_associative`, `assertion_temporal_associative`, `assertion_spatial_commutative`, [AssertionAlgebra.v](../theories/AssertionAlgebra.v) | Strong-temporal associativity is excluded |
| Barrier, lock and write laws | `assertion_barrier_distribution`, [AssertionBarrierAlgebra.v](../theories/AssertionBarrierAlgebra.v); `assertion_lock_symmetric`, [AssertionLockAlgebra.v](../theories/AssertionLockAlgebra.v); `assertion_successive_writes_collapse`, [AssertionWriteAlgebra.v](../theories/AssertionWriteAlgebra.v) | Complete instance classifications in the algebra audit |
| Writer-existential cell in the existing grammar | `writer_points_to_shape`, `writer_points_to_from_shape`, [InvariantFragment.v](../theories/InvariantFragment.v) | Abbreviation, not a new atom; original `A.points_to` retained |
| Guarded heap invariants and controlled re-marking | `invariant_fragment_shape`, `invariant_fragment_remark`, `invariant_spatial_pending_retained`, same file | Buffer/token freedom; release cannot hide a foreign pending write in the pool |
| Keep blocked-set lock encoding; require two active processors | `two_processors_separate_free_held`, [LockRepresentation.v](../theories/LockRepresentation.v) | Design choice instead of changing the machine's representation |
| Fix the external frame within each actual program step | `ordered_residual_unique`, [ResidualUniqueness.v](../theories/ResidualUniqueness.v) | Buffer uniqueness only; no claimed heap/mark cancellation |
| Attribute each flush to one component | `pooled_resource_flush_attribution`, [FlushAttribution.v](../theories/FlushAttribution.v) | Pool and unaffected component fixed; duplicates attributed to the frame |
| Capture-avoiding substitution | `persistent_assertion_subst`, [AssertionSubstitution.v](../theories/AssertionSubstitution.v); `substitution_capture_regression`, [OwnedRoutineExamples.v](../theories/OwnedRoutineExamples.v) | Whole grammar, including wands |
| Preserve assertion meaning under thread interference | `owned_safe_stack_agrees`, [OwnedInterference.v](../theories/OwnedInterference.v) | Used by EX and parallel composition; explicit variable conditions |
| Remove INV; transfer at machine actions | `OwnedRules.owned_lock_valid`, `owned_unlock_valid`, [OwnedRules.v](../theories/OwnedRules.v) | Active protocol, not protected/private compartments |
| Omit FRAME-STM and SHARE | Counterexamples below; common-split framing above | Deliberate omissions; restricted SHARE remains an open proposal |

The safety record's footprint bound and mark budget are explicit fields of
`owned_update` in [OwnedSafety.v](../theories/OwnedSafety.v). Pool status
covers free, held locally, held externally, and admissible split-token
contexts. No additional validity predicate has been layered on top of it.

## Counterexamples: distinguish original errors from repaired-design limits

| Claim or regression | Checked declaration / source | Interpretation and qualification |
| --- | --- | --- |
| Printed Conjecture 1 | `printed_conjecture1_false`, [SeparationExamples.v](../theories/SeparationExamples.v) | Original relation; arbitrary overlapping heaps obstruct the proposed decomposition |
| Printed buffer associativity | `printed_buffer_override_not_associative`, [OrderedBuffers.v](../theories/OrderedBuffers.v) | Original overriding |
| Printed compatibility / spatiotemporal associativity | `printed_memory_compatibility_not_associative`, `printed_spatiotemporal_not_associative`, [StableCompatibility.v](../theories/StableCompatibility.v) | Original blocking exception |
| Unqualified assignment | `printed_assignment_invalid`, `printed_assignment_soundness_false`, [SafetyExamples.v](../theories/SafetyExamples.v) | Printed safety; changing an invariant variable breaks the environment |
| Pointwise temporal wand flushing closure | `pointwise_temporal_wand_not_flush_closed`, [FlushingCounterexample.v](../theories/FlushingCounterexample.v) | Checked for the earlier repaired, pointwise-wand interpretation; do not silently relabel this theorem as an original-`models` theorem |
| INV + FRAME-TM stale value | `printed_points_stale_value_unsound`, [PrintedPointsToDerivations.v](../theories/PrintedPointsToDerivations.v) | Original `models`, original all-processor points-to, printed derivation and invalidity |
| INV + FRAME-TM foreign barrier | `printed_points_foreign_barrier_unsound`, same file | Same original scope; an actual foreign write remains pending |
| INV + FRAME-STM witness mismatch | `printed_strong_frame_counterexample`, [PrintedStrongFrame.v](../theories/PrintedStrongFrame.v) | Original interpretation and points-to; minimal adapted witness, not the identical checkpoint-6 program; does not isolate FRAME-STM from INV |
| Strong associativity, both directions | `assertion_strong_associativity_printed_right_model`, `assertion_strong_associativity_printed_left_not_model`, [AssertionAlgebraCounterexamples.v](../theories/AssertionAlgebraCounterexamples.v); opposite direction in [OriginalAlgebraCounterexamples.v](../theories/OriginalAlgebraCounterexamples.v) | Original and final interpretations; table in algebra audit |
| Unrestricted lock multiplication | `assertion_lock_multiplication_printed_model`, `assertion_lock_multiplication_refuted`, [AssertionAlgebraCounterexamples.v](../theories/AssertionAlgebraCounterexamples.v) | Original and final; witness has no admissible machine environment; same-owner exclusion survives with two processors |
| T4 with invalid writer annotation | `original_points_to_invalid_writer_refuted`, [OriginalAlgebraCounterexamples.v](../theories/OriginalAlgebraCounterexamples.v) | Original and final; active annotation is the qualification |
| T7/T8 with strong connective outside | `original_small_exchange_strong_left_refuted`, `original_small_exchange_strong_right_refuted`, same file | Original-model counterparts; literal/uniform premise distinction remains essential |
| T9 full exchange | `original_full_exchange_refuted`, same file | Original and final interpretations |
| Arbitrarily evolving frame during one program step | `overlap_frame_shape_counterexample`, `overlap_acquire_frame_shape_counterexample`, [FrameShapeCounterexample.v](../theories/FrameShapeCounterexample.v) | Failed checkpoint-3 proposal; excluded by `fixed_frame_excludes_assume_counterexample` and `fixed_frame_excludes_acquire_counterexample` in [FixedFrameExamples.v](../theories/FixedFrameExamples.v) |
| Singleton processor lock ambiguity | `singleton_emp_lock_equivalent`, `singleton_acquire_still_free`, [LockRepresentation.v](../theories/LockRepresentation.v) | Original machine encoding; motivates two distinct active processors |
| Bare pure invariant can absorb buffered writes | `bare_pure_is_not_buffer_free`, `checkpoint_unlock_foreign_write_test`, [InvariantFragmentExamples.v](../theories/InvariantFragmentExamples.v) | Final assertion interpretation; motivates syntactic guards |
| Acquired weak cell is not an all-processor cell | `processor_cell_does_not_imply_all_processor_cell`, [OwnershipTransferLimits.v](../theories/OwnershipTransferLimits.v); `checkpoint_cell_remark_and_no_foreign_barrier`, [InvariantFragmentExamples.v](../theories/InvariantFragmentExamples.v) | Assertion distinction; not a changed definition of the old points-to |
| Donation in overlap mode | `owned_overlap_donation_invalid`, [OwnedAcceptance.v](../theories/OwnedAcceptance.v) | Current safety; corresponding DJ donation is valid |
| Foreign barrier after acquire/release | `owned_foreign_barrier_invalid`, same file | Current safety, both modes; all allowed successors ruled out |
| Reacquisition | `double_acquire_stuck`, same file | With two processors: stuck, not unsafe and not a second transfer |
| Blocked local flush and external token | `owned_blocked_local_future_regression`, `owned_foreign_holder_both_safe`, same file | Positive non-vacuity regressions for the existing closure and environment clauses |
| Strong-temporal frame over release | `owned_disjoint_strong_temporal_frame_invalid`, [StrongTemporalCounterexample.v](../theories/StrongTemporalCounterexample.v) | Current DJ validity, weak-conjunction abbreviation; corresponding spatial frame is valid in [OwnedFramingExamples.v](../theories/OwnedFramingExamples.v) |
| Unfenced flushed-cell postcondition | `owned_plain_store_cell_invalid`, `owned_plain_store_cell_not_derivable`, [OwnedFenceExamples.v](../theories/OwnedFenceExamples.v) | Current semantics/calculus, both modes; inhabited precondition |
| Literal displayed STORE-P | `owned_literal_store_p_invalid`, [OwnedAlternativeCounterexamples.v](../theories/OwnedAlternativeCounterexamples.v) | Final interpretation; literal postcondition false on all resources; source transcription separated from corrected derived form |
| Unrestricted SHARE with transferring LOCK | `owned_printed_share_lock_counterexample`, same file | Current semantics, both modes; duplicates a cell |
| Merely syntactically lock-free SHARE | `owned_syntactic_lock_free_share_counterexample`, same file | `emp` and `C * true` contain no Lock atom but the latter can hide its token; semantic restriction is still open |
| Retirement erases unrelated live ownership | `ReviewObstructions.retired_later_cell_can_erase_earlier`, [ReviewObstructions.v](../theories/ReviewObstructions.v) | Abandoned retirement interpretation only |
| General framing/unit/transfer tension | `ReviewObstructions.trilemma`, same file | Abstract conditional theorem, not a discharged soundness theorem |

All individual E1–E12 / T1–T9 instances, including mixed spatial/temporal
exchange and the precise nonempty-domain qualifications, remain enumerated
in the [algebra table](../review/paper-algebra-audit.md). The original review's
owner-specific derivations and history-invention lemma are also audited in
`PrintedDerivations.v` and `ReviewObstructions.v`; use the newer
all-processor statements when describing the printed calculus in the paper.

## Original message-passing example

| Result | Declaration and source | Scope |
| --- | --- | --- |
| Sender, receiver and parallel derivations | `mp_sender_derived`, `mp_receiver_derived`, `mp_parallel_derived`, [MessagePassingDerivation.v](../theories/MessagePassingDerivation.v) | Same commands as Section 4.1; token invariant; all assertion premises are proof trees. |
| Original one-cell all-execution conclusion | `message_passing_all_runs`, [MessagePassingAdequacy.v](../theories/MessagePassingAdequacy.v) | Tokens chosen and erased internally; arbitrary initial result register; no abort, terminal singleton heap containing x+1, empty buffers/free lock. |
| Original all-processor points-to | `message_passing_points_to`, same file | At full completeness on the actual final memory. |
| Execution and abort lifting by unused cells | `execution_heap_extension`, `abort_heap_extension`, [HeapExtension.v](../theories/HeapExtension.v) | General machine lemmas; abort lifting requires added cells absent at the accessed address. |
| Both outcomes and pending private store | `message_passing_zero_trace`, `message_passing_one_trace`, `message_passing_one_pending_trace`, [MessagePassingTrace.v](../theories/MessagePassingTrace.v) | 16-step and 20-step complete original-heap runs; 17-step prefix with private write still buffered. |

The [result report](../review/paper-message-passing.md) distinguishes this
execution theorem from an emp-invariant derivation of the printed triple.
Neither SHARE nor AUX is added. The original derivation's rejected steps
are classified in the [design diagnosis](../review/paper-priority-1-design.md).

## Named spinlocks

| Result | Declaration and source | Scope |
| --- | --- | --- |
| Acquire/release any member of a finite family | `named_lock_acquire_family`, `named_lock_release_family`, [NamedLockRules.v](../theories/NamedLockRules.v) | DJ derivation trees; acquire scratch fresh for J; release has a certificate I * I proves false. |
| Both contracts semantically valid | `named_lock_family_valid`, [NamedLockExamples.v](../theories/NamedLockExamples.v) | Existing fragment and two-processor hypotheses only. |
| Inhabited two-lock instance and nested client | `named_lock_two_initial_inhabited`, `named_lock_nested_derived`, `named_lock_nested_all_runs`, same file | Concrete four-cell heap; all finite executions avoid abort, terminal pool restored. |
| Retry, acquisition and release traces | `named_lock_retry_iteration_trace`, `named_lock_acquire_success_trace`, `named_lock_release_trace`, [NamedLockTrace.v](../theories/NamedLockTrace.v) | General concrete traces, including other processors' pending buffers. |
| Two named locks held while physical lock free | `named_lock_nested_trace`, `named_lock_nested_state`, [NamedLockExamples.v](../theories/NamedLockExamples.v) | 59-step nested run; protected values unchanged, flags zero on completion. |
| Finite cell products and exclusivity | `cell_family_models`, `cell_family_exclusive`, [CellFamilies.v](../theories/CellFamilies.v) | Rocq families of existing assertions; no recursive assertion constructor. |

## Arbitrary-length mailbox

| Result | Declaration and source | Scope |
| --- | --- | --- |
| Buffered named-lock interfaces | `named_lock_acquire_retained_family`, `named_lock_release_buffered_family`, [NamedBufferedRules.v](../theories/NamedBufferedRules.v) | Same implementation, DJ; expose retained draining and accept a completion proof on return. |
| Fill/read arbitrary finite regions | `fill_region_derived`, `read_region_derived`, `history_family_complete`, [RegionRules.v](../theories/RegionRules.v) | List-parameterized, including empty lists; all assertion premises derived. |
| Producer/consumer parallel derivation | `mailbox_parallel_derived`, [MailboxDerivation.v](../theories/MailboxDerivation.v) | No producer fence; retrying consumer ends owning the specified value region. |
| Concrete initial-memory adequacy for arbitrary lists | `mailbox_all_runs`, [MailboxAdequacy.v](../theories/MailboxAdequacy.v) | Distinct flags, message and foreign address; three processors; every finite run safe, terminal invariant restored and region owned. |
| Complete transfer and failed retry | `mailbox_parallel_trace`, `mailbox_failed_iteration_retries`, [MailboxTrace.v](../theories/MailboxTrace.v) | 95-step two-cell successful run and 41-step failed iteration. |
| Unrelated write remains pending in witnesses | `mailbox_foreign_pending_throughout`, `mailbox_trace_contents`, same file | Includes internal physical lock/store/flush states; all-run theorem permits the foreign write to flush. |

## Mechanization figures and outstanding work

At this batch, `make check` passes with **1,232 audited declarations closed**,
no axioms and no admitted proofs, using Rocq 9.3.0. There are **182 theory
files and 28,865 physical lines** listed in `_CoqProject`, including comments,
blank lines, the audit commands, original transcriptions and superseded
experiments. This is the entire checked development, not a claim that the
active soundness proof alone is that large. The nine new mailbox/helper files have 956 physical lines and
75 newly audited declarations.
Declaration totals count
`Print Assumptions` entries, not every generated inductive eliminator.

Reproduce the line count by summing `len(path.read_text().splitlines())` for
the `.v` paths in `_CoqProject`; reproduce the audit count from the closed
reports emitted while rebuilding `Audit.v`. `rocq check` independently
checks the imported proof objects after compilation. The complete fixed
bounded-search output for common splitting is in
[paper-common-split-search.jsonl](../review/paper-common-split-search.jsonl).

The assertion soundness and [4C reconstruction](../review/paper-container-assertions.md)
checkpoints and the [message-passing result](../review/paper-message-passing.md)
and the [named-lock result](../review/paper-named-locks.md) are complete and
ready for review. The [mailbox region client](../review/paper-mailbox.md) is
now complete too. Restricted SHARE is the remaining main queue item. The separate retrying container's remaining semantic
entailments have not been reconstructed in this batch.
Restricted SHARE's semantic lock-free pre/post premises are approved;
its proof and mode scope remain open and are next in the queue.
Fenced Dekker lacks a shared-access rule; see the scope paragraph in the
[batch report](../review/paper-independent-batch.md). No completeness or
automation claim is made for the sound assertion system.

The historical `RepairedSafety`, `PersistentCalculus`, `OwnershipCalculus`,
`PrivateCalculus`, `RegionalCalculus`, `SeparatedCalculus` and `Retired*`
paths are **superseded experiments**, not extra validity layers needed by
`owned_derivation`. Their utility lemmas may still be imported by the active
proof. [Current-calculus notes](current-calculus.md) and
[development history](development-history.md) record that distinction.
