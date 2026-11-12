From Stdlib Require Import List ZArith.
From WMLR Require Import Expressions Languages Machine BufferRelations Separation RepairedSeparation
  OperationalSemantics ProgramSteps ExecutionExamples Assertions AssertionSemantics ConcreteAssertions
  RepairedAssertions PersistentAssertions PersistentRules Safety Specifications PrivateOwnership
  TemporalSafety TemporalFence RegionalResources InvariantFragment OwnedSafety OwnedResources
  OwnedRules OwnedFraming OwnedStructural OwnedPrimitives OwnedHeap OwnedAcceptance
  StrongTemporalCounterexample OwnedContainerEntailments OwnedContainer OwnedCalculus OwnedDerivedRules
  AssertionDerivation AssertionDerivedRules AssertionSoundness AssertionRearrangements
  OwnedAssertionRules OwnedContainerAssertions.
Import ListNotations.

(** Checkpoint 4C reconstruction of the same container and specifications.
    Every CONS/UNLOCK obligation is supplied by an assertion proof tree.
    The cell LOAD/STORE helpers likewise use the assertion interfaces. *)

Lemma container_read_flag_derived mode tail v : ~ In 0 (A.fv tail) ->
  owned_derivation two_processors container_invariant mode (container_held (A.Spatial (container_flag v) tail))
    container_load_flag (A.And (container_held (A.Spatial (container_flag v) tail)) (A.Pure (container_guard v))).
Proof.
  intros Hfresh; eapply owned_assertion_consequence.
  - apply container_assert_held_swap.
  - apply OwnedFrameSP.
    + apply owned_derive_load_cell; [apply container_invariant_closed |intros H; contradiction].
    + intros x Hx; cbn [container_load_flag load_command C.modifies] in Hx.
      destruct Hx as [E |Hfalse]; [subst x |contradiction]. exact Hfresh.
  - eapply AssertTrans; [apply container_assert_spatial_pure |].
    apply assert_derive_and_mono; [apply container_assert_held_restore |apply AssertRefl].
Qed.

Lemma container_read_cases_derived mode p q : ~ In 0 (A.fv p) -> ~ In 0 (A.fv q) ->
  owned_derivation two_processors container_invariant mode (container_cases p q) container_load_flag (container_read_cases p q).
Proof.
  intros Hp Hq; apply OwnedDisjunction.
  - eapply owned_assertion_consequence; [apply AssertRefl |apply container_read_flag_derived, Hp |apply AssertOrLeft].
  - eapply owned_assertion_consequence; [apply AssertRefl |apply container_read_flag_derived, Hq |apply AssertOrRight].
Qed.

Lemma container_select_one_derived mode p q : ~ In 0 (A.fv p) -> ~ In 0 (A.fv q) ->
  owned_derivation two_processors container_invariant mode (container_cases p q) (container_select 1%Z)
    (container_held (A.Spatial (container_flag 1%Z) q)).
Proof.
  intros Hp Hq; eapply OwnedSequence; [apply container_read_cases_derived; assumption |].
  eapply owned_assertion_consequence;
    [apply container_assert_select_one |apply OwnedAssume |apply AssertRefl].
Qed.

Lemma container_select_zero_derived mode p q : ~ In 0 (A.fv p) -> ~ In 0 (A.fv q) ->
  owned_derivation two_processors container_invariant mode (container_cases p q) (container_select 0%Z)
    (container_held (A.Spatial (container_flag 0%Z) p)).
Proof.
  intros Hp Hq; eapply OwnedSequence; [apply container_read_cases_derived; assumption |].
  eapply owned_assertion_consequence;
    [apply container_assert_select_zero |apply OwnedAssume |apply AssertRefl].
Qed.

Lemma container_store_known_derived mode loc old value :
  owned_derivation two_processors container_invariant mode (container_cell loc old)
    (store_command 1%positive loc value) (container_history loc 1%positive value).
Proof.
  eapply owned_assertion_consequence; [apply AssertRefl |apply owned_derive_store_cell |].
  apply (AssertSeparateMono two_processors SepTemporal); [apply container_assert_cell_some |apply AssertRefl].
Qed.

(** Compatibility corollary for the earlier API, now obtained from its
    assertion derivation. The program proof below uses that derivation
    directly, not this semantic corollary. *)
Lemma container_expression_cell_some active loc expression :
  persistent_entails active (writer_points_to (EVal (Z.pos loc)) expression) (container_some_cell loc).
Proof.
  apply assertion_derivation_sound,container_assert_cell_some.
Qed.

Lemma container_store_some_derived mode loc value :
  owned_derivation two_processors container_invariant mode (container_some_cell loc)
    (store_command 1%positive loc value) (container_history loc 1%positive value).
Proof.
  apply OwnedExists.
  - apply container_invariant_closed.
  - intros H; contradiction.
  - cbn [container_history container_some_cell container_write writer_points_to A.fv expr_fv fresh]; tauto.
  - eapply owned_assertion_consequence; [apply AssertRefl |apply owned_derive_store_cell |].
    apply (AssertSeparateMono two_processors SepTemporal); [apply container_assert_cell_some |apply AssertRefl].
Qed.


Lemma container_store_flag_derived mode tail old value :
  owned_derivation two_processors container_invariant mode (container_held (A.Spatial (container_flag old) tail))
    (store_command 1%positive 1%positive value) (container_held (A.Spatial (container_flag_history value) tail)).
Proof.
  eapply owned_assertion_consequence; [apply container_assert_held_swap | |apply container_assert_held_restore].
  apply OwnedFrameSP; [apply container_store_known_derived |intros x H; contradiction].
Qed.

Theorem container_remove_derived :
  owned_derivation two_processors container_invariant DisjointMode A.Emp container_remove container_item.
Proof.
  eapply OwnedSequence with (middle := container_cases A.Emp container_item).
  - eapply owned_assertion_consequence; [apply AssertRefl | |apply container_assert_first_acquire].
    apply OwnedLock.
  - eapply OwnedSequence.
    + apply container_select_one_derived; cbn [container_item container_some_cell writer_points_to A.fv expr_fv fresh]; tauto.
    + eapply OwnedSequence; [apply container_store_flag_derived |].
      apply owned_assertion_unlock,container_assert_remove_unlock.
Qed.

Theorem container_return_derived :
  owned_derivation two_processors container_invariant DisjointMode container_private_history container_return A.Emp.
Proof.
  eapply OwnedSequence with (middle := container_cases (container_cell 2%positive 9%Z) container_item).
  - apply OwnedWeaken.
    eapply owned_assertion_consequence;
      [apply (AssertUnitRight two_processors SepTemporal Backward) | |apply container_assert_reacquire].
    apply OwnedFrameTM; [|intros x H; contradiction].
    apply OwnedLock.
  - eapply OwnedSequence.
    + apply container_select_zero_derived;
        cbn [container_item container_some_cell container_cell writer_points_to A.fv expr_fv fresh]; tauto.
    + eapply OwnedSequence; [apply container_store_flag_derived |].
      apply owned_assertion_unlock,container_assert_return_unlock.
Qed.

Theorem container_core_derived :
  owned_derivation two_processors container_invariant DisjointMode A.Emp container_program A.Emp.
Proof.
  eapply OwnedSequence; [apply container_remove_derived |].
  eapply OwnedSequence; [apply container_store_some_derived |apply container_return_derived].
Qed.

Theorem owned_container_derived :
  owned_derivation two_processors container_invariant DisjointMode container_foreign container_program container_foreign.
Proof.
  eapply owned_assertion_consequence; [apply (AssertUnitRight two_processors SepSpatial Backward) | |].
  - apply OwnedFrameSP; [apply container_core_derived |intros x _ H; contradiction].
  - apply (AssertUnitRight two_processors SepSpatial Forward).
Qed.
