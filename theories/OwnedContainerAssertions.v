From Stdlib Require Import List ZArith Bool.
From WMLR Require Import Expressions Machine Assertions AssertionSemantics InvariantFragment
  ExecutionExamples OwnedContainerEntailments OwnedContainer AssertionDerivation
  AssertionDerivedRules AssertionRearrangements.
Import ListNotations.

(** Checkpoint 4C: assertion proof trees for the existing container.
    The old semantic entailments are retained in their original modules
    for comparison, but none is used to construct these derivations. *)
Lemma container_assert_held_swap p q :
  assertion_derivation two_processors (container_held (A.Spatial p q)) (A.Spatial (container_held q) p).
Proof. apply assert_derive_spatial_swap. Qed.

Lemma container_assert_held_restore p q :
  assertion_derivation two_processors (A.Spatial (container_held q) p) (container_held (A.Spatial p q)).
Proof. apply assert_derive_spatial_restore. Qed.

Lemma container_assert_spatial_pure p q b :
  assertion_derivation two_processors (A.Spatial p (A.And q (A.Pure b)))
    (A.And (A.Spatial p q) (A.Pure b)).
Proof. apply (AssertPureSeparateRight two_processors SepSpatial Forward). Qed.

Lemma container_assert_cell_some active loc expression :
  assertion_derivation active (writer_points_to (EVal (Z.pos loc)) expression) (container_some_cell loc).
Proof. apply assert_derive_cell_value_hiding; cbn; tauto. Qed.

Lemma container_assert_history_complete active loc owner value :
  assertion_derivation active
    (A.Temporal (container_history loc owner value) (A.Barrier (EVal (Z.pos owner))))
    (container_cell loc value).
Proof. apply assert_derive_drained_history; cbn; tauto. Qed.

Lemma container_assert_first_acquire :
  assertion_derivation two_processors
    (A.Temporal (container_held container_invariant) (A.Barrier (EVal 1%Z)))
    (container_cases A.Emp container_item).
Proof.
  eapply AssertTrans; [apply assert_derive_barrier_suffix |].
  eapply AssertTrans; [apply (AssertOrSeparateRight two_processors SepSpatial Forward) |].
  apply assert_derive_or_mono; [|apply AssertRefl].
  apply (AssertSeparateMono two_processors SepSpatial); [apply AssertRefl |].
  apply (AssertUnitRight two_processors SepSpatial Backward).
Qed.

Lemma container_assert_remove_unlock :
  assertion_derivation two_processors
    (A.Temporal (A.Spatial (container_flag_history 0%Z) container_item) (A.Barrier (EVal 1%Z)))
    (A.Spatial container_invariant container_item).
Proof.
  eapply AssertTrans; [apply (AssertBarrierDistribute two_processors SepSpatial Forward) |].
  apply (AssertSeparateMono two_processors SepSpatial).
  - eapply AssertTrans; [apply container_assert_history_complete |apply AssertOrLeft].
  - apply assert_derive_barrier_suffix.
Qed.

Lemma container_assert_return_unlock :
  assertion_derivation two_processors
    (A.Temporal (A.Spatial (container_flag_history 1%Z) (container_cell 2%positive 9%Z)) (A.Barrier (EVal 1%Z)))
    (A.Spatial container_invariant A.Emp).
Proof.
  eapply AssertTrans; [apply (AssertBarrierDistribute two_processors SepSpatial Forward) |].
  eapply AssertTrans with (q := A.Spatial (container_flag 1%Z) container_item).
  - apply (AssertSeparateMono two_processors SepSpatial).
    + apply container_assert_history_complete.
    + eapply AssertTrans; [apply assert_derive_barrier_suffix |apply container_assert_cell_some].
  - eapply AssertTrans; [apply AssertOrRight |apply (AssertUnitRight two_processors SepSpatial Backward)].
Qed.

(** Reassociate only ordinary temporal conjunction. Distinct flag/item
    cells can change separator; the two item cells then use overwrite. *)
Lemma container_assert_full_cell_overwrite active old next :
  assertion_derivation active
    (A.Temporal (writer_points_to (EVal 2%Z) old)
      (A.Spatial (container_flag 1%Z) (writer_points_to (EVal 2%Z) next)))
    (A.Spatial (container_flag 1%Z) (writer_points_to (EVal 2%Z) next)).
Proof.
  eapply AssertTrans with (q := A.Temporal (writer_points_to (EVal 2%Z) old)
    (A.Temporal (container_flag 1%Z) (writer_points_to (EVal 2%Z) next))).
  - apply (AssertSeparateMono active SepTemporal); [apply AssertRefl |].
    apply (assert_derive_distinct_cells active Backward); intros; reflexivity.
  - eapply AssertTrans; [apply (AssertAssociative active SepTemporal Backward) |].
    eapply AssertTrans with (q := A.Temporal
      (A.Temporal (container_flag 1%Z) (writer_points_to (EVal 2%Z) old))
      (writer_points_to (EVal 2%Z) next)).
    + apply (AssertSeparateMono active SepTemporal); [|apply AssertRefl].
      eapply AssertTrans; [apply (assert_derive_distinct_cells active Forward); intros; reflexivity |].
      eapply AssertTrans; [apply AssertSpatialComm |].
      apply (assert_derive_distinct_cells active Backward); intros; reflexivity.
    + eapply AssertTrans; [apply (AssertAssociative active SepTemporal Forward) |].
      eapply AssertTrans with (q := A.Temporal (container_flag 1%Z) (writer_points_to (EVal 2%Z) next)).
      * apply (AssertSeparateMono active SepTemporal); [apply AssertRefl |apply AssertCellOverwrite].
      * apply (assert_derive_distinct_cells active Forward); intros; reflexivity.
Qed.

Lemma container_assert_full_overwrite :
  assertion_derivation two_processors
    (A.Temporal (container_cell 2%positive 9%Z) (A.Spatial (container_flag 1%Z) container_item))
    (A.Spatial (container_flag 1%Z) container_item).
Proof.
  eapply AssertTrans with (q := A.Temporal (container_cell 2%positive 9%Z)
    (A.Exists 0 (A.Spatial (container_flag 1%Z) (writer_points_to (EVal 2%Z) (EVar 0))))).
  - apply (AssertSeparateMono two_processors SepTemporal); [apply AssertRefl |].
    apply (AssertExistsSeparateRight two_processors SepSpatial Forward); cbn; tauto.
  - eapply AssertTrans; [apply (AssertExistsSeparateRight two_processors SepTemporal Forward); cbn; tauto |].
    apply assert_derive_exists_elim; [cbn; tauto |].
    eapply AssertTrans; [apply container_assert_full_cell_overwrite |].
    apply (AssertSeparateMono two_processors SepSpatial); [apply AssertRefl |apply container_assert_cell_some].
Qed.

Lemma container_assert_reacquire :
  assertion_derivation two_processors
    (A.Temporal container_private_history
      (A.Temporal (container_held container_invariant) (A.Barrier (EVal 1%Z))))
    (container_cases (container_cell 2%positive 9%Z) container_item).
Proof.
  eapply AssertTrans; [apply (AssertAssociative two_processors SepTemporal Backward) |].
  eapply AssertTrans; [apply (AssertBarrierDistribute two_processors SepTemporal Forward) |].
  eapply AssertTrans with (q := A.Temporal (container_cell 2%positive 9%Z) (container_held container_invariant)).
  - apply (AssertSeparateMono two_processors SepTemporal);
      [apply container_assert_history_complete |apply assert_derive_barrier_suffix].
  - eapply AssertTrans; [apply assert_derive_lock_temporal_out |].
    eapply AssertTrans.
    + apply (AssertSeparateMono two_processors SepSpatial); [apply AssertRefl |].
      apply (AssertOrSeparateRight two_processors SepTemporal Forward).
    + eapply AssertTrans; [apply (AssertOrSeparateRight two_processors SepSpatial Forward) |].
      apply assert_derive_or_mono; apply (AssertSeparateMono two_processors SepSpatial); try apply AssertRefl.
      * eapply AssertTrans; [apply (assert_derive_distinct_cells two_processors Forward); intros; reflexivity
          |apply AssertSpatialComm].
      * apply container_assert_full_overwrite.
Qed.

Lemma container_assert_select_one p q :
  assertion_derivation two_processors (container_read_cases p q)
    (A.Or (A.Pure (BNot (container_guard 1%Z))) (container_held (A.Spatial (container_flag 1%Z) q))).
Proof.
  apply assert_derive_or_elim.
  - eapply AssertTrans; [apply AssertAndRight |].
    eapply AssertTrans; [|apply AssertOrLeft].
    apply assert_derive_pure_implication; intros s H.
    change (Z.eqb (s 0) 0%Z = true) in H; apply Z.eqb_eq in H.
    change (negb (Z.eqb (s 0) 1%Z) = true); rewrite H; reflexivity.
  - eapply AssertTrans; [apply AssertAndLeft |apply AssertOrRight].
Qed.

Lemma container_assert_select_zero p q :
  assertion_derivation two_processors (container_read_cases p q)
    (A.Or (A.Pure (BNot (container_guard 0%Z))) (container_held (A.Spatial (container_flag 0%Z) p))).
Proof.
  apply assert_derive_or_elim.
  - eapply AssertTrans; [apply AssertAndLeft |apply AssertOrRight].
  - eapply AssertTrans; [apply AssertAndRight |].
    eapply AssertTrans; [|apply AssertOrLeft].
    apply assert_derive_pure_implication; intros s H.
    change (Z.eqb (s 0) 1%Z = true) in H; apply Z.eqb_eq in H.
    change (negb (Z.eqb (s 0) 0%Z) = true); rewrite H; reflexivity.
Qed.
