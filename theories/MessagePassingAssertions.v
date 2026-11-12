From Stdlib Require Import List ZArith Bool.
From WMLR Require Import Expressions Machine Assertions AssertionSemantics InvariantFragment
  AssertionDerivation AssertionDerivedRules AssertionRearrangements AssertionClientRules MessagePassingSyntax.
Import ListNotations.

Lemma mp_assert_acquire active owner retained invariant result :
  assertion_derivation active (A.Spatial retained invariant) result ->
  assertion_derivation active
    (A.Spatial retained (A.Temporal (mp_held owner invariant) (A.Barrier (EVal (Z.pos owner)))))
    (mp_held owner result).
Proof.
  intros H; eapply AssertTrans; [apply (AssertSeparateMono active SepSpatial);
    [apply AssertRefl |apply assert_derive_barrier_suffix] |].
  eapply AssertTrans; [apply assert_derive_spatial_rotate |].
  apply (AssertSeparateMono active SepSpatial); [apply AssertRefl |exact H].
Qed.

Lemma mp_assert_sender_payload active t r :
  assertion_derivation active (A.Spatial (mp_token t) (mp_invariant t r))
    (A.Spatial (mp_data 0%Z) (mp_token t)).
Proof.
  eapply AssertTrans; [apply (AssertOrSeparateRight active SepSpatial Forward) |].
  apply assert_derive_or_elim; [apply AssertSpatialComm |].
  eapply AssertTrans; [apply (AssertOrSeparateRight active SepSpatial Forward) |].
  apply assert_derive_or_elim.
  - eapply AssertTrans; [apply assert_derive_spatial_rotate |].
    eapply AssertTrans with (q := A.Spatial (mp_data 1%Z) (A.Pure BFalse)).
    + apply (AssertSeparateMono active SepSpatial); [apply AssertRefl |apply assert_derive_cells_exclusive].
    + eapply AssertTrans; [apply (assert_derive_separate_pure_right active SepSpatial) |apply AssertFalse].
  - eapply AssertTrans; [apply (AssertAssociative active SepSpatial Backward) |].
    eapply AssertTrans with (q := A.Spatial (A.Pure BFalse) (mp_token r)).
    + apply (AssertSeparateMono active SepSpatial); [apply assert_derive_cells_exclusive |apply AssertRefl].
    + eapply AssertTrans; [apply (assert_derive_separate_pure_left active SepSpatial) |apply AssertFalse].
Qed.

Lemma mp_assert_receiver_payload active t r :
  assertion_derivation active (A.Spatial (mp_token r) (mp_invariant t r))
    (A.Or (A.Spatial (mp_data 0%Z) (mp_token r))
      (A.Spatial (mp_data 1%Z) (A.Spatial (mp_token t) (mp_token r)))).
Proof.
  eapply AssertTrans; [apply (AssertOrSeparateRight active SepSpatial Forward) |].
  apply assert_derive_or_elim.
  - eapply AssertTrans; [apply AssertSpatialComm |apply AssertOrLeft].
  - eapply AssertTrans; [apply (AssertOrSeparateRight active SepSpatial Forward) |].
    apply assert_derive_or_elim.
    + eapply AssertTrans; [apply assert_derive_spatial_rotate |].
      eapply AssertTrans; [apply (AssertSeparateMono active SepSpatial);
        [apply AssertRefl |apply AssertSpatialComm] |apply AssertOrRight].
    + eapply AssertTrans; [apply assert_derive_spatial_rotate |].
      eapply AssertTrans with (q := A.Spatial (mp_token t) (A.Pure BFalse)).
      * apply (AssertSeparateMono active SepSpatial); [apply AssertRefl |apply assert_derive_cells_exclusive].
      * eapply AssertTrans; [apply (assert_derive_separate_pure_right active SepSpatial) |apply AssertFalse].
Qed.

Lemma mp_assert_receiver_acquire active t r :
  assertion_derivation active
    (A.Spatial (mp_token r) (A.Temporal (mp_held 2%positive (mp_invariant t r)) (A.Barrier (EVal 2%Z))))
    (mp_load_cases t r).
Proof.
  eapply AssertTrans; [apply mp_assert_acquire,mp_assert_receiver_payload |].
  apply (AssertOrSeparateRight active SepSpatial Forward).
Qed.

Lemma mp_assert_sender_release active t r :
  assertion_derivation active
    (A.Temporal (A.Spatial (A.Temporal (mp_data 0%Z) (A.LeadsTo mp_address (EVal 1%Z) (EVal 1%Z)))
      (mp_token t)) (A.Barrier (EVal 1%Z))) (A.Spatial (mp_invariant t r) A.Emp).
Proof.
  eapply AssertTrans; [apply (AssertBarrierDistribute active SepSpatial Forward) |].
  eapply AssertTrans with (q := A.Spatial (mp_data 1%Z) (mp_token t)).
  - apply (AssertSeparateMono active SepSpatial);
      [apply assert_derive_cell_write_drained |apply assert_derive_barrier_suffix].
  - eapply AssertTrans with (q := mp_invariant t r); [|apply (AssertUnitRight active SepSpatial Backward)].
    eapply AssertTrans; [apply AssertOrLeft |apply AssertOrRight].
Qed.

Lemma mp_assert_release_zero active t r :
  assertion_derivation active
    (A.Temporal (A.Spatial (mp_data 0%Z) (mp_token r)) (A.Barrier (EVal 2%Z)))
    (A.Spatial (mp_invariant t r) (mp_token r)).
Proof.
  eapply AssertTrans; [apply assert_derive_barrier_suffix |].
  apply (AssertSeparateMono active SepSpatial); [apply AssertOrLeft |apply AssertRefl].
Qed.

Lemma mp_assert_release_one active t r :
  assertion_derivation active
    (A.Temporal (A.Spatial (mp_data 1%Z) (A.Spatial (mp_token t) (mp_token r))) (A.Barrier (EVal 2%Z)))
    (A.Spatial (mp_invariant t r) (mp_data 1%Z)).
Proof.
  eapply AssertTrans; [apply assert_derive_barrier_suffix |].
  eapply AssertTrans; [apply AssertSpatialComm |].
  apply (AssertSeparateMono active SepSpatial); [|apply AssertRefl].
  eapply AssertTrans; [apply AssertOrRight |apply AssertOrRight].
Qed.

Lemma mp_assert_select_one active r v :
  assertion_derivation active (mp_received r v)
    (A.Or (A.Pure (BNot (mp_guard 1%Z))) (A.And (mp_data v) (A.Pure (mp_guard 1%Z)))).
Proof.
  apply assert_derive_or_elim; [|apply AssertOrRight].
  eapply AssertTrans; [apply AssertAndRight |].
  eapply AssertTrans; [|apply AssertOrLeft].
  apply assert_derive_pure_implication; intros s H; cbn [mp_guard eval_bexpr eval_expr] in *.
  apply Z.eqb_eq in H; rewrite H; reflexivity.
Qed.

Lemma mp_assert_select_not_one active r v :
  assertion_derivation active (mp_received r v)
    (A.Or (A.Pure (BNot (BNot (mp_guard 1%Z)))) (A.And (mp_token r) (A.Pure (mp_guard 0%Z)))).
Proof.
  apply assert_derive_or_elim; [apply AssertOrRight |].
  eapply AssertTrans; [apply AssertAndRight |].
  eapply AssertTrans; [|apply AssertOrLeft].
  apply assert_derive_pure_implication; intros s H.
  change (negb (negb (eval_bexpr s (mp_guard 1%Z))) = true); rewrite H; reflexivity.
Qed.
