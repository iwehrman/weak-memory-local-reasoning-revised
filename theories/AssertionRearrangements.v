From Stdlib Require Import List ZArith.
From WMLR Require Import Expressions Machine Assertions AssertionSemantics InvariantFragment
  AssertionDerivation AssertionDerivedRules.
Import ListNotations.

(** Reusable proof trees for the container reconstruction. These use only
    the approved assertion constructors; no semantic entailments enter. *)
Lemma assert_derive_or_mono active p p' q q' :
  assertion_derivation active p p' -> assertion_derivation active q q' ->
  assertion_derivation active (A.Or p q) (A.Or p' q').
Proof.
  intros HP HQ; apply assert_derive_or_elim;
    eapply AssertTrans; [exact HP |apply AssertOrLeft |exact HQ |apply AssertOrRight].
Qed.

Lemma assert_derive_pure_fact active p b : (forall s, eval_bexpr s b = true) ->
  assertion_derivation active p (A.Pure b).
Proof.
  intros H; eapply AssertTrans; [apply AssertTrue |].
  apply (AssertPure active [] b); intros s _; apply H.
Qed.

Lemma assert_derive_pure_implication active b c :
  (forall s, eval_bexpr s b = true -> eval_bexpr s c = true) ->
  assertion_derivation active (A.Pure b) (A.Pure c).
Proof.
  intros H; eapply AssertTrans with (q := pure_assumptions [b]).
  - apply AssertAndIntro; [apply AssertRefl |apply AssertTrue].
  - apply AssertPure; intros s Hb; apply H,Hb; cbn; auto.
Qed.

Lemma assert_derive_strong_emp_right active direction p :
  assertion_derivation active
    (assertion_source direction (A.strong_temporal p A.Emp) p)
    (assertion_target direction (A.strong_temporal p A.Emp) p).
Proof.
  destruct direction; cbn [assertion_source assertion_target A.strong_temporal].
  - eapply AssertTrans; [apply AssertAndLeft |apply (AssertUnitRight active SepSpatial Forward)].
  - apply AssertAndIntro;
      [apply (AssertUnitRight active SepSpatial Backward) |apply (AssertUnitRight active SepTemporal Backward)].
Qed.

Lemma assert_derive_spatial_swap active p q r :
  assertion_derivation active (A.Spatial p (A.Spatial q r)) (A.Spatial (A.Spatial p r) q).
Proof.
  eapply AssertTrans; [apply (AssertSeparateMono active SepSpatial);
    [apply AssertRefl |apply AssertSpatialComm] |apply (AssertAssociative active SepSpatial Backward)].
Qed.

Lemma assert_derive_spatial_restore active p q r :
  assertion_derivation active (A.Spatial (A.Spatial p r) q) (A.Spatial p (A.Spatial q r)).
Proof.
  eapply AssertTrans; [apply (AssertAssociative active SepSpatial Forward) |].
  apply (AssertSeparateMono active SepSpatial); [apply AssertRefl |apply AssertSpatialComm].
Qed.

Lemma assert_derive_lock_temporal_out active annotation p q :
  assertion_derivation active (A.Temporal p (A.Spatial (A.Lock annotation) q))
    (A.Spatial (A.Lock annotation) (A.Temporal p q)).
Proof.
  eapply AssertTrans with (q := A.Temporal p (A.Temporal q (A.Lock annotation))).
  - apply (AssertSeparateMono active SepTemporal); [apply AssertRefl |].
    eapply AssertTrans; [apply AssertSpatialComm |apply (AssertLockRight active Backward)].
  - eapply AssertTrans; [apply (AssertAssociative active SepTemporal Backward) |].
    eapply AssertTrans; [apply (AssertLockRight active Forward) |apply AssertSpatialComm].
Qed.

(** A convenient specialization of the guarded cell rule. Its only
    semantic premise is a pure boolean fact, via the existing pure rule. *)
Lemma assert_derive_distinct_cells active direction address other old next :
  (forall s, eval_bexpr s (BNot (BEq address other)) = true) ->
  assertion_derivation active
    (assertion_source direction
      (A.Temporal (writer_points_to address old) (writer_points_to other next))
      (A.Spatial (writer_points_to address old) (writer_points_to other next)))
    (assertion_target direction
      (A.Temporal (writer_points_to address old) (writer_points_to other next))
      (A.Spatial (writer_points_to address old) (writer_points_to other next))).
Proof.
  intros H; eapply AssertTrans; [apply AssertAndIntro;
    [apply assert_derive_pure_fact,H |apply AssertRefl] |].
  eapply AssertTrans; [apply (AssertCellsSeparate active direction) |apply AssertAndRight].
Qed.
