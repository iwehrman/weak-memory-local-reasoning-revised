From Stdlib Require Import List Arith ZArith.
From WMLR Require Import Expressions Machine Assertions AssertionSemantics AssertionSubstitution
  InvariantFragment AssertionDerivation AssertionCellSubstitution.
Import ListNotations.

(** Proof trees in the 47-constructor basis. No satisfaction or semantic
    entailment lemma is used in this file. *)
Lemma assert_derive_and_mono active p p' q q' :
  assertion_derivation active p p' -> assertion_derivation active q q' ->
  assertion_derivation active (A.And p q) (A.And p' q').
Proof.
  intros HP HQ; apply AssertAndIntro.
  - eapply AssertTrans; [apply AssertAndLeft |exact HP].
  - eapply AssertTrans; [apply AssertAndRight |exact HQ].
Qed.

Lemma assert_derive_or_elim active p q r :
  assertion_derivation active p r -> assertion_derivation active q r ->
  assertion_derivation active (A.Or p q) r.
Proof.
  intros HP HQ; eapply AssertTrans with (q := A.And (A.Pure BTrue) (A.Or p q)).
  - apply AssertAndIntro; [apply AssertTrue |apply AssertRefl].
  - apply AssertOrCases; eapply AssertTrans; [apply AssertAndRight |exact HP |apply AssertAndRight |exact HQ].
Qed.

Lemma assert_derive_exists_elim active x p q : ~ In x (A.fv q) ->
  assertion_derivation active p q -> assertion_derivation active (A.Exists x p) q.
Proof.
  intros Hfresh H; eapply AssertTrans with (q := A.And (A.Pure BTrue) (A.Exists x p)).
  - apply AssertAndIntro; [apply AssertTrue |apply AssertRefl].
  - apply AssertExistsElim; [exact Hfresh |].
    eapply AssertTrans; [apply AssertAndRight |exact H].
Qed.

Lemma assert_derive_barrier_suffix active p annotation :
  assertion_derivation active (A.Temporal p (A.Barrier annotation)) p.
Proof.
  eapply AssertTrans with (q := A.Temporal p A.Emp).
  - apply (AssertSeparateMono active SepTemporal); [apply AssertRefl |apply AssertBarrierEmp].
  - apply (AssertUnitRight active SepTemporal Forward).
Qed.

Lemma assert_derive_drained_write_cell active address annotation value :
  assertion_derivation active (cell_body address annotation value) (writer_points_to address value).
Proof.
  unfold writer_points_to; change (assertion_derivation active (cell_body address annotation value)
    (A.Exists (fresh (expr_fv address ++ expr_fv value))
      (cell_body address (EVar (fresh (expr_fv address ++ expr_fv value))) value))).
  rewrite <- (assertion_cell_body_subst (fresh (expr_fv address ++ expr_fv value))
    annotation address value (fresh_not_in _)).
  apply AssertExistsIntro.
Qed.

(** Rename only the cell's hidden writer, using existential introduction
    and elimination. The replacement name may equal the original name. *)
Lemma assert_derive_cell_named active name address value :
  ~ In name (expr_fv address ++ expr_fv value) ->
  assertion_derivation active (writer_points_to address value)
    (A.Exists name (cell_body address (EVar name) value)).
Proof.
  intros Hname; unfold writer_points_to; apply assert_derive_exists_elim.
  - rewrite assertion_named_cell_fv by assumption; apply fresh_not_in.
  - change (assertion_derivation active
      (cell_body address (EVar (fresh (expr_fv address ++ expr_fv value))) value)
      (A.Exists name (cell_body address (EVar name) value))).
    rewrite <- (assertion_cell_body_subst name
      (EVar (fresh (expr_fv address ++ expr_fv value))) address value Hname).
    apply AssertExistsIntro.
Qed.

Lemma assert_derive_named_cell active name address value :
  ~ In name (expr_fv address ++ expr_fv value) ->
  assertion_derivation active (A.Exists name (cell_body address (EVar name) value))
    (writer_points_to address value).
Proof.
  intros Hfresh; apply assert_derive_exists_elim.
  - rewrite assertion_writer_cell_fv; exact Hfresh.
  - apply assert_derive_drained_write_cell.
Qed.

Theorem assert_derive_cell_value_hiding active x address value : ~ In x (expr_fv address) ->
  assertion_derivation active (writer_points_to address value)
    (A.Exists x (writer_points_to address (EVar x))).
Proof.
  intros Hfresh; rewrite <- (assertion_cell_value_subst x address value Hfresh).
  apply AssertExistsIntro.
Qed.

Theorem assert_derive_cells_exclusive active address old next :
  assertion_derivation active (A.Spatial (writer_points_to address old) (writer_points_to address next))
    (A.Pure BFalse).
Proof.
  set (names := expr_fv address ++ expr_fv old ++ expr_fv next).
  set (j := fresh names).
  set (i := fresh (j :: names)).
  assert (Hj : ~ In j names) by (unfold j; apply fresh_not_in).
  assert (Hi : ~ In i names /\ i <> j).
  { pose proof (fresh_not_in (j :: names)); fold i in H; cbn in H; intuition congruence. }
  unfold names in Hj,Hi; rewrite !in_app_iff in Hj,Hi.
  eapply AssertTrans with (q := A.Spatial
    (A.Exists i (cell_body address (EVar i) old))
    (A.Exists j (cell_body address (EVar j) next))).
  - apply (AssertSeparateMono active SepSpatial); apply assert_derive_cell_named;
      rewrite in_app_iff; tauto.
  - eapply AssertTrans.
    + apply (AssertExistsSeparateLeft active SepSpatial Forward).
      rewrite assertion_named_cell_fv by (rewrite in_app_iff; tauto).
      rewrite in_app_iff; tauto.
    + apply assert_derive_exists_elim; [cbn; tauto |].
      eapply AssertTrans.
      * apply (AssertExistsSeparateRight active SepSpatial Forward).
        rewrite assertion_cell_body_fv; cbn [expr_fv]. rewrite !in_app_iff; cbn; intuition congruence.
      * apply assert_derive_exists_elim; [cbn; tauto |].
        eapply AssertTrans with (q := A.Spatial (A.LeadsTo address (EVar i) old) (A.LeadsTo address (EVar j) next)).
        -- apply (AssertSeparateMono active SepSpatial); apply assert_derive_barrier_suffix.
        -- apply AssertWritesExclusive.
Qed.

(** The value binder need only be fresh for the address and final value;
    its freshness for the writer annotation is unnecessary in this route. *)
Theorem assert_derive_drained_history active x address annotation value :
  ~ In x (expr_fv address ++ expr_fv value) ->
  assertion_derivation active
    (A.Temporal
      (A.Temporal (A.Exists x (writer_points_to address (EVar x)))
        (A.LeadsTo address annotation value)) (A.Barrier annotation))
    (writer_points_to address value).
Proof.
  intros Hfresh.
  eapply AssertTrans; [apply (AssertBarrierDistribute active SepTemporal Forward) |].
  eapply AssertTrans with (q := A.Temporal (A.Exists x (writer_points_to address (EVar x)))
    (writer_points_to address value)).
  - apply (AssertSeparateMono active SepTemporal);
      [apply assert_derive_barrier_suffix |apply assert_derive_drained_write_cell].
  - eapply AssertTrans.
    + apply (AssertExistsSeparateLeft active SepTemporal Forward).
      rewrite assertion_writer_cell_fv; exact Hfresh.
    + apply assert_derive_exists_elim.
      * rewrite assertion_writer_cell_fv; exact Hfresh.
      * apply AssertCellOverwrite.
Qed.
