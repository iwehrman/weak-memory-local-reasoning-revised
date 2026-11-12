From Stdlib Require Import List Arith ZArith.
From WMLR Require Import Expressions Assertions AssertionSemantics AssertionSubstitution InvariantFragment.
Import ListNotations.

(** Syntactic facts only: these equations normalize the existing
    capture-avoiding substitution; they are not entailment or alpha rules. *)
Lemma assertion_expression_substitution_agrees sigma tau e :
  (forall x, In x (expr_fv e) -> sigma x = tau x) ->
  substitute_expression sigma e = substitute_expression tau e.
Proof.
  induction e; cbn; intros H; try reflexivity.
  - apply H; auto.
  - f_equal; [apply IHe1 |apply IHe2]; intros x Hx; apply H,in_or_app; auto.
  - f_equal; [apply IHe1 |apply IHe2]; intros x Hx; apply H,in_or_app; auto.
Qed.

Lemma assertion_expression_substitution_identity e : substitute_expression EVar e = e.
Proof. induction e; cbn; congruence. Qed.

Lemma assertion_expression_substitution_fv sigma e :
  expr_fv (substitute_expression sigma e) = flat_map (fun x => expr_fv (sigma x)) (expr_fv e).
Proof. induction e; cbn; try reflexivity; rewrite ?app_nil_r,?IHe1,?IHe2,?flat_map_app; reflexivity. Qed.

Lemma assertion_expression_substitution_irrelevant x expression e : ~ In x (expr_fv e) ->
  substitute_expression (fun y => if Nat.eq_dec y x then expression else EVar y) e = e.
Proof.
  intros Hfresh; rewrite <- (assertion_expression_substitution_identity e) at 2.
  apply assertion_expression_substitution_agrees; intros y Hy.
  destruct (Nat.eq_dec y x); [subst; contradiction |reflexivity].
Qed.

Lemma assertion_expression_binder_irrelevant sigma x z e : ~ In x (expr_fv e) ->
  substitute_expression (substitution_binder sigma x z) e = substitute_expression sigma e.
Proof.
  intros Hfresh; apply assertion_expression_substitution_agrees; intros y Hy.
  unfold substitution_binder; destruct (Nat.eq_dec y x); [subst; contradiction |reflexivity].
Qed.

Definition cell_body address annotation value :=
  A.Temporal (A.LeadsTo address annotation value) (A.Barrier annotation).

Lemma assertion_cell_body_subst x expression address value :
  ~ In x (expr_fv address ++ expr_fv value) ->
  assertion_subst x expression (cell_body address (EVar x) value) = cell_body address expression value.
Proof.
  intros Hfresh; rewrite in_app_iff in Hfresh.
  unfold assertion_subst,cell_body; cbn [substitute_assertion substitute_expression].
  destruct (Nat.eq_dec x x); [|contradiction].
  rewrite !assertion_expression_substitution_irrelevant by tauto; reflexivity.
Qed.

Lemma assertion_cell_body_fv address annotation value :
  A.fv (cell_body address annotation value) =
    (expr_fv address ++ expr_fv annotation ++ expr_fv value) ++ expr_fv annotation.
Proof. reflexivity. Qed.

Lemma assertion_named_cell_fv name address value :
  ~ In name (expr_fv address ++ expr_fv value) ->
  A.fv (A.Exists name (cell_body address (EVar name) value)) = expr_fv address ++ expr_fv value.
Proof.
  intros Hfresh; rewrite in_app_iff in Hfresh.
  cbn [A.fv cell_body expr_fv]. rewrite !remove_app,!remove_cons.
  rewrite !notin_remove by tauto; cbn; rewrite !app_nil_r; reflexivity.
Qed.

Lemma assertion_writer_cell_fv address value :
  A.fv (writer_points_to address value) = expr_fv address ++ expr_fv value.
Proof. apply assertion_named_cell_fv,fresh_not_in. Qed.

Theorem assertion_substitute_writer_cell sigma address value :
  substitute_assertion sigma (writer_points_to address value) =
  writer_points_to (substitute_expression sigma address) (substitute_expression sigma value).
Proof.
  pose proof (A.points_to_binder_fresh address value) as [Ha Hv].
  unfold writer_points_to at 1; cbn [substitute_assertion].
  rewrite (assertion_expression_binder_irrelevant sigma _ _ address Ha),
    (assertion_expression_binder_irrelevant sigma _ _ value Hv).
  cbn [substitute_expression]; unfold substitution_binder.
  destruct (Nat.eq_dec (fresh (expr_fv address ++ expr_fv value))
    (fresh (expr_fv address ++ expr_fv value))); [|contradiction].
  unfold substitution_name.
  change (A.Exists
    (fresh (flat_map (fun y => expr_fv (sigma y))
      (A.fv (writer_points_to address value))))
    (cell_body (substitute_expression sigma address)
      (EVar (fresh (flat_map (fun y => expr_fv (sigma y))
        (A.fv (writer_points_to address value)))))
      (substitute_expression sigma value)) =
    writer_points_to (substitute_expression sigma address) (substitute_expression sigma value)).
  rewrite assertion_writer_cell_fv,flat_map_app.
  rewrite <- !assertion_expression_substitution_fv; reflexivity.
Qed.

Corollary assertion_cell_value_subst x address value : ~ In x (expr_fv address) ->
  assertion_subst x value (writer_points_to address (EVar x)) = writer_points_to address value.
Proof.
  intros Hfresh; unfold assertion_subst; rewrite assertion_substitute_writer_cell.
  rewrite assertion_expression_substitution_irrelevant by assumption.
  cbn [substitute_expression]; destruct (Nat.eq_dec x x); congruence.
Qed.
