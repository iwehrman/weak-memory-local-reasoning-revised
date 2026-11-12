From Stdlib Require Import List Arith ZArith.
From WMLR Require Import Expressions Assertions AssertionSemantics PersistentAssertions.
Import ListNotations.

(** Simultaneous substitution freshens binders using the free variables of
    the substituted free names. Recursion is on the original assertion, so
    neither fuel nor a partial substitution operation is needed. *)
Fixpoint substitute_expression (sigma : ident -> expr) e : expr :=
  match e with
  | EVal v => EVal v
  | EVar x => sigma x
  | EAdd a b => EAdd (substitute_expression sigma a) (substitute_expression sigma b)
  | ESub a b => ESub (substitute_expression sigma a) (substitute_expression sigma b)
  end.

Fixpoint substitute_boolean (sigma : ident -> expr) b : bexpr :=
  match b with
  | BFalse => BFalse | BTrue => BTrue
  | BNot b => BNot (substitute_boolean sigma b)
  | BEq a b => BEq (substitute_expression sigma a) (substitute_expression sigma b)
  end.

Definition substitution_stack (sigma : ident -> expr) s : stack :=
  fun x => eval_expr s (sigma x).

Definition substitution_name sigma x p :=
  fresh (flat_map (fun y => expr_fv (sigma y)) (remove Nat.eq_dec x (A.fv p))).

Definition substitution_binder sigma x z : ident -> expr :=
  fun y => if Nat.eq_dec y x then EVar z else sigma y.

Fixpoint substitute_assertion (sigma : ident -> expr) p : A.assertion :=
  match p with
  | A.Pure b => A.Pure (substitute_boolean sigma b)
  | A.Or a b => A.Or (substitute_assertion sigma a) (substitute_assertion sigma b)
  | A.And a b => A.And (substitute_assertion sigma a) (substitute_assertion sigma b)
  | A.Exists x p => let z := substitution_name sigma x p in
      A.Exists z (substitute_assertion (substitution_binder sigma x z) p)
  | A.Forall x p => let z := substitution_name sigma x p in
      A.Forall z (substitute_assertion (substitution_binder sigma x z) p)
  | A.Emp => A.Emp
  | A.Barrier i => A.Barrier (substitute_expression sigma i)
  | A.Lock i => A.Lock (substitute_expression sigma i)
  | A.LeadsTo e i v => A.LeadsTo (substitute_expression sigma e)
      (substitute_expression sigma i) (substitute_expression sigma v)
  | A.Spatial a b => A.Spatial (substitute_assertion sigma a) (substitute_assertion sigma b)
  | A.Temporal a b => A.Temporal (substitute_assertion sigma a) (substitute_assertion sigma b)
  | A.SpatialWand a b => A.SpatialWand (substitute_assertion sigma a) (substitute_assertion sigma b)
  | A.TemporalWandLeft a b => A.TemporalWandLeft (substitute_assertion sigma a) (substitute_assertion sigma b)
  | A.TemporalWandRight a b => A.TemporalWandRight (substitute_assertion sigma a) (substitute_assertion sigma b)
  end.

Definition assertion_subst x rhs p :=
  substitute_assertion (fun y => if Nat.eq_dec y x then rhs else EVar y) p.

Lemma eval_substitute_expression sigma e s :
  eval_expr s (substitute_expression sigma e) = eval_expr (substitution_stack sigma s) e.
Proof. induction e; cbn; try reflexivity; rewrite IHe1, IHe2; reflexivity. Qed.

Lemma eval_substitute_boolean sigma b s :
  eval_bexpr s (substitute_boolean sigma b) = eval_bexpr (substitution_stack sigma s) b.
Proof. induction b; cbn; try congruence; rewrite !eval_substitute_expression; reflexivity. Qed.

Lemma substitution_binder_agrees sigma x p s v :
  let z := substitution_name sigma x p in
  agrees (A.fv p) (substitution_stack (substitution_binder sigma x z) (update s z v))
    (update (substitution_stack sigma s) x v).
Proof.
  cbn zeta; intros y Hy; unfold substitution_stack, substitution_binder, update at 2.
  destruct (Nat.eq_dec y x) as [-> |Hne].
  - cbn [eval_expr]; apply update_same.
  - apply eval_expr_update_irrelevant.
    intros Hbad; apply (fresh_not_in
      (flat_map (fun y => expr_fv (sigma y)) (remove Nat.eq_dec x (A.fv p)))).
    apply in_flat_map; exists y; split; [apply in_in_remove; [congruence |exact Hy] |exact Hbad].
Qed.

Theorem future_satisfies_substitute {R} (model : interpretation R) future p sigma s r :
  future_satisfies model future s r (substitute_assertion sigma p) <->
  future_satisfies model future (substitution_stack sigma s) r p.
Proof.
  revert sigma s r; induction p; intros sigma s r; cbn [substitute_assertion future_satisfies].
  - rewrite eval_substitute_boolean; reflexivity.
  - rewrite IHp1, IHp2; reflexivity.
  - rewrite IHp1, IHp2; reflexivity.
  - split; intros [v Hv]; exists v.
    + apply (proj1 (future_satisfies_agrees model future p _ _
        (substitution_binder_agrees sigma name p s v) r)), (proj1 (IHp _ _ _)), Hv.
    + apply (proj2 (IHp _ _ _)), (proj2 (future_satisfies_agrees model future p _ _
        (substitution_binder_agrees sigma name p s v) r)), Hv.
  - split; intros H v.
    + apply (proj1 (future_satisfies_agrees model future p _ _
        (substitution_binder_agrees sigma name p s v) r)), (proj1 (IHp _ _ _)), H.
    + apply (proj2 (IHp _ _ _)), (proj2 (future_satisfies_agrees model future p _ _
        (substitution_binder_agrees sigma name p s v) r)), H.
  - reflexivity.
  - rewrite eval_substitute_expression; reflexivity.
  - rewrite eval_substitute_expression; reflexivity.
  - rewrite !eval_substitute_expression; reflexivity.
  - split; intros (a & b & Hsplit & Ha & Hb); exists a, b; split; [exact Hsplit | |exact Hsplit |];
      split; [apply (proj1 (IHp1 _ _ _)), Ha |apply (proj1 (IHp2 _ _ _)), Hb
             |apply (proj2 (IHp1 _ _ _)), Ha |apply (proj2 (IHp2 _ _ _)), Hb].
  - split; intros (a & b & Hsplit & Ha & Hb); exists a, b; split; [exact Hsplit | |exact Hsplit |];
      split; [apply (proj1 (IHp1 _ _ _)), Ha |apply (proj1 (IHp2 _ _ _)), Hb
             |apply (proj2 (IHp1 _ _ _)), Ha |apply (proj2 (IHp2 _ _ _)), Hb].
  - split; intros H later Hfuture a out Ha Hsplit.
    + apply (proj1 (IHp2 _ _ _)), (H later Hfuture a out); [apply (proj2 (IHp1 _ _ _)), Ha |exact Hsplit].
    + apply (proj2 (IHp2 _ _ _)), (H later Hfuture a out); [apply (proj1 (IHp1 _ _ _)), Ha |exact Hsplit].
  - split; intros H later Hfuture a out Ha Hsplit.
    + apply (proj1 (IHp2 _ _ _)), (H later Hfuture a out); [apply (proj2 (IHp1 _ _ _)), Ha |exact Hsplit].
    + apply (proj2 (IHp2 _ _ _)), (H later Hfuture a out); [apply (proj1 (IHp1 _ _ _)), Ha |exact Hsplit].
  - split; intros H later Hfuture a out Ha Hsplit.
    + apply (proj1 (IHp1 _ _ _)), (H later Hfuture a out); [apply (proj2 (IHp2 _ _ _)), Ha |exact Hsplit].
    + apply (proj2 (IHp1 _ _ _)), (H later Hfuture a out); [apply (proj1 (IHp2 _ _ _)), Ha |exact Hsplit].
Qed.

Theorem future_satisfies_subst {R} (model : interpretation R) future p x rhs s r :
  future_satisfies model future s r (assertion_subst x rhs p) <->
  future_satisfies model future (update s x (eval_expr s rhs)) r p.
Proof.
  unfold assertion_subst; rewrite future_satisfies_substitute.
  apply future_satisfies_agrees; intros y Hy.
  unfold substitution_stack, update; destruct (Nat.eq_dec y x); reflexivity.
Qed.

Corollary persistent_assertion_subst active p x rhs s r :
  persistent_models active s r (assertion_subst x rhs p) <->
  persistent_models active (update s x (eval_expr s rhs)) r p.
Proof. apply future_satisfies_subst. Qed.
