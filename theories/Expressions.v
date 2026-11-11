From Stdlib Require Import List Arith.PeanoNat ZArith Bool Lia.
Import ListNotations.

(** Dissertation sections 2.1 and 3.2. Identifiers are natural-number names.
    Values remain mathematical integers. Variable lists represent finite sets
    through membership, so ordering and duplicate entries are immaterial. *)
Definition ident := nat.
Definition value := Z.
Definition stack := ident -> value.

Definition update (s : stack) (x : ident) (v : value) : stack :=
  fun y => if Nat.eq_dec y x then v else s y.

Definition agrees (xs : list ident) (s t : stack) : Prop :=
  forall x, In x xs -> s x = t x.

Lemma update_same s x v : update s x v x = v.
Proof. unfold update; destruct (Nat.eq_dec x x); congruence. Qed.

Lemma update_other s x y v : x <> y -> update s x v y = s y.
Proof. unfold update; destruct (Nat.eq_dec y x); congruence. Qed.

Lemma agrees_app_left xs ys s t :
  agrees (xs ++ ys) s t -> agrees xs s t.
Proof. unfold agrees; intros H x Hin; apply H, in_or_app; auto. Qed.

Lemma agrees_app_right xs ys s t :
  agrees (xs ++ ys) s t -> agrees ys s t.
Proof. unfold agrees; intros H x Hin; apply H, in_or_app; auto. Qed.

Lemma agrees_update_irrelevant xs s x v :
  ~ In x xs -> agrees xs s (update s x v).
Proof.
  intros Hfresh y Hin. symmetry. apply update_other.
  intros Heq. subst y. contradiction.
Qed.

(** The explicit arithmetic grammar on p. 39. Additional operators left as
    ellipses in the dissertation can be added when a proof needs them. *)
Inductive expr : Type :=
| EVal (v : value)
| EVar (x : ident)
| EAdd (lhs rhs : expr)
| ESub (lhs rhs : expr).

Inductive bexpr : Type :=
| BFalse
| BTrue
| BNot (body : bexpr)
| BEq (lhs rhs : expr).

Fixpoint eval_expr (s : stack) (e : expr) : value :=
  match e with
  | EVal v => v
  | EVar x => s x
  | EAdd lhs rhs => (eval_expr s lhs + eval_expr s rhs)%Z
  | ESub lhs rhs => (eval_expr s lhs - eval_expr s rhs)%Z
  end.

Fixpoint eval_bexpr (s : stack) (b : bexpr) : bool :=
  match b with
  | BFalse => false
  | BTrue => true
  | BNot body => negb (eval_bexpr s body)
  | BEq lhs rhs => Z.eqb (eval_expr s lhs) (eval_expr s rhs)
  end.

Fixpoint expr_fv (e : expr) : list ident :=
  match e with
  | EVal _ => []
  | EVar x => [x]
  | EAdd lhs rhs | ESub lhs rhs => expr_fv lhs ++ expr_fv rhs
  end.

Fixpoint bexpr_fv (b : bexpr) : list ident :=
  match b with
  | BFalse | BTrue => []
  | BNot body => bexpr_fv body
  | BEq lhs rhs => expr_fv lhs ++ expr_fv rhs
  end.

(** Lemma 1, p. 41, including its boolean counterpart. *)
Theorem eval_expr_agrees e s t :
  agrees (expr_fv e) s t -> eval_expr s e = eval_expr t e.
Proof.
  induction e; simpl; intros H; try reflexivity.
  - apply H. simpl; auto.
  - rewrite (IHe1 (agrees_app_left _ _ _ _ H)),
            (IHe2 (agrees_app_right _ _ _ _ H)). reflexivity.
  - rewrite (IHe1 (agrees_app_left _ _ _ _ H)),
            (IHe2 (agrees_app_right _ _ _ _ H)). reflexivity.
Qed.

Theorem eval_bexpr_agrees b s t :
  agrees (bexpr_fv b) s t -> eval_bexpr s b = eval_bexpr t b.
Proof.
  induction b; simpl; intros H; try reflexivity.
  - rewrite (IHb H). reflexivity.
  - rewrite (eval_expr_agrees _ _ _ (agrees_app_left _ _ _ _ H)),
            (eval_expr_agrees _ _ _ (agrees_app_right _ _ _ _ H)).
    reflexivity.
Qed.

Corollary eval_expr_update_irrelevant e s x v :
  ~ In x (expr_fv e) -> eval_expr (update s x v) e = eval_expr s e.
Proof.
  intros H. symmetry. apply eval_expr_agrees, agrees_update_irrelevant, H.
Qed.

Corollary eval_bexpr_update_irrelevant b s x v :
  ~ In x (bexpr_fv b) -> eval_bexpr (update s x v) b = eval_bexpr s b.
Proof.
  intros H. symmetry. apply eval_bexpr_agrees, agrees_update_irrelevant, H.
Qed.

Fixpoint subst_expr (x : ident) (replacement e : expr) : expr :=
  match e with
  | EVal v => EVal v
  | EVar y => if Nat.eq_dec y x then replacement else EVar y
  | EAdd lhs rhs =>
      EAdd (subst_expr x replacement lhs) (subst_expr x replacement rhs)
  | ESub lhs rhs =>
      ESub (subst_expr x replacement lhs) (subst_expr x replacement rhs)
  end.

Fixpoint subst_bexpr (x : ident) (replacement : expr) (b : bexpr) : bexpr :=
  match b with
  | BFalse => BFalse
  | BTrue => BTrue
  | BNot body => BNot (subst_bexpr x replacement body)
  | BEq lhs rhs =>
      BEq (subst_expr x replacement lhs) (subst_expr x replacement rhs)
  end.

Theorem eval_subst_expr e x replacement s :
  eval_expr s (subst_expr x replacement e) =
  eval_expr (update s x (eval_expr s replacement)) e.
Proof.
  induction e; simpl; try (rewrite IHe1, IHe2; reflexivity).
  - reflexivity.
  - unfold update. destruct (Nat.eq_dec x0 x); reflexivity.
Qed.

Theorem eval_subst_bexpr b x replacement s :
  eval_bexpr s (subst_bexpr x replacement b) =
  eval_bexpr (update s x (eval_expr s replacement)) b.
Proof.
  induction b; simpl; try reflexivity.
  - rewrite IHb. reflexivity.
  - rewrite !eval_subst_expr. reflexivity.
Qed.

Lemma subst_expr_irrelevant e x replacement :
  ~ In x (expr_fv e) -> subst_expr x replacement e = e.
Proof.
  induction e; simpl; intros H; try reflexivity.
  - destruct (Nat.eq_dec x0 x); [subst; exfalso; apply H; auto | reflexivity].
  - rewrite IHe1, IHe2; try reflexivity;
      intros Hin; apply H, in_or_app; auto.
  - rewrite IHe1, IHe2; try reflexivity;
      intros Hin; apply H, in_or_app; auto.
Qed.

(** Fresh names for assertion abbreviations with bound variables. *)
Fixpoint max_name (xs : list ident) : ident :=
  match xs with
  | [] => 0
  | x :: rest => Nat.max x (max_name rest)
  end.

Definition fresh (xs : list ident) : ident := S (max_name xs).

Lemma in_max_name x xs : In x xs -> x <= max_name xs.
Proof.
  induction xs as [|y ys IH]; simpl; intros H.
  - contradiction.
  - destruct H as [-> | H].
    + apply Nat.le_max_l.
    + eapply Nat.le_trans; [apply IH, H | apply Nat.le_max_r].
Qed.

Theorem fresh_not_in xs : ~ In (fresh xs) xs.
Proof. intros H. apply in_max_name in H. unfold fresh in H. lia. Qed.
