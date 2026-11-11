From Stdlib Require Import List Arith.PeanoNat.
From WMLR Require Import Expressions.
Import ListNotations.

(** Sections 3.5 and 3.5.3, including the separating implications introduced
    after the core sequential grammar. Binders use the same names as stacks. *)
Module SequentialAssertion.

Inductive assertion : Type :=
| Pure (condition : bexpr)
| Or (lhs rhs : assertion)
| And (lhs rhs : assertion)
| Exists (name : ident) (body : assertion)
| Forall (name : ident) (body : assertion)
| Emp
| Barrier
| LeadsTo (address contents : expr)
| Spatial (lhs rhs : assertion)
| Temporal (past future : assertion)
| SpatialWand (premise conclusion : assertion)
| TemporalWandLeft (past conclusion : assertion)
| TemporalWandRight (conclusion future : assertion).

Fixpoint fv (p : assertion) : list ident :=
  match p with
  | Pure b => bexpr_fv b
  | Emp | Barrier => []
  | LeadsTo address contents => expr_fv address ++ expr_fv contents
  | Exists x body | Forall x body => remove Nat.eq_dec x (fv body)
  | Or lhs rhs | And lhs rhs | Spatial lhs rhs | Temporal lhs rhs
  | SpatialWand lhs rhs | TemporalWandLeft lhs rhs
  | TemporalWandRight lhs rhs => fv lhs ++ fv rhs
  end.

Definition points_to (address contents : expr) : assertion :=
  Temporal (LeadsTo address contents) Barrier.

Definition strong_temporal (past future : assertion) : assertion :=
  And (Temporal past future) (Spatial past future).

Definition temporal_reverse (future past : assertion) : assertion :=
  Temporal past future.

Definition strong_temporal_reverse (future past : assertion) : assertion :=
  strong_temporal past future.

End SequentialAssertion.

(** The complete concurrent assertion grammar on pp. 113-115. There is no
    general assertion negation. BNot only negates a boolean expression. *)
Module ConcurrentAssertion.

Inductive assertion : Type :=
| Pure (condition : bexpr)
| Or (lhs rhs : assertion)
| And (lhs rhs : assertion)
| Exists (name : ident) (body : assertion)
| Forall (name : ident) (body : assertion)
| Emp
| Barrier (processor : expr)
| Lock (processor : expr)
| LeadsTo (address processor contents : expr)
| Spatial (lhs rhs : assertion)
| Temporal (past future : assertion)
| SpatialWand (premise conclusion : assertion)
| TemporalWandLeft (past conclusion : assertion)
| TemporalWandRight (conclusion future : assertion).

Fixpoint fv (p : assertion) : list ident :=
  match p with
  | Pure b => bexpr_fv b
  | Emp => []
  | Barrier processor | Lock processor => expr_fv processor
  | LeadsTo address processor contents =>
      expr_fv address ++ expr_fv processor ++ expr_fv contents
  | Exists x body | Forall x body => remove Nat.eq_dec x (fv body)
  | Or lhs rhs | And lhs rhs | Spatial lhs rhs | Temporal lhs rhs
  | SpatialWand lhs rhs | TemporalWandLeft lhs rhs
  | TemporalWandRight lhs rhs => fv lhs ++ fv rhs
  end.

Definition strong_temporal (past future : assertion) : assertion :=
  And (Spatial past future) (Temporal past future).

Definition temporal_reverse (future past : assertion) : assertion :=
  Temporal past future.

Definition strong_temporal_reverse (future past : assertion) : assertion :=
  strong_temporal past future.

(** Section 4.4.2. Choosing a fresh bound name prevents the existential
    processor variable from capturing variables in address or contents. *)
Definition points_to (address contents : expr) : assertion :=
  let processor_name := fresh (expr_fv address ++ expr_fv contents) in
  Temporal
    (Exists processor_name (LeadsTo address (EVar processor_name) contents))
    (Forall processor_name (Barrier (EVar processor_name))).

Lemma points_to_binder_fresh address contents :
  ~ In (fresh (expr_fv address ++ expr_fv contents)) (expr_fv address) /\
  ~ In (fresh (expr_fv address ++ expr_fv contents)) (expr_fv contents).
Proof.
  pose proof (fresh_not_in (expr_fv address ++ expr_fv contents)) as H.
  rewrite in_app_iff in H. tauto.
Qed.

Theorem points_to_fv address contents x :
  In x (fv (points_to address contents)) <->
  In x (expr_fv address) \/ In x (expr_fv contents).
Proof.
  unfold points_to. cbn [fv expr_fv].
  set (name := fresh (expr_fv address ++ expr_fv contents)).
  assert (Hfresh : ~ In name (expr_fv address ++ expr_fv contents)).
  { unfold name. apply fresh_not_in. }
  assert (Hremove : remove Nat.eq_dec name [name] = []).
  { change ((if Nat.eq_dec name name then [] else [name]) = []).
    destruct (Nat.eq_dec name name); congruence. }
  rewrite Hremove, app_nil_r. split.
  - intros H. apply in_remove in H. destruct H as [H Hneq].
    rewrite in_app_iff in H. simpl in H. intuition congruence.
  - intros H. apply in_in_remove.
    + intros Heq. subst x. apply Hfresh. rewrite in_app_iff. exact H.
    + rewrite in_app_iff. simpl. tauto.
Qed.

End ConcurrentAssertion.
