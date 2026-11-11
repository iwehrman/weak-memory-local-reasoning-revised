From Stdlib Require Import List Arith.PeanoNat.
From WMLR Require Import Expressions Assertions.
Import ListNotations.

(** A semantic interface for Figure 4.4. Each interpretation supplies a
    resource model, atomic predicates and two composition relations.
    ConcreteAssertions supplies the multiprocessor memory interpretation.
    In particular, this record assumes no separation-algebra laws. *)
Record interpretation (resource : Type) := {
  empty_resource : resource -> Prop;
  barrier_resource : value -> resource -> Prop;
  lock_resource : value -> resource -> Prop;
  write_resource : value -> value -> value -> resource -> Prop;
  spatial_composition : resource -> resource -> resource -> Prop;
  temporal_composition : resource -> resource -> resource -> Prop
}.

Arguments empty_resource {resource} _ _.
Arguments barrier_resource {resource} _ _ _.
Arguments lock_resource {resource} _ _ _.
Arguments write_resource {resource} _ _ _ _ _.
Arguments spatial_composition {resource} _ _ _ _.
Arguments temporal_composition {resource} _ _ _ _.

Module A := ConcurrentAssertion.

Fixpoint satisfies {resource : Type} (model : interpretation resource)
    (s : stack) (r : resource) (p : A.assertion) : Prop :=
  match p with
  | A.Pure b => eval_bexpr s b = true
  | A.Or lhs rhs => satisfies model s r lhs \/ satisfies model s r rhs
  | A.And lhs rhs => satisfies model s r lhs /\ satisfies model s r rhs
  | A.Exists x body => exists v, satisfies model (update s x v) r body
  | A.Forall x body => forall v, satisfies model (update s x v) r body
  | A.Emp => empty_resource model r
  | A.Barrier processor => barrier_resource model (eval_expr s processor) r
  | A.Lock processor => lock_resource model (eval_expr s processor) r
  | A.LeadsTo address processor contents =>
      write_resource model (eval_expr s address) (eval_expr s processor)
        (eval_expr s contents) r
  | A.Spatial lhs rhs =>
      exists r1 r2, spatial_composition model r1 r2 r /\
        satisfies model s r1 lhs /\ satisfies model s r2 rhs
  | A.Temporal past future =>
      exists r1 r2, temporal_composition model r1 r2 r /\
        satisfies model s r1 past /\ satisfies model s r2 future
  | A.SpatialWand premise conclusion =>
      forall r0 r1, satisfies model s r0 premise ->
        spatial_composition model r0 r r1 -> satisfies model s r1 conclusion
  | A.TemporalWandLeft past conclusion =>
      forall r0 r1, satisfies model s r0 past ->
        temporal_composition model r0 r r1 -> satisfies model s r1 conclusion
  | A.TemporalWandRight conclusion future =>
      forall r0 r1, satisfies model s r0 future ->
        temporal_composition model r r0 r1 -> satisfies model s r1 conclusion
  end.

Lemma agrees_under_binder xs s t x v :
  agrees (remove Nat.eq_dec x xs) s t ->
  agrees xs (update s x v) (update t x v).
Proof.
  intros H y Hin. unfold update. destruct (Nat.eq_dec y x) as [Heq | Hneq].
  - reflexivity.
  - apply H. apply in_in_remove; assumption.
Qed.

(** The concurrent version of Lemma 3, including all three wands and both
    quantifiers. The proof works for every interpretation above. *)
Theorem satisfies_agrees {resource} (model : interpretation resource) p s t :
  agrees (A.fv p) s t ->
  forall r, satisfies model s r p <-> satisfies model t r p.
Proof.
  revert s t. induction p; intros s t H r; simpl in *.
  - rewrite (eval_bexpr_agrees _ _ _ H). reflexivity.
  - rewrite (IHp1 s t (agrees_app_left _ _ _ _ H) r),
            (IHp2 s t (agrees_app_right _ _ _ _ H) r). reflexivity.
  - rewrite (IHp1 s t (agrees_app_left _ _ _ _ H) r),
            (IHp2 s t (agrees_app_right _ _ _ _ H) r). reflexivity.
  - split; intros [v Hv]; exists v.
    + apply (proj1 (IHp _ _ (agrees_under_binder _ _ _ _ _ H) r)), Hv.
    + apply (proj2 (IHp _ _ (agrees_under_binder _ _ _ _ _ H) r)), Hv.
  - split; intros Hv v.
    + apply (proj1 (IHp _ _ (agrees_under_binder _ _ _ _ _ H) r)), Hv.
    + apply (proj2 (IHp _ _ (agrees_under_binder _ _ _ _ _ H) r)), Hv.
  - reflexivity.
  - rewrite (eval_expr_agrees _ _ _ H). reflexivity.
  - rewrite (eval_expr_agrees _ _ _ H). reflexivity.
  - pose proof (agrees_app_left _ _ _ _ H) as Haddr.
    pose proof (agrees_app_right _ _ _ _ H) as Hrest.
    rewrite (eval_expr_agrees _ _ _ Haddr),
            (eval_expr_agrees _ _ _ (agrees_app_left _ _ _ _ Hrest)),
            (eval_expr_agrees _ _ _ (agrees_app_right _ _ _ _ Hrest)).
    reflexivity.
  - split; intros [r1 [r2 [Hsplit [Hleft Hright]]]];
      exists r1, r2; split; [exact Hsplit | | exact Hsplit | ]; split.
    + apply (proj1 (IHp1 _ _ (agrees_app_left _ _ _ _ H) r1)), Hleft.
    + apply (proj1 (IHp2 _ _ (agrees_app_right _ _ _ _ H) r2)), Hright.
    + apply (proj2 (IHp1 _ _ (agrees_app_left _ _ _ _ H) r1)), Hleft.
    + apply (proj2 (IHp2 _ _ (agrees_app_right _ _ _ _ H) r2)), Hright.
  - split; intros [r1 [r2 [Hsplit [Hleft Hright]]]];
      exists r1, r2; split; [exact Hsplit | | exact Hsplit | ]; split.
    + apply (proj1 (IHp1 _ _ (agrees_app_left _ _ _ _ H) r1)), Hleft.
    + apply (proj1 (IHp2 _ _ (agrees_app_right _ _ _ _ H) r2)), Hright.
    + apply (proj2 (IHp1 _ _ (agrees_app_left _ _ _ _ H) r1)), Hleft.
    + apply (proj2 (IHp2 _ _ (agrees_app_right _ _ _ _ H) r2)), Hright.
  - split; intros Hwand r0 r1 Hprem Hcomp.
    + apply (proj1 (IHp2 _ _ (agrees_app_right _ _ _ _ H) r1)).
      apply Hwand with (r0 := r0); [|exact Hcomp].
      apply (proj2 (IHp1 _ _ (agrees_app_left _ _ _ _ H) r0)), Hprem.
    + apply (proj2 (IHp2 _ _ (agrees_app_right _ _ _ _ H) r1)).
      apply Hwand with (r0 := r0); [|exact Hcomp].
      apply (proj1 (IHp1 _ _ (agrees_app_left _ _ _ _ H) r0)), Hprem.
  - split; intros Hwand r0 r1 Hprem Hcomp.
    + apply (proj1 (IHp2 _ _ (agrees_app_right _ _ _ _ H) r1)).
      apply Hwand with (r0 := r0); [|exact Hcomp].
      apply (proj2 (IHp1 _ _ (agrees_app_left _ _ _ _ H) r0)), Hprem.
    + apply (proj2 (IHp2 _ _ (agrees_app_right _ _ _ _ H) r1)).
      apply Hwand with (r0 := r0); [|exact Hcomp].
      apply (proj1 (IHp1 _ _ (agrees_app_left _ _ _ _ H) r0)), Hprem.
  - split; intros Hwand r0 r1 Hprem Hcomp.
    + apply (proj1 (IHp1 _ _ (agrees_app_left _ _ _ _ H) r1)).
      apply Hwand with (r0 := r0); [|exact Hcomp].
      apply (proj2 (IHp2 _ _ (agrees_app_right _ _ _ _ H) r0)), Hprem.
    + apply (proj2 (IHp1 _ _ (agrees_app_left _ _ _ _ H) r1)).
      apply Hwand with (r0 := r0); [|exact Hcomp].
      apply (proj1 (IHp2 _ _ (agrees_app_right _ _ _ _ H) r0)), Hprem.
Qed.

Corollary satisfies_update_irrelevant {resource} (model : interpretation resource)
    p s r x v :
  ~ In x (A.fv p) ->
  (satisfies model s r p <-> satisfies model (update s x v) r p).
Proof.
  intros H. apply satisfies_agrees, agrees_update_irrelevant, H.
Qed.
