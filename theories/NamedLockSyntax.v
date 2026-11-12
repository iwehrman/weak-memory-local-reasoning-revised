From Stdlib Require Import List ZArith.
From WMLR Require Import Expressions Languages Machine OperationalSemantics Assertions AssertionSemantics
  InvariantFragment AssertionCellSubstitution.
Import ListNotations.

Definition nl_cell flag value := writer_points_to (EVal (Z.pos flag)) (EVal value).
Definition nl_component flag invariant := A.Or (A.Spatial (nl_cell flag 0%Z) invariant) (nl_cell flag 1%Z).
Definition nl_family := list (location * A.assertion).
Fixpoint nl_pool (locks : nl_family) : A.assertion :=
  match locks with
  | [] => A.Emp
  | (flag,invariant) :: rest => A.Spatial (nl_component flag invariant) (nl_pool rest)
  end.
Definition nl_is x value := BEq (EVar x) (EVal value).
Definition nl_held actor payload := A.Spatial (A.Lock (EVal (Z.pos actor))) payload.
Definition nl_acquire_global actor := C.Prim C.Lock (EVal (Z.pos actor)).
Definition nl_release_global actor := C.Prim C.Unlock (EVal (Z.pos actor)).
Definition nl_store actor flag value := C.Prim (C.Common (S.Store (EVal (Z.pos flag)) (EVal value))) (EVal (Z.pos actor)).
Definition nl_load actor flag x := C.Prim (C.Common (S.Load x (EVal (Z.pos flag)))) (EVal (Z.pos actor)).
Definition nl_attempt actor flag x := C.Seq (nl_acquire_global actor)
  (C.Seq (nl_load actor flag x) (C.if_then_else (EVal (Z.pos actor)) (nl_is x 0%Z)
    (C.Seq (nl_store actor flag 1%Z) (nl_release_global actor)) (nl_release_global actor))).
Definition nl_acquire actor flag x := C.Seq
  (C.Prim (C.Common (S.Assign x (EVal 1%Z))) (EVal (Z.pos actor)))
  (C.while_do (EVal (Z.pos actor)) (nl_is x 1%Z) (nl_attempt actor flag x)).
Definition nl_release actor flag := C.Seq (nl_acquire_global actor)
  (C.Seq (nl_store actor flag 0%Z) (nl_release_global actor)).

Definition nl_cases actor flag invariant rest := A.Or
  (nl_held actor (A.Spatial (nl_cell flag 0%Z) (A.Spatial invariant rest)))
  (nl_held actor (A.Spatial (nl_cell flag 1%Z) rest)).
Definition nl_read_cases actor flag x invariant rest := A.Or
  (A.And (nl_held actor (A.Spatial (nl_cell flag 0%Z) (A.Spatial invariant rest))) (A.Pure (nl_is x 0%Z)))
  (A.And (nl_held actor (A.Spatial (nl_cell flag 1%Z) rest)) (A.Pure (nl_is x 1%Z))).
Definition nl_loop_invariant x invariant := A.Or (A.And invariant (A.Pure (nl_is x 0%Z)))
  (A.And A.Emp (A.Pure (nl_is x 1%Z))).

Lemma nl_cell_fv flag value : A.fv (nl_cell flag value) = [].
Proof. apply assertion_writer_cell_fv. Qed.

Lemma nl_component_fv flag invariant : A.fv (nl_component flag invariant) = A.fv invariant.
Proof. cbn [nl_component A.fv]; rewrite !nl_cell_fv; cbn; apply app_nil_r. Qed.

Lemma nl_component_fragment flag invariant : invariant_fragment invariant -> invariant_fragment (nl_component flag invariant).
Proof. intros H; constructor; [constructor; [constructor |exact H] |constructor]. Qed.

Theorem nl_pool_fragment locks : Forall (fun item => invariant_fragment (snd item)) locks ->
  invariant_fragment (nl_pool locks).
Proof. induction 1 as [|[flag invariant] rest HI HR IH]; [constructor |constructor; [apply nl_component_fragment,HI |exact IH]]. Qed.

Lemma nl_acquire_modifies actor flag x : forall y, In y (C.modifies (nl_acquire actor flag x)) <-> y = x.
Proof. cbn; intros y; intuition congruence. Qed.

Lemma nl_release_modifies actor flag : C.modifies (nl_release actor flag) = [].
Proof. reflexivity. Qed.
