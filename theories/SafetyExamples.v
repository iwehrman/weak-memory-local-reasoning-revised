From Stdlib Require Import List ZArith.
From WMLR Require Import Expressions Languages Machine Separation OperationalSemantics
  Assertions AssertionSemantics ConcreteAssertions SeparationExamples Safety.
Import ListNotations.

Lemma empty_memory_well_formed active : memory_well_formed active empty_memory.
Proof. split; [intros i H; contradiction | intros i _; reflexivity]. Qed.

Lemma empty_memory_not_locked : ~ locked all_processors empty_memory.
Proof.
  intros [owner [_ Hblocks]]. destruct (Pos.eq_dec owner 1%positive) as [Heq | Hneq].
  - subst owner. apply (proj2 (Hblocks 2%positive)). split; [exact I | discriminate].
  - apply (proj2 (Hblocks 1%positive)). split; [exact I | congruence].
Qed.

Lemma empty_environment (J : state_predicate) s : J s empty_memory ->
  environment all_processors J s empty_memory empty_memory empty_memory empty_memory.
Proof.
  intros HJ. constructor; try apply empty_memory_well_formed.
  - exists empty_memory. split.
    + exact (proj1 (spatiotemporal_empty_left all_processors empty_generalized)).
    + exact (proj1 (spatial_empty_left empty_generalized)).
  - left. intros i H; contradiction.
  - left; exact HJ.
Qed.

Lemma full_pure_empty s b : eval_bexpr s b = true ->
  full_satisfies all_processors s empty_memory (ConcurrentAssertion.Pure b).
Proof.
  intros H. exists full_barrier_resource. split; [reflexivity | exact H].
Qed.

Definition invariant_x_zero := ConcurrentAssertion.Pure (BEq (EVar 0) (EVal 0%Z)).
Definition pure_true := ConcurrentAssertion.Pure BTrue.
Definition set_x_one := Concurrent.Prim
  (Concurrent.Common (Sequential.Assign 0 (EVal 1%Z))) (EVal 1%Z).
Definition zero_stack : stack := fun _ => 0%Z.

(** A concrete instance of Figure 4.7's unrestricted assignment axiom. The
    conclusion uses precisely the full safety semantics of pp. 131-132. *)
Theorem printed_assignment_invalid :
  ~ valid_specification all_processors invariant_x_zero pure_true set_x_one pure_true.
Proof.
  intros Hvalid.
  assert (Hpre : full_satisfies all_processors zero_stack empty_memory pure_true).
  { apply full_pure_empty; reflexivity. }
  specialize (Hvalid zero_stack empty_memory Hpre 1).
  destruct Hvalid as [_ [_ Hprogress]].
  assert (Henv : environment all_processors
    (fun s m => full_satisfies all_processors s m invariant_x_zero)
    zero_stack empty_memory empty_memory empty_memory empty_memory).
  { apply empty_environment, full_pure_empty; reflexivity. }
  assert (Hstep : step all_processors set_x_one (State zero_stack empty_memory)
    halt (State (update zero_stack 0 1%Z) empty_memory)).
  { eapply StepPrimitive with (i := 1%positive); [reflexivity |].
    apply PrimitiveAssign; exact I. }
  destruct (Hprogress _ _ _ _ _ _ Henv Hstep)
    as [local [shared [frame [Hafter _]]]].
  destruct Hafter as [_ _ _ _ _ _ [Hinv | Hlocked]].
  - apply full_satisfies_pure in Hinv. discriminate.
  - apply empty_memory_not_locked, Hlocked.
Qed.

(** Only the pure-postcondition subset of the printed assignment axiom is
    needed for the refutation. This is not a replacement definition of the
    entire dissertation calculus. *)
Inductive printed_pure_assignment : ConcurrentAssertion.assertion ->
    ConcurrentAssertion.assertion -> Concurrent.command -> ConcurrentAssertion.assertion -> Prop :=
| PrintedPureAssign invariant b x rhs processor :
    printed_pure_assignment invariant
      (ConcurrentAssertion.Pure (subst_bexpr x rhs b))
      (Concurrent.Prim (Concurrent.Common (Sequential.Assign x rhs)) processor)
      (ConcurrentAssertion.Pure b).

Theorem printed_assignment_soundness_false :
  ~ (forall invariant pre c post,
    printed_pure_assignment invariant pre c post ->
    valid_specification all_processors invariant pre c post).
Proof.
  intros Hsound. apply printed_assignment_invalid.
  apply Hsound. exact (PrintedPureAssign invariant_x_zero BTrue 0 (EVal 1%Z) (EVal 1%Z)).
Qed.
