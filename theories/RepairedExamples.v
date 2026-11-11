From Stdlib Require Import List ZArith.
From WMLR Require Import Expressions Languages Machine Separation OperationalSemantics
  ExecutionExamples Assertions AssertionSemantics ConcreteAssertions SeparationExamples
  RepairedSeparation RepairedAssertions Safety RepairedSafety RepairedRules.
Import ListNotations.

(** A nontrivial points-to model survives the stronger temporal guard. *)
Example repaired_points_to_cell s :
  repaired_models all_processors s (cell_resource 1%positive 7%Z)
    (ConcurrentAssertion.points_to (EVal 1%Z) (EVal 7%Z)).
Proof.
  change (exists a b : resource all_processors,
    repaired_temporal all_processors (proj1_sig a) (proj1_sig b)
      (cell_generalized 1%positive 7%Z) /\
    (exists i, write_atom all_processors 1%Z i 7%Z (proj1_sig a)) /\
    (forall i, barrier_atom all_processors i (proj1_sig b))).
  exists (cell_resource 1%positive 7%Z), full_barrier_resource. split.
  - split; [|apply cell_temporal_full_barrier]. apply spatial_compatible_stable.
    exact (proj1 (proj1 (spatial_empty_right (cell_generalized 1%positive 7%Z)))).
  - split.
    + exists 1%Z. split; [exact I | right; apply cell_flushed].
    + intros i. split.
      * split; [intros; reflexivity |]. split; [intros; reflexivity | intros j H; contradiction].
      * destruct i; simpl; [exact I | right; exact I | exact I].
Qed.

Definition register_invariant := BEq (EVar 1) (EVal 0%Z).
Definition register_result := BEq (EVar 0) (EVal 2%Z).
Definition register_second := Concurrent.Prim
  (Concurrent.Common (Sequential.Assign 0 (EAdd (EVar 0) (EVal 1%Z)))) (EVal 1%Z).
Definition register_program := Concurrent.Seq
  (Concurrent.Prim (Concurrent.Common (Sequential.Assign 0 (EVal 1%Z))) (EVal 1%Z))
  register_second.

Example register_program_derivable :
  pure_derivation register_invariant BTrue register_program register_result.
Proof.
  eapply PureConsequence with
    (p' := subst_bexpr 0 (EVal 1%Z) (subst_bexpr 0 (EAdd (EVar 0) (EVal 1%Z)) register_result))
    (q' := register_result).
  - intros s _; reflexivity.
  - apply PureSequence with (r := subst_bexpr 0 (EAdd (EVar 0) (EVal 1%Z)) register_result);
      apply PureAssign; simpl; intuition discriminate.
  - intros s H; exact H.
Qed.

Example register_program_valid :
  repaired_valid_specification two_processors (ConcurrentAssertion.Pure register_invariant)
    (ConcurrentAssertion.Pure BTrue) register_program (ConcurrentAssertion.Pure register_result).
Proof. apply pure_fragment_sound, register_program_derivable. Qed.

Definition register_initial : stack := fun _ => 0%Z.
Definition register_after_one := update register_initial 0 1%Z.
Definition register_final := update register_after_one 0 2%Z.
Definition register_flushed := flush_write after_first_store 1%positive 1%positive 1%Z [].

Lemma pending_full_valid :
  generalized_well_formed two_processors (Generalized after_first_store two_processors).
Proof.
  split.
  - unfold after_first_store, enqueue. apply update_buffers_well_formed;
      [left; reflexivity | apply initial_memory_well_formed].
  - split; [intros i Hi; exact Hi |]. intros Hempty loc; exfalso.
    apply (Hempty 1%positive); left; reflexivity.
Qed.

Definition pending_full_resource : resource two_processors :=
  exist _ (Generalized after_first_store two_processors) pending_full_valid.

Lemma empty_full_valid active : generalized_well_formed active (Generalized empty_memory active).
Proof.
  split; [exact (proj1 (empty_generalized_well_formed active)) |].
  split; [intros i Hi; exact Hi | intros; reflexivity].
Qed.

Lemma register_initial_environment :
  repaired_environment two_processors
    (fun s m => repaired_full_satisfies two_processors s m (ConcurrentAssertion.Pure register_invariant))
    register_initial after_first_store empty_memory empty_memory after_first_store.
Proof.
  constructor.
  - exact (proj1 pending_full_valid).
  - exact (proj1 (empty_generalized_well_formed two_processors)).
  - exact (proj1 (empty_generalized_well_formed two_processors)).
  - exact (proj1 pending_full_valid).
  - exists after_first_store. split.
    + exact (proj1 (repaired_empty_left two_processors (Generalized after_first_store two_processors))).
    + exact (proj1 (spatial_empty_left (Generalized after_first_store two_processors))).
  - left; intros i H; contradiction.
  - left. exists (exist _ (Generalized empty_memory two_processors) (empty_full_valid two_processors)).
    split; reflexivity.
Qed.

(** Concrete execution: assign x=1; flush a previously buffered store;
    remove skip; assign x=x+1. The invariant register y remains zero. *)
Example register_program_flush_trace :
  execution two_processors 4 register_program register_initial after_first_store
    halt register_final register_flushed.
Proof.
  unfold register_program. eapply ExecuteNext with
    (next := Concurrent.Seq halt register_second) (t := register_after_one).
  - apply StepSeq. eapply StepPrimitive; [reflexivity |]. apply PrimitiveAssign; left; reflexivity.
  - eapply ExecuteNext with (middle := register_flushed).
    + apply StepFlush. eapply FlushWrite with (i := 1%positive).
      * left; reflexivity.
      * intros H; contradiction.
      * reflexivity.
    + eapply ExecuteNext; [apply StepSeqDone |].
      eapply ExecuteNext.
      * eapply StepPrimitive; [reflexivity |]. apply PrimitiveAssign; left; reflexivity.
      * constructor.
Qed.

(** The derivation, initial resource, and initial environment discharge all
    safety premises. This covers every terminating execution, not only the
    particular flush schedule above. *)
Theorem register_program_all_terminating_runs n last t final :
  execution two_processors n register_program register_initial after_first_store last t final ->
  terminal last -> t 0 = 2%Z.
Proof.
  intros Hrun Hterminal.
  assert (Hpre : repaired_full_satisfies two_processors register_initial after_first_store
    (ConcurrentAssertion.Pure BTrue)).
  { exists pending_full_resource; split; reflexivity. }
  destruct (repaired_safe_execution_post _ _ _ _ _ _ _ _ _ _ _ _ _ Hrun
    (register_program_valid _ _ Hpre (S n)) register_initial_environment Hterminal)
    as [local' [shared' [frame' [_ [_ [r [_ Hpost]]]]]]].
  change (Z.eqb (t 0) 2%Z = true) in Hpost. apply Z.eqb_eq, Hpost.
Qed.
