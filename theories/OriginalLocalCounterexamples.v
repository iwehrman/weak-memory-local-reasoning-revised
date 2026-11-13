From Stdlib Require Import List ZArith.
From WMLR Require Import Expressions Languages Machine Separation GeneralizedFlushing
  OperationalSemantics Assertions AssertionSemantics ConcreteAssertions ExecutionExamples
  Safety SafetyExamples FlushingCounterexample UnlockCounterexample.
Import ListNotations.

(** Definition 6 of the dissertation, with arguments in execution order.
    Unlike [generalized_future], this relation has no mark-only step.
    Both endpoints below are well-formed resources, so membership of marks
    in the active processor domain is already enforced. *)
Definition original_generalized_flush active (before after : generalized_memory) : Prop :=
  exists i, active i /\
    (forall j, complete before j -> complete after j) /\
    complete after i /\ flush_at active i (underlying before) (underlying after).

Inductive original_generalized_future active : generalized_memory -> generalized_memory -> Prop :=
| OriginalFutureRefl before : original_generalized_future active before before
| OriginalFutureNext before middle after :
    original_generalized_flush active before middle ->
    original_generalized_future active middle after ->
    original_generalized_future active before after.

Lemma original_impossible_future_before s :
  models two_processors s wand_pending_resource impossible_future.
Proof.
  intros future out [_ Hbar] [_ [Hbefore _]].
  destruct Hbar as [Hinactive | Hcomplete];
    [exfalso; apply Hinactive; left; reflexivity |].
  specialize (Hbefore 1%positive Hcomplete).
  change (buffer_update empty_buffers 1%positive [(1%positive,7%Z)] 1%positive = []) in Hbefore.
  rewrite buffer_update_same in Hbefore; discriminate.
Qed.

Lemma original_wand_after_barrier_composition :
  temporal two_processors (proj1_sig wand_flushed_resource)
    (proj1_sig wand_barrier_resource) (proj1_sig wand_flushed_resource).
Proof. exact (proj2 wand_after_barrier_composition). Qed.

Lemma original_impossible_future_after s :
  ~ models two_processors s wand_flushed_resource impossible_future.
Proof.
  intros Hwand.
  assert (Hbar : models two_processors s wand_barrier_resource (A.Barrier (EVal 1%Z))).
  { split.
    - split; [intros; reflexivity |]. split; [intros; reflexivity |intros i H; exact H].
    - right; left; reflexivity. }
  specialize (Hwand _ _ Hbar original_wand_after_barrier_composition); discriminate.
Qed.

Lemma original_wand_flush :
  original_generalized_flush two_processors (proj1_sig wand_pending_resource)
    (proj1_sig wand_flushed_resource).
Proof.
  exists 1%positive; split; [left; reflexivity |].
  split; [intros j H; exact H |]. split; [left; reflexivity |].
  constructor; [left; reflexivity |intros H; exact H |apply buffer_update_same].
Qed.

Theorem original_pointwise_temporal_wand_not_flush_closed s :
  original_generalized_future two_processors (proj1_sig wand_pending_resource)
    (proj1_sig wand_flushed_resource) /\
  models two_processors s wand_pending_resource impossible_future /\
  ~ models two_processors s wand_flushed_resource impossible_future.
Proof.
  split; [eapply OriginalFutureNext; [apply original_wand_flush |constructor] |].
  split; [apply original_impossible_future_before |apply original_impossible_future_after].
Qed.

Theorem original_flushing_closure_false :
  ~ (forall p s (before after : resource two_processors),
      original_generalized_future two_processors (proj1_sig before) (proj1_sig after) ->
      models two_processors s before p -> models two_processors s after p).
Proof.
  intros Hclosed; apply (original_impossible_future_after zero_stack).
  apply (Hclosed impossible_future zero_stack wand_pending_resource wand_flushed_resource);
    [exact (proj1 (original_pointwise_temporal_wand_not_flush_closed zero_stack))
     |apply original_impossible_future_before].
Qed.

(** This is [valid_specification], not any repaired validity predicate. *)
Theorem original_arbitrary_invariant_unlock_invalid :
  ~ valid_specification two_processors (A.Pure BFalse) (A.Lock (EVal 1%Z))
    (Concurrent.Prim Concurrent.Unlock (EVal 1%Z)) A.Emp.
Proof.
  intros Hvalid.
  assert (HP : full_satisfies two_processors zero_stack owned_lock_memory (A.Lock (EVal 1%Z))).
  { exists owned_lock_resource; split; [reflexivity |].
    split; [intros; reflexivity |]. split; [intros; reflexivity |apply owned_lock_held]. }
  specialize (Hvalid _ _ HP 1); destruct Hvalid as [_ [_ Hprogress]].
  assert (Henv : environment two_processors
    (fun s m => full_satisfies two_processors s m (A.Pure BFalse))
    zero_stack owned_lock_memory empty_memory empty_memory owned_lock_memory).
  { constructor.
    - exact (proj1 owned_lock_valid).
    - apply empty_memory_well_formed.
    - apply empty_memory_well_formed.
    - exact (proj1 owned_lock_valid).
    - exists owned_lock_memory; split.
      + exact (proj1 (spatiotemporal_empty_left two_processors (proj1_sig owned_lock_resource))).
      + exact (proj1 (spatial_empty_left (proj1_sig owned_lock_resource))).
    - right; exists 1%positive; apply owned_lock_held.
    - right; exists 1%positive; apply owned_lock_held. }
  assert (Hstep : step two_processors (Concurrent.Prim Concurrent.Unlock (EVal 1%Z))
    (State zero_stack owned_lock_memory) halt (State zero_stack empty_memory)).
  { eapply StepPrimitive; [reflexivity |]. apply PrimitiveUnlock;
      [left; reflexivity |reflexivity |apply owned_lock_held]. }
  destruct (Hprogress _ _ _ _ _ _ Henv Hstep) as (local & shared & frame & Hafter & _).
  destruct Hafter as [_ _ _ _ _ _ [HJ |Hheld]].
  - apply full_satisfies_pure in HJ; discriminate.
  - apply two_processor_empty_not_locked,Hheld.
Qed.

(** Optional D1: INV alone, with an explicitly vacuous valid premise and
    an inhabited invalid conclusion. No frame rule is used. *)
Theorem original_inv_alone_counterexample :
  valid_specification two_processors A.Emp
    (A.Spatial (A.Pure BFalse) (A.Spatial A.Emp (A.Lock (EVal 1%Z))))
    (Concurrent.skip (EVal 1%Z))
    (A.Spatial (A.Pure BFalse) (A.Spatial (A.Pure BFalse) (A.Lock (EVal 1%Z)))) /\
  ~ valid_specification two_processors (A.Pure BFalse)
    (A.Spatial A.Emp (A.Lock (EVal 1%Z))) (Concurrent.skip (EVal 1%Z))
    (A.Spatial (A.Pure BFalse) (A.Lock (EVal 1%Z))).
Proof.
  split.
  - intros s m (r & Er & a & b & Hsp & Hfalse & HB); discriminate Hfalse.
  - intros Hvalid.
    assert (HP : full_satisfies two_processors zero_stack owned_lock_memory
      (A.Spatial A.Emp (A.Lock (EVal 1%Z)))).
    { exists owned_lock_resource; split; [reflexivity |].
      exists (empty_resource_value two_processors),owned_lock_resource; split.
      - apply spatial_empty_left.
      - split.
        + split; [intros; reflexivity |]. split; [intros; reflexivity |intros i H; exact H].
        + split; [intros; reflexivity |]. split; [intros; reflexivity |apply owned_lock_held]. }
    destruct (Hvalid _ _ HP 1) as [Hterminal _].
    destruct (Hterminal ltac:(eexists; reflexivity)) as (r & Er & a & b & Hsp & Hfalse & HB).
    discriminate Hfalse.
Qed.
