From Stdlib Require Import List ZArith.
From WMLR Require Import Expressions Languages Machine Separation RepairedSeparation
  OperationalSemantics ProgramSteps ExecutionExamples GeneralizedFlushing
  Assertions AssertionSemantics PersistentAssertions TemporalSafety OwnershipProtocol
  InvariantFragment OwnedSafety OwnedAdequacy OwnedResources OwnedAcceptance
  OwnedHeapResources OwnedHeapExamples OwnedContainerEntailments OwnedCalculus OwnedBufferedLoad.
Import ListNotations.

(** The old heap value is 7; processor 2 has buffered 9 at the same address.
    The existential binder and the load destination may both be register 0. *)
Definition buffered_load_history := container_history 2%positive 2%positive 9%Z.
Definition buffered_load_pending := owned_enqueue_resource two_processors heap_foreign_cell
  2%positive 2%positive 9%Z (or_intror eq_refl).

Theorem buffered_load_history_derived mode :
  owned_derivation two_processors A.Emp mode buffered_load_history heap_foreign_load
    (A.And buffered_load_history (A.Pure (BEq (EVar 0) (EVal 9%Z)))).
Proof. apply owned_derive_load_after_history; cbn; tauto. Qed.

Lemma buffered_load_pending_models s :
  persistent_models two_processors s buffered_load_pending buffered_load_history.
Proof.
  apply owned_enqueue_temporal_post.
  - apply container_some_cell_models; exists 7%Z; apply acceptance_cell_models.
  - intros other Hne [v H]; contradiction.
Qed.

Lemma buffered_load_pending_environment mode s :
  owned_environment two_processors mode A.Emp s buffered_load_pending empty_memory
    (empty_resource_value two_processors) (resource_memory two_processors buffered_load_pending) PoolFree.
Proof.
  apply owned_empty_frame_intro.
  - exact (proj1 (empty_generalized_well_formed two_processors)).
  - exact (proj1 (spatial_empty_left (proj1_sig buffered_load_pending))).
  - split; [intros i H; exact H |apply protocol_empty_satisfies].
Qed.

Theorem buffered_load_pending_enabled mode s :
  persistent_models two_processors s buffered_load_pending buffered_load_history /\
  owned_environment two_processors mode A.Emp s buffered_load_pending empty_memory
    (empty_resource_value two_processors) (resource_memory two_processors buffered_load_pending) PoolFree /\
  shared_heap (resource_memory two_processors buffered_load_pending) 2%positive = Some 7%Z /\
  buffers (resource_memory two_processors buffered_load_pending) 2%positive = [(2%positive,9%Z)] /\
  program_step two_processors OrdinaryAction heap_foreign_load
    (State s (resource_memory two_processors buffered_load_pending)) halt
    (State (update s 0 9%Z) (resource_memory two_processors buffered_load_pending)) /\
  persistent_models two_processors (update s 0 9%Z) buffered_load_pending
    (A.And buffered_load_history (A.Pure (BEq (EVar 0) (EVal 9%Z)))) /\
  ~ complete (proj1_sig buffered_load_pending) 2%positive.
Proof.
  split; [apply buffered_load_pending_models |]. split; [apply buffered_load_pending_environment |].
  split; [reflexivity |]. split; [reflexivity |]. split.
  - eapply ProgramPrimitive with (p := C.Common (S.Load 0 (EVal 2%Z))) (i := 2%positive); [reflexivity |].
    apply PrimitiveLoad; [right; reflexivity |intros H; exact H |reflexivity].
  - split; [split; [apply buffered_load_pending_models |reflexivity] |intros H; discriminate].
Qed.

Definition buffered_load_flushed : resource two_processors.
Proof.
  refine (exist _ (Generalized
    (flush_write (resource_memory two_processors buffered_load_pending) 2%positive 2%positive 9%Z [])
    two_processors) _).
  eapply generalized_step_well_formed; [|exact (proj2_sig buffered_load_pending)].
  eapply GeneralizedFlush with (i := 2%positive).
  - constructor; [right; reflexivity |intros H; exact H |reflexivity].
  - intros j Hj; left; exact Hj.
  - intros; assumption.
  - right; reflexivity.
Defined.

Lemma buffered_load_flush_future :
  resource_future two_processors buffered_load_pending buffered_load_flushed.
Proof.
  apply generalized_future_one; eapply GeneralizedFlush with (i := 2%positive).
  - constructor; [right; reflexivity |intros H; exact H |reflexivity].
  - intros j Hj; left; exact Hj.
  - intros; assumption.
  - right; reflexivity.
Qed.

Theorem buffered_load_after_flush_enabled s :
  persistent_models two_processors s buffered_load_flushed buffered_load_history /\
  shared_heap (resource_memory two_processors buffered_load_flushed) 2%positive = Some 9%Z /\
  buffers (resource_memory two_processors buffered_load_flushed) 2%positive = [] /\
  program_step two_processors OrdinaryAction heap_foreign_load
    (State s (resource_memory two_processors buffered_load_flushed)) halt
    (State (update s 0 9%Z) (resource_memory two_processors buffered_load_flushed)).
Proof.
  split.
  - eapply persistent_assertion_flushing_closed;
      [apply buffered_load_flush_future |apply buffered_load_pending_models].
  - split; [reflexivity |]. split; [reflexivity |].
    eapply ProgramPrimitive with (p := C.Common (S.Load 0 (EVal 2%Z))) (i := 2%positive); [reflexivity |].
    apply PrimitiveLoad; [right; reflexivity |intros H; exact H |reflexivity].
Qed.

(** The corresponding load by processor 1 sees the old heap value while
    processor 2's write is pending. The derived rule uses the same actor. *)
Theorem buffered_load_other_processor_reads_old s :
  program_step two_processors OrdinaryAction
    (C.Prim (C.Common (S.Load 0 (EVal 2%Z))) (EVal 1%Z))
    (State s (resource_memory two_processors buffered_load_pending)) halt
    (State (update s 0 7%Z) (resource_memory two_processors buffered_load_pending)).
Proof.
  eapply ProgramPrimitive with (p := C.Common (S.Load 0 (EVal 2%Z))) (i := 1%positive); [reflexivity |].
  apply PrimitiveLoad; [left; reflexivity |intros H; exact H |reflexivity].
Qed.
