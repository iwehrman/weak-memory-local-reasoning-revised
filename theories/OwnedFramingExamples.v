From Stdlib Require Import List ZArith.
From WMLR Require Import Expressions Languages Machine Separation RepairedSeparation
  OperationalSemantics ProgramSteps ExecutionExamples Assertions AssertionSemantics ConcreteAssertions
  PersistentAssertions Specifications TemporalSafety RegionalResources InvariantFragment
  InvariantFragmentExamples OwnedSafety OwnedAdequacy OwnedResources OwnedRules
  OwnedAcceptance StrongTemporalCounterexample OwnedFraming.
Import ListNotations.

(** The precise checkpoint-6 instance becomes valid when spatially framed.
    The existing initial witness and release step make its precondition
    inhabited and its command enabled; no change to the negative theorem. *)
Theorem owned_counterexample_spatial_frame_valid :
  owned_valid two_processors DisjointMode stm_cell (A.Spatial stm_frame stm_pre)
    acceptance_release (A.Spatial stm_frame stm_post).
Proof.
  apply owned_spatial_frame_valid; [apply stm_unframed_release_valid |].
  intros x H; contradiction.
Qed.

(** A retained lock token and protected cell can be inside the spatial
    assertion frame while the other processor stores to its private cell. *)
Theorem owned_holder_spatial_store_valid mode :
  owned_valid two_processors mode acceptance_invariant
    (A.Spatial acceptance_holder_pre acceptance_private_pre)
    (store_command 2%positive 3%positive 9%Z)
    (A.Spatial acceptance_holder_pre acceptance_private_post).
Proof.
  apply owned_spatial_frame_valid; [apply owned_private_store_valid |].
  intros x H; contradiction.
Qed.

(** Genuine pending history is allowed before acquisition. Only the
    acquiring processor earns a barrier, even though the pool was full. *)
Theorem owned_pending_temporal_lock_valid :
  owned_valid two_processors OverlapMode acceptance_invariant
    (A.Temporal checkpoint_foreign_write A.Emp) acceptance_acquire
    (A.Temporal checkpoint_foreign_write
      (A.Temporal (A.Spatial (A.Lock (EVal 1%Z)) acceptance_invariant) (A.Barrier (EVal 1%Z)))).
Proof.
  apply owned_temporal_frame_valid; [constructor | |intros x H; contradiction].
  apply owned_lock_valid; [apply acceptance_two_active |constructor].
Qed.

Theorem owned_pending_temporal_lock_enabled s :
  persistent_models two_processors s checkpoint_foreign_pending
    (A.Temporal checkpoint_foreign_write A.Emp) /\
  owned_environment two_processors OverlapMode acceptance_invariant s checkpoint_foreign_pending
    (resource_memory two_processors checkpoint_full_cell) (empty_resource_value two_processors)
    acceptance_initial PoolFree /\
  program_step two_processors (AcquireAction 1%positive) acceptance_acquire
    (State s acceptance_initial) halt (State s (acquire two_processors acceptance_initial 1%positive)) /\
  buffers acceptance_initial 2%positive = [(3%positive,17%Z)].
Proof.
  split.
  - apply temporal_emp_right_intro.
    split; [right; reflexivity |left]. split; [intros; reflexivity |].
    split; [intros; reflexivity |intros i H; contradiction].
  - split.
    + apply owned_empty_frame_intro.
      * exact (proj1 (proj2_sig checkpoint_full_cell)).
      * exact (proj1 checkpoint_cell_pending_spatial).
      * split; [intros i H; exact H |].
        exists checkpoint_full_cell; split; [reflexivity |apply checkpoint_full_cell_models].
    + split.
      * eapply ProgramPrimitive with (p := C.Lock) (i := 1%positive); [reflexivity |].
        apply PrimitiveLock; [left; reflexivity |reflexivity |intros i H; exact H].
      * reflexivity.
Qed.
