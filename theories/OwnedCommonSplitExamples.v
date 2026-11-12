From Stdlib Require Import List ZArith.
From WMLR Require Import Expressions Languages Machine BufferRelations Separation StableCompatibility
  RepairedSeparation ExecutionExamples OperationalSemantics ProgramSteps Assertions AssertionSemantics PersistentAssertions
  TemporalSafety RegionalResources OwnedSafety OwnedAdequacy OwnedAcceptance InvariantFragment
  StrongTemporalCounterexample OwnedCommonSplit OwnershipTransfer.
Import ListNotations.

(** Same ingredients as checkpoint 6, but now the retained pending write
    comes FIRST on processor 2. One common split exists, and release is safe. *)
Definition common_release_whole := resource_memory two_processors
  (stm_holder [(2%positive,0%Z);(1%positive,0%Z)]).

Lemma common_release_spatial_split :
  spatial (proj1_sig (stm_pending [(2%positive,0%Z)]))
    (proj1_sig (stm_holder [(1%positive,0%Z)]))
    (proj1_sig (stm_holder [(2%positive,0%Z);(1%positive,0%Z)])).
Proof.
  split.
  - split.
    + split.
      * intros loc Hleft Hright.
        apply stm_pending_domain in Hleft.
        change (memory_domain (resource_memory two_processors (stm_payload [(1%positive,0%Z)])) loc) in Hright.
        apply stm_payload_domain in Hright.
        destruct Hleft as [v [E |H]]; [inversion E; subst |contradiction].
        destruct Hright as [Er |[w [Er |H]]]; discriminate || contradiction.
      * intros i H; contradiction.
    + split.
      * intros loc; cbn [stm_pending stm_holder acquired_resource stm_payload resource_memory proj1_sig underlying acquire shared_heap].
        unfold heap_override, heap_update, empty_heap; destruct (Pos.eq_dec loc 3%positive); reflexivity.
      * split.
        -- intros i; cbn [stm_pending stm_holder acquired_resource stm_payload resource_memory proj1_sig underlying acquire buffers].
           unfold buffer_update; destruct (Pos.eq_dec i 2%positive); [|constructor].
           apply InterleaveLeft, InterleaveRight, InterleaveNil.
        -- intros i; change (blocked_except two_processors 1%positive i <->
             False \/ blocked_except two_processors 1%positive i); tauto.
  - intros i; change (i = 1%positive <-> False \/ i = 1%positive); tauto.
Qed.

Lemma common_release_temporal_split :
  repaired_temporal two_processors (proj1_sig (stm_pending [(2%positive,0%Z)]))
    (proj1_sig (stm_holder [(1%positive,0%Z)]))
    (proj1_sig (stm_holder [(2%positive,0%Z);(1%positive,0%Z)])).
Proof.
  destruct common_release_spatial_split as [[Hcompat [Hh [Hb Hk]]] HM].
  split; [apply spatial_compatible_stable,Hcompat |]. split.
  - split; [apply spatial_compatible_temporal,Hcompat |]. split; [exact Hh |].
    split; [|exact Hk].
    intros i; cbn [stm_pending stm_holder acquired_resource stm_payload resource_memory proj1_sig underlying acquire buffers].
    unfold buffer_update; destruct (Pos.eq_dec i 2%positive); reflexivity.
  - split; [|exact HM]. intros i Hi; change (i = 1%positive) in Hi; subst i; reflexivity.
Qed.

Theorem owned_common_release_safe s n :
  owned_safe two_processors DisjointMode stm_cell n acceptance_release s
    (stm_holder [(2%positive,0%Z);(1%positive,0%Z)])
    (A.strong_temporal (stm_write 2%positive) stm_post).
Proof.
  eapply owned_safe_common_frame.
  - constructor.
  - apply stm_unframed_release_valid,stm_holder_one_models.
  - intros x H; contradiction.
  - apply stm_singleton_models.
  - apply common_release_spatial_split.
  - apply common_release_temporal_split.
Qed.

Theorem owned_common_release_enabled s :
  persistent_models two_processors s (stm_holder [(2%positive,0%Z);(1%positive,0%Z)])
    (A.strong_temporal (stm_write 2%positive) stm_pre) /\
  owned_environment two_processors DisjointMode stm_cell s
    (stm_holder [(2%positive,0%Z);(1%positive,0%Z)]) empty_memory
    (empty_resource_value two_processors) common_release_whole (PoolHeld 1%positive) /\
  program_step two_processors (ReleaseAction 1%positive) acceptance_release
    (State s common_release_whole) halt (State s (release common_release_whole)) /\
  buffers (release common_release_whole) 2%positive = [(2%positive,0%Z);(1%positive,0%Z)].
Proof.
  split.
  - split; exists (stm_pending [(2%positive,0%Z)]),(stm_holder [(1%positive,0%Z)]).
    + split; [apply common_release_spatial_split |split; [apply stm_singleton_models |apply stm_holder_one_models]].
    + split; [apply common_release_temporal_split |split; [apply stm_singleton_models |apply stm_holder_one_models]].
  - split.
    + apply owned_empty_frame_intro.
      * exact (proj1 (empty_generalized_well_formed two_processors)).
      * exact (proj1 (spatial_empty_left (proj1_sig (stm_holder [(2%positive,0%Z);(1%positive,0%Z)])))).
      * split; [split; [left; reflexivity |intros i; reflexivity] |reflexivity].
    + split; [|reflexivity].
      eapply ProgramPrimitive with (p := C.Unlock) (i := 1%positive); [reflexivity |].
      apply PrimitiveUnlock; [left; reflexivity |reflexivity |].
      split; [left; reflexivity |intros i; reflexivity].
Qed.
