From Stdlib Require Import List ZArith.
From WMLR Require Import Expressions Languages Machine BufferRelations OrderedBuffers Separation
  RepairedSeparation OperationalSemantics ExecutionExamples Assertions AssertionSemantics
  PersistentAssertions OwnershipProtocol TemporalSafety InvariantFragment OwnedSafety OwnedResources OwnedAcceptance
  OwnedFenceExamples OwnedShareAdequacy OwnedShareOverlapResources OwnedShareOverlap.
Import ListNotations.

Theorem owned_share_overlap_store_fence active invariant loc old next actor :
  invariant_fragment invariant -> two_active_processors active -> active actor ->
  owned_valid active OverlapMode A.Emp
    (A.Spatial invariant (writer_points_to (EVal (Z.pos loc)) (EVal old)))
    (C.Seq (store_command actor loc next) (C.Prim (C.Common S.Fence) (EVal (Z.pos actor))))
    (A.Spatial invariant (writer_points_to (EVal (Z.pos loc)) (EVal next))).
Proof.
  intros Hfragment Htwo Hi; apply owned_share_overlap_derivation_valid;
    [exact Htwo |exact Hfragment |apply invariant_assertion_lock_free,InvariantCell
      |apply invariant_assertion_lock_free,InvariantCell |apply owned_derive_store_fence_cell,Hi].
Qed.

Definition share_example_owned := acceptance_cell 2%positive 7%Z 1%positive (or_introl eq_refl).

Theorem share_stale_external_environment s :
  persistent_models two_processors s share_example_owned acceptance_invariant /\
  owned_environment two_processors OverlapMode A.Emp s share_example_owned empty_memory
    acceptance_stale (resource_memory two_processors share_example_owned) PoolFree.
Proof.
  split; [apply acceptance_cell_models |].
  apply owned_emp_overlap_intro; [exact (proj1 (empty_generalized_well_formed two_processors))
    |intros; reflexivity |intros; reflexivity |intros i H; exact H | |].
  - split.
    + split; [intros i H; contradiction |]. split;
        [intros i _ loc [v H] |intros i j _ _ _ loc [v H]]; contradiction.
    + split.
      * intros loc; change (heap_update empty_heap 2%positive 7%Z loc =
          heap_override (heap_update empty_heap 2%positive 5%Z) (heap_update empty_heap 2%positive 7%Z) loc).
        unfold heap_override,heap_update,empty_heap; destruct (Pos.eq_dec loc 2%positive); reflexivity.
      * split; [intros i; constructor |]. intros i; change (False <-> False \/ False); tauto.
  - split; [intros i H; exact H |apply protocol_empty_satisfies].
Qed.

Theorem share_stale_frame_requires_projection s local whole :
  ~ owned_environment two_processors OverlapMode acceptance_invariant s local
    (resource_memory two_processors share_example_owned) acceptance_stale whole PoolFree.
Proof.
  intros Henv; destruct (owned_composition _ _ _ _ _ _ _ _ _ Henv)
    as (combined & Hinner & [[Hd _] _]).
  apply (Hd 2%positive).
  - left; exists 7%Z; apply heap_update_same.
  - apply (repaired_memory_domain _ _ _ _ (proj1 Hinner) 2%positive).
    left; left; exists 5%Z; apply heap_update_same.
Qed.
