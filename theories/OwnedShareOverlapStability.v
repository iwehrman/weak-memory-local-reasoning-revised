From Stdlib Require Import List ZArith.
From WMLR Require Import Expressions Languages Machine BufferRelations Separation
  RepairedSeparation GeneralizedFlushing OperationalSemantics ProgramSteps
  Assertions AssertionSemantics PersistentAssertions OwnershipProtocol PrivateOwnership
  SpatialExchange Safety TemporalSafety TemporalTransfer InvariantFragment
  OwnedSafety OwnedAdequacy OwnedResources OwnedShareResources OwnedShareInvariant OwnedShareStability OwnedShareOverlapResources.
Import ListNotations.

Lemma owned_share_overlap_preserves_invariant active invariant n command next s t local retained big frame whole whole' action post :
  invariant_fragment invariant -> (exists i, active i) ->
  persistent_models active s retained invariant ->
  lock_free (resource_memory active local) ->
  spatial (proj1_sig retained) (proj1_sig local) (proj1_sig big) ->
  memory_repaired active (resource_memory active frame) (resource_memory active big) whole ->
  owned_safe active OverlapMode invariant (S n) command s local post ->
  program_step active action command (State s whole) next (State t whole') ->
  (match action with AcquireAction _ | ReleaseAction _ => False | _ => True end) ->
  persistent_models active t retained invariant.
Proof.
  intros Hfragment Hactive HJ Hlocalfree Hinner Houter Hsafe Hstep Hkind.
  assert (Hbigfree : lock_free (resource_memory active big)).
  { eapply spatial_free_union; [exact (proj1 Hinner)
      |exact (proj2 (invariant_fragment_shape _ Hfragment _ _ _ HJ)) |exact Hlocalfree]. }
  assert (Houter' : memory_repaired active (resource_memory active (released_resource active frame))
    (resource_memory active big) (release whole)).
  { destruct Houter as [[Hdis [Hheap Hbuffer]] [Eh [Eb Ek]]]; split.
    - split; [intros i H _; exact H |]. split; assumption.
    - split; [exact Eh |]. split; [exact Eb |].
      intros i; split; [intros H; contradiction |intros [H |H]; [exact H |exact (Hbigfree i H)]]. }
  assert (Henv : owned_environment active OverlapMode invariant s local
    (resource_memory active retained) (share_cut_resource active (released_resource active frame) retained) (release whole) PoolFree).
  { apply (owned_share_overlap_unpool _ _ _ _ _ _ _ _ Hfragment Hactive HJ Hinner Houter').
    intros i H; exact H. }
  pose proof (program_step_unblock _ _ _ _ _ _ Hstep Hkind) as Hstep'.
  destruct (owned_safe_program_step _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hsafe Henv Hstep')
    as (local' & pool' & phase' & Henv' & Hupdate & _).
  pose proof (owned_action_transfer _ _ _ _ _ _ _ _ Hupdate) as Htransfer.
  destruct action; try contradiction; destruct Htransfer as [-> [-> _]];
    destruct (proj2 (owned_pool_status _ _ _ _ _ _ _ _ _ Henv')) as (r & Er & Hr).
  all: apply (invariant_restore_marks active invariant s t retained Hfragment HJ).
  all: exists r; split; assumption.
Qed.
