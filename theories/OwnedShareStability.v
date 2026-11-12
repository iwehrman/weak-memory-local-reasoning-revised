From Stdlib Require Import List ZArith.
From WMLR Require Import Expressions Languages Machine BufferRelations Separation
  RepairedSeparation GeneralizedFlushing OperationalSemantics ProgramSteps
  Assertions AssertionSemantics PersistentAssertions OwnershipProtocol PrivateOwnership
  SpatialExchange Safety TemporalSafety TemporalTransfer InvariantFragment
  OwnedSafety OwnedAdequacy OwnedResources OwnedShareResources OwnedShareInvariant.
Import ListNotations.

(** Removing blocked bits preserves a non-lock action which was already
    enabled. The converse is deliberately not asserted: loads may unblock. *)
Lemma program_step_unblock active action command initial next final :
  program_step active action command initial next final ->
  (match action with AcquireAction _ | ReleaseAction _ => False | _ => True end) ->
  program_step active action command (State (registers initial) (release (memory_state initial)))
    next (State (registers final) (release (memory_state final))).
Proof.
  induction 1; intros Hkind; try solve [constructor; auto].
  inversion H0; subst; cbn [primitive_action] in Hkind; try contradiction.
  all: eapply ProgramPrimitive; [exact H |]; cbn [registers memory_state].
  - apply PrimitiveAssume; assumption.
  - apply PrimitiveAssert; assumption.
  - apply PrimitiveAssign; assumption.
  - apply PrimitiveLoad; [assumption |intros Hbad; exact Hbad |assumption].
  - apply PrimitiveStore with (loc := loc) (previous := previous); assumption.
  - apply PrimitiveFence; assumption.
Qed.

Lemma owned_share_preserves_invariant active invariant n command next s t local retained big frame whole whole' action post :
  invariant_fragment invariant -> (exists i, active i) ->
  persistent_models active s retained invariant ->
  lock_free (resource_memory active local) ->
  spatial (proj1_sig retained) (proj1_sig local) (proj1_sig big) ->
  memory_spatial (resource_memory active frame) (resource_memory active big) whole ->
  owned_safe active DisjointMode invariant (S n) command s local post ->
  program_step active action command (State s whole) next (State t whole') ->
  (match action with AcquireAction _ | ReleaseAction _ => False | _ => True end) ->
  persistent_models active t retained invariant.
Proof.
  intros Hfragment Hactive HJ Hlocalfree Hinner Houter Hsafe Hstep Hkind.
  assert (Hbigfree : lock_free (resource_memory active big)).
  { eapply spatial_free_union; [exact (proj1 Hinner)
      |exact (proj2 (invariant_fragment_shape _ Hfragment _ _ _ HJ)) |exact Hlocalfree]. }
  assert (Houter' : memory_spatial (resource_memory active (released_resource active frame))
    (resource_memory active big) (release whole)).
  { apply memory_spatial_comm.
    exact (protocol_spatial_reblock _ _ _ no_blocked Hbigfree (memory_spatial_comm _ _ _ Houter)). }
  assert (Henv : owned_environment active DisjointMode invariant s local
    (resource_memory active retained) (released_resource active frame) (release whole) PoolFree).
  { apply (owned_share_unpool _ _ _ _ _ _ _ _ Hfragment Hactive HJ Hinner Houter').
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
