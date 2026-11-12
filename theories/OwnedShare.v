From Stdlib Require Import List ZArith.
From WMLR Require Import Expressions Languages Machine BufferRelations Separation RepairedSeparation
  GeneralizedFlushing FrameDecomposition OperationalSemantics ProgramSteps Assertions
  AssertionSemantics ConcreteAssertions PersistentAssertions OwnershipProtocol PrivateOwnership
  SpatialExchange Safety TemporalSafety RegionalResources InvariantFragment LockRepresentation
  OwnedSafety OwnedAdequacy OwnedResources OwnedFraming OwnedCalculus OwnedShareAdequacy
  OwnedShareResources OwnedShareInvariant OwnedShareStability OwnedShareUpdates.
Import ListNotations.

(** A resource decomposition used only in this proof, not a second safety or
    validity predicate. Both sides below use the unchanged owned_safe. *)
Inductive share_resource_decomposition active invariant s : resource active -> resource active -> Prop :=
| ShareClosed local retained big :
    lock_free (resource_memory active local) ->
    persistent_models active s retained invariant ->
    spatial (proj1_sig retained) (proj1_sig local) (proj1_sig big) ->
    share_resource_decomposition active invariant s local big
| ShareHeld local owner : lock_held active (resource_memory active local) owner ->
    share_resource_decomposition active invariant s local local.

Lemma share_resource_future active invariant s local big later :
  share_resource_decomposition active invariant s local big ->
  resource_future active big later ->
  exists local0, resource_future active local local0 /\
    share_resource_decomposition active invariant s local0 later.
Proof.
  intros Hsplit Hfuture; destruct Hsplit as [local retained big Hfree HJ Hsp |local owner Hheld].
  - destruct (resource_spatial_future_split _ _ _ _ _ Hfuture Hsp)
      as (retained0 & local0 & Hrf & Hlf & Hsp0).
    exists local0; split; [exact Hlf |]. eapply ShareClosed; [| |exact Hsp0].
    + intros i H; apply (Hfree i), (resource_future_blocks _ _ _ Hlf i),H.
    + eapply persistent_assertion_flushing_closed; eassumption.
  - exists later; split; [exact Hfuture |]. apply ShareHeld with (owner := owner).
    destruct Hheld as [Hi Hheld]; split; [exact Hi |].
    intros i; rewrite <- (resource_future_blocks _ _ _ Hfuture i); apply Hheld.
Qed.

Theorem owned_safe_share active invariant n command s local big post :
  two_active_processors active -> invariant_fragment invariant -> assertion_lock_free active post ->
  owned_safe active DisjointMode invariant n command s local post ->
  share_resource_decomposition active invariant s local big ->
  owned_safe active DisjointMode A.Emp n command s big (A.Spatial invariant post).
Proof.
  intros Htwo Hfragment HQfree.
  assert (Hactive : exists i, active i) by (destruct Htwo as (i & j & Hi & Hj & Hne); eauto).
  revert command s local big; induction n; intros command s local big Hsafe Hsplit; [exact I |].
  intros later Hfuture.
  destruct (share_resource_future _ _ _ _ _ _ Hsplit Hfuture) as (local0 & Hlf & Hsplit0).
  pose proof (owned_safe_future _ _ _ _ _ _ _ _ _ Hlf Hsafe) as Hsafe0.
  split.
  - intros Hdone; pose proof (owned_safe_terminal _ _ _ _ _ _ _ _ Hsafe0 Hdone) as HQ.
    destruct Hsplit0 as [local0 retained later Hfree HJ Hsp |local0 owner Hheld].
    + exists retained,local0; auto.
    + exfalso; exact (no_free_held _ _ _ Htwo (HQfree _ _ HQ) Hheld).
  - intros pool frame whole phase Henv.
    pose proof (owned_emp_environment_spatial _ _ _ _ _ _ _ Henv) as Houter.
    destruct Hsplit0 as [local0 retained later Hfree HJ Hsp |local0 owner Hheld].
    + destruct phase as [|holder].
      * assert (Hsource : owned_environment active DisjointMode invariant s local0
          (resource_memory active retained) frame whole PoolFree).
        { apply (owned_share_unpool _ _ _ _ _ _ _ _ Hfragment Hactive HJ Hsp Houter).
          exact (proj1 (owned_pool_status _ _ _ _ _ _ _ _ _ Henv)). }
        split; [eapply owned_safe_no_abort; eassumption |].
        intros action next t whole' Hstep.
        destruct (owned_safe_program_step _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hsafe0 Hsource Hstep)
          as (local' & returned & phase' & Hsource' & Hupdate & Hsafe').
        pose proof (owned_action_transfer _ _ _ _ _ _ _ _ Hupdate) as Htransfer.
        pose proof (source_update_free _ _ _ _ _ _ _ _ Hupdate Hfree Htwo) as Hstate'.
        destruct action as [|actor|actor|actor]; [ | | |contradiction].
        -- destruct Htransfer as [-> [-> Hblocks]].
           destruct (owned_share_repool _ _ _ _ _ _ _ _ Hfragment eq_refl Hsource' retained eq_refl)
             as (big' & Hsp' & Houter').
           exists big',pool,PoolFree; split.
           ++ eapply owned_emp_environment_intro; [exact (owned_pool_wf _ _ _ _ _ _ _ _ _ Henv) | | | |exact Houter' |].
              all: try (exact (proj1 (owned_emp_pool_shape _ _ _ _ _ _ _ _ Henv))).
              all: try (exact (proj1 (proj2 (owned_emp_pool_shape _ _ _ _ _ _ _ _ Henv)))).
              all: try (exact (proj2 (proj2 (owned_emp_pool_shape _ _ _ _ _ _ _ _ Henv)))).
              split; [exact (proj1 (owned_pool_status _ _ _ _ _ _ _ _ _ Hsource')) |].
              eapply persistent_full_agrees; [intros x H; contradiction |exact (proj2 (owned_pool_status _ _ _ _ _ _ _ _ _ Henv))].
           ++ split; [eapply owned_share_update_closed; [exact I |exact Hsp |exact Hsp' |exact Hupdate] |].
              eapply IHn; [exact Hsafe' |]. eapply ShareClosed; [exact Hstate' | |exact Hsp'].
              eapply invariant_restore_marks; [exact Hfragment |exact HJ |exact (proj2 (owned_pool_status _ _ _ _ _ _ _ _ _ Hsource'))].
        -- destruct Htransfer as [-> [-> Hblocks]].
           destruct (owned_share_repool _ _ _ _ _ _ _ _ Hfragment eq_refl Hsource' retained eq_refl)
             as (big' & Hsp' & Houter').
           exists big',pool,PoolFree; split.
           ++ eapply owned_emp_environment_intro; [exact (owned_pool_wf _ _ _ _ _ _ _ _ _ Henv) | | | |exact Houter' |].
              all: try (exact (proj1 (owned_emp_pool_shape _ _ _ _ _ _ _ _ Henv))).
              all: try (exact (proj1 (proj2 (owned_emp_pool_shape _ _ _ _ _ _ _ _ Henv)))).
              all: try (exact (proj2 (proj2 (owned_emp_pool_shape _ _ _ _ _ _ _ _ Henv)))).
              split; [exact (proj1 (owned_pool_status _ _ _ _ _ _ _ _ _ Hsource')) |].
              eapply persistent_full_agrees; [intros x H; contradiction |exact (proj2 (owned_pool_status _ _ _ _ _ _ _ _ _ Henv))].
           ++ split; [eapply owned_share_update_closed; [exact I |exact Hsp |exact Hsp' |exact Hupdate] |].
              eapply IHn; [exact Hsafe' |]. eapply ShareClosed; [exact Hstate' | |exact Hsp'].
              eapply invariant_restore_marks; [exact Hfragment |exact HJ |exact (proj2 (owned_pool_status _ _ _ _ _ _ _ _ _ Hsource'))].
        -- destruct Htransfer as [_ [-> [-> Hheld']]].
           exists local',empty_memory,(PoolHeld actor); split.
           ++ eapply owned_environment_held_invariant,Hsource'.
           ++ split; [eapply owned_share_update_acquire; eassumption |].
              apply IHn with (local := local'); [exact Hsafe' |eapply ShareHeld; exact Hheld'].
      * pose proof (spatial_in_repaired active _ _ _ Hsp) as Hrepair.
        destruct (owned_environment_unframe active DisjointMode _ _ _ _ _ _ _ _ _ Hrepair
          (proj1 (proj1 (proj1 Hsp))) Henv) as (grouped & Hgroup & Hsmall).
        assert (Hsource : owned_environment active DisjointMode invariant s local0 pool grouped whole (PoolHeld holder)).
        { eapply owned_environment_held_invariant,Hsmall. }
        split; [eapply owned_safe_no_abort; eassumption |].
        intros action next t whole' Hstep.
        destruct (owned_safe_program_step _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hsafe0 Hsource Hstep)
          as (local' & returned & phase' & Hsource' & Hupdate & Hsafe').
        pose proof (owned_action_transfer _ _ _ _ _ _ _ _ Hupdate) as Htransfer.
        pose proof (source_update_free _ _ _ _ _ _ _ _ Hupdate Hfree Htwo) as Hstate'.
        assert (Hkind : match action with AcquireAction _ | ReleaseAction _ => False | _ => True end).
        { destruct action; try exact I; [destruct Htransfer as [Hbad _]; discriminate |exact Hstate']. }
        assert (Ephase : phase' = PoolHeld holder /\ returned = pool).
        { destruct action; try contradiction; exact (conj (proj1 Htransfer) (proj1 (proj2 Htransfer))). }
        destruct Ephase as [-> ->].
        pose proof (proj1 (owned_mode_parts _ _ _ _ _ _ Hrepair (owned_mode _ _ _ _ _ _ _ _ _ Henv))) as HFR.
        destruct (owned_environment_reframe _ _ _ _ _ _ _ _ _ _ _ Hgroup HFR Hsource')
          as (big' & Hrepair' & Henv').
        pose proof (owned_spatial_reconstruction _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
          Hgroup Hsp Hrepair' Hsource Hupdate) as Hsp'.
        exists big',pool,(PoolHeld holder); split; [eapply owned_environment_held_invariant,Henv' |].
        split; [exact (owned_update_frame _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hgroup Hrepair Hrepair' Hsource Hupdate) |].
        eapply IHn; [exact Hsafe' |]. eapply ShareClosed; [| |exact Hsp'].
        -- destruct action; try contradiction; exact Hstate'.
        -- exact (owned_share_preserves_invariant _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
             Hfragment Hactive HJ Hfree Hsp Houter Hsafe0 Hstep Hkind).
    + destruct (owned_token_environment _ _ _ _ _ _ _ _ _ _ Htwo Henv Hheld) as [-> [-> Hframefree]].
      assert (Hsource : owned_environment active DisjointMode invariant s local0 empty_memory frame whole (PoolHeld owner)).
      { eapply owned_environment_held_invariant,Henv. }
      split; [eapply owned_safe_no_abort; eassumption |].
      intros action next t whole' Hstep.
      destruct (owned_safe_program_step _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hsafe0 Hsource Hstep)
        as (local' & returned & phase' & Hsource' & Hupdate & Hsafe').
      pose proof (owned_action_transfer _ _ _ _ _ _ _ _ Hupdate) as Htransfer.
      destruct action as [|actor|actor|actor].
      * destruct Htransfer as [-> [-> Hblocks]].
        exists local',empty_memory,(PoolHeld owner); split; [eapply owned_environment_held_invariant,Hsource' |].
        split; [exact Hupdate |]. eapply IHn; [exact Hsafe' |]. apply ShareHeld with (owner := owner).
        destruct Hheld as [Hi Hheld]; split; [exact Hi |intros i; rewrite Hblocks; apply Hheld].
      * destruct Htransfer as [-> [-> Hblocks]].
        exists local',empty_memory,(PoolHeld owner); split; [eapply owned_environment_held_invariant,Hsource' |].
        split; [exact Hupdate |]. eapply IHn; [exact Hsafe' |]. apply ShareHeld with (owner := owner).
        destruct Hheld as [Hi Hheld]; split; [exact Hi |intros i; rewrite Hblocks; apply Hheld].
      * destruct Htransfer as [Hbad _]; discriminate.
      * destruct Htransfer as [Eowner [-> [Hheld0 Hfree']]]. inversion Eowner; subst actor.
        destruct (invariant_singleton_remark active owner t returned invariant (proj1 Hheld) Hfragment
          (proj2 (owned_pool_status _ _ _ _ _ _ _ _ _ Hsource')))
          as (retained & Ereturned & Hmarks & HJ & Hbuffers & Hfree).
        destruct (owned_share_repool _ _ _ _ _ _ _ _ Hfragment eq_refl Hsource' retained Ereturned)
          as (big' & Hsp' & Houter').
        exists big',empty_memory,PoolFree; split.
        -- eapply owned_emp_environment_intro; [exact (proj1 (empty_generalized_well_formed active))
             |intros; reflexivity |intros; reflexivity |intros i H; exact H |exact Houter' |].
           split; [exact (proj1 (owned_pool_status _ _ _ _ _ _ _ _ _ Hsource')) |apply protocol_empty_satisfies].
        -- split.
           ++ eapply owned_share_update_release; [exact Hsp' |exact Hfree |intros i H; apply Hmarks,H |].
              rewrite Ereturned; exact Hupdate.
           ++ eapply IHn; [exact Hsafe' |]. eapply ShareClosed; eassumption.
Qed.

Theorem owned_share_valid active invariant pre command post :
  two_active_processors active -> invariant_fragment invariant ->
  assertion_lock_free active pre -> assertion_lock_free active post ->
  owned_valid active DisjointMode invariant pre command post ->
  owned_valid active DisjointMode A.Emp (A.Spatial invariant pre) command (A.Spatial invariant post).
Proof.
  intros Htwo Hfragment HPfree HQfree Hvalid s big (retained & local & Hsp & HJ & HP) n.
  eapply owned_safe_share; [exact Htwo |exact Hfragment |exact HQfree |apply Hvalid,HP |].
  eapply ShareClosed; [exact (HPfree _ _ HP) |exact HJ |exact Hsp].
Qed.

Corollary owned_share_derivation_valid active invariant pre command post :
  two_active_processors active -> invariant_fragment invariant ->
  assertion_lock_free active pre -> assertion_lock_free active post ->
  owned_derivation active invariant DisjointMode pre command post ->
  owned_valid active DisjointMode A.Emp (A.Spatial invariant pre) command (A.Spatial invariant post).
Proof.
  intros Htwo Hfragment HP HQ Hderive; apply owned_share_valid; try assumption.
  apply owned_calculus_sound; assumption.
Qed.
