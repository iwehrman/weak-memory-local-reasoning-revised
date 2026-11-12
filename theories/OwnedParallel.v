From Stdlib Require Import List.
From WMLR Require Import Expressions Languages Machine Separation RepairedSeparation
  GeneralizedFlushing FrameDecomposition OperationalSemantics ProgramSteps Assertions
  AssertionSemantics PersistentAssertions Safety Specifications OwnedSafety OwnedFraming
  OwnedInterference.
Import ListNotations.

(** Parallel composition for the single owned-safety predicate. Each thread
    may modify registers, provided it preserves the invariant's variables and
    the other thread's program and postcondition. *)

Lemma owned_safe_post_mono active mode invariant n command s local post post' :
  (forall t r, persistent_models active t r post -> persistent_models active t r post') ->
  owned_safe active mode invariant n command s local post ->
  owned_safe active mode invariant n command s local post'.
Proof.
  intros Hpost; revert command s local; induction n; intros command s local Hsafe; [exact I |].
  intros later Hfuture; destruct (Hsafe later Hfuture) as [Hdone Hprogress].
  split; [intros Hterminal; apply Hpost, Hdone, Hterminal |].
  intros pool frame whole phase Henv; destruct (Hprogress _ _ _ _ Henv) as [Hnoabort Hsteps].
  split; [exact Hnoabort |]. intros action next t whole' Hstep.
  destruct (Hsteps _ _ _ _ Hstep) as (local' & pool' & phase' & Henv' & Hupdate & Hsafe').
  exists local', pool', phase'; split; [exact Henv' |]. split; [exact Hupdate |apply IHn, Hsafe'].
Qed.

Lemma owned_update_identity active phase local pool :
  owned_update active OrdinaryAction phase phase local pool local pool.
Proof.
  constructor.
  - split; [reflexivity |]. split; [reflexivity |intros; reflexivity].
  - intros; assumption.
  - intros; left; assumption.
Qed.

Lemma owned_safe_spatial_frame_right active mode invariant n command s local post retained big frame_assertion :
  owned_safe active mode invariant n command s local post ->
  frame_variable_condition command frame_assertion ->
  persistent_models active s retained frame_assertion ->
  spatial (proj1_sig local) (proj1_sig retained) (proj1_sig big) ->
  owned_safe active mode invariant n command s big (A.Spatial post frame_assertion).
Proof.
  intros Hsafe Hvariables HR Hspatial.
  eapply owned_safe_post_mono with (post := A.Spatial frame_assertion post).
  - intros t r (a & b & Hsplit & Ha & Hb); exists b, a.
    split; [apply spatial_comm, Hsplit |auto].
  - eapply owned_safe_spatial_frame; [exact Hsafe |exact Hvariables |exact HR |].
    apply spatial_comm, Hspatial.
Qed.

Lemma owned_safe_step_interference active mode invariant n actor sibling s t whole whole' action next local post :
  program_step active action actor (State s whole) next (State t whole') ->
  Specifications.disjoint (C.modifies actor) (C.fv sibling ++ A.fv post) ->
  frame_variable_condition actor invariant ->
  owned_safe active mode invariant n sibling s local post ->
  owned_safe active mode invariant n sibling t local post.
Proof.
  intros Hstep Hsibling HJ Hsafe.
  eapply owned_safe_stack_agrees with (variables := A.fv invariant ++ (C.fv sibling ++ A.fv post));
    [| | | |exact Hsafe].
  - intros x Hx; apply in_or_app; auto.
  - intros x Hx; apply in_or_app; right; apply in_or_app; auto.
  - intros x Hx; apply in_or_app; right; apply in_or_app; auto.
  - intros x Hx; apply (step_preserves_unmodified _ _ _ _ _ (program_step_erases _ _ _ _ _ _ Hstep) x).
    intros Hmod; apply in_app_or in Hx; destruct Hx as [Hx |Hx];
      [exact (HJ x Hmod Hx) |exact (Hsibling x Hmod Hx)].
Qed.

(** A component step keeps its sibling exactly fixed, including at acquire
    and release. The sibling can then choose the changed component as a fresh
    environment at its next turn. *)
Lemma owned_spatial_component_step active mode invariant n command s local post (retained big : resource active)
    pool frame whole phase action next t whole' :
  owned_safe active mode invariant (S n) command s local post ->
  spatial (proj1_sig retained) (proj1_sig local) (proj1_sig big) ->
  owned_environment active mode invariant s big pool frame whole phase ->
  program_step active action command (State s whole) next (State t whole') ->
  exists local' big' pool' phase',
    spatial (proj1_sig retained) (proj1_sig local') (proj1_sig big') /\
    owned_environment active mode invariant t big' pool' frame whole' phase' /\
    owned_update active action phase phase' big pool big' pool' /\
    owned_safe active mode invariant n next t local' post.
Proof.
  intros Hsafe Hspatial Henv Hstep.
  pose proof (spatial_in_repaired active _ _ _ Hspatial) as Hinner.
  assert (Hmode : mode_compatible active mode retained local).
  { destruct mode; [exact I |exact (proj1 (proj1 (proj1 Hspatial)))]. }
  destruct (owned_environment_unframe _ _ _ _ _ _ _ _ _ _ _ Hinner Hmode Henv)
    as (grouped & Hgroup & Hsmall).
  destruct (owned_safe_program_step _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hsafe Hsmall Hstep)
    as (local' & pool' & phase' & Hsmall' & Hupdate & Hsafe').
  pose proof (proj1 (owned_mode_parts _ _ _ _ _ _ Hinner
    (owned_mode _ _ _ _ _ _ _ _ _ Henv))) as HFR.
  destruct (owned_environment_reframe _ _ _ _ _ _ _ _ _ _ _ Hgroup HFR Hsmall')
    as (big' & Hinner' & Henv').
  exists local', big', pool', phase'; split.
  - exact (owned_spatial_reconstruction _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
      Hgroup Hspatial Hinner' Hsmall Hupdate).
  - split; [exact Henv' |]. split; [|exact Hsafe'].
    exact (owned_update_frame _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
      Hgroup Hinner Hinner' Hsmall Hupdate).
Qed.

Theorem owned_safe_parallel active mode invariant n left right s l r big left_post right_post :
  owned_safe active mode invariant n left s l left_post ->
  owned_safe active mode invariant n right s r right_post ->
  Specifications.disjoint (C.modifies left) (C.fv right ++ A.fv right_post) ->
  Specifications.disjoint (C.modifies right) (C.fv left ++ A.fv left_post) ->
  frame_variable_condition left invariant -> frame_variable_condition right invariant ->
  spatial (proj1_sig l) (proj1_sig r) (proj1_sig big) ->
  owned_safe active mode invariant n (C.Parallel left right) s big (A.Spatial left_post right_post).
Proof.
  revert left right s l r big; induction n;
    intros left right s l r big HL HR HLR HRL HJL HJR Hsplit; [exact I |].
  intros later Hfuture.
  destruct (resource_spatial_future_split _ _ _ _ _ Hfuture Hsplit)
    as (l0 & r0 & HLfuture & HRfuture & Hsplit0).
  pose proof (owned_safe_future _ _ _ _ _ _ _ _ _ HLfuture HL) as HL0.
  pose proof (owned_safe_future _ _ _ _ _ _ _ _ _ HRfuture HR) as HR0.
  pose proof (spatial_comm _ _ _ Hsplit0) as Hswap0.
  split; [intros [annotation E]; discriminate E |].
  intros pool frame whole phase Henv.
  assert (HmodeL : mode_compatible active mode r0 l0).
  { destruct mode; [exact I |exact (proj1 (proj1 (proj1 Hswap0)))]. }
  assert (HmodeR : mode_compatible active mode l0 r0).
  { destruct mode; [exact I |exact (proj1 (proj1 (proj1 Hsplit0)))]. }
  destruct (owned_environment_unframe _ _ _ _ _ _ _ _ _ _ _
    (spatial_in_repaired active _ _ _ Hswap0) HmodeL Henv) as (frameL & HgroupL & HenvL).
  destruct (owned_environment_unframe _ _ _ _ _ _ _ _ _ _ _
    (spatial_in_repaired active _ _ _ Hsplit0) HmodeR Henv) as (frameR & HgroupR & HenvR).
  split.
  - intros Hfault; inversion Hfault; subst.
    + eapply (owned_safe_no_abort _ _ _ _ _ _ _ _ _ _ _ _ HL0 HenvL); eassumption.
    + eapply (owned_safe_no_abort _ _ _ _ _ _ _ _ _ _ _ _ HR0 HenvR); eassumption.
  - intros action next t whole' Hstep; inversion Hstep; subst.
    + match goal with
      | Hcomponent : program_step active _ left (State _ _) _ (State _ _) |- _ =>
        pose proof Hcomponent as Hleft
      end.
      destruct (owned_spatial_component_step _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
        HL0 Hswap0 Henv Hleft)
        as (l' & big' & pool' & phase' & Hsplit' & Henv' & Hupdate & HL').
      exists big', pool', phase'; split; [exact Henv' |]. split; [exact Hupdate |].
      eapply IHn; [exact HL' | | | | |exact HJR |apply spatial_comm, Hsplit'].
      * eapply owned_safe_step_interference; [exact Hleft |exact HLR |exact HJL |].
        apply owned_safe_weaken_one, HR0.
      * intros x Hmod Hfv; apply (HLR x); [|exact Hfv].
        eapply step_modifies_subset; [exact (program_step_erases _ _ _ _ _ _ Hleft) |exact Hmod].
      * intros x Hmod Hfv; apply (HRL x Hmod); apply in_app_or in Hfv.
        destruct Hfv as [Hfv |Hfv]; apply in_or_app; [left |right; exact Hfv].
        eapply step_fv_subset; [exact (program_step_erases _ _ _ _ _ _ Hleft) |exact Hfv].
      * intros x Hmod Hfv; apply (HJL x); [|exact Hfv].
        eapply step_modifies_subset; [exact (program_step_erases _ _ _ _ _ _ Hleft) |exact Hmod].
    + match goal with
      | Hcomponent : program_step active _ right (State _ _) _ (State _ _) |- _ =>
        pose proof Hcomponent as Hright
      end.
      destruct (owned_spatial_component_step _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
        HR0 Hsplit0 Henv Hright)
        as (r' & big' & pool' & phase' & Hsplit' & Henv' & Hupdate & HR').
      exists big', pool', phase'; split; [exact Henv' |]. split; [exact Hupdate |].
      eapply IHn; [|exact HR' | | |exact HJL | |exact Hsplit'].
      * eapply owned_safe_step_interference; [exact Hright |exact HRL |exact HJR |].
        apply owned_safe_weaken_one, HL0.
      * intros x Hmod Hfv; apply (HLR x Hmod); apply in_app_or in Hfv.
        destruct Hfv as [Hfv |Hfv]; apply in_or_app; [left |right; exact Hfv].
        eapply step_fv_subset; [exact (program_step_erases _ _ _ _ _ _ Hright) |exact Hfv].
      * intros x Hmod Hfv; apply (HRL x); [|exact Hfv].
        eapply step_modifies_subset; [exact (program_step_erases _ _ _ _ _ _ Hright) |exact Hmod].
      * intros x Hmod Hfv; apply (HJR x); [|exact Hfv].
        eapply step_modifies_subset; [exact (program_step_erases _ _ _ _ _ _ Hright) |exact Hmod].
    + exists later, pool, phase; split; [exact Henv |].
      split; [apply owned_update_identity |].
      eapply owned_safe_spatial_frame; [apply owned_safe_weaken_one, HR0 | | |exact Hsplit0].
      * intros x Hmod Hfv; apply (HRL x Hmod), in_or_app; auto.
      * eapply owned_safe_terminal; [exact HL0 |eexists; reflexivity].
    + exists later, pool, phase; split; [exact Henv |].
      split; [apply owned_update_identity |].
      eapply owned_safe_spatial_frame_right; [apply owned_safe_weaken_one, HL0 | | |exact Hsplit0].
      * intros x Hmod Hfv; apply (HLR x Hmod), in_or_app; auto.
      * eapply owned_safe_terminal; [exact HR0 |eexists; reflexivity].
Qed.

Theorem owned_parallel_valid active mode invariant left_pre left left_post right_pre right right_post :
  owned_valid active mode invariant left_pre left left_post ->
  owned_valid active mode invariant right_pre right right_post ->
  parallel_variable_condition
    (Build_concurrent_specification invariant left_pre left left_post)
    (Build_concurrent_specification invariant right_pre right right_post) ->
  frame_variable_condition left invariant -> frame_variable_condition right invariant ->
  owned_valid active mode invariant (A.Spatial left_pre right_pre)
    (C.Parallel left right) (A.Spatial left_post right_post).
Proof.
  intros HL HR [Hright Hleft] HJL HJR s big (l & r & Hsplit & HP & HRP) n.
  eapply owned_safe_parallel; [apply HL, HP |apply HR, HRP | | |exact HJL |exact HJR |exact Hsplit].
  - intros x Hmod Hfv; apply (Hleft x); [|exact Hmod].
    unfold branch_fv; cbn; apply in_or_app; right; exact Hfv.
  - intros x Hmod Hfv; apply (Hright x); [|exact Hmod].
    unfold branch_fv; cbn; apply in_or_app; right; exact Hfv.
Qed.
