From Stdlib Require Import List.
From WMLR Require Import Expressions Languages Machine Separation RepairedSeparation
  GeneralizedFlushing FrameDecomposition OperationalSemantics ProgramSteps Assertions
  AssertionSemantics PersistentAssertions Safety Specifications OwnedSafety
  BufferedPoolCandidate BufferedPoolResources BufferedPoolRules BufferedPoolFraming BufferedPoolInterference.
Import ListNotations.

Theorem buffered_safe_parallel active invariant n left right s l r big left_post right_post :
  buffered_safe active DisjointMode invariant n left s l left_post ->
  buffered_safe active DisjointMode invariant n right s r right_post ->
  Specifications.disjoint (C.modifies left) (C.fv right ++ A.fv right_post) ->
  Specifications.disjoint (C.modifies right) (C.fv left ++ A.fv left_post) ->
  frame_variable_condition left invariant -> frame_variable_condition right invariant ->
  spatial (proj1_sig l) (proj1_sig r) (proj1_sig big) ->
  buffered_safe active DisjointMode invariant n (C.Parallel left right) s big (A.Spatial left_post right_post).
Proof.
  revert left right s l r big; induction n;
    intros left right s l r big HL HR HLR HRL HJL HJR Hsplit; [exact I |].
  intros later Hfuture.
  destruct (resource_spatial_future_split _ _ _ _ _ Hfuture Hsplit)
    as (l0 & r0 & HLfuture & HRfuture & Hsplit0).
  pose proof (buffered_safe_future _ _ _ _ _ _ _ _ _ HLfuture HL) as HL0.
  pose proof (buffered_safe_future _ _ _ _ _ _ _ _ _ HRfuture HR) as HR0.
  pose proof (spatial_comm _ _ _ Hsplit0) as Hswap0.
  split; [intros [annotation E]; discriminate E |].
  intros pool frame whole Henv.
  destruct (buffered_environment_unframe _ _ _ _ _ _ _ _ _ Hswap0 Henv)
    as (frameL & HgroupL & HenvL).
  destruct (buffered_environment_unframe _ _ _ _ _ _ _ _ _ Hsplit0 Henv)
    as (frameR & HgroupR & HenvR).
  split.
  - intros Hfault; inversion Hfault; subst.
    + eapply (buffered_safe_no_abort _ _ _ _ _ _ _ _ _ _ _ HL0 HenvL); eassumption.
    + eapply (buffered_safe_no_abort _ _ _ _ _ _ _ _ _ _ _ HR0 HenvR); eassumption.
  - split.
    + intros action next t whole' Hstep; inversion Hstep; subst.
      * match goal with
        | Hcomponent : program_step active _ left (State _ _) _ (State _ _) |- _ =>
          pose proof Hcomponent as Hleft
        end.
        destruct (buffered_spatial_component_step _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
          HL0 Hswap0 Henv Hleft)
          as (l' & big' & pool' & Hsplit' & Henv' & Hupdate & HL').
        exists big', pool'; split; [exact Henv' |]. split; [exact Hupdate |].
        eapply IHn; [exact HL' | | | | |exact HJR |apply spatial_comm, Hsplit'].
        -- eapply buffered_safe_step_interference; [exact Hleft |exact HLR |exact HJL |].
        apply buffered_safe_weaken_one, HR0.
        -- intros x Hmod Hfv; apply (HLR x); [|exact Hfv].
        eapply step_modifies_subset; [exact (program_step_erases _ _ _ _ _ _ Hleft) |exact Hmod].
        -- intros x Hmod Hfv; apply (HRL x Hmod); apply in_app_or in Hfv.
        destruct Hfv as [Hfv |Hfv]; apply in_or_app; [left |right; exact Hfv].
        eapply step_fv_subset; [exact (program_step_erases _ _ _ _ _ _ Hleft) |exact Hfv].
        -- intros x Hmod Hfv; apply (HJL x); [|exact Hfv].
        eapply step_modifies_subset; [exact (program_step_erases _ _ _ _ _ _ Hleft) |exact Hmod].
      * match goal with
        | Hcomponent : program_step active _ right (State _ _) _ (State _ _) |- _ =>
          pose proof Hcomponent as Hright
        end.
        destruct (buffered_spatial_component_step _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
          HR0 Hsplit0 Henv Hright)
          as (r' & big' & pool' & Hsplit' & Henv' & Hupdate & HR').
        exists big', pool'; split; [exact Henv' |]. split; [exact Hupdate |].
        eapply IHn; [|exact HR' | | |exact HJL | |exact Hsplit'].
        -- eapply buffered_safe_step_interference; [exact Hright |exact HRL |exact HJR |].
        apply buffered_safe_weaken_one, HL0.
        -- intros x Hmod Hfv; apply (HLR x Hmod); apply in_app_or in Hfv.
        destruct Hfv as [Hfv |Hfv]; apply in_or_app; [left |right; exact Hfv].
        eapply step_fv_subset; [exact (program_step_erases _ _ _ _ _ _ Hright) |exact Hfv].
        -- intros x Hmod Hfv; apply (HRL x); [|exact Hfv].
        eapply step_modifies_subset; [exact (program_step_erases _ _ _ _ _ _ Hright) |exact Hmod].
        -- intros x Hmod Hfv; apply (HJR x); [|exact Hfv].
        eapply step_modifies_subset; [exact (program_step_erases _ _ _ _ _ _ Hright) |exact Hmod].
      * exists later, pool; split; [exact Henv |].
        split; [apply buffered_update_identity |].
        eapply buffered_safe_spatial_frame; [apply buffered_safe_weaken_one, HR0 | | |exact Hsplit0].
        -- intros x Hmod Hfv; apply (HRL x Hmod), in_or_app; auto.
        -- eapply buffered_safe_terminal; [exact HL0 |eexists; reflexivity].
      * exists later, pool; split; [exact Henv |].
        split; [apply buffered_update_identity |].
        eapply buffered_safe_spatial_frame_right; [apply buffered_safe_weaken_one, HL0 | | |exact Hsplit0].
        -- intros x Hmod Hfv; apply (HLR x Hmod), in_or_app; auto.
        -- eapply buffered_safe_terminal; [exact HR0 |eexists; reflexivity].
    + intros actor whole' Hflush.
      destruct (buffered_environment_flush _ _ _ _ _ _ _ _ _ Henv Hflush)
        as (big' & frame' & pool' & Hupdate & Henv' & Hbigfuture).
      exists big', frame', pool'; split; [exact Hupdate |]. split; [exact Henv' |].
      destruct (resource_spatial_future_split _ _ _ _ _ Hbigfuture Hsplit0)
        as (l' & r' & HLfuture' & HRfuture' & Hsplit').
      eapply IHn; [| |exact HLR |exact HRL |exact HJL |exact HJR |exact Hsplit'].
      * eapply buffered_safe_future; [exact HLfuture' |apply buffered_safe_weaken_one, HL0].
      * eapply buffered_safe_future; [exact HRfuture' |apply buffered_safe_weaken_one, HR0].
Qed.

Theorem buffered_parallel_valid active J LP left LQ RP right RQ :
  buffered_parallel_rule active J LP left LQ RP right RQ.
Proof.
  intros [Hlf HL] [Hrf HR] [Hright Hleft] HJL HJR; split; [split; assumption |].
  intros s big (l & r & Hsplit & HP & HRP) n.
  eapply buffered_safe_parallel; [apply HL, HP |apply HR, HRP | | |exact HJL |exact HJR |exact Hsplit].
  - intros x Hmod Hfv; apply (Hleft x); [|exact Hmod].
    unfold branch_fv; cbn; apply in_or_app; right; exact Hfv.
  - intros x Hmod Hfv; apply (Hright x); [|exact Hmod].
    unfold branch_fv; cbn; apply in_or_app; right; exact Hfv.
Qed.
