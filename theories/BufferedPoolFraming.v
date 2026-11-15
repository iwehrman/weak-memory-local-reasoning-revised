From Stdlib Require Import List Arith ZArith.
From WMLR Require Import Expressions Languages Machine BufferRelations Separation
  RepairedSeparation GeneralizedFlushing FrameDecomposition OperationalSemantics ProgramSteps
  Assertions AssertionSemantics PersistentAssertions PersistentRules Specifications Safety TemporalSafety
  InvariantFragment OwnedSafety BufferedPoolCandidate BufferedPoolResources BufferedPoolRules.
Import ListNotations.

Lemma buffered_spatial_component_step active J n c s local Q (retained big : resource active)
    pool frame whole action next t whole' :
  buffered_safe active DisjointMode J (S n) c s local Q ->
  spatial (proj1_sig retained) (proj1_sig local) (proj1_sig big) ->
  buffered_environment active DisjointMode J s big pool frame whole ->
  program_step active action c (State s whole) next (State t whole') ->
  exists local' big' pool',
    spatial (proj1_sig retained) (proj1_sig local') (proj1_sig big') /\
    buffered_environment active DisjointMode J t big' pool' frame whole' /\
    buffered_update active action big pool big' pool' /\
    buffered_safe active DisjointMode J n next t local' Q.
Proof.
  intros Hsafe Hsp Henv Hstep.
  destruct (buffered_environment_unframe _ _ _ _ _ _ _ _ _ Hsp Henv) as (grouped & Hgroup & Hsmall).
  destruct (buffered_safe_program_step _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hsafe Hsmall Hstep)
    as (local' & pool' & Hsmall' & Hupdate & Hsafe').
  destruct (buffered_environment_reframe _ _ _ _ _ _ _ _ _ Hgroup Hsmall') as (big' & Hsp' & Henv').
  exists local', big', pool'; split; [exact Hsp' |]. split; [exact Henv' |].
  split; [eapply buffered_update_frame; eassumption |exact Hsafe'].
Qed.

Theorem buffered_safe_spatial_frame active J n c s local Q retained big R :
  buffered_safe active DisjointMode J n c s local Q -> frame_variable_condition c R ->
  persistent_models active s retained R ->
  spatial (proj1_sig retained) (proj1_sig local) (proj1_sig big) ->
  buffered_safe active DisjointMode J n c s big (A.Spatial R Q).
Proof.
  revert c s local retained big; induction n; intros c s local retained big Hsafe Hvars HR Hsp; [exact I |].
  intros later Hfuture.
  destruct (resource_spatial_future_split _ _ _ _ _ Hfuture Hsp)
    as (retained0 & local0 & HRfuture & HPfuture & Hsp0).
  pose proof (buffered_safe_future _ _ _ _ _ _ _ _ _ HPfuture Hsafe) as Hsafe0.
  pose proof (persistent_assertion_flushing_closed _ _ _ _ _ HRfuture HR) as HR0.
  split.
  - intros Hdone; exists retained0, local0; split; [exact Hsp0 |].
    split; [exact HR0 |eapply buffered_safe_terminal; eassumption].
  - intros pool frame whole Henv.
    destruct (buffered_environment_unframe _ _ _ _ _ _ _ _ _ Hsp0 Henv) as (grouped & Hgroup & Hsmall).
    split; [eapply buffered_safe_no_abort; eassumption |]. split.
    + intros action next t whole' Hstep.
      destruct (buffered_spatial_component_step _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hsafe0 Hsp0 Henv Hstep)
        as (local' & big' & pool' & Hsp' & Henv' & Hupdate & Hsafe').
      exists big', pool'; split; [exact Henv' |]. split; [exact Hupdate |].
      eapply IHn; [exact Hsafe' | | |exact Hsp'].
      * intros x Hmod Hfv; apply (Hvars x); [|exact Hfv].
        eapply step_modifies_subset; [exact (program_step_erases _ _ _ _ _ _ Hstep) |exact Hmod].
      * assert (Hagrees : agrees (A.fv R) s t).
        { intros x Hfv; apply (step_preserves_unmodified _ _ _ _ _ (program_step_erases _ _ _ _ _ _ Hstep) x).
          intros Hmod; exact (Hvars x Hmod Hfv). }
        apply (proj1 (future_satisfies_agrees _ _ R s t Hagrees retained0)), HR0.
    + intros actor whole' Hflush.
      destruct (buffered_environment_flush _ _ _ _ _ _ _ _ _ Henv Hflush)
        as (big' & frame' & pool' & Hupdate & Henv' & Hbigfuture).
      exists big', frame', pool'; split; [exact Hupdate |]. split; [exact Henv' |].
      destruct (resource_spatial_future_split _ _ _ _ _ Hbigfuture Hsp0)
        as (retained' & local' & HRfuture' & HPfuture' & Hsp').
      eapply IHn; [|exact Hvars | |exact Hsp'].
      * eapply buffered_safe_future; [exact HPfuture' |apply buffered_safe_weaken_one, Hsafe0].
      * eapply persistent_assertion_flushing_closed; eassumption.
Qed.

Theorem buffered_spatial_frame_valid active J P c Q R : buffered_frame_rule active J P c Q R.
Proof.
  intros [Hfree Hvalid] Hvars; split; [exact Hfree |].
  intros s big (retained & local & Hsp & HR & HP) n.
  eapply buffered_safe_spatial_frame; [apply Hvalid, HP |exact Hvars |exact HR |exact Hsp].
Qed.

Lemma buffered_safe_spatial_frame_right active J n c s local Q retained big R :
  buffered_safe active DisjointMode J n c s local Q -> frame_variable_condition c R ->
  persistent_models active s retained R ->
  spatial (proj1_sig local) (proj1_sig retained) (proj1_sig big) ->
  buffered_safe active DisjointMode J n c s big (A.Spatial Q R).
Proof.
  intros Hsafe Hvars HR Hsp; eapply buffered_safe_post_mono with (Q := A.Spatial R Q).
  - intros t r (a & b & Hsplit & Ha & Hb); exists b, a; split; [apply spatial_comm, Hsplit |auto].
  - eapply buffered_safe_spatial_frame; [exact Hsafe |exact Hvars |exact HR |apply spatial_comm, Hsp].
Qed.
