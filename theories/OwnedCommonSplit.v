From Stdlib Require Import List ZArith.
From WMLR Require Import Expressions Languages Machine BufferRelations Separation
  RepairedSeparation GeneralizedFlushing FrameDecomposition OperationalSemantics ProgramSteps
  Assertions AssertionSemantics ConcreteAssertions PersistentAssertions Specifications
  TemporalSafety InvariantFragment OwnedSafety OwnedFraming.
Import ListNotations.

(** Queue 5.3. The hypotheses refer to ONE pair of witnesses. No new
    assertion connective or safety predicate is introduced. *)
Lemma common_temporal_spatial active a b out :
  BufferRelations.disjoint (memory_domain (underlying a)) (memory_domain (underlying b)) ->
  repaired_temporal active a b out -> spatial a b out.
Proof.
  intros Hd [Hstable [[Hcompat [Hh [Hb Hk]]] [Hbefore Hmarks]]].
  split; [|exact Hmarks]. split.
  - split; [exact Hd |exact (proj1 Hstable)].
  - split; [exact Hh |]. split; [|exact Hk].
    intros i; rewrite Hb; apply interleaves_app.
Qed.

Lemma resource_common_future_split active (out later a b : resource active) :
  resource_future active out later ->
  spatial (proj1_sig a) (proj1_sig b) (proj1_sig out) ->
  repaired_temporal active (proj1_sig a) (proj1_sig b) (proj1_sig out) ->
  exists a' b', resource_future active a a' /\ resource_future active b b' /\
    spatial (proj1_sig a') (proj1_sig b') (proj1_sig later) /\
    repaired_temporal active (proj1_sig a') (proj1_sig b') (proj1_sig later).
Proof.
  intros HF Hsp Htm.
  destruct (resource_temporal_future_split _ _ _ _ _ HF Htm) as (a' & b' & HA & HB & HT).
  exists a',b'; split; [exact HA |]. split; [exact HB |]. split; [|exact HT].
  apply (common_temporal_spatial active); [|exact HT].
  intros loc Ha Hb; apply (proj1 (proj1 (proj1 Hsp)) loc).
  - eapply flushes_domain_subset; [apply generalized_future_memory_flushes,HA |exact Ha].
  - eapply flushes_domain_subset; [apply generalized_future_memory_flushes,HB |exact Hb].
Qed.

Lemma common_environment_overlap active mode invariant s local pool frame whole phase :
  owned_environment active mode invariant s local pool frame whole phase ->
  owned_environment active OverlapMode invariant s local pool frame whole phase.
Proof. intros [HP HW HC HM HS]; constructor; assumption || exact I. Qed.

(** The retained resource is fixed within the actual program step; both
    successor relations use precisely [retained], [local'] and [big']. *)
Theorem owned_common_reconstruction active mode invariant s t action command next
    (local local' retained big big' frame grouped : resource active)
    pool pool' whole whole' phase phase' :
  invariant_fragment invariant ->
  repaired_spatiotemporal active (proj1_sig frame) (proj1_sig retained) (proj1_sig grouped) ->
  spatial (proj1_sig retained) (proj1_sig local) (proj1_sig big) ->
  repaired_temporal active (proj1_sig retained) (proj1_sig local) (proj1_sig big) ->
  repaired_spatiotemporal active (proj1_sig retained) (proj1_sig local') (proj1_sig big') ->
  owned_environment active mode invariant s big pool frame whole phase ->
  owned_environment active mode invariant t big' pool' frame whole' phase' ->
  owned_environment active mode invariant s local pool grouped whole phase ->
  owned_environment active mode invariant t local' pool' grouped whole' phase' ->
  owned_update active action phase phase' local pool local' pool' ->
  program_step active action command (State s whole) next (State t whole') ->
  spatial (proj1_sig retained) (proj1_sig local') (proj1_sig big') /\
  repaired_temporal active (proj1_sig retained) (proj1_sig local') (proj1_sig big').
Proof.
  intros Hfragment Hgroup Hsp Htm Hout Henv Henv' Hsmall Hsmall' Hupdate Hstep; split.
  - eapply owned_spatial_reconstruction; eassumption.
  - eapply owned_temporal_reconstruction; try eassumption;
      eapply common_environment_overlap; eassumption.
Qed.

Theorem owned_safe_common_frame active mode invariant n command s local post retained big frame_assertion :
  invariant_fragment invariant ->
  owned_safe active mode invariant n command s local post ->
  frame_variable_condition command frame_assertion ->
  persistent_models active s retained frame_assertion ->
  spatial (proj1_sig retained) (proj1_sig local) (proj1_sig big) ->
  repaired_temporal active (proj1_sig retained) (proj1_sig local) (proj1_sig big) ->
  owned_safe active mode invariant n command s big (A.strong_temporal frame_assertion post).
Proof.
  intros Hfragment; revert command s local retained big; induction n;
    intros command s local retained big Hsafe Hvariables HR Hsp Htm; [exact I |].
  intros later Hfuture.
  destruct (resource_common_future_split _ _ _ _ _ Hfuture Hsp Htm)
    as (retained0 & local0 & HRfuture & HPfuture & Hsp0 & Htm0).
  assert (HR0 : persistent_models active s retained0 frame_assertion).
  { eapply persistent_assertion_flushing_closed; eassumption. }
  pose proof (owned_safe_future _ _ _ _ _ _ _ _ _ HPfuture Hsafe) as Hsafe0.
  pose proof (spatial_in_repaired active _ _ _ Hsp0) as Hrepair0.
  split.
  - intros Hdone.
    assert (HQ : persistent_models active s local0 post) by
      (eapply owned_safe_terminal; eassumption).
    split; exists retained0,local0; auto.
  - intros pool frame whole phase Henv.
    assert (HRP : mode_compatible active mode retained0 local0).
    { destruct mode; [exact I |exact (proj1 (proj1 (proj1 Hsp0)))]. }
    destruct (owned_environment_unframe _ _ _ _ _ _ _ _ _ _ _ Hrepair0 HRP Henv)
      as (grouped & Hgroup & Hsmall).
    split; [eapply owned_safe_no_abort; eassumption |].
    intros action next t whole' Hstep.
    destruct (owned_safe_program_step _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hsafe0 Hsmall Hstep)
      as (local' & pool' & phase' & Hsmall' & Hupdate & Hsafe').
    pose proof (proj1 (owned_mode_parts _ _ _ _ _ _ Hrepair0
      (owned_mode _ _ _ _ _ _ _ _ _ Henv))) as HFR.
    destruct (owned_environment_reframe _ _ _ _ _ _ _ _ _ _ _ Hgroup HFR Hsmall')
      as (big' & Hrepair' & Henv').
    destruct (owned_common_reconstruction _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
      Hfragment Hgroup Hsp0 Htm0 Hrepair' Henv Henv' Hsmall Hsmall' Hupdate Hstep) as [Hsp' Htm'].
    exists big',pool',phase'; split; [exact Henv' |]. split.
    + exact (owned_update_frame _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
        Hgroup Hrepair0 Hrepair' Hsmall Hupdate).
    + eapply IHn; [exact Hsafe' | | |exact Hsp' |exact Htm'].
      * intros x Hmod Hfv; apply (Hvariables x); [|exact Hfv].
        eapply step_modifies_subset; [exact (program_step_erases _ _ _ _ _ _ Hstep) |exact Hmod].
      * assert (Hagrees : agrees (A.fv frame_assertion) s t).
        { intros x Hfv; apply (step_preserves_unmodified _ _ _ _ _ (program_step_erases _ _ _ _ _ _ Hstep) x).
          intros Hmod; exact (Hvariables x Hmod Hfv). }
        apply (proj1 (future_satisfies_agrees _ _ frame_assertion s t Hagrees retained0)),HR0.
Qed.
