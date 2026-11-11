From Stdlib Require Import List ZArith.
From WMLR Require Import Expressions Languages Machine BufferRelations Separation RepairedSeparation
  GeneralizedFlushing OperationalSemantics Assertions AssertionSemantics PersistentAssertions
  Safety Specifications OwnershipProtocol TemporalSafety RegionalResources RegionalSafety.
Import ListNotations.

Lemma execution_steps active n command s whole last t final :
  execution active n command s whole last t final -> steps active command (State s whole) last (State t final).
Proof. induction 1; [constructor |econstructor; eassumption]. Qed.

Lemma temporal_free_parts active (past region combined : resource active) :
  repaired_temporal active (proj1_sig past) (proj1_sig region) (proj1_sig combined) ->
  lock_free (resource_memory active combined) ->
  lock_free (resource_memory active past) /\ lock_free (resource_memory active region).
Proof.
  intros [_ [[_ [_ [_ Hblocks]]] _]] Hfree.
  split; intros i H; apply (Hfree i), Hblocks; auto.
Qed.

(** A checked replacement at the boundary of the whole ownership region:
       { R ; (J * P) } c { R ; (J * Q) }.
    This differs from placing R around only P/Q under a hidden invariant.
    The usual variable condition suffices; past heap overlap with J is allowed. *)
Theorem regional_history_frame_rule active owner invariant pre command post history_assertion s whole :
  regional_valid active owner invariant Closed pre command Closed post ->
  frame_variable_condition command history_assertion -> lock_free whole ->
  persistent_full_satisfies active s whole (A.Temporal history_assertion (A.Spatial invariant pre)) ->
  forall n last t final, execution active n command s whole last t final ->
    ~ abort active last (State t final) /\
    (terminal last -> lock_free final /\
      persistent_full_satisfies active t final (A.Temporal history_assertion (A.Spatial invariant post))).
Proof.
  intros Hvalid Hvariables Hfree (combined & Eworld & history & region & Htm & HR & pool & local & Hsp & HJ & HP).
  assert (Eraw : resource_memory active combined = whole) by (unfold resource_memory; rewrite Eworld; reflexivity).
  assert (Hcombinedfree : lock_free (resource_memory active combined)) by (rewrite Eraw; exact Hfree).
  destruct (temporal_free_parts _ _ _ _ Htm Hcombinedfree) as [Hhistoryfree Hregionfree].
  assert (Hr : marked_region active owner invariant Closed s local region) by (split; [exact Hregionfree |exists pool; auto]).
  assert (Henv : regional_environment active owner invariant Closed s local region history whole).
  { constructor; [exact Hr |exact Hhistoryfree |exists combined; auto]. }
  intros n last t final Hrun.
  pose proof (Hvalid _ _ _ Hr HP (S n)) as Hsafe.
  split; [eapply regional_execution_no_abort; eassumption |]. intros Hlast.
  destruct (regional_execution_residual _ _ _ _ _ _ _ _ _ _ Hrun _ _ _ _ _ _ Hsafe Henv)
    as (phase' & local' & region' & history' & Henv' & Hhf & _ & Hdone & _).
  destruct (Hdone Hlast) as [-> HQ].
  destruct Henv' as [[Hregionfree' [pool' [HJ' Hsp']]] Hhistoryfree' [combined' [Efinal Htm']]].
  assert (HR' : persistent_models active t history' history_assertion).
  { assert (Hagree : agrees (A.fv history_assertion) s t).
    { intros x Hx. apply (steps_preserve_unmodified _ _ _ _ _ (execution_steps _ _ _ _ _ _ _ _ Hrun) x).
      intros Hwrite; exact (Hvariables x Hwrite Hx). }
    apply (proj1 (future_satisfies_agrees _ _ _ _ _ Hagree history')).
    eapply persistent_assertion_flushing_closed; eassumption. }
  split.
  - intros i H; rewrite <- Efinal in H.
    apply (proj2 (proj2 (proj2 (proj1 (proj2 Htm')))) i) in H.
    destruct H; [apply (Hhistoryfree' i) |apply (Hregionfree' i)]; assumption.
  - rewrite <- Efinal. apply persistent_promote_full.
    exists history', region'; split; [exact Htm' |]. split; [exact HR' |].
    exists pool', local'; split; [exact Hsp' |auto].
Qed.
