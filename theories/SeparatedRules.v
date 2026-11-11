From Stdlib Require Import List ZArith.
From WMLR Require Import Expressions Languages Machine BufferRelations Separation RepairedSeparation
  GeneralizedFlushing FrameDecomposition OperationalSemantics Assertions AssertionSemantics PersistentAssertions
  Safety Specifications OwnershipProtocol OwnershipRules OwnershipHeap OwnershipCalculus PrivateOwnership
  TemporalSafety TemporalFence RegionalResources RegionalSafety RegionalFraming SeparatedSafety.
Import ListNotations.

(** Existing protected-region proofs lift while keeping the private resource
    separate. Their external frame can evolve only by actual buffer flushes. *)
Theorem separated_safe_from_protocol active owner invariant n command s phase protected finish protected_post
    (local : resource active) private_assertion :
  protocol_safe active owner invariant n command s phase protected finish protected_post ->
  frame_variable_condition command private_assertion ->
  lock_free (resource_memory active local) -> persistent_models active s local private_assertion ->
  separated_safe active owner invariant n command s phase local protected finish protected_post private_assertion.
Proof.
  revert command s phase protected local.
  induction n; intros command s phase protected local Hsafe Hvariables Hfree HP; [exact I |].
  destruct Hsafe as [Hr [Hdone [Hnoabort Hprogress]]].
  split; [exact Hr |]. split; [exact Hfree |]. split.
  - intros Hlast; destruct (Hdone Hlast) as [E HS]; auto.
  - split.
    + intros history whole Henv; destruct (separated_composition _ _ _ _ _ _ _ _ _ Henv) as (combined & Htm & Hsp).
      apply (Hnoabort (resource_memory active combined) whole).
      eapply separated_protocol_environment; eassumption.
    + intros history whole next t whole' Henv Hstep.
      destruct (separated_composition _ _ _ _ _ _ _ _ _ Henv) as (combined & Htm & Hsp).
      pose proof (separated_protocol_environment _ _ _ _ _ _ _ _ _ _ Henv Htm Hsp) as Hprotocol.
      destruct (Hprogress _ _ _ _ _ Hprotocol Hstep)
        as (phase' & protected' & combined_memory & Hprotocol' & Hcf & Hpd & Hsafe').
      destruct (resource_actual_flushes _ _ _ Hcf) as (combined' & Ec & Hfuture).
      destruct (resource_temporal_future_split _ _ _ _ _ Hfuture Htm)
        as (history' & local' & Hhf & Hlf & Htm').
      assert (Hcombinedfree : lock_free (resource_memory active combined')).
      { rewrite Ec; exact (protocol_frame_free _ _ _ _ _ _ _ _ Hprotocol'). }
      destruct (temporal_free_parts _ _ _ _ Htm' Hcombinedfree) as [Hhfree Hlfree].
      exists phase', local', protected', history'; split.
      * constructor; try assumption.
        -- exact (protocol_region_ok _ _ _ _ _ _ _ _ Hprotocol').
        -- exists combined'; split; [exact Htm' |rewrite Ec; exact (protocol_separation _ _ _ _ _ _ _ _ Hprotocol')].
      * split; [exact Hhf |]. split.
        -- eapply flushes_domain_subset; apply generalized_future_memory_flushes, Hlf.
        -- split; [exact Hpd |]. apply IHn; try assumption.
           ++ intros x Hwrite Hx; apply (Hvariables x); [eapply step_modifies_subset; eassumption |exact Hx].
           ++ assert (Hagree : agrees (A.fv private_assertion) s t).
              { intros x Hx; apply (step_preserves_unmodified _ _ _ _ _ Hstep x).
                intros Hwrite; exact (Hvariables x Hwrite Hx). }
              apply (proj1 (future_satisfies_agrees _ _ _ _ _ Hagree local')).
              eapply persistent_assertion_flushing_closed; eassumption.
Qed.

Theorem separated_protocol_valid active owner invariant start protected_pre command finish protected_post private_assertion :
  protocol_valid active owner invariant start protected_pre command finish protected_post ->
  frame_variable_condition command private_assertion ->
  separated_valid active owner invariant start protected_pre private_assertion command finish protected_post private_assertion.
Proof.
  intros Hvalid Hvariables s local protected Hr Hl HS HP n.
  apply separated_safe_from_protocol; try assumption; apply Hvalid; assumption.
Qed.

Lemma separated_skip_safe active owner invariant n annotation s phase local protected protected_post post :
  protocol_region active owner invariant phase s protected -> lock_free (resource_memory active local) ->
  protocol_assertion active phase s protected protected_post -> persistent_models active s local post ->
  separated_safe active owner invariant n (Concurrent.skip annotation) s phase local protected phase protected_post post.
Proof.
  intros Hr Hl HS HP; apply separated_safe_from_protocol; try assumption.
  - apply protocol_skip_safe; assumption.
  - intros x H; contradiction.
Qed.

Theorem separated_acquire_valid active owner invariant pre :
  separated_valid active owner invariant Closed A.Emp pre
    (Concurrent.Prim Concurrent.Lock (EVal (Z.pos owner))) Open (owned_assertion owner invariant) pre.
Proof. apply separated_protocol_valid; [apply protocol_acquire_valid |intros x H; contradiction]. Qed.

Theorem separated_release_valid active owner invariant post :
  separated_valid active owner invariant Open (owned_assertion owner invariant) post
    (Concurrent.Prim Concurrent.Unlock (EVal (Z.pos owner))) Closed A.Emp post.
Proof. apply separated_protocol_valid; [apply protocol_release_valid |intros x H; contradiction]. Qed.

Theorem separated_safe_sequence active owner invariant n first second s phase local protected
    middle protected_mid mid finish protected_post post :
  separated_safe active owner invariant n first s phase local protected middle protected_mid mid ->
  separated_valid active owner invariant middle protected_mid mid second finish protected_post post ->
  separated_safe active owner invariant n (Concurrent.Seq first second) s phase local protected finish protected_post post.
Proof.
  intros Hfirst Hsecond; revert first s phase local protected Hfirst.
  induction n; intros first s phase local protected Hfirst; [exact I |].
  destruct Hfirst as [Hr [Hl [Hterminal [Habort Hprogress]]]].
  split; [exact Hr |]. split; [exact Hl |]. split; [intros [ann E]; discriminate |]. split.
  - intros history whole Henv Hfault; inversion Hfault; subst; eapply Habort; eassumption.
  - intros history whole next t whole' Henv Hstep; inversion Hstep; subst.
    + assert (Hfirststep : step active first (State t whole) first (State t whole')) by (apply StepFlush; assumption).
      destruct (Hprogress _ _ _ _ _ Henv Hfirststep)
        as (phase' & local' & protected' & history' & Henv' & Hhf & Hld & Hpd & Hsafe).
      exists phase', local', protected', history'; split; [exact Henv' |]. split; [exact Hhf |].
      split; [exact Hld |]. split; [exact Hpd |apply IHn, Hsafe].
    + match goal with H : step _ first _ _ _ |- _ =>
        destruct (Hprogress _ _ _ _ _ Henv H)
          as (phase' & local' & protected' & history' & Henv' & Hhf & Hld & Hpd & Hsafe) end.
      exists phase', local', protected', history'; split; [exact Henv' |]. split; [exact Hhf |].
      split; [exact Hld |]. split; [exact Hpd |apply IHn, Hsafe].
    + destruct (Hterminal ltac:(eexists; reflexivity)) as [E [HS HP]]; subst phase.
      exists middle, local, protected, history; split; [exact Henv |]. split; [constructor |].
      split; [intros loc H; exact H |]. split; [intros loc H; exact H |apply Hsecond; assumption].
Qed.

Theorem separated_sequence_valid active owner invariant start protected_pre pre first middle protected_mid mid
    second finish protected_post post :
  separated_valid active owner invariant start protected_pre pre first middle protected_mid mid ->
  separated_valid active owner invariant middle protected_mid mid second finish protected_post post ->
  separated_valid active owner invariant start protected_pre pre (Concurrent.Seq first second) finish protected_post post.
Proof.
  intros Hfirst Hsecond s local protected Hr Hl HS HP n; eapply separated_safe_sequence;
    [apply Hfirst; eassumption |exact Hsecond].
Qed.

Lemma protocol_assertion_entails active phase s protected pre post :
  regional_entails active pre post -> protocol_assertion active phase s protected pre ->
  protocol_assertion active phase s protected post.
Proof. intros H (r & E & HP); exists r; split; [exact E |apply H, HP]. Qed.

(** Consequence is componentwise. Entailments over a spatial combination of
    protected and private assertions are deliberately not a consequence rule. *)
Lemma separated_safe_post_mono active owner invariant n command s phase local protected finish protected_post post protected_post' post' :
  regional_entails active protected_post protected_post' -> regional_entails active post post' ->
  separated_safe active owner invariant n command s phase local protected finish protected_post post ->
  separated_safe active owner invariant n command s phase local protected finish protected_post' post'.
Proof.
  intros HS HQ; revert command s phase local protected.
  induction n; intros command s phase local protected Hsafe; [exact I |].
  destruct Hsafe as [Hr [Hl [Hdone [Habort Hprogress]]]].
  split; [exact Hr |]. split; [exact Hl |]. split.
  - intros Hlast; destruct (Hdone Hlast) as [E [Hprotected Hlocal]]; split; [exact E |].
    split; [eapply protocol_assertion_entails; eassumption |apply HQ, Hlocal].
  - split; [exact Habort |]. intros history whole next t whole' Henv Hstep.
    destruct (Hprogress _ _ _ _ _ Henv Hstep)
      as (phase' & local' & protected' & history' & Henv' & Hhf & Hld & Hpd & Hsafe').
    exists phase', local', protected', history'; split; [exact Henv' |]. split; [exact Hhf |].
    split; [exact Hld |]. split; [exact Hpd |apply IHn, Hsafe'].
Qed.

Theorem separated_consequence_valid active owner invariant start protected_pre pre protected_pre' pre' command finish
    protected_post' post' protected_post post :
  regional_entails active protected_pre protected_pre' -> regional_entails active pre pre' ->
  separated_valid active owner invariant start protected_pre' pre' command finish protected_post' post' ->
  regional_entails active protected_post' protected_post -> regional_entails active post' post ->
  separated_valid active owner invariant start protected_pre pre command finish protected_post post.
Proof.
  intros HS HP Hvalid HT HQ s local protected Hr Hl Hprotected Hlocal n.
  eapply separated_safe_post_mono; [exact HT |exact HQ |].
  apply Hvalid; try assumption; [eapply protocol_assertion_entails; eassumption |apply HP, Hlocal].
Qed.

Lemma separated_environment_fence active owner invariant phase s local protected history whole i (Hi : active i) :
  separated_environment active owner invariant phase s local protected history whole -> buffers whole i = [] ->
  separated_environment active owner invariant phase s (mark_processor active local i Hi) protected history whole.
Proof.
  intros [Hr Hl Hh [combined [Htm Hsp]]] Hempty; constructor; try assumption.
  exists (mark_processor active combined i Hi); split; [|exact Hsp].
  apply temporal_mark_right; [exact Htm |].
  exact (proj1 (spatial_empty_buffer_parts _ _ _ _ Hsp Hempty)).
Qed.

(** A real fence may earn a private barrier. Its machine guard drains the
    entire issuing buffer, including any pending private temporal frame. *)
Theorem separated_fence_valid active owner invariant phase protected_assertion i :
  separated_valid active owner invariant phase protected_assertion A.Emp
    (Concurrent.Prim (Concurrent.Common Sequential.Fence) (EVal (Z.pos i))) phase
    protected_assertion (A.Barrier (EVal (Z.pos i))).
Proof.
  intros s local protected Hr Hl HS HP n; revert s local protected Hr Hl HS HP.
  induction n; intros s local protected Hr Hl HS HP; [exact I |].
  split; [exact Hr |]. split; [exact Hl |]. split; [intros [ann E]; discriminate |]. split.
  - intros history whole Henv Hfault; inversion Hfault; subst.
    match goal with H : primitive_abort _ _ _ _ |- _ => inversion H end.
  - intros history whole next t whole' Henv Hstep; inversion Hstep; subst.
    + match goal with H : primitive_step _ _ _ _ _ |- _ => inversion H; subst end.
      match goal with E : eval_expr _ (EVal (Z.pos _)) = Z.pos _ |- _ => simpl in E; inversion E; subst end.
      match goal with Hi : active ?j |- _ => exists phase, (mark_processor active local j Hi), protected, history end.
      split; [eapply separated_environment_fence; eassumption |]. split; [constructor |].
      split; [intros loc H; exact H |]. split; [intros loc H; exact H |].
      apply separated_skip_safe; try assumption; apply marked_emp_barrier, HP.
    + match goal with H : flush _ _ _ |- _ =>
        destruct (separated_environment_flush _ _ _ _ _ _ _ _ _ _ Henv H)
          as (local' & protected' & history' & Henv' & Hlf & Hpf & Hhf & Hld & Hpd) end.
      exists phase, local', protected', history'; split; [exact Henv' |]. split; [exact Hhf |].
      split; [exact Hld |]. split; [exact Hpd |]. apply IHn.
      * exact (separated_protected_ok _ _ _ _ _ _ _ _ _ Henv').
      * exact (separated_local_free _ _ _ _ _ _ _ _ _ Henv').
      * eapply protocol_assertion_flush; eassumption.
      * eapply persistent_assertion_flushing_closed; eassumption.
Qed.
