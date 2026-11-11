From Stdlib Require Import List ZArith.
From WMLR Require Import Expressions Languages Machine BufferRelations Separation RepairedSeparation
  RepairedFlushing GeneralizedFlushing FrameDecomposition OperationalSemantics Assertions AssertionSemantics
  PersistentAssertions Safety RepairedSafety Specifications OwnershipProtocol TemporalSafety
  RegionalResources RegionalFraming SpatialExchange.
Import ListNotations.

(** Protected assertions and private assertions have separate interpretations.
    The protected compartment uses the existing ownership protocol, including
    its full-memory interpretation. Private resources retain their actual marks.
    Opening the invariant never combines these two assertion resources.

    In BOTH phases the machine is: (history ; private) * protected.
    Thus private histories are spatially disjoint from protected memory, even
    while the invariant is open. This is an explicit ownership discipline. *)
Record separated_environment active owner invariant phase s
    (local : resource active) protected (history : resource active) whole : Prop := {
  separated_protected_ok : protocol_region active owner invariant phase s protected;
  separated_local_free : lock_free (resource_memory active local);
  separated_history_free : lock_free (resource_memory active history);
  separated_composition : exists combined : resource active,
    repaired_temporal active (proj1_sig history) (proj1_sig local) (proj1_sig combined) /\
    memory_spatial (resource_memory active combined) protected whole
}.

Lemma temporal_free_union active (a b out : resource active) :
  repaired_temporal active (proj1_sig a) (proj1_sig b) (proj1_sig out) ->
  lock_free (resource_memory active a) -> lock_free (resource_memory active b) ->
  lock_free (resource_memory active out).
Proof.
  intros [_ [[_ [_ [_ Hblocks]]] _]] Ha Hb i H.
  apply Hblocks in H; destruct H; [apply (Ha i) |apply (Hb i)]; assumption.
Qed.

Lemma separated_protocol_environment active owner invariant phase s local protected history whole combined :
  separated_environment active owner invariant phase s local protected history whole ->
  repaired_temporal active (proj1_sig history) (proj1_sig local) (proj1_sig combined) ->
  memory_spatial (resource_memory active combined) protected whole ->
  protocol_environment active owner invariant phase s protected (resource_memory active combined) whole.
Proof.
  intros [Hregion Hlocal Hhistory _] Htm Hsp; constructor; try assumption.
  - exact (proj1 (proj2_sig combined)).
  - eapply raw_spatial_well_formed; [exact (proj1 (proj2_sig combined)) |exact (proj1 Hregion) |exact Hsp].
  - eapply temporal_free_union; eassumption.
Qed.

Lemma resource_actual_flushes active (r : resource active) m' :
  memory_flushes active (resource_memory active r) m' -> exists r' : resource active,
    resource_memory active r' = m' /\ resource_future active r r'.
Proof.
  intros H; remember (resource_memory active r) as m eqn:E.
  revert r E; induction H; intros r E; subst.
  - exists r; split; [reflexivity |constructor].
  - destruct (resource_actual_flush _ _ _ H) as (middle & Em & Hf).
    destruct (IHmemory_flushes middle (eq_sym Em)) as (last & El & Htail).
    exists last; split; [exact El |eapply generalized_future_trans; eassumption].
Qed.

Lemma separated_environment_flush active owner invariant phase s local protected history whole whole' :
  separated_environment active owner invariant phase s local protected history whole ->
  flush active whole whole' -> exists local' protected' history',
    separated_environment active owner invariant phase s local' protected' history' whole' /\
    resource_future active local local' /\ memory_flushes active protected protected' /\
    resource_future active history history' /\
    domain_included (resource_memory active local') (resource_memory active local) /\
    domain_included protected' protected.
Proof.
  intros Henv Hflush.
  destruct Henv as [Hp Hl Hh [combined [Htm Hsp]]].
  assert (Henv : separated_environment active owner invariant phase s local protected history whole).
  { constructor; try assumption; exists combined; auto. }
  pose proof (separated_protocol_environment _ _ _ _ _ _ _ _ _ _ Henv Htm Hsp) as Hprotocol.
  destruct (protocol_environment_flush _ _ _ _ _ _ _ _ _ Hprotocol Hflush)
    as (protected' & combined_memory & Hprotocol' & Hpf & Hcf & Hpd).
  destruct (resource_actual_flushes _ _ _ Hcf) as (combined' & Ec & Hfuture).
  destruct (resource_temporal_future_split _ _ _ _ _ Hfuture Htm)
    as (history' & local' & Hhf & Hlf & Htm').
  exists local', protected', history'; split.
  - constructor.
    + exact (protocol_region_ok _ _ _ _ _ _ _ _ Hprotocol').
    + intros i H; apply (Hl i), (resource_future_blocks _ _ _ Hlf i), H.
    + intros i H; apply (Hh i), (resource_future_blocks _ _ _ Hhf i), H.
    + exists combined'; split; [exact Htm' |rewrite Ec; exact (protocol_separation _ _ _ _ _ _ _ _ Hprotocol')].
  - split; [exact Hlf |]. split; [exact Hpf |]. split; [exact Hhf |]. split; [|exact Hpd].
    eapply flushes_domain_subset; apply generalized_future_memory_flushes, Hlf.
Qed.

Fixpoint separated_safe active owner invariant n command s phase
    (local : resource active) protected finish protected_post post : Prop :=
  match n with
  | O => True
  | S remaining =>
    protocol_region active owner invariant phase s protected /\
    lock_free (resource_memory active local) /\
    (terminal command -> phase = finish /\
      protocol_assertion active phase s protected protected_post /\ persistent_models active s local post) /\
    (forall history whole, separated_environment active owner invariant phase s local protected history whole ->
      ~ abort active command (State s whole)) /\
    (forall history whole next t whole',
      separated_environment active owner invariant phase s local protected history whole ->
      step active command (State s whole) next (State t whole') ->
      exists phase' local' protected' history',
        separated_environment active owner invariant phase' t local' protected' history' whole' /\
        resource_future active history history' /\
        domain_included (resource_memory active local') (resource_memory active local) /\
        domain_included protected' protected /\
        separated_safe active owner invariant remaining next t phase' local' protected' finish protected_post post)
  end.

Definition separated_valid active owner invariant start protected_pre pre command finish protected_post post :=
  forall s local protected, protocol_region active owner invariant start s protected ->
    lock_free (resource_memory active local) -> protocol_assertion active start s protected protected_pre ->
    persistent_models active s local pre -> forall n,
      separated_safe active owner invariant n command s start local protected finish protected_post post.

(** Closed judgments recover the original one-private-assertion interface. *)
Definition separated_closed_valid active owner invariant pre command post :=
  separated_valid active owner invariant Closed A.Emp pre command Closed A.Emp post.

Theorem separated_safe_temporal_frame active owner invariant n command s phase local protected finish protected_post post
    (retained biglocal : resource active) frame_assertion :
  separated_safe active owner invariant n command s phase local protected finish protected_post post ->
  frame_variable_condition command frame_assertion -> persistent_models active s retained frame_assertion ->
  lock_free (resource_memory active biglocal) ->
  repaired_temporal active (proj1_sig retained) (proj1_sig local) (proj1_sig biglocal) ->
  separated_safe active owner invariant n command s phase biglocal protected finish protected_post (A.Temporal frame_assertion post).
Proof.
  revert command s phase local protected retained biglocal.
  induction n; intros command s phase local protected retained biglocal Hsafe Hvariables HR Hbigfree Hinner; [exact I |].
  destruct Hsafe as [Hp [Hl [Hdone [Hnoabort Hprogress]]]].
  split; [exact Hp |]. split; [exact Hbigfree |]. split.
  - intros Hlast; destruct (Hdone Hlast) as [E [HS HQ]]; split; [exact E |]. split; [exact HS |].
    exists retained, local; auto.
  - split.
    + intros external whole [Hp0 Hl0 He [combined [Houter Hsp]]].
      destruct (proj1 (repaired_temporal_resource_associative active external retained local combined)
        (ex_intro _ biglocal (conj Hinner Houter))) as (history & Hhistory & Hsep).
      apply (Hnoabort history whole); constructor; try assumption.
      * eapply temporal_free_union; [exact Hhistory |exact He |].
        exact (proj1 (temporal_free_parts _ _ _ _ Hinner Hbigfree)).
      * exists combined; auto.
    + intros external whole next t whole' [Hp0 Hl0 He [combined [Houter Hsp]]] Hstep.
      destruct (proj1 (repaired_temporal_resource_associative active external retained local combined)
        (ex_intro _ biglocal (conj Hinner Houter))) as (history & Hhistory & Hsep).
      assert (Henv : separated_environment active owner invariant phase s local protected history whole).
      { constructor; try assumption.
        - eapply temporal_free_union; [exact Hhistory |exact He |].
          exact (proj1 (temporal_free_parts _ _ _ _ Hinner Hbigfree)).
        - exists combined; auto. }
      destruct (Hprogress _ _ _ _ _ Henv Hstep)
        as (phase' & local' & protected' & history' & Henv' & Hfuture & Hld & Hpd & Hsafe').
      destruct (resource_temporal_future_split _ _ _ _ _ Hfuture Hhistory)
        as (external' & retained' & Hef & Hrf & Hhistory').
      destruct Henv' as [Hp' Hl' Hh' [combined' [Hsep' Hsp']]].
      destruct (proj2 (repaired_temporal_resource_associative active external' retained' local' combined')
        (ex_intro _ history' (conj Hhistory' Hsep'))) as (biglocal' & Hinner' & Houter').
      assert (Hrfree : lock_free (resource_memory active retained')).
      { exact (proj2 (temporal_free_parts _ _ _ _ Hhistory' Hh')). }
      assert (Hbfree : lock_free (resource_memory active biglocal')).
      { eapply temporal_free_union; eassumption. }
      exists phase', biglocal', protected', external'. split.
      * constructor; try assumption.
        -- exact (proj1 (temporal_free_parts _ _ _ _ Hhistory' Hh')).
        -- exists combined'; auto.
      * split; [exact Hef |]. split.
        -- intros loc Hloc; apply (temporal_memory_domain _ _ _ _ Hinner') in Hloc.
           apply (temporal_memory_domain _ _ _ _ Hinner).
           destruct Hloc as [Hret |Hloc]; [left |right; apply Hld, Hloc].
           eapply flushes_domain_subset; [apply generalized_future_memory_flushes; exact Hrf |exact Hret].
        -- split; [exact Hpd |]. eapply IHn; [exact Hsafe' | | |exact Hbfree |exact Hinner'].
           ++ intros x Hwrite Hx; apply (Hvariables x); [eapply step_modifies_subset; eassumption |exact Hx].
           ++ assert (Hagrees : agrees (A.fv frame_assertion) s t).
              { intros x Hx; apply (step_preserves_unmodified _ _ _ _ _ Hstep x).
                intros Hwrite; exact (Hvariables x Hwrite Hx). }
              apply (proj1 (future_satisfies_agrees _ _ _ _ _ Hagrees retained')).
              eapply persistent_assertion_flushing_closed; eassumption.
Qed.

Theorem separated_temporal_frame_valid active owner invariant start protected_pre pre command finish protected_post post frame :
  separated_valid active owner invariant start protected_pre pre command finish protected_post post ->
  frame_variable_condition command frame ->
  separated_valid active owner invariant start protected_pre (A.Temporal frame pre) command finish
    protected_post (A.Temporal frame post).
Proof.
  intros Hvalid Hvariables s biglocal protected Hp Hfree HS (retained & local & Htm & HR & HP) n.
  eapply separated_safe_temporal_frame; [|exact Hvariables |exact HR |exact Hfree |exact Htm].
  apply Hvalid; try assumption; exact (proj2 (temporal_free_parts _ _ _ _ Htm Hfree)).
Qed.

Corollary separated_FRAME_TM active owner invariant pre command post frame :
  separated_closed_valid active owner invariant pre command post -> frame_variable_condition command frame ->
  separated_closed_valid active owner invariant (A.Temporal frame pre) command (A.Temporal frame post).
Proof. apply separated_temporal_frame_valid. Qed.

Theorem separated_execution_residual active owner invariant n command s whole last t final :
  execution active n command s whole last t final -> forall phase local protected history finish protected_post post,
  separated_safe active owner invariant (S n) command s phase local protected finish protected_post post ->
  separated_environment active owner invariant phase s local protected history whole ->
  exists phase' local' protected' history', separated_environment active owner invariant phase' t local' protected' history' final /\
    resource_future active history history' /\
    separated_safe active owner invariant 1 last t phase' local' protected' finish protected_post post.
Proof.
  induction 1; intros phase local protected history finish protected_post post Hsafe Henv.
  - exists phase, local, protected, history; split; [exact Henv |]. split; [constructor |exact Hsafe].
  - destruct Hsafe as [_ [_ [_ [_ Hprogress]]]].
    destruct (Hprogress _ _ _ _ _ Henv H) as (phase' & local' & protected' & history' & Henv' & Hhf & _ & _ & Hsafe').
    destruct (IHexecution _ _ _ _ _ _ _ Hsafe' Henv') as (phase'' & local'' & protected'' & history'' & Henv'' & Hhf' & Hsafe'').
    exists phase'', local'', protected'', history''; split; [exact Henv'' |]. split; [|exact Hsafe''].
    eapply generalized_future_trans; eassumption.
Qed.

Theorem separated_execution_no_abort active owner invariant n command s whole last t final phase local protected history finish protected_post post :
  execution active n command s whole last t final ->
  separated_safe active owner invariant (S n) command s phase local protected finish protected_post post ->
  separated_environment active owner invariant phase s local protected history whole -> ~ abort active last (State t final).
Proof.
  intros Hrun Hsafe Henv; destruct (separated_execution_residual _ _ _ _ _ _ _ _ _ _ Hrun _ _ _ _ _ _ _ Hsafe Henv)
    as (phase' & local' & protected' & history' & Henv' & _ & _ & _ & _ & Hnoabort & _).
  exact (Hnoabort _ _ Henv').
Qed.

Theorem separated_execution_post active owner invariant n command s whole last t final phase local protected history finish protected_post post :
  execution active n command s whole last t final ->
  separated_safe active owner invariant (S n) command s phase local protected finish protected_post post ->
  separated_environment active owner invariant phase s local protected history whole -> terminal last ->
  exists local' protected' history', separated_environment active owner invariant finish t local' protected' history' final /\
    resource_future active history history' /\ protocol_assertion active finish t protected' protected_post /\
    persistent_models active t local' post.
Proof.
  intros Hrun Hsafe Henv Hlast; destruct (separated_execution_residual _ _ _ _ _ _ _ _ _ _ Hrun _ _ _ _ _ _ _ Hsafe Henv)
    as (phase' & local' & protected' & history' & Henv' & Hhf & _ & _ & Hdone & _).
  destruct (Hdone Hlast) as [-> [HS HQ]]; exists local', protected', history'; auto.
Qed.
