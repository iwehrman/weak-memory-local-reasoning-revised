From Stdlib Require Import List ZArith.
From WMLR Require Import Expressions Languages Machine BufferRelations Separation
  FrameDecomposition OperationalSemantics Assertions AssertionSemantics PersistentAssertions
  Safety RepairedSafety Specifications OwnershipProtocol OwnershipRules TemporalSafety SpatialExchange RetiredHeaps.
Import ListNotations.

(** A deliberately separate buffer-free test of retirement. Actual machine
    transitions are unchanged. Every admissible environment has empty buffers;
    arbitrary overlapping HEAP histories are allowed and retained exactly.
    No spatial-frame or parallel rule is claimed for this experiment. *)
Record retired_environment active owner invariant phase s local protected history whole : Prop := {
  retired_region_ok : protocol_region active owner invariant phase s protected;
  retired_pool_flushed : forall i, buffers protected i = [];
  retired_composition : exists combined,
    RH.temporal history local combined /\ memory_spatial (RH.project combined) protected whole
}.

Lemma retired_whole_flushed active owner invariant phase s local protected history whole :
  retired_environment active owner invariant phase s local protected history whole ->
  forall i, buffers whole i = [].
Proof.
  intros [_ Hb [combined [_ [_ [_ [Hmerge _]]]]]] i.
  specialize (Hmerge i); cbn [RH.project buffers empty_buffers] in Hmerge.
  rewrite Hb in Hmerge; apply interleaves_nil_left in Hmerge; exact Hmerge.
Qed.

Lemma retired_no_flush active owner invariant phase s local protected history whole whole' :
  retired_environment active owner invariant phase s local protected history whole -> ~ flush active whole whole'.
Proof.
  intros Henv Hflush; inversion Hflush; subst.
  match goal with H : buffers whole ?i = _ |- _ =>
    rewrite (retired_whole_flushed _ _ _ _ _ _ _ _ _ Henv i) in H; discriminate end.
Qed.

Lemma retired_environment_protocol active owner invariant phase s local protected history whole combined :
  retired_environment active owner invariant phase s local protected history whole ->
  RH.temporal history local combined -> memory_spatial (RH.project combined) protected whole ->
  protocol_environment active owner invariant phase s protected (RH.project combined) whole.
Proof.
  intros [Hp Hb _] Htm Hsp; constructor; try assumption.
  - split; [intros i H; contradiction |intros i H; reflexivity].
  - eapply raw_spatial_well_formed; [|exact (proj1 Hp) |exact Hsp].
    split; [intros i H; contradiction |intros i H; reflexivity].
  - intros i H; contradiction.
Qed.

Theorem retired_pool_excludes_private_cell active owner invariant phase s local protected history whole loc v :
  retired_environment active owner invariant phase s local protected history whole ->
  shared_heap protected loc = Some v -> RH.live_heap local loc = None.
Proof.
  intros [_ _ [combined [Htm [[Hd _] _]]]] Hpool.
  destruct (RH.live_heap local loc) as [w|] eqn:E; [|reflexivity].
  exfalso; apply (Hd loc); left.
  - exists w; eapply RH.temporal_live_right; eassumption.
  - exists v; exact Hpool.
Qed.

Fixpoint retired_safe active owner invariant n command s phase local protected finish protected_post post : Prop :=
  match n with
  | O => True
  | S remaining =>
    protocol_region active owner invariant phase s protected /\
    (forall i, buffers protected i = []) /\
    (terminal command -> phase = finish /\ protocol_assertion active phase s protected protected_post /\
      RH.models active s local post) /\
    (forall history whole, retired_environment active owner invariant phase s local protected history whole ->
      ~ abort active command (State s whole)) /\
    (forall history whole next t whole',
      retired_environment active owner invariant phase s local protected history whole ->
      step active command (State s whole) next (State t whole') ->
      exists phase' local' protected',
        retired_environment active owner invariant phase' t local' protected' history whole' /\
        retired_safe active owner invariant remaining next t phase' local' protected' finish protected_post post)
  end.

Definition retired_valid active owner invariant start protected_pre pre command finish protected_post post :=
  forall s local protected, protocol_region active owner invariant start s protected ->
    (forall i, buffers protected i = []) -> protocol_assertion active start s protected protected_pre ->
    RH.models active s local pre -> forall n,
      retired_safe active owner invariant n command s start local protected finish protected_post post.

Theorem retired_safe_temporal_frame active owner invariant n command s phase local protected finish protected_post post
    retained biglocal frame :
  retired_safe active owner invariant n command s phase local protected finish protected_post post ->
  frame_variable_condition command frame -> RH.models active s retained frame ->
  RH.temporal retained local biglocal ->
  retired_safe active owner invariant n command s phase biglocal protected finish protected_post (A.Temporal frame post).
Proof.
  revert command s phase local protected retained biglocal.
  induction n; intros command s phase local protected retained biglocal Hsafe Hvariables HR Hinner; [exact I |].
  destruct Hsafe as [Hp [Hb [Hdone [Habort Hprogress]]]].
  split; [exact Hp |]. split; [exact Hb |]. split.
  - intros Hlast; destruct (Hdone Hlast) as [E [HS HQ]]; split; [exact E |]. split; [exact HS |].
    exists retained, local; auto.
  - split.
    + intros external whole [Hp0 Hb0 [combined [Houter Hsp]]].
      destruct (proj2 (RH.temporal_associative external retained local combined)
        (ex_intro _ biglocal (conj Hinner Houter))) as (history & Hhistory & Hsep).
      apply (Habort history whole); constructor; try assumption; exists combined; auto.
    + intros external whole next t whole' [Hp0 Hb0 [combined [Houter Hsp]]] Hstep.
      destruct (proj2 (RH.temporal_associative external retained local combined)
        (ex_intro _ biglocal (conj Hinner Houter))) as (history & Hhistory & Hsep).
      assert (Henv : retired_environment active owner invariant phase s local protected history whole).
      { constructor; try assumption; exists combined; auto. }
      destruct (Hprogress _ _ _ _ _ Henv Hstep) as (phase' & local' & protected' & Henv' & Hsafe').
      destruct Henv' as [Hp' Hb' [combined' [Hsep' Hsp']]].
      destruct (proj1 (RH.temporal_associative external retained local' combined')
        (ex_intro _ history (conj Hhistory Hsep'))) as (biglocal' & Hinner' & Houter').
      exists phase', biglocal', protected'; split.
      * constructor; try assumption; exists combined'; auto.
      * eapply IHn; [exact Hsafe' | | |exact Hinner'].
        -- intros x Hwrite Hx; apply (Hvariables x); [eapply step_modifies_subset; eassumption |exact Hx].
        -- assert (Hagrees : agrees (A.fv frame) s t).
           { intros x Hx; apply (step_preserves_unmodified _ _ _ _ _ Hstep x).
             intros Hwrite; exact (Hvariables x Hwrite Hx). }
           apply (proj1 (satisfies_agrees (RH.interpretation active) frame s t Hagrees retained)), HR.
Qed.

(** Printed variable condition, for every assertion including wands. The
    limitation is the resource universe (no pending buffers), not the frame. *)
Theorem retired_FRAME_TM active owner invariant start protected_pre pre command finish protected_post post frame :
  retired_valid active owner invariant start protected_pre pre command finish protected_post post ->
  frame_variable_condition command frame ->
  retired_valid active owner invariant start protected_pre (A.Temporal frame pre) command finish
    protected_post (A.Temporal frame post).
Proof.
  intros Hvalid Hvariables s biglocal protected Hp Hb HS (retained & local & Htm & HR & HP) n.
  eapply retired_safe_temporal_frame; [apply Hvalid; eassumption |exact Hvariables |exact HR |exact Htm].
Qed.

Lemma retired_skip_safe active owner invariant n annotation s phase local protected protected_post post :
  protocol_region active owner invariant phase s protected -> (forall i, buffers protected i = []) ->
  protocol_assertion active phase s protected protected_post -> RH.models active s local post ->
  retired_safe active owner invariant n (Concurrent.skip annotation) s phase local protected phase protected_post post.
Proof.
  intros Hp Hb HS HQ; destruct n; [exact I |]. split; [exact Hp |]. split; [exact Hb |].
  split; [intros _; auto |]. split; [intros; apply skip_no_abort |].
  intros history whole next t whole' Henv Hstep.
  destruct (skip_step_flush _ _ _ _ _ _ _ Hstep) as [-> [-> Hflush]].
  exfalso; eapply retired_no_flush; eassumption.
Qed.

Lemma retired_primitive_rule active owner invariant start protected_pre pre primitive annotation finish protected_post post :
  primitive <> Concurrent.Common Sequential.Skip ->
  (forall s local protected history whole,
    retired_environment active owner invariant start s local protected history whole ->
    protocol_assertion active start s protected protected_pre -> RH.models active s local pre -> forall i,
    eval_expr s annotation = Z.pos i -> ~ primitive_abort active primitive i (State s whole)) ->
  (forall s local protected history whole,
    retired_environment active owner invariant start s local protected history whole ->
    protocol_assertion active start s protected protected_pre -> RH.models active s local pre -> forall i t whole',
    eval_expr s annotation = Z.pos i -> primitive_step active primitive i (State s whole) (State t whole') ->
    exists local' protected', retired_environment active owner invariant finish t local' protected' history whole' /\
      protocol_assertion active finish t protected' protected_post /\ RH.models active t local' post) ->
  retired_valid active owner invariant start protected_pre pre (Concurrent.Prim primitive annotation) finish protected_post post.
Proof.
  intros Hnot Hfault Haction s local protected Hr Hb HS HP n; destruct n; [exact I |].
  split; [exact Hr |]. split; [exact Hb |]. split.
  - intros [ann E]; inversion E; contradiction.
  - split.
    + intros history whole Henv Habort; inversion Habort; subst; eapply Hfault; eassumption.
    + intros history whole next t whole' Henv Hstep; inversion Hstep; subst.
      * match goal with H : primitive_step _ _ _ _ _ |- _ =>
          destruct (Haction _ _ _ _ _ Henv HS HP _ _ _ ltac:(eassumption) H)
            as (local' & protected' & Henv' & HS' & HQ) end.
        exists finish, local', protected'; split; [exact Henv' |].
        apply retired_skip_safe; [exact (retired_region_ok _ _ _ _ _ _ _ _ _ Henv') |
          exact (retired_pool_flushed _ _ _ _ _ _ _ _ _ Henv') |exact HS' |exact HQ].
      * exfalso; eapply retired_no_flush; eassumption.
Qed.

Theorem retired_execution_residual active owner invariant n command s whole last t final :
  execution active n command s whole last t final -> forall phase local protected history finish protected_post post,
  retired_safe active owner invariant (S n) command s phase local protected finish protected_post post ->
  retired_environment active owner invariant phase s local protected history whole ->
  exists phase' local' protected', retired_environment active owner invariant phase' t local' protected' history final /\
    retired_safe active owner invariant 1 last t phase' local' protected' finish protected_post post.
Proof.
  induction 1; intros phase local protected history finish protected_post post Hsafe Henv.
  - exists phase, local, protected; auto.
  - destruct Hsafe as [_ [_ [_ [_ Hprogress]]]].
    destruct (Hprogress _ _ _ _ _ Henv H) as (phase' & local' & protected' & Henv' & Hsafe').
    exact (IHexecution _ _ _ _ _ _ _ Hsafe' Henv').
Qed.

Theorem retired_execution_no_abort active owner invariant n command s whole last t final phase local protected history finish protected_post post :
  execution active n command s whole last t final ->
  retired_safe active owner invariant (S n) command s phase local protected finish protected_post post ->
  retired_environment active owner invariant phase s local protected history whole -> ~ abort active last (State t final).
Proof.
  intros Hrun Hsafe Henv; destruct (retired_execution_residual _ _ _ _ _ _ _ _ _ _ Hrun _ _ _ _ _ _ _ Hsafe Henv)
    as (phase' & local' & protected' & Henv' & _ & _ & _ & Hnoabort & _).
  exact (Hnoabort _ _ Henv').
Qed.

Theorem retired_execution_post active owner invariant n command s whole last t final phase local protected history finish protected_post post :
  execution active n command s whole last t final ->
  retired_safe active owner invariant (S n) command s phase local protected finish protected_post post ->
  retired_environment active owner invariant phase s local protected history whole -> terminal last ->
  exists local' protected', retired_environment active owner invariant finish t local' protected' history final /\
    protocol_assertion active finish t protected' protected_post /\ RH.models active t local' post.
Proof.
  intros Hrun Hsafe Henv Hlast; destruct (retired_execution_residual _ _ _ _ _ _ _ _ _ _ Hrun _ _ _ _ _ _ _ Hsafe Henv)
    as (phase' & local' & protected' & Henv' & _ & _ & Hdone & _).
  destruct (Hdone Hlast) as [-> [HS HQ]]; exists local', protected'; auto.
Qed.
