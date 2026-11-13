From Stdlib Require Import List ZArith.
From WMLR Require Import Expressions Languages Machine BufferRelations OrderedBuffers Separation
  StableCompatibility RepairedSeparation GeneralizedFlushing FrameDecomposition ResidualUniqueness
  OperationalSemantics ProgramSteps Assertions AssertionSemantics ConcreteAssertions
  PersistentAssertions Safety RepairedSafety Specifications HeapRules LockRules OwnershipProtocol
  OwnershipHeap PrivateOwnership SpatialExchange TemporalSafety InvariantFragment
  OwnedSafety OwnedAdequacy OwnedResources.
Import ListNotations.

(** Fixed-frame reconstruction and semantic framing for the single owned
    safety predicate. FRAME-STM is deliberately absent. *)

Lemma resource_repaired_domain active (a b out : resource active) :
  repaired_spatiotemporal active (proj1_sig a) (proj1_sig b) (proj1_sig out) ->
  forall loc, memory_domain (resource_memory active out) loc <->
    memory_domain (resource_memory active a) loc \/ memory_domain (resource_memory active b) loc.
Proof. intros [H _]; exact (repaired_memory_domain _ _ _ _ H). Qed.

Lemma owned_mode_parts active mode (frame retained local big : resource active) :
  repaired_spatiotemporal active (proj1_sig retained) (proj1_sig local) (proj1_sig big) ->
  mode_compatible active mode frame big ->
  mode_compatible active mode frame retained /\ mode_compatible active mode frame local.
Proof.
  intros Hinner Hmode; destruct mode; [split; exact I |].
  split; intros loc HF HR; apply (Hmode loc HF), (resource_repaired_domain _ _ _ _ Hinner loc); auto.
Qed.

Lemma owned_environment_unframe active mode invariant s local retained big pool frame whole phase :
  repaired_spatiotemporal active (proj1_sig retained) (proj1_sig local) (proj1_sig big) ->
  mode_compatible active mode retained local ->
  owned_environment active mode invariant s big pool frame whole phase ->
  exists grouped : resource active,
    repaired_spatiotemporal active (proj1_sig frame) (proj1_sig retained) (proj1_sig grouped) /\
    owned_environment active mode invariant s local pool grouped whole phase.
Proof.
  intros Hinner HRP [Hp Hw [combined [Houter Hpool]] Hmode Hstatus].
  destruct (proj1 (repaired_resource_associative active frame retained local combined)
    (ex_intro _ big (conj Hinner Houter))) as (grouped & Hgroup & Hsmall).
  exists grouped; split; [exact Hgroup |]. constructor; try assumption.
  - exists combined; auto.
  - destruct mode; [exact I |].
    pose proof (proj2 (owned_mode_parts _ _ _ _ _ _ Hinner Hmode)) as HFP.
    intros loc HG HP; apply (resource_repaired_domain _ _ _ _ Hgroup loc) in HG.
    destruct HG as [HF |HR]; [exact (HFP loc HF HP) |exact (HRP loc HR HP)].
Qed.

Lemma owned_environment_reframe active mode invariant s local retained pool frame grouped whole phase :
  repaired_spatiotemporal active (proj1_sig frame) (proj1_sig retained) (proj1_sig grouped) ->
  mode_compatible active mode frame retained ->
  owned_environment active mode invariant s local pool grouped whole phase ->
  exists big : resource active,
    repaired_spatiotemporal active (proj1_sig retained) (proj1_sig local) (proj1_sig big) /\
    owned_environment active mode invariant s big pool frame whole phase.
Proof.
  intros Hgroup HFR [Hp Hw [combined [Hsmall Hpool]] Hmode Hstatus].
  destruct (proj2 (repaired_resource_associative active frame retained local combined)
    (ex_intro _ grouped (conj Hgroup Hsmall))) as (big & Hinner & Houter).
  exists big; split; [exact Hinner |]. constructor; try assumption.
  - exists combined; auto.
  - destruct mode; [exact I |]. intros loc HF HB.
    apply (resource_repaired_domain _ _ _ _ Hinner loc) in HB; destruct HB as [HR |HP].
    + exact (HFR loc HF HR).
    + apply (Hmode loc); [apply (resource_repaired_domain _ _ _ _ Hgroup loc); auto |exact HP].
Qed.

Lemma owned_update_frame active mode invariant s action phase phase' local pool local' pool'
    (retained big big' frame grouped : resource active) whole :
  repaired_spatiotemporal active (proj1_sig frame) (proj1_sig retained) (proj1_sig grouped) ->
  repaired_spatiotemporal active (proj1_sig retained) (proj1_sig local) (proj1_sig big) ->
  repaired_spatiotemporal active (proj1_sig retained) (proj1_sig local') (proj1_sig big') ->
  owned_environment active mode invariant s local pool grouped whole phase ->
  owned_update active action phase phase' local pool local' pool' ->
  owned_update active action phase phase' big pool big' pool'.
Proof.
  intros Hgroup Hinner Hinner' Henv [Htransfer Hdomain Hmarks].
  pose proof (proj2 (proj2 (proj2 (proj1 Hinner)))) as Hblocks.
  pose proof (proj2 (proj2 (proj2 (proj1 Hinner')))) as Hblocks'.
  assert (Hretainedfree :
    (phase = PoolFree \/ exists owner, phase = PoolHeld owner /\ lock_held active (resource_memory active local) owner) ->
    lock_free (resource_memory active retained)).
  { intros Hphase; assert (HG : lock_free (resource_memory active grouped)).
    { destruct Hphase as [-> |(owner & -> & Hheld)].
      - apply (proj2 (framed_free_externals _ _ _ _ _
          (owned_environment_as_framed _ _ _ _ _ _ _ _ _ Henv)
          (proj1 (owned_pool_status _ _ _ _ _ _ _ _ _ Henv)))).
      - apply (proj2 (framed_owned_lock_externals _ _ _ _ _ _
          (owned_environment_as_framed _ _ _ _ _ _ _ _ _ Henv) Hheld
          (proj1 (owned_pool_status _ _ _ _ _ _ _ _ _ Henv)))). }
    intros i HR; apply (HG i), (proj2 (proj2 (proj2 (proj1 Hgroup))) i); auto. }
  constructor.
  - destruct action as [|owner|owner|owner]; cbn [action_transfer] in *.
    + destruct Htransfer as [-> [-> Hsame]]; split; [reflexivity |].
      split; [reflexivity |intros i; rewrite Hblocks', Hblocks, Hsame; reflexivity].
    + destruct Htransfer as [-> [-> Hsame]]; split; [reflexivity |].
      split; [reflexivity |intros i; rewrite Hblocks', Hblocks, Hsame; reflexivity].
    + destruct Htransfer as [-> [-> [-> [Hi Hheld]]]].
      pose proof (Hretainedfree (or_introl eq_refl)) as HRfree.
      split; [reflexivity |]. split; [reflexivity |]. split; [reflexivity |].
      split; [exact Hi |]. intros i; rewrite Hblocks', Hheld.
      split; [intros [H |H]; [exfalso; exact (HRfree i H) |exact H] |auto].
    + destruct Htransfer as [-> [-> [Hheld Hfree]]].
      pose proof (Hretainedfree (or_intror (ex_intro _ owner (conj eq_refl Hheld)))) as HRfree.
      split; [reflexivity |]. split; [reflexivity |]. split.
      * destruct Hheld as [Hi Hheld]; split; [exact Hi |]. intros i; rewrite Hblocks, Hheld.
        split; [intros [H |H]; [exfalso; exact (HRfree i H) |exact H] |auto].
      * intros i H; apply Hblocks' in H; destruct H; [exact (HRfree i H) |exact (Hfree i H)].
  - intros loc [Hp |HB].
    + destruct (Hdomain loc (or_introl Hp)) as [Hp0 |HP]; [auto |right].
      apply (resource_repaired_domain _ _ _ _ Hinner loc); auto.
    + apply (resource_repaired_domain _ _ _ _ Hinner' loc) in HB; destruct HB as [HR |HP].
      * right; apply (resource_repaired_domain _ _ _ _ Hinner loc); auto.
      * destruct (Hdomain loc (or_intror HP)) as [Hp0 |HP0]; [auto |right].
        apply (resource_repaired_domain _ _ _ _ Hinner loc); auto.
  - intros i H; apply (proj2 Hinner' i) in H; destruct H as [HR |HP].
    + left; apply (proj2 Hinner i); auto.
    + destruct (Hmarks i HP) as [HP0 |Hearn]; [left; apply (proj2 Hinner i); auto |auto].
Qed.

Lemma owned_spatial_reconstruction active mode invariant s action phase phase' local pool local' pool'
    (retained big big' frame grouped : resource active) whole :
  repaired_spatiotemporal active (proj1_sig frame) (proj1_sig retained) (proj1_sig grouped) ->
  spatial (proj1_sig retained) (proj1_sig local) (proj1_sig big) ->
  repaired_spatiotemporal active (proj1_sig retained) (proj1_sig local') (proj1_sig big') ->
  owned_environment active mode invariant s local pool grouped whole phase ->
  owned_update active action phase phase' local pool local' pool' ->
  spatial (proj1_sig retained) (proj1_sig local') (proj1_sig big').
Proof.
  intros Hgroup Hinner [[Hstable Hmerge] Hmarks] Henv Hupdate.
  split; [|exact Hmarks]. split; [|exact (repaired_merge_interleaves _ _ _ _ (conj Hstable Hmerge))].
  split; [|exact (proj1 Hstable)]. intros loc HR HP.
  destruct (owned_footprint _ _ _ _ _ _ _ _ Hupdate loc (or_intror HP)) as [Hp |HP0].
  - destruct (owned_composition _ _ _ _ _ _ _ _ _ Henv)
      as (combined & Hsmall & [[Hpool _] _]).
    apply (Hpool loc Hp), (resource_repaired_domain _ _ _ _ Hsmall loc); left.
    apply (resource_repaired_domain _ _ _ _ Hgroup loc); auto.
  - exact (proj1 (proj1 (proj1 Hinner)) loc HR HP0).
Qed.

Theorem owned_safe_spatial_frame active mode invariant n command s local post retained big frame_assertion :
  owned_safe active mode invariant n command s local post ->
  frame_variable_condition command frame_assertion ->
  persistent_models active s retained frame_assertion ->
  spatial (proj1_sig retained) (proj1_sig local) (proj1_sig big) ->
  owned_safe active mode invariant n command s big (A.Spatial frame_assertion post).
Proof.
  revert command s local retained big; induction n;
    intros command s local retained big Hsafe Hvariables HR Hinner; [exact I |].
  intros later Hfuture.
  destruct (resource_spatial_future_split _ _ _ _ _ Hfuture Hinner)
    as (retained0 & local0 & HRfuture & HPfuture & Hinner0).
  assert (HR0 : persistent_models active s retained0 frame_assertion).
  { eapply persistent_assertion_flushing_closed; eassumption. }
  pose proof (owned_safe_future _ _ _ _ _ _ _ _ _ HPfuture Hsafe) as Hsafe0.
  pose proof (spatial_in_repaired active _ _ _ Hinner0) as Hrepair0.
  split.
  - intros Hdone; exists retained0, local0; split; [exact Hinner0 |].
    split; [exact HR0 |eapply owned_safe_terminal; eassumption].
  - intros pool frame whole phase Henv.
    assert (HRP : mode_compatible active mode retained0 local0).
    { destruct mode; [exact I |exact (proj1 (proj1 (proj1 Hinner0)))]. }
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
    pose proof (owned_spatial_reconstruction _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
      Hgroup Hinner0 Hrepair' Hsmall Hupdate) as Hinner'.
    exists big', pool', phase'; split; [exact Henv' |]. split.
    + exact (owned_update_frame _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
        Hgroup Hrepair0 Hrepair' Hsmall Hupdate).
    + eapply IHn; [exact Hsafe' | | |exact Hinner'].
      * intros x Hmod Hfv; apply (Hvariables x); [|exact Hfv].
        eapply step_modifies_subset; [exact (program_step_erases _ _ _ _ _ _ Hstep) |exact Hmod].
      * assert (Hagrees : agrees (A.fv frame_assertion) s t).
        { intros x Hfv; apply (step_preserves_unmodified _ _ _ _ _ (program_step_erases _ _ _ _ _ _ Hstep) x).
          intros Hmod; exact (Hvariables x Hmod Hfv). }
        apply (proj1 (future_satisfies_agrees _ _ frame_assertion s t Hagrees retained0)), HR0.
Qed.

Theorem owned_spatial_frame_valid active mode invariant pre command post frame_assertion :
  owned_valid active mode invariant pre command post ->
  frame_variable_condition command frame_assertion ->
  owned_valid active mode invariant (A.Spatial frame_assertion pre) command (A.Spatial frame_assertion post).
Proof.
  intros Hvalid Hvariables s big (retained & local & Hinner & HR & HP) n.
  eapply owned_safe_spatial_frame; [apply Hvalid, HP |exact Hvariables |exact HR |exact Hinner].
Qed.

Lemma program_step_buffer_shape active action command initial next final :
  program_step active action command initial next final ->
  (forall i, buffers (memory_state final) i = buffers (memory_state initial) i) \/
  (exists actor w, forall i, buffers (memory_state final) i =
    if Pos.eq_dec i actor then buffers (memory_state initial) i ++ [w]
    else buffers (memory_state initial) i).
Proof.
  induction 1; try assumption; try (left; intros i0; reflexivity).
  inversion H0; subst; try (left; intros i0; reflexivity).
  right; exists i, (loc, eval_expr s rhs); intros i0.
  cbn [memory_state enqueue buffers]; unfold buffer_update.
  destruct (Pos.eq_dec i0 i); subst; reflexivity.
Qed.

Lemma program_step_earns_empty active action command initial next final :
  program_step active action command initial next final ->
  forall i, action_earns action i -> buffers (memory_state initial) i = [].
Proof.
  induction 1; try assumption; try solve [intros i H; contradiction].
  inversion H0; subst; cbn [primitive_action action_earns];
    intros j Hmark; try contradiction; subst j; assumption.
Qed.

Lemma owned_environment_buffer_merge active mode invariant s local pool frame whole phase :
  invariant_fragment invariant ->
  owned_environment active mode invariant s local pool frame whole phase ->
  forall i, ordered_overrides (buffers (resource_memory active frame) i)
    (buffers (resource_memory active local) i) (buffers whole i).
Proof.
  intros Hfragment Henv i.
  pose proof (owned_pool_buffers_empty _ _ _ _ _ _ _ _ _ Hfragment Henv i) as Hempty.
  destruct (owned_composition _ _ _ _ _ _ _ _ _ Henv)
    as (combined & [[_ [_ [Hinner _]]] _] & [_ [_ [Houter _]]]).
  specialize (Houter i); rewrite Hempty in Houter.
  rewrite (interleaves_nil_left _ _ Houter); exact (Hinner i).
Qed.

(** Both cancellations use the same concrete machine change. The grouped
    frame need not be a temporal concatenation itself. *)
Lemma ordered_fixed_frame_prefix frame grouped retained local big local' big' whole whole' :
  ordered_overrides frame big whole -> ordered_overrides grouped local whole ->
  ordered_overrides frame big' whole' -> ordered_overrides grouped local' whole' ->
  big = retained ++ local ->
  (whole' = whole \/ exists w, whole' = whole ++ [w]) ->
  big' = retained ++ local'.
Proof.
  intros HF HG HF' HG' Ebig [Ewhole |[w Ewhole]]; subst whole'.
  - pose proof (ordered_residual_unique _ _ _ HF' _ HF) as Eb.
    pose proof (ordered_residual_unique _ _ _ HG' _ HG) as Ep.
    rewrite Eb, Ep; exact Ebig.
  - pose proof (ordered_residual_unique _ _ _ HF' _ (ordered_append_future _ _ _ w HF)) as Eb.
    pose proof (ordered_residual_unique _ _ _ HG' _ (ordered_append_future _ _ _ w HG)) as Ep.
    rewrite Eb, Ep, Ebig, app_assoc; reflexivity.
Qed.

Lemma owned_temporal_reconstruction active invariant s t action command next
    (local local' retained big big' frame grouped : resource active)
    pool pool' whole whole' phase phase' :
  invariant_fragment invariant ->
  repaired_temporal active (proj1_sig retained) (proj1_sig local) (proj1_sig big) ->
  repaired_spatiotemporal active (proj1_sig retained) (proj1_sig local') (proj1_sig big') ->
  owned_environment active OverlapMode invariant s big pool frame whole phase ->
  owned_environment active OverlapMode invariant t big' pool' frame whole' phase' ->
  owned_environment active OverlapMode invariant s local pool grouped whole phase ->
  owned_environment active OverlapMode invariant t local' pool' grouped whole' phase' ->
  owned_update active action phase phase' local pool local' pool' ->
  program_step active action command (State s whole) next (State t whole') ->
  repaired_temporal active (proj1_sig retained) (proj1_sig local') (proj1_sig big').
Proof.
  intros Hfragment Hinner [[Hstable [Hheap [Hordered Hblocks]]] Hmarks]
    Henv Henv' Hsmall Hsmall' Hupdate Hstep.
  pose proof (owned_environment_buffer_merge _ _ _ _ _ _ _ _ _ Hfragment Henv) as HF.
  pose proof (owned_environment_buffer_merge _ _ _ _ _ _ _ _ _ Hfragment Henv') as HF'.
  pose proof (owned_environment_buffer_merge _ _ _ _ _ _ _ _ _ Hfragment Hsmall) as HG.
  pose proof (owned_environment_buffer_merge _ _ _ _ _ _ _ _ _ Hfragment Hsmall') as HG'.
  destruct Hinner as [_ [[_ [_ [Hconcat _]]] [Hbefore _]]].
  split; [exact Hstable |]. split.
  - split; [apply stable_implies_original_compatible, Hstable |].
    split; [exact Hheap |]. split; [|exact Hblocks].
    intros i; apply (ordered_fixed_frame_prefix _ _ _ _ _ _ _ _ _ (HF i) (HG i) (HF' i) (HG' i) (Hconcat i)).
    destruct (program_step_buffer_shape _ _ _ _ _ _ Hstep) as [Hsame |(actor & w & Happend)].
    + left; exact (Hsame i).
    + specialize (Happend i); cbn [memory_state] in Happend.
      destruct (Pos.eq_dec i actor); [right; exists w |left]; exact Happend.
  - split; [|exact Hmarks]. intros i Hi.
    destruct (owned_mark_budget _ _ _ _ _ _ _ _ Hupdate i Hi) as [Hold |Hearn].
    + apply Hbefore, Hold.
    + pose proof (program_step_earns_empty _ _ _ _ _ _ Hstep i Hearn) as Hempty.
      cbn [memory_state] in Hempty.
      pose proof (ordered_interleaves _ _ _ (HF i)) as Hparts; rewrite Hempty in Hparts.
      assert (Hbigempty : buffers (resource_memory active big) i = []).
      { inversion Hparts; reflexivity. }
      rewrite Hconcat in Hbigempty; apply app_eq_nil in Hbigempty; exact (proj1 Hbigempty).
Qed.

Theorem owned_safe_temporal_frame active invariant n command s local post retained big frame_assertion :
  invariant_fragment invariant ->
  owned_safe active OverlapMode invariant n command s local post ->
  frame_variable_condition command frame_assertion ->
  persistent_models active s retained frame_assertion ->
  repaired_temporal active (proj1_sig retained) (proj1_sig local) (proj1_sig big) ->
  owned_safe active OverlapMode invariant n command s big (A.Temporal frame_assertion post).
Proof.
  intros Hfragment; revert command s local retained big; induction n;
    intros command s local retained big Hsafe Hvariables HR Hinner; [exact I |].
  intros later Hfuture.
  destruct (resource_temporal_future_split _ _ _ _ _ Hfuture Hinner)
    as (retained0 & local0 & HRfuture & HPfuture & Hinner0).
  assert (HR0 : persistent_models active s retained0 frame_assertion).
  { eapply persistent_assertion_flushing_closed; eassumption. }
  pose proof (owned_safe_future _ _ _ _ _ _ _ _ _ HPfuture Hsafe) as Hsafe0.
  pose proof (repaired_temporal_in_spatiotemporal active _ _ _ Hinner0) as Hrepair0.
  split.
  - intros Hdone; exists retained0, local0; split; [exact Hinner0 |].
    split; [exact HR0 |eapply owned_safe_terminal; eassumption].
  - intros pool frame whole phase Henv.
    destruct (owned_environment_unframe _ OverlapMode _ _ _ _ _ _ _ _ _ Hrepair0 I Henv)
      as (grouped & Hgroup & Hsmall).
    split; [eapply owned_safe_no_abort; eassumption |].
    intros action next t whole' Hstep.
    destruct (owned_safe_program_step _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hsafe0 Hsmall Hstep)
      as (local' & pool' & phase' & Hsmall' & Hupdate & Hsafe').
    destruct (owned_environment_reframe _ OverlapMode _ _ _ _ _ _ _ _ _ Hgroup I Hsmall')
      as (big' & Hrepair' & Henv').
    assert (Hinner' : repaired_temporal active (proj1_sig retained0) (proj1_sig local') (proj1_sig big')).
    { exact (owned_temporal_reconstruction _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
        Hfragment Hinner0 Hrepair' Henv Henv' Hsmall Hsmall' Hupdate Hstep). }
    exists big', pool', phase'; split; [exact Henv' |]. split.
    + exact (owned_update_frame _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
        Hgroup Hrepair0 Hrepair' Hsmall Hupdate).
    + eapply IHn; [exact Hsafe' | | |exact Hinner'].
      * intros x Hmod Hfv; apply (Hvariables x); [|exact Hfv].
        eapply step_modifies_subset; [exact (program_step_erases _ _ _ _ _ _ Hstep) |exact Hmod].
      * assert (Hagrees : agrees (A.fv frame_assertion) s t).
        { intros x Hfv; apply (step_preserves_unmodified _ _ _ _ _ (program_step_erases _ _ _ _ _ _ Hstep) x).
          intros Hmod; exact (Hvariables x Hmod Hfv). }
        apply (proj1 (future_satisfies_agrees _ _ frame_assertion s t Hagrees retained0)), HR0.
Qed.

Theorem owned_temporal_frame_valid active invariant pre command post frame_assertion :
  invariant_fragment invariant ->
  owned_valid active OverlapMode invariant pre command post ->
  frame_variable_condition command frame_assertion ->
  owned_valid active OverlapMode invariant (A.Temporal frame_assertion pre) command (A.Temporal frame_assertion post).
Proof.
  intros Hfragment Hvalid Hvariables s big (retained & local & Hinner & HR & HP) n.
  eapply owned_safe_temporal_frame; [exact Hfragment |apply Hvalid, HP |exact Hvariables |exact HR |exact Hinner].
Qed.
