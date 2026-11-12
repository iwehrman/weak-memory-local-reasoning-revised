From Stdlib Require Import List ZArith.
From WMLR Require Import Expressions Languages Machine BufferRelations Separation RepairedSeparation
  StableCompatibility RepairedFlushing GeneralizedFlushing FrameDecomposition OperationalSemantics ProgramSteps
  Assertions AssertionSemantics PersistentAssertions AssertionResourceEquivalence OwnershipProtocol PrivateOwnership SpatialExchange
  TemporalSafety InvariantFragment OwnedSafety OwnedAdequacy OwnedResources OwnedShareResources.
Import ListNotations.

(** Only the proof's source environment is projected. The target frame is
    retained exactly across each action, as required by owned_safe. *)
Definition share_cut_heap (frame pool : memory) : memory :=
  Memory (fun loc => match shared_heap pool loc with Some _ => None |None => shared_heap frame loc end)
    (buffers frame) (blocked frame).

Definition share_cut_resource active (frame retained : resource active) : resource active.
Proof.
  refine (exist _ (Generalized (share_cut_heap (resource_memory active frame)
    (resource_memory active retained)) (complete (proj1_sig frame))) _).
  destruct (proj2_sig frame) as [Hwf [Hactive Hheap]]; split; [exact Hwf |].
  split; [exact Hactive |]. intros Hnone loc; cbn [underlying share_cut_heap shared_heap].
  destruct (shared_heap (resource_memory active retained) loc); [reflexivity |apply Hheap,Hnone].
Defined.

Lemma share_cut_preserves_composition active frame retained local big whole :
  memory_spatial retained local big -> memory_repaired active frame big whole ->
  memory_repaired active (share_cut_heap frame retained) big whole.
Proof.
  intros [_ [Ej _]] [Hstable [Ewhole [Bwhole Kwhole]]]; split; [exact Hstable |].
  split; [|split; assumption]. intros loc; rewrite Ewhole.
  unfold heap_override; cbn [underlying share_cut_heap shared_heap].
  destruct (shared_heap retained loc) eqn:Er; [|reflexivity].
  rewrite Ej; unfold heap_override; rewrite Er; destruct (shared_heap local loc); reflexivity.
Qed.

Lemma share_cut_spatial_compatible active frame retained local big whole :
  memory_well_formed active frame ->
  (forall i, buffers retained i = []) -> lock_free retained ->
  memory_spatial retained local big -> memory_repaired active frame big whole ->
  spatial_compatible (share_cut_heap frame retained) retained.
Proof.
  intros Hwf Hb Hk Hsp [Hstable Hmerge]; split; [|intros i _ H; exact (Hk i H)].
  intros loc Hcut Hr; destruct Hr as [[v Hv] |[i [v Hv]]];
    [|rewrite Hb in Hv; contradiction].
  destruct Hcut as [[w Hw] |[i [w Hw]]].
  - cbn [share_cut_heap shared_heap] in Hw; rewrite Hv in Hw; discriminate.
  - assert (Hnot : ~ active i).
    { intros Hi; apply (proj1 (proj2 Hstable) i Hi loc); [exists w; exact Hw |].
      destruct Hsp as [_ [Ej _]]; unfold heap_domain; rewrite Ej.
      apply heap_override_domain; left; exists v; exact Hv. }
    change (In (loc,w) (buffers frame i)) in Hw.
    rewrite (proj2 Hwf i Hnot) in Hw; contradiction.
Qed.

Lemma repaired_spatial_parts active a b out pool :
  memory_repaired active a b out -> spatial_compatible pool out ->
  spatial_compatible pool a /\ spatial_compatible pool b.
Proof.
  intros Hmerge Hcompat; apply (proj1 (compatible_merge_right _ _ _ _
    (repaired_merge_interleaves active _ _ _ Hmerge))),Hcompat.
Qed.

Lemma share_pool_reassociate active pool frame local combined whole :
  memory_repaired active frame local combined -> memory_spatial pool combined whole ->
  exists big, memory_spatial pool local big /\ memory_repaired active frame big whole.
Proof.
  intros Hinner Houter.
  destruct (repaired_spatial_parts _ _ _ _ _ Hinner (proj1 Houter)) as [HPF HPL].
  destruct (proj1 (memory_repaired_associative active pool frame local whole)
    (ex_intro _ combined (conj Hinner (memory_spatial_in_repaired active _ _ _ Houter))))
    as (middle & Hfirst & Hlast).
  assert (Hcomm : memory_spatial frame pool middle).
  { apply memory_spatial_comm; split; [exact HPF |exact (repaired_merge_interleaves active _ _ _ Hfirst)]. }
  destruct (proj2 (memory_repaired_associative active frame pool local whole)
    (ex_intro _ middle (conj (memory_spatial_in_repaired active _ _ _ Hcomm) Hlast)))
    as (big & Hpool & Hframe).
  exists big; split; [split; [exact HPL |exact (repaired_merge_interleaves active _ _ _ Hpool)] |exact Hframe].
Qed.

Lemma share_cut_unpool_memory active frame retained local big whole :
  memory_well_formed active frame ->
  (forall i, buffers retained i = []) -> lock_free retained ->
  memory_spatial retained local big -> memory_repaired active frame big whole ->
  exists combined,
    memory_repaired active (share_cut_heap frame retained) local combined /\
    memory_spatial retained combined whole.
Proof.
  intros Hwf Hb Hk Hinner Houter.
  pose proof (share_cut_preserves_composition _ _ _ _ _ _ Hinner Houter) as Hcut.
  pose proof (share_cut_spatial_compatible _ _ _ _ _ _ Hwf Hb Hk Hinner Houter) as Hcompatible.
  destruct (proj1 (memory_repaired_associative active (share_cut_heap frame retained) retained local whole)
    (ex_intro _ big (conj (memory_spatial_in_repaired active _ _ _ Hinner) Hcut)))
    as (middle & Hfirst & Hlast).
  assert (Hcomm : memory_spatial retained (share_cut_heap frame retained) middle).
  { apply memory_spatial_comm; split; [exact Hcompatible |exact (repaired_merge_interleaves active _ _ _ Hfirst)]. }
  destruct (proj2 (memory_repaired_associative active retained (share_cut_heap frame retained) local whole)
    (ex_intro _ middle (conj (memory_spatial_in_repaired active _ _ _ Hcomm) Hlast)))
    as (combined & Hsmall & Hpool).
  exists combined; split; [exact Hsmall |]. split.
  - apply (proj2 (compatible_merge_right _ _ _ _ (repaired_merge_interleaves active _ _ _ Hsmall))).
    split; [exact (proj1 Hcomm) |exact (proj1 Hinner)].
  - exact (repaired_merge_interleaves active _ _ _ Hpool).
Qed.

(** Restoring a projected heap entry is harmless when the right-hand
    resource still overrides it. Buffers and blocked bits never changed. *)
Lemma share_cut_restore_composition active frame retained local whole :
  (forall loc v, shared_heap retained loc = Some v -> exists w, shared_heap local loc = Some w) ->
  memory_repaired active (share_cut_heap frame retained) local whole ->
  memory_repaired active frame local whole.
Proof.
  intros Hcover [Hstable [Hheap [Hbuffer Hblocks]]]; split; [exact Hstable |].
  split; [|split; assumption]. intros loc; rewrite Hheap; unfold heap_override.
  cbn [share_cut_heap shared_heap]. destruct (shared_heap retained loc) as [v|] eqn:Er; [|reflexivity].
  destruct (Hcover loc v Er) as [w Hw]; rewrite Hw; reflexivity.
Qed.

Definition repaired_output_resource active (a b : resource active) m
    (Hmerge : memory_repaired active (resource_memory active a) (resource_memory active b) m) : resource active.
Proof.
  refine (exist _ (Generalized m (fun i => complete (proj1_sig a) i \/ complete (proj1_sig b) i)) _).
  eapply repaired_well_formed; [exact (proj2_sig a) |exact (proj2_sig b) |].
  split; [exact Hmerge |intros i; reflexivity].
Defined.

Lemma repaired_pool_environment active invariant s local pool frame whole phase :
  memory_well_formed active pool ->
  (exists combined, memory_repaired active (resource_memory active frame) (resource_memory active local) combined /\
    memory_spatial pool combined whole) ->
  pool_status active invariant s pool whole phase ->
  owned_environment active OverlapMode invariant s local pool frame whole phase.
Proof.
  intros Hpool (combined & Hinner & Houter) Hstatus.
  pose (r := repaired_output_resource active frame local combined Hinner).
  constructor.
  - exact Hpool.
  - eapply raw_spatial_well_formed; [exact Hpool |exact (proj1 (proj2_sig r)) |exact Houter].
  - exists r; split; [split; [exact Hinner |intros i; reflexivity] |exact Houter].
  - exact I.
  - exact Hstatus.
Qed.

Lemma owned_emp_environment_repaired active mode s local pool frame whole phase :
  owned_environment active mode A.Emp s local pool frame whole phase ->
  memory_repaired active (resource_memory active frame) (resource_memory active local) whole.
Proof.
  intros Henv; destruct (owned_emp_pool_shape _ _ _ _ _ _ _ _ Henv) as [Hh [Hb Hk]].
  destruct (owned_composition _ _ _ _ _ _ _ _ _ Henv) as (combined & [[Hstable Hmerge] Hmarks] & Houter).
  pose proof (empty_memory_spatial_remove _ _ _ Hh Hb Hk Houter) as E.
  split; [exact Hstable |]. eapply assertion_merge_equiv;
    [apply assertion_memory_equiv_refl |apply assertion_memory_equiv_refl |apply assertion_memory_equiv_sym,E |exact Hmerge].
Qed.

Lemma owned_emp_overlap_intro active s local pool frame whole phase :
  memory_well_formed active pool ->
  (forall loc, shared_heap pool loc = None) -> (forall i, buffers pool i = []) ->
  lock_free pool ->
  memory_repaired active (resource_memory active frame) (resource_memory active local) whole ->
  pool_status active A.Emp s pool whole phase ->
  owned_environment active OverlapMode A.Emp s local pool frame whole phase.
Proof.
  intros Hwf Hh Hb Hk Hsp Hstatus; apply repaired_pool_environment; [exact Hwf | |exact Hstatus].
  exists whole; split; [exact Hsp |apply empty_pool_spatial_intro; assumption].
Qed.

Lemma owned_share_overlap_unpool active invariant s (local retained big frame : resource active) whole :
  invariant_fragment invariant -> (exists i, active i) ->
  persistent_models active s retained invariant ->
  spatial (proj1_sig retained) (proj1_sig local) (proj1_sig big) ->
  memory_repaired active (resource_memory active frame) (resource_memory active big) whole ->
  lock_free whole ->
  owned_environment active OverlapMode invariant s local (resource_memory active retained)
    (share_cut_resource active frame retained) whole PoolFree.
Proof.
  intros Hfragment [owner Hi] HJ Hinner Houter Hfree.
  destruct (invariant_fragment_shape _ Hfragment _ _ _ HJ) as [Hb Hk].
  destruct (share_cut_unpool_memory _ _ _ _ _ _ (proj1 (proj2_sig frame)) Hb Hk (proj1 Hinner) Houter)
    as (combined & Hsmall & Hpool).
  apply repaired_pool_environment; [exact (proj1 (proj2_sig retained)) |eauto |].
  split; [exact Hfree |]. eapply invariant_return_full_completeness; eassumption.
Qed.

Lemma owned_share_overlap_repool active invariant s local pool frame whole :
  owned_environment active OverlapMode invariant s local pool frame whole PoolFree ->
  forall retained : resource active, resource_memory active retained = pool ->
  exists big : resource active,
    spatial (proj1_sig retained) (proj1_sig local) (proj1_sig big) /\
    memory_repaired active (resource_memory active frame) (resource_memory active big) whole.
Proof.
  intros Henv retained Epool.
  destruct (owned_composition _ _ _ _ _ _ _ _ _ Henv) as (combined & [Hinner Hmarks] & Houter).
  destruct (share_pool_reassociate _ _ _ _ _ _ Hinner Houter) as (out & Hpo & Hfo).
  rewrite <- Epool in Hpo.
  exists (spatial_output_resource active retained local out Hpo); split;
    [apply spatial_output_split |exact Hfo].
Qed.

Lemma spatial_left_heap_cover retained local big :
  memory_spatial retained local big ->
  forall loc v, shared_heap retained loc = Some v -> exists w, shared_heap big loc = Some w.
Proof.
  intros [_ [Hheap _]] loc v H; rewrite Hheap; unfold heap_override; rewrite H.
  destruct (shared_heap local loc); eexists; reflexivity.
Qed.

Lemma program_step_shared_heap active action command initial next final :
  program_step active action command initial next final ->
  forall loc, shared_heap (memory_state final) loc = shared_heap (memory_state initial) loc.
Proof.
  induction 1; try assumption; try (intros; reflexivity).
  inversion H0; subst; intros; reflexivity.
Qed.

Lemma share_cut_after_acquire_cover active action command next s t frame retained local big whole local' whole' :
  memory_spatial retained local big -> memory_repaired active frame big whole ->
  program_step active action command (State s whole) next (State t whole') ->
  memory_repaired active (share_cut_heap frame retained) local' whole' ->
  forall loc v, shared_heap retained loc = Some v -> exists w, shared_heap local' loc = Some w.
Proof.
  intros Hsp [_ [Hbefore _]] Hstep [_ [Hafter _]] loc v H.
  destruct (spatial_left_heap_cover _ _ _ Hsp loc v H) as [w Hw].
  pose proof (program_step_shared_heap _ _ _ _ _ _ Hstep loc) as E.
  cbn [memory_state] in E; rewrite Hafter,Hbefore in E; unfold heap_override in E.
  cbn [share_cut_heap shared_heap] in E; rewrite H,Hw in E.
  destruct (shared_heap local' loc) as [u|] eqn:Eu; [eauto |discriminate].
Qed.

Lemma owned_restore_cut_environment active s local pool frame retained whole phase :
  (forall loc v, shared_heap (resource_memory active retained) loc = Some v ->
    exists w, shared_heap (resource_memory active local) loc = Some w) ->
  owned_environment active OverlapMode A.Emp s local pool
    (share_cut_resource active frame retained) whole phase ->
  owned_environment active OverlapMode A.Emp s local pool frame whole phase.
Proof.
  intros Hcover Henv; destruct (owned_emp_pool_shape _ _ _ _ _ _ _ _ Henv) as [Hh [Hb Hk]].
  eapply owned_emp_overlap_intro; [exact (owned_pool_wf _ _ _ _ _ _ _ _ _ Henv)
    |exact Hh |exact Hb |exact Hk | |exact (owned_pool_status _ _ _ _ _ _ _ _ _ Henv)].
  apply (share_cut_restore_composition _ _ _ _ _ Hcover).
  exact (owned_emp_environment_repaired _ _ _ _ _ _ _ _ Henv).
Qed.
