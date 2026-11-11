From Stdlib Require Import List ZArith.
From WMLR Require Import Expressions Languages Machine BufferRelations Separation RepairedSeparation
  FrameDecomposition OperationalSemantics Assertions AssertionSemantics ConcreteAssertions PersistentAssertions
  Safety Specifications HeapRules OwnershipProtocol OwnershipRules OwnershipHeap PrivateOwnership SpatialExchange
  TemporalSafety TransferredCells RetiredHeaps RetiredSafety.
Import ListNotations.

Lemma retired_project_wf active r : memory_well_formed active (RH.project r).
Proof. split; [intros i H; contradiction |intros i H; reflexivity]. Qed.

Lemma retired_cell_to_protected active owner s r loc v : active owner -> RH.cell owner loc v r ->
  persistent_full_satisfies active s (RH.project r) (processor_cell owner loc v).
Proof.
  intros Hi [Hheap _]. pose (g := exist _ (Generalized (RH.project r) active)
    (full_memory_valid_with_processor active owner _ Hi (retired_project_wf active r))).
  exists g; split; [reflexivity |]. apply processor_cell_from_shape.
  - exact Hi.
  - exact Hheap.
  - intros i; reflexivity.
  - intros i H; contradiction.
  - exact Hi.
Qed.

Lemma protected_processor_cell_shape active owner s m loc v : active owner ->
  persistent_full_satisfies active s m (processor_cell owner loc v) ->
  (forall address, shared_heap m address = heap_update empty_heap loc v address) /\
  (forall i, buffers m i = []) /\ lock_free m.
Proof.
  intros Hi [r [E HP]]. destruct (processor_cell_shape _ _ _ _ _ _ Hi HP) as [Hh [Hb [Hk _]]].
  unfold resource_memory in Hh, Hb, Hk.
  rewrite E in Hh, Hb, Hk; auto.
Qed.

(** Repartition a live current cell, retaining all earlier heap history.
    Retirement masks overlapping history instead of demanding disjointness. *)
Lemma retired_cell_split history local combined owner loc v :
  RH.temporal history local combined -> RH.cell owner loc v local ->
  memory_spatial (RH.project (RH.compose history (RH.retire local loc)))
    (RH.project (RH.singleton owner loc v)) (RH.project combined).
Proof.
  intros [Htm Hmarks] [Hcell Hmark].
  assert (Hsingleton : forall address, RH.live_heap (RH.singleton owner loc v) address = heap_update empty_heap loc v address).
  { apply RH.take_vacant_cell; intros address; reflexivity. }
  split.
  - split.
    + intros address [[w Hw] |[i [w Hw]]] [[z Hz] |[j [z Hz]]]; try contradiction.
      cbn [RH.project shared_heap] in Hw, Hz; rewrite Hsingleton in Hz.
      destruct (Pos.eq_dec address loc) as [-> |Hne].
      * unfold RH.live_heap, RH.compose, RH.retire in Hw; cbn [RH.entries] in Hw.
        rewrite RH.set_same in Hw; discriminate.
      * rewrite heap_update_other in Hz by exact Hne; discriminate.
    + intros i H; contradiction.
  - split.
    + intros address; cbn [RH.project shared_heap]; unfold heap_override; rewrite Hsingleton.
      destruct (Pos.eq_dec address loc) as [-> |Hne].
      * rewrite heap_update_same.
        eapply RH.temporal_live_right; [split; [exact Htm |exact Hmarks] |].
        rewrite Hcell, heap_update_same; reflexivity.
      * rewrite heap_update_other by exact Hne; cbn [heap_override empty_heap].
        unfold RH.live_heap; rewrite Htm; cbn [RH.compose RH.entries].
        unfold RH.retire; rewrite RH.set_other by exact Hne; reflexivity.
    + split; [intros i; constructor |intros i; cbn [RH.project blocked no_blocked]; tauto].
Qed.

Theorem retired_donate_environment active owner invariant s local protected history whole rest loc v :
  retired_environment active owner invariant Open s local protected history whole ->
  protocol_assertion active Open s protected (owned_assertion owner rest) ->
  RH.models active s local (processor_cell owner loc v) ->
  exists protected', retired_environment active owner invariant Open s (RH.retire local loc) protected' history whole /\
    protocol_assertion active Open s protected' (owned_assertion owner (A.Spatial rest (processor_cell owner loc v))) /\
    RH.models active s (RH.retire local loc) A.Emp.
Proof.
  intros [Hr Hb [combined [Htm Hsp]]] HS HP.
  destruct (RH.processor_cell_shape _ _ _ _ _ _ HP) as [Hi Hcell].
  pose proof (retired_cell_split _ _ _ _ _ _ Htm Hcell) as Hsplit.
  destruct (proj2 (memory_spatial_associative _ _ _ _)
    (ex_intro _ (RH.project combined) (conj Hsplit Hsp))) as (protected' & Hnewpool & Hwhole).
  destruct (full_spatial_elim _ _ _ _ _ HS) as (token & payload & Htoken & Hlock & Hpayload).
  destruct (proj2 (memory_spatial_associative token payload (RH.project (RH.singleton owner loc v)) protected')
    (ex_intro _ protected (conj Htoken (memory_spatial_comm _ _ _ Hnewpool)))) as (payload' & Hpayload' & Htoken').
  assert (HS' : protocol_assertion active Open s protected'
    (owned_assertion owner (A.Spatial rest (processor_cell owner loc v)))).
  { eapply full_spatial_intro; [exact Htoken' |exact Hlock |].
    eapply full_spatial_intro; [exact Hpayload' |exact Hpayload |].
    apply retired_cell_to_protected; [exact Hi |apply RH.take_vacant_cell; intros address; reflexivity]. }
  exists protected'; split.
  - constructor.
    + split; [exact (proj1 (persistent_full_well_formed _ _ _ _ HS')) |].
      destruct Hr as [_ [Hactive Hheld]]; split; [exact Hactive |]. intros i.
      rewrite (proj2 (proj2 (proj2 Hnewpool)) i); cbn [RH.project blocked no_blocked].
      rewrite Hheld; unfold blocked_except, no_blocked; tauto.
    + intros i; pose proof (proj1 (proj2 (proj2 Hnewpool)) i) as Hmerge.
      cbn [RH.project buffers empty_buffers] in Hmerge; rewrite Hb in Hmerge.
      apply interleaves_nil_left, Hmerge.
    + exists (RH.compose history (RH.retire local loc)); split; [apply RH.temporal_compose |exact Hwhole].
  - split; [exact HS' |apply RH.retire_cell_vacant with (owner := owner) (v := v), Hcell].
Qed.

Theorem retired_donate_fence_valid active owner invariant rest loc v :
  retired_valid active owner invariant Open (owned_assertion owner rest) (processor_cell owner loc v)
    (Concurrent.Prim (Concurrent.Common Sequential.Fence) (EVal (Z.pos owner)))
    Open (owned_assertion owner (A.Spatial rest (processor_cell owner loc v))) A.Emp.
Proof.
  apply retired_primitive_rule; [discriminate | |].
  - intros s local protected history whole Henv HS HP i E Hfault; inversion Hfault.
  - intros s local protected history whole Henv HS HP i t whole' E Hstep.
    simpl in E; inversion E; subst i; inversion Hstep; subst.
    destruct (retired_donate_environment _ _ _ _ _ _ _ _ _ _ _ Henv HS HP)
      as (protected' & Henv' & HS' & HQ).
    exists (RH.retire local loc), protected'; auto.
Qed.

Lemma retired_release_environment active owner invariant s local protected history whole :
  retired_environment active owner invariant Open s local protected history whole ->
  protocol_assertion active Open s protected (owned_assertion owner invariant) ->
  exists pool, retired_environment active owner invariant Closed s local pool history (release whole).
Proof.
  intros [[Hwf Hheld] Hb [combined [Htm Hsp]]] HS.
  destruct (release_returns_invariant _ _ _ _ _ Hheld HS) as (pool & HJ & Hfree & Heq).
  exists pool; constructor.
  - split; [exact (proj1 (persistent_full_well_formed _ _ _ _ HJ)) |auto].
  - intros i; rewrite <- (proj1 (proj2 Heq) i); apply Hb.
  - exists combined; split; [exact Htm |].
    eapply protocol_spatial_equiv_right; [exact Heq |].
    apply protocol_spatial_reblock; [intros i H; contradiction |exact Hsp].
Qed.

Theorem retired_release_valid active owner invariant post :
  retired_valid active owner invariant Open (owned_assertion owner invariant) post
    (Concurrent.Prim Concurrent.Unlock (EVal (Z.pos owner))) Closed A.Emp post.
Proof.
  apply retired_primitive_rule; [discriminate | |].
  - intros s local protected history whole Henv HS HP i E Hfault; inversion Hfault.
  - intros s local protected history whole Henv HS HP i t whole' E Hstep.
    simpl in E; inversion E; subst i; inversion Hstep; subst.
    destruct (retired_release_environment _ _ _ _ _ _ _ _ Henv HS) as (pool & Henv').
    exists local, pool; split; [exact Henv' |]. split; [apply protocol_empty_satisfies |exact HP].
Qed.

(** Donation at unlock: no extra machine fence, and no disjoint-history premise. *)
Theorem retired_donate_release_valid active owner rest loc v :
  retired_valid active owner (A.Spatial rest (processor_cell owner loc v))
    Open (owned_assertion owner rest) (processor_cell owner loc v)
    (Concurrent.Prim Concurrent.Unlock (EVal (Z.pos owner))) Closed A.Emp A.Emp.
Proof.
  apply retired_primitive_rule; [discriminate | |].
  - intros s local protected history whole Henv HS HP i E Hfault; inversion Hfault.
  - intros s local protected history whole Henv HS HP i t whole' E Hstep.
    simpl in E; inversion E; subst i; inversion Hstep; subst.
    destruct (retired_donate_environment _ _ _ _ _ _ _ _ _ _ _ Henv HS HP)
      as (protected' & Henv' & HS' & HQ).
    destruct (retired_release_environment _ _ _ _ _ _ _ _ Henv' HS') as (pool & Henv'').
    exists (RH.retire local loc), pool; split; [exact Henv'' |]. split; [apply protocol_empty_satisfies |exact HQ].
Qed.

Lemma retired_cell_join history local combined owner loc v cell out :
  RH.temporal history local combined ->
  (forall address, shared_heap cell address = heap_update empty_heap loc v address) ->
  (forall i, buffers cell i = []) -> lock_free cell ->
  memory_spatial (RH.project combined) cell out ->
  memory_equiv out (RH.project (RH.compose history (RH.take local owner loc v))).
Proof.
  intros [Htm _] Hcell Hb Hfree [_ [Hheap [Hbuffers Hblocks]]]. split.
  - intros address; rewrite Hheap; cbn [RH.project shared_heap]; unfold heap_override; rewrite Hcell.
    unfold RH.live_heap, RH.compose, RH.take; cbn [RH.entries].
    destruct (Pos.eq_dec address loc) as [-> |Hne].
    + rewrite heap_update_same, RH.set_same; reflexivity.
    + rewrite heap_update_other, RH.set_other by exact Hne; cbn [empty_heap]. rewrite Htm; reflexivity.
  - split.
    + intros i; specialize (Hbuffers i); cbn [RH.project buffers empty_buffers] in Hbuffers.
      rewrite Hb in Hbuffers; exact (interleaves_nil_left _ _ Hbuffers).
    + intros i; rewrite Hblocks; cbn [RH.project blocked]; unfold no_blocked.
      split; [intros [H |H]; [exact H |exact (Hfree i H)] |contradiction].
Qed.

Theorem retired_take_environment active owner invariant s local protected history whole rest loc v :
  retired_environment active owner invariant Open s local protected history whole ->
  protocol_assertion active Open s protected (owned_assertion owner (A.Spatial rest (processor_cell owner loc v))) ->
  RH.models active s local A.Emp ->
  exists kept, retired_environment active owner invariant Open s (RH.take local owner loc v) kept history whole /\
    protocol_assertion active Open s kept (owned_assertion owner rest) /\
    RH.models active s (RH.take local owner loc v) (processor_cell owner loc v).
Proof.
  intros [[Hwf Hheld] Hb [combined [Htm Hsp]]] HS HP.
  destruct (full_spatial_elim _ _ _ _ _ HS) as (token & payload & Htoken & Hlock & Hpayload).
  destruct (full_spatial_elim _ _ _ _ _ Hpayload) as (restmem & cell & Hpayloadsplit & Hrest & Hcell).
  destruct (proj1 (memory_spatial_associative token restmem cell protected)
    (ex_intro _ payload (conj Hpayloadsplit Htoken))) as (kept & Hkept & Hsplit).
  assert (HS' : protocol_assertion active Open s kept (owned_assertion owner rest)).
  { eapply full_spatial_intro; eassumption. }
  destruct (protected_processor_cell_shape _ _ _ _ _ _ (proj1 Hheld) Hcell) as [Hcellh [Hcellb Hcellfree]].
  destruct (spatial_exchange cell kept (RH.project combined) protected whole
    (memory_spatial_comm _ _ _ Hsplit) Hsp) as (joined & Hjoin & Hwhole).
  pose proof (retired_cell_join _ _ _ owner _ _ _ _ Htm Hcellh Hcellb Hcellfree
    (memory_spatial_comm _ _ _ Hjoin)) as Heq.
  exists kept; split.
  - constructor.
    + split; [exact (proj1 (persistent_full_well_formed _ _ _ _ HS')) |].
      split; [exact (proj1 Hheld) |]. intros i.
      pose proof (proj2 Hheld i) as Hheldi; rewrite (proj2 (proj2 (proj2 Hsplit)) i) in Hheldi.
      split; [intros H; apply Hheldi; auto |intros H; apply Hheldi in H; destruct H; [assumption |exfalso; exact (Hcellfree i H)]].
    + intros i; exact (proj1 (spatial_empty_buffer_parts _ _ _ i Hsplit (Hb i))).
    + exists (RH.compose history (RH.take local owner loc v)); split; [apply RH.temporal_compose |].
      apply memory_spatial_comm; eapply protocol_spatial_equiv_right; eassumption.
  - split; [exact HS' |apply RH.processor_cell_intro; [exact (proj1 Hheld) |apply RH.take_vacant_cell, HP]].
Qed.

Theorem retired_take_release_valid active owner invariant loc v :
  retired_valid active owner invariant Open (owned_assertion owner (A.Spatial invariant (processor_cell owner loc v))) A.Emp
    (Concurrent.Prim Concurrent.Unlock (EVal (Z.pos owner))) Closed A.Emp (processor_cell owner loc v).
Proof.
  apply retired_primitive_rule; [discriminate | |].
  - intros s local protected history whole Henv HS HP i E Hfault; inversion Hfault.
  - intros s local protected history whole Henv HS HP i t whole' E Hstep.
    simpl in E; inversion E; subst i; inversion Hstep; subst.
    destruct (retired_take_environment _ _ _ _ _ _ _ _ _ _ _ Henv HS HP)
      as (kept & Henv' & HS' & HQ).
    destruct (retired_release_environment _ _ _ _ _ _ _ _ Henv' HS') as (pool & Henv'').
    exists (RH.take local owner loc v), pool; split; [exact Henv'' |]. split; [apply protocol_empty_satisfies |exact HQ].
Qed.
