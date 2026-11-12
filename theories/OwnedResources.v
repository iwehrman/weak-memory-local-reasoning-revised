From Stdlib Require Import List ZArith.
From WMLR Require Import Expressions Languages Machine BufferRelations OrderedBuffers Separation
  StableCompatibility RepairedSeparation GeneralizedFlushing FrameDecomposition
  OperationalSemantics ProgramSteps Assertions AssertionSemantics ConcreteAssertions
  PersistentAssertions Safety RepairedSafety HeapRules LockRules OwnershipProtocol
  OwnershipHeap PrivateOwnership SpatialExchange TemporalSafety RegionalResources
  InvariantFragment LockRepresentation OwnedSafety OwnedAdequacy.
Import ListNotations.

Definition owned_enqueue_resource active (r : resource active) actor (loc : location) (v : value)
    (Hactor : active actor) : resource active.
Proof.
  refine (exist _ (Generalized (enqueue (resource_memory active r) actor loc v)
    (complete (proj1_sig r))) _).
  destruct (proj2_sig r) as [Hwf [Hmarks Hheap]]; split.
  - apply update_buffers_well_formed; assumption.
  - split; assumption.
Defined.

Lemma owned_environment_as_framed active mode invariant s local pool frame whole phase :
  owned_environment active mode invariant s local pool frame whole phase ->
  repaired_framed active pool (resource_memory active frame) (resource_memory active local) whole.
Proof.
  intros [_ _ [combined [[Hinner _] Houter]] _ _].
  exists (resource_memory active combined); auto.
Qed.

Lemma owned_disjoint_empty_pool active invariant s local frame whole phase :
  owned_environment active DisjointMode invariant s local empty_memory frame whole phase ->
  memory_spatial (resource_memory active frame) (resource_memory active local) whole.
Proof.
  intros [_ _ [combined [[[Hstable [Hh [Hb Hk]]] Hmarks] Houter]] Hdomains _].
  assert (Hempty : spatial empty_generalized (proj1_sig combined)
    (Generalized whole (complete (proj1_sig combined)))).
  { split; [exact Houter |intros i; cbn; unfold no_blocked; tauto]. }
  destruct (proj1 (spatial_empty_left_unique _ _ Hempty)) as [Eheap [Ebuffers Eblocks]].
  split; [split; [exact Hdomains |exact (proj1 Hstable)] |].
  split; [intros loc; rewrite Eheap; apply Hh |]. split.
  - intros i; rewrite Ebuffers; apply ordered_interleaves, Hb.
  - intros i; rewrite Eblocks; apply Hk.
Qed.

Lemma owned_held_spatial_environment active mode invariant s (local frame : resource active) whole owner :
  memory_spatial (resource_memory active frame) (resource_memory active local) whole ->
  lock_held active whole owner ->
  owned_environment active mode invariant s local empty_memory frame whole (PoolHeld owner).
Proof.
  intros Hsp Hheld.
  assert (Hmarked : spatial (proj1_sig frame) (proj1_sig local)
    (Generalized whole (fun i => complete (proj1_sig frame) i \/ complete (proj1_sig local) i))).
  { split; [exact Hsp |intros i; reflexivity]. }
  pose (combined := exist _ _
    (spatial_well_formed _ _ _ _ (proj2_sig frame) (proj2_sig local) Hmarked)).
  constructor.
  - exact (proj1 (empty_generalized_well_formed active)).
  - eapply raw_spatial_well_formed; [exact (proj1 (proj2_sig frame)) |exact (proj1 (proj2_sig local)) |exact Hsp].
  - exists combined; split; [apply spatial_in_repaired, Hmarked |].
    exact (proj1 (spatial_empty_left (proj1_sig combined))).
  - destruct mode; [exact I |exact (proj1 (proj1 Hsp))].
  - split; [exact Hheld |reflexivity].
Qed.

Lemma owned_environment_enqueue active mode invariant s local pool frame whole phase actor loc v old
    (Hactor : active actor) :
  owned_environment active mode invariant s local pool frame whole phase ->
  shared_heap (resource_memory active local) loc = Some old ->
  owned_environment active mode invariant s (owned_enqueue_resource active local actor loc v Hactor)
    pool frame (enqueue whole actor loc v) phase.
Proof.
  intros [Hp Hw [combined [[Hinner Hmarks] Houter]] Hmode Hstatus] Hcell.
  constructor; [exact Hp |apply update_buffers_well_formed; assumption | | |].
  - exists (owned_enqueue_resource active combined actor loc v Hactor); split.
    + split; [eapply repaired_enqueue_right; eassumption |exact Hmarks].
    + apply spatial_enqueue_right; [exact Houter |]. left; exists old.
      rewrite (proj1 (proj2 Hinner)); unfold heap_override.
      fold (resource_memory active local); rewrite Hcell; reflexivity.
  - destruct mode; [exact I |]. intros address Hframe Hlocal; apply (Hmode address Hframe).
    apply (enqueue_domain_subset (resource_memory active local) actor loc v
      ltac:(left; exists old; exact Hcell)), Hlocal.
  - destruct phase; exact Hstatus.
Qed.

Lemma owned_enqueue_update active phase (local : resource active) pool actor loc v old (Hi : active actor) :
  shared_heap (resource_memory active local) loc = Some old ->
  owned_update active OrdinaryAction phase phase local pool
    (owned_enqueue_resource active local actor loc v Hi) pool.
Proof.
  intros Hcell; constructor.
  - split; [reflexivity |]. split; [reflexivity |intros; reflexivity].
  - intros address [Hpool |Hlocal]; [left; exact Hpool |right].
    apply (enqueue_domain_subset (resource_memory active local) actor loc v
      ltac:(left; exists old; exact Hcell)), Hlocal.
  - intros i Hmark; left; exact Hmark.
Qed.

Lemma writer_cell_enqueue_post active s (local : resource active) loc old actor v (Hi : active actor) :
  persistent_models active s local (writer_points_to (EVal (Z.pos loc)) (EVal old)) ->
  persistent_models active s (owned_enqueue_resource active local actor loc v Hi)
    (A.Temporal (writer_points_to (EVal (Z.pos loc)) (EVal old))
      (A.LeadsTo (EVal (Z.pos loc)) (EVal (Z.pos actor)) (EVal v))).
Proof.
  intros HP; pose proof (writer_points_to_shape _ _ _ _ _ HP)
    as (address & owner & Eaddress & Howner & Hheap & Hbuffers & Hfree & Hmark).
  cbn in Eaddress; injection Eaddress as Eaddress; subst address.
  exists local, (pending_write_resource active actor loc v Hi); split.
  - assert (Hstable : stable_compatible active (resource_memory active local)
      (pending_write_memory actor loc v)).
    { split; [intros i _ H; contradiction |]. split;
        [intros i _ address [w Hw] |intros i j _ _ _ address [w Hw]];
        rewrite Hbuffers in Hw; contradiction. }
    split; [exact Hstable |]. split.
    + split; [apply stable_implies_printed_compatible, Hstable |].
      split; [intros; reflexivity |]. split.
      * intros i; cbn [owned_enqueue_resource pending_write_resource proj1_sig underlying enqueue buffers pending_write_memory].
        unfold buffer_update; destruct (Pos.eq_dec i actor) as [-> |Hne];
          [reflexivity |rewrite app_nil_r; reflexivity].
      * intros i; cbn; unfold no_blocked; tauto.
    + split; [intros i H; contradiction |]. intros i; cbn; unfold no_blocked; tauto.
  - split; [exact HP |]. split; [exact Hi |left].
    split; [intros; reflexivity |]. split; [intros; reflexivity |intros i H; contradiction].
Qed.

Lemma owned_done_safe active mode invariant n annotation s local post :
  persistent_models active s local post ->
  owned_safe active mode invariant n (C.skip annotation) s local post.
Proof.
  intros HQ; destruct n; [exact I |]. intros later Hfuture; split.
  - intros _; eapply persistent_assertion_flushing_closed; eassumption.
  - intros pool frame whole phase Henv; split; [apply skip_no_abort |].
    intros action next t whole' Hstep; exfalso; eapply program_skip_impossible; exact Hstep.
Qed.

Lemma owned_lock_cell_shape active s local owner loc v :
  persistent_models active s local
    (A.Spatial (A.Lock (EVal (Z.pos owner))) (writer_points_to (EVal (Z.pos loc)) (EVal v))) ->
  (forall address, shared_heap (resource_memory active local) address = heap_update empty_heap loc v address) /\
  (forall i, buffers (resource_memory active local) i = []) /\
  lock_held active (resource_memory active local) owner.
Proof.
  intros (token & cell & [[_ [Hheap [Hbuffers Hblocks]]] _] & Htoken & Hcell).
  destruct Htoken as [HtHeap [HtBuffers [Howner Hheld]]].
  destruct (writer_points_to_shape _ _ _ _ _ Hcell)
    as (address & writer & Eaddress & Hwriter & HcHeap & HcBuffers & HcFree & HcMark).
  cbn in Eaddress; injection Eaddress as Eaddress; subst address.
  split.
  - intros address; rewrite Hheap; unfold heap_override; rewrite HcHeap, HtHeap.
    unfold heap_update, empty_heap; destruct (Pos.eq_dec address loc); reflexivity.
  - split.
    + intros i; specialize (Hbuffers i); rewrite HtBuffers, HcBuffers in Hbuffers.
      apply interleaves_nil_left, Hbuffers.
    + split; [exact Howner |]. intros i; rewrite Hblocks, <- (Hheld i).
      split; [intros [H |H]; [exact H |exfalso; exact (HcFree i H)] |auto].
Qed.

Lemma owned_blocked_union active mode invariant s local pool frame whole phase i :
  owned_environment active mode invariant s local pool frame whole phase ->
  (blocked whole i <-> blocked pool i \/ blocked (resource_memory active frame) i \/
    blocked (resource_memory active local) i).
Proof.
  intros [_ _ [combined [[[_ [_ [_ Hinner]]] _] [_ [_ [_ Houter]]]]] _ _].
  rewrite Houter, Hinner; tauto.
Qed.

Lemma owned_token_environment active mode invariant s local pool frame whole phase owner :
  two_active_processors active ->
  owned_environment active mode invariant s local pool frame whole phase ->
  lock_held active (resource_memory active local) owner ->
  phase = PoolHeld owner /\ pool = empty_memory /\ lock_free (resource_memory active frame).
Proof.
  intros Hdomain Henv Hheld.
  pose proof (owned_pool_status _ _ _ _ _ _ _ _ _ Henv) as Hstatus.
  assert (HlocalWhole : forall i, blocked (resource_memory active local) i -> blocked whole i).
  { intros i H; apply (owned_blocked_union _ _ _ _ _ _ _ _ _ i Henv); auto. }
  destruct phase.
  - destruct Hstatus as [Hfree _]; exfalso.
    destruct Hdomain as (first & second & Hfirst & Hsecond & Hne).
    eapply (two_processors_separate_free_held active first second
      (resource_memory active local) owner Hfirst Hsecond Hne); [|exact Hheld].
    intros i H; apply (Hfree i), HlocalWhole, H.
  - destruct Hstatus as [[Hactive HwholeHeld] ->].
    assert (Eowner : owner0 = owner).
    { destruct (Pos.eq_dec owner0 owner) as [E |Hne]; [exact E |].
      exfalso; assert (Hb : blocked whole owner0).
      { apply HlocalWhole, (proj2 Hheld); auto. }
      destruct (proj1 (HwholeHeld owner0) Hb) as [_ Hbad]; contradiction. }
    subst owner0; split; [reflexivity |]. split; [reflexivity |].
    intros i Hframe.
    assert (Hglobal : blocked whole i).
    { apply (owned_blocked_union _ _ _ _ _ _ _ _ _ i Henv); auto. }
    destruct (owned_composition _ _ _ _ _ _ _ _ _ Henv)
      as [combined [[[Hstable _] _] _]].
    apply (proj1 Hstable i Hframe), (proj2 Hheld), HwholeHeld, Hglobal.
Qed.

Lemma owned_disjoint_donation_environment active invariant s local pool frame whole phase owner :
  two_active_processors active ->
  owned_environment active DisjointMode invariant s local pool frame whole phase ->
  lock_held active (resource_memory active local) owner ->
  persistent_full_satisfies active s (release (resource_memory active local)) invariant ->
  owned_environment active DisjointMode invariant s (bare_resource active)
    (release (resource_memory active local)) frame (release whole) PoolFree /\
  owned_update active (ReleaseAction owner) phase PoolFree local pool (bare_resource active)
    (release (resource_memory active local)).
Proof.
  intros Hdomain Henv Hheld HJ.
  destruct (owned_token_environment _ _ _ _ _ _ _ _ _ _ Hdomain Henv Hheld)
    as [-> [-> Hframefree]].
  pose proof (owned_disjoint_empty_pool _ _ _ _ _ _ _ Henv) as Hsp.
  split.
  - constructor.
    + apply release_well_formed; exact (proj1 (proj2_sig local)).
    + apply release_well_formed; exact (owned_whole_wf _ _ _ _ _ _ _ _ _ Henv).
    + exists frame; split; [apply repaired_empty_right |].
      apply memory_spatial_comm.
      exact (protocol_spatial_reblock _ _ _ no_blocked Hframefree Hsp).
    + intros address _ [[v H] |[i [v H]]]; discriminate || contradiction.
    + split; [intros i H; exact H |exact HJ].
  - constructor.
    + split; [reflexivity |]. split; [reflexivity |]. split; [exact Hheld |intros i H; exact H].
    + intros address [Hpool |[[v H] |[i [v H]]]];
        [right; exact Hpool |discriminate |contradiction].
    + intros i H; contradiction.
Qed.

Lemma repaired_memory_domain active frame local whole : memory_repaired active frame local whole ->
  forall loc, memory_domain whole loc <-> memory_domain frame loc \/ memory_domain local loc.
Proof.
  intros [_ [Hh [Hb _]]] loc.
  assert (Hheap : heap_domain (shared_heap whole) loc <->
    heap_domain (shared_heap frame) loc \/ heap_domain (shared_heap local) loc).
  { unfold heap_domain; rewrite Hh; apply heap_override_domain. }
  assert (Hbuffers : forall i, buffer_domain (buffers whole i) loc <->
    buffer_domain (buffers frame i) loc \/ buffer_domain (buffers local i) loc).
  { intros i; apply ordered_domain, Hb. }
  unfold memory_domain; rewrite Hheap; setoid_rewrite Hbuffers; firstorder.
Qed.

(** In particular, acquisition may add only cells from the spatially
    separate pool. No new frame-disjointness premise is needed for that step. *)
Theorem owned_update_preserves_disjoint active invariant s local pool frame whole phase
    action phase' local' pool' :
  owned_environment active DisjointMode invariant s local pool frame whole phase ->
  owned_update active action phase phase' local pool local' pool' ->
  mode_compatible active DisjointMode frame local'.
Proof.
  intros [_ _ [combined [[Hinner _] [[Hpool _] _]]] Hmode _] Hupdate address Hframe Hlocal.
  destruct (owned_footprint _ _ _ _ _ _ _ _ Hupdate address (or_intror Hlocal)) as [Hp |Hl].
  - apply (Hpool address Hp), (repaired_memory_domain _ _ _ _ Hinner address); auto.
  - exact (Hmode address Hframe Hl).
Qed.

Lemma owned_environment_forget_mode active invariant s local pool frame whole phase :
  owned_environment active DisjointMode invariant s local pool frame whole phase ->
  owned_environment active OverlapMode invariant s local pool frame whole phase.
Proof. intros [Hp Hw Hcomp Hmode Hstatus]; constructor; assumption || exact I. Qed.

Theorem owned_safe_overlap_disjoint active invariant n command s local post :
  owned_safe active OverlapMode invariant n command s local post ->
  owned_safe active DisjointMode invariant n command s local post.
Proof.
  revert command s local; induction n; intros command s local Hsafe; [exact I |].
  intros later Hfuture; destruct (Hsafe later Hfuture) as [Hdone Henvs].
  split; [exact Hdone |]. intros pool frame whole phase Henv.
  destruct (Henvs _ _ _ _ (owned_environment_forget_mode _ _ _ _ _ _ _ _ Henv)) as [Habort Hprogress].
  split; [exact Habort |]. intros action next t whole' Hstep.
  destruct (Hprogress _ _ _ _ Hstep) as (local' & pool' & phase' & Henv' & Hupdate & Hsafe').
  exists local', pool', phase'; split.
  - destruct Henv' as [Hp Hw Hcomp _ Hstatus]; constructor; try assumption.
    eapply owned_update_preserves_disjoint; eassumption.
  - split; [exact Hupdate |exact (IHn next t local' Hsafe')].
Qed.

Corollary owned_valid_overlap_disjoint active invariant pre command post :
  owned_valid active OverlapMode invariant pre command post ->
  owned_valid active DisjointMode invariant pre command post.
Proof. intros Hvalid s local HP n; apply owned_safe_overlap_disjoint, Hvalid, HP. Qed.
