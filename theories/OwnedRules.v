From Stdlib Require Import List ZArith.
From WMLR Require Import Expressions Languages Machine BufferRelations OrderedBuffers Separation
  StableCompatibility RepairedSeparation GeneralizedFlushing FrameDecomposition
  OperationalSemantics ProgramSteps Assertions AssertionSemantics ConcreteAssertions
  PersistentAssertions Safety RepairedSafety HeapRules LockRules OwnershipProtocol
  OwnershipHeap PrivateOwnership SpatialExchange TemporalSafety TemporalFence TemporalTransfer
  RegionalResources InvariantFragment LockRepresentation OwnedSafety OwnedAdequacy OwnedResources.
Import ListNotations.

(** General transfer rules for the checkpoint-5 predicate. No new safety
    predicate, assertion atom, or interpretation is introduced. *)

Lemma owned_lock_payload_held active mode invariant s local pool frame whole phase owner pre :
  two_active_processors active ->
  owned_environment active mode invariant s local pool frame whole phase ->
  persistent_models active s local (A.Spatial (A.Lock (EVal (Z.pos owner))) pre) ->
  lock_held active (resource_memory active local) owner.
Proof.
  intros Htwo Henv (token & payload & [[_ [_ [_ Hblocks]]] _] & Htoken & _).
  destruct Htoken as [_ [_ [Hi Htoken]]].
  assert (Hinclude : forall i, active i /\ i <> owner -> blocked whole i).
  { intros i H; apply (owned_blocked_union _ _ _ _ _ _ _ _ _ i Henv).
    right; right; apply Hblocks; left; apply Htoken, H. }
  pose proof (owned_pool_status _ _ _ _ _ _ _ _ _ Henv) as Hstatus.
  destruct phase as [|holder].
  - destruct Hstatus as [Hfree _]; exfalso.
    destruct Htwo as (first & second & Hfirst & Hsecond & Hne).
    destruct (Pos.eq_dec first owner) as [-> |Hno].
    + apply (Hfree second), Hinclude; split; [exact Hsecond |congruence].
    + apply (Hfree first), Hinclude; auto.
  - destruct Hstatus as [[Hholder Hwhole] _].
    assert (E : holder = owner).
    { destruct (Pos.eq_dec holder owner) as [E |Hno]; [exact E |].
      destruct (proj1 (Hwhole holder) (Hinclude holder (conj Hholder Hno))) as [_ Hbad].
      contradiction. }
    subst holder; split; [exact Hi |]. intros i; split.
    + intros H; apply Hwhole, (owned_blocked_union _ _ _ _ _ _ _ _ _ i Henv); auto.
    + intros H; apply Hblocks; left; apply Htoken, H.
Qed.

Lemma owned_marked_barrier_intro active s (local : resource active) pre owner (Hi : active owner) :
  persistent_models active s local pre -> buffers (resource_memory active local) owner = [] ->
  persistent_models active s (mark_processor active local owner Hi)
    (A.Temporal pre (A.Barrier (EVal (Z.pos owner)))).
Proof.
  intros HP Hempty.
  exists local, (mark_processor active (bare_resource active) owner Hi); split.
  - destruct (repaired_temporal_bare_right active local) as [Hstable [Hmemory _]].
    split; [exact Hstable |]. split; [exact Hmemory |]. split.
    + intros i [H | ->]; [contradiction |exact Hempty].
    + intros i; cbn [mark_processor proj1_sig complete bare_resource empty_generalized].
      unfold no_blocked; tauto.
  - split; [exact HP |apply marked_emp_barrier, bare_resource_models].
Qed.

Lemma owned_barrier_suffix_intro active s (local : resource active) pre owner (Hi : active owner) :
  persistent_models active s local pre -> buffers (resource_memory active local) owner = [] ->
  complete (proj1_sig local) owner ->
  persistent_models active s local (A.Temporal pre (A.Barrier (EVal (Z.pos owner)))).
Proof.
  intros HP Hempty Hmark.
  exists local, (mark_processor active (bare_resource active) owner Hi); split.
  - destruct (repaired_temporal_bare_right active local) as [Hstable [Hmemory _]].
    split; [exact Hstable |]. split; [exact Hmemory |]. split.
    + intros i [H | ->]; [contradiction |exact Hempty].
    + intros i; change (complete (proj1_sig local) i <->
        complete (proj1_sig local) i \/ False \/ i = owner).
      split; [auto |intros [H |[H | ->]]; assumption || contradiction].
  - split; [exact HP |apply marked_emp_barrier, bare_resource_models].
Qed.

Lemma owned_lock_transfer active mode invariant owner s local pool frame whole phase :
  two_active_processors active -> invariant_fragment invariant -> active owner ->
  persistent_models active s local A.Emp ->
  owned_environment active mode invariant s local pool frame whole phase ->
  lock_free whole ->
  exists local',
    owned_environment active mode invariant s local' empty_memory frame
      (acquire active whole owner) (PoolHeld owner) /\
    owned_update active (AcquireAction owner) phase (PoolHeld owner) local pool local' empty_memory /\
    persistent_models active s local'
      (A.Temporal (A.Spatial (A.Lock (EVal (Z.pos owner))) invariant)
        (A.Barrier (EVal (Z.pos owner)))).
Proof.
  intros Htwo Hfragment Hi Hemp Henv Hfree.
  assert (Ephase : phase = PoolFree).
  { pose proof (owned_pool_status _ _ _ _ _ _ _ _ _ Henv) as Hstatus.
    destruct phase as [|holder]; [reflexivity |].
    destruct Htwo as (first & second & Hfirst & Hsecond & Hne).
    exfalso; eapply (two_processors_separate_free_held active first second whole holder
      Hfirst Hsecond Hne); [exact Hfree |exact (proj1 Hstatus)]. }
  subst phase.
  destruct (proj2 (owned_pool_status _ _ _ _ _ _ _ _ _ Henv)) as (original & Eoriginal & HJ).
  assert (Hactive : forall i, complete (proj1_sig local) i \/ i = owner -> active i).
  { intros i [H | ->]; [exact (proj1 (proj2 (proj2_sig local)) i H) |exact Hi]. }
  assert (Hnonempty : exists i, complete (proj1_sig local) i \/ i = owner) by (exists owner; auto).
  pose (payload := remark_resource active original
    (fun i => complete (proj1_sig local) i \/ i = owner) Hactive Hnonempty).
  assert (Epayload : resource_memory active payload = pool).
  { change (underlying (proj1_sig original) = pool); rewrite Eoriginal; reflexivity. }
  assert (HJ' : persistent_models active s payload invariant).
  { exact (invariant_fragment_remark invariant Hfragment active s original payload
      eq_refl Hnonempty HJ). }
  destruct (invariant_fragment_shape _ Hfragment _ _ _ HJ') as [Hbuffers Hpayloadfree].
  destruct (owned_composition _ _ _ _ _ _ _ _ _ Henv)
    as (combined & [[_ [Hh [Hb Hk]]] _] & Houter).
  destruct Hemp as [He [Hempty Hlocalfree]].
  assert (Ecombined : memory_equiv (resource_memory active combined) (resource_memory active frame)).
  { split.
    - intros loc; unfold resource_memory; rewrite Hh; unfold heap_override; rewrite He; reflexivity.
    - split.
      + intros i; specialize (Hb i); rewrite Hempty in Hb.
        apply interleaves_nil_right, ordered_interleaves, Hb.
      + intros i; rewrite Hk; split; [intros [H |H]; [exact H |exfalso; exact (Hlocalfree i H)] |auto]. }
  assert (Hframepool : memory_spatial (resource_memory active frame)
    (resource_memory active payload) whole).
  { rewrite Epayload; apply memory_spatial_comm.
    eapply protocol_spatial_equiv_right; eassumption. }
  pose proof (proj1 (spatial_free_parts _ _ _ Hframepool Hfree)) as Hframefree.
  exists (acquired_resource active payload owner); split.
  - apply owned_held_spatial_environment with (owner := owner).
    + exact (protocol_spatial_reblock _ _ _ (blocked_except active owner) Hframefree Hframepool).
    + split; [exact Hi |intros i; reflexivity].
  - split.
    + constructor.
      * split; [reflexivity |]. split; [reflexivity |]. split; [reflexivity |].
        split; [exact Hi |intros i; reflexivity].
      * intros loc [H |H]; [destruct H as [[v H] |[i [v H]]]; discriminate || contradiction |].
        left; change (memory_domain (resource_memory active payload) loc) in H; rewrite Epayload in H; exact H.
      * intros i H; exact H.
    + apply owned_barrier_suffix_intro with (Hi := Hi).
      * apply acquire_marked_payload; assumption.
      * exact (Hbuffers owner).
      * right; reflexivity.
Qed.

Theorem owned_lock_valid active mode invariant owner :
  two_active_processors active -> invariant_fragment invariant ->
  owned_valid active mode invariant A.Emp (C.Prim C.Lock (EVal (Z.pos owner)))
    (A.Temporal (A.Spatial (A.Lock (EVal (Z.pos owner))) invariant)
      (A.Barrier (EVal (Z.pos owner)))).
Proof.
  intros Htwo Hfragment s local HP n; destruct n; [exact I |].
  intros later Hfuture.
  assert (HP' : persistent_models active s later A.Emp).
  { eapply persistent_assertion_flushing_closed; eassumption. }
  split; [intros [annotation H]; discriminate |].
  intros pool frame whole phase Henv; split.
  - intros Hfault; inversion Hfault; subst.
    match goal with H : primitive_abort _ _ _ _ |- _ => inversion H end.
  - intros action next t whole' Hstep; inversion Hstep; subst.
    match goal with E : eval_expr _ (EVal (Z.pos owner)) = Z.pos _ |- _ => cbn in E; inversion E; subst end.
    match goal with H : primitive_step _ _ _ _ _ |- _ => inversion H; subst end.
    match goal with Hi : active ?actor |- _ =>
      destruct (owned_lock_transfer active mode invariant actor _ _ _ _ _ _ Htwo Hfragment Hi HP' Henv
        ltac:(assumption)) as (local' & Henv' & Hupdate & HQ) end.
    exists local', empty_memory; eexists; split; [exact Henv' |].
    split; [exact Hupdate |apply owned_done_safe, HQ].
Qed.

Lemma owned_free_spatial_environment active mode invariant s (local frame : resource active)
    pool combined whole :
  memory_well_formed active pool ->
  memory_spatial (resource_memory active frame) (resource_memory active local) combined ->
  memory_spatial pool combined whole -> lock_free whole ->
  persistent_full_satisfies active s pool invariant ->
  owned_environment active mode invariant s local pool frame whole PoolFree.
Proof.
  intros Hp Hinner Houter Hfree HJ.
  assert (Hsp : spatial (proj1_sig frame) (proj1_sig local)
    (Generalized combined (fun i => complete (proj1_sig frame) i \/ complete (proj1_sig local) i))).
  { split; [exact Hinner |intros i; reflexivity]. }
  pose (joined := exist _ _ (spatial_well_formed _ _ _ _ (proj2_sig frame) (proj2_sig local) Hsp)).
  constructor.
  - exact Hp.
  - eapply raw_spatial_well_formed; [exact Hp |exact (proj1 (proj2_sig joined)) |exact Houter].
  - exists joined; split; [apply spatial_in_repaired, Hsp |exact Houter].
  - destruct mode; [exact I |exact (proj1 (proj1 Hinner))].
  - split; assumption.
Qed.

Lemma owned_unlock_transfer active invariant pre post owner s local pool frame whole phase :
  two_active_processors active -> invariant_fragment invariant ->
  (forall t (r : resource active),
    persistent_models active t r (A.Temporal pre (A.Barrier (EVal (Z.pos owner)))) ->
    persistent_models active t r (A.Spatial invariant post)) ->
  persistent_models active s local (A.Spatial (A.Lock (EVal (Z.pos owner))) pre) ->
  owned_environment active DisjointMode invariant s local pool frame whole phase ->
  buffers whole owner = [] ->
  exists local' pool',
    owned_environment active DisjointMode invariant s local' pool' frame (release whole) PoolFree /\
    owned_update active (ReleaseAction owner) phase PoolFree local pool local' pool' /\
    persistent_models active s local' post.
Proof.
  intros Htwo Hfragment Hent HP Henv Hdrained.
  pose proof (owned_lock_payload_held _ _ _ _ _ _ _ _ _ _ _ Htwo Henv HP) as Hheld.
  destruct (owned_token_environment _ _ _ _ _ _ _ _ _ _ Htwo Henv Hheld)
    as [-> [-> Hframefree]].
  pose proof (owned_disjoint_empty_pool _ _ _ _ _ _ _ Henv) as Houter.
  destruct (release_marked_invariant _ _ _ _ _ Hheld HP)
    as (payload & Hpre & Hfree & Hequiv & Hmarks).
  assert (Hpayloadempty : buffers (resource_memory active payload) owner = []).
  { rewrite <- (proj1 (proj2 Hequiv)).
    exact (proj2 (spatial_empty_buffer_parts _ _ _ _ Houter Hdrained)). }
  pose (marked := mark_processor active payload owner (proj1 Hheld)).
  destruct (Hent s marked (owned_marked_barrier_intro _ _ _ _ _ _ Hpre Hpayloadempty))
    as (returned & retained & Hsplit & HJ & HQ).
  assert (Hframepayload : memory_spatial (resource_memory active frame)
    (resource_memory active marked) (release whole)).
  { eapply protocol_spatial_equiv_right; [exact Hequiv |].
    exact (protocol_spatial_reblock _ _ _ no_blocked Hframefree Houter). }
  destruct (spatial_free_parts _ _ _ (proj1 Hsplit) Hfree) as [Hreturnedfree Hretainedfree].
  destruct (proj1 (memory_spatial_associative (resource_memory active frame)
    (resource_memory active returned) (resource_memory active retained) (release whole))
    (ex_intro _ (resource_memory active marked) (conj (proj1 Hsplit) Hframepayload)))
    as (fr & Hfr & Hfrretained).
  destruct (proj2 (memory_spatial_associative (resource_memory active returned)
    (resource_memory active frame) (resource_memory active retained) (release whole))
    (ex_intro _ fr (conj (memory_spatial_comm _ _ _ Hfr) Hfrretained)))
    as (combined & Hcombined & Hfinal).
  exists retained, (resource_memory active returned); split.
  - eapply owned_free_spatial_environment; [exact (proj1 (proj2_sig returned))
      |exact Hcombined |exact Hfinal |intros i H; exact H |].
    eapply invariant_return_full_completeness; [exact (proj1 Hheld) |exact Hfragment |exact HJ].
  - split; [|exact HQ]. constructor.
    + split; [reflexivity |]. split; [reflexivity |]. split; assumption.
    + intros loc Hdom; right.
      apply (proj2 (memory_equiv_domain _ _ Hequiv loc)).
      apply (proj2 (spatial_merge_domain _ _ _ (proj2 (proj1 Hsplit)) loc)), Hdom.
    + intros i Hmark.
      assert (Hm : complete (proj1_sig marked) i) by (apply (proj2 Hsplit i); auto).
      destruct Hm as [Hm |E]; [left; apply Hmarks, Hm |right; exact E].
Qed.

Theorem owned_unlock_valid active invariant pre post owner :
  two_active_processors active -> invariant_fragment invariant ->
  (forall s (r : resource active),
    persistent_models active s r (A.Temporal pre (A.Barrier (EVal (Z.pos owner)))) ->
    persistent_models active s r (A.Spatial invariant post)) ->
  owned_valid active DisjointMode invariant (A.Spatial (A.Lock (EVal (Z.pos owner))) pre)
    (C.Prim C.Unlock (EVal (Z.pos owner))) post.
Proof.
  intros Htwo Hfragment Hent s local HP n; destruct n; [exact I |].
  intros later Hfuture.
  assert (HP' : persistent_models active s later (A.Spatial (A.Lock (EVal (Z.pos owner))) pre)).
  { eapply persistent_assertion_flushing_closed; eassumption. }
  split; [intros [annotation H]; discriminate |].
  intros pool frame whole phase Henv; split.
  - intros Hfault; inversion Hfault; subst.
    match goal with H : primitive_abort _ _ _ _ |- _ => inversion H end.
  - intros action next t whole' Hstep; inversion Hstep; subst.
    match goal with E : eval_expr _ (EVal (Z.pos owner)) = Z.pos _ |- _ => cbn in E; inversion E; subst end.
    match goal with H : primitive_step _ _ _ _ _ |- _ => inversion H; subst end.
    destruct (owned_unlock_transfer _ _ _ _ _ _ _ _ _ _ _ Htwo Hfragment Hent HP' Henv)
      as (local' & pool' & Henv' & Hupdate & HQ); [assumption |].
    exists local', pool', PoolFree; split; [exact Henv' |].
    split; [exact Hupdate |apply owned_done_safe, HQ].
Qed.
