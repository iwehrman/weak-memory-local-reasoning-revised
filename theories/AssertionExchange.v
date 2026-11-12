From Stdlib Require Import List ZArith.
From WMLR Require Import Expressions Machine BufferRelations Separation StableCompatibility
  RepairedSeparation Assertions AssertionSemantics ConcreteAssertions PersistentAssertions
  PersistentRules HeapRules TemporalSafety TemporalFence RegionalResources OwnedResources OwnedHeapResources
  AssertionResourceEquivalence AssertionUnits AssertionAlgebra AssertionBarrierAlgebra AssertionWriteAlgebra.
Import ListNotations.

(** Helpers for T7/T8. No program judgment or assertion grammar changes. *)
Lemma assertion_spatial_write_cannot_mix active a b whole loc owner value :
  memory_spatial (underlying a) (underlying b) whole ->
  write_atom active (Z.pos loc) (Z.pos owner) value b ->
  heap_domain (shared_heap whole) loc -> buffer_domain (buffers whole owner) loc -> False.
Proof.
  intros [[Hd Hk] [Hheap [Hbuffers Hblocks]]] HW [v Hv] [w Hw].
  pose proof (assertion_write_domain _ _ _ _ _ HW) as Hdom.
  destruct HW as [_ [[Hh [Hb HK]] |[Hh [Hb HK]]]].
  - apply (Hd loc); [left; exists v |exact Hdom].
    rewrite Hheap in Hv; unfold heap_override in Hv; rewrite Hh in Hv; exact Hv.
  - apply (Hd loc); [right; exists owner,w |exact Hdom].
    apply (interleaves_in _ _ _ _ (Hbuffers owner)) in Hw.
    destruct Hw as [H |H]; [exact H |rewrite Hb in H; contradiction].
Qed.

Definition exchange_bar active owner (Hi : active owner) :=
  mark_processor active (bare_resource active) owner Hi.
Definition exchange_pending active owner (Hi : active owner) :=
  owned_enqueue_resource active (exchange_bar active owner Hi) owner 1%positive 0%Z Hi.
Definition exchange_heap active owner (Hi : active owner) :=
  assertion_revalue_cell active (exchange_bar active owner Hi) 1%positive 0%Z owner (or_intror eq_refl).
Definition exchange_mixed active owner (Hi : active owner) :=
  owned_enqueue_resource active (exchange_heap active owner Hi) owner 1%positive 0%Z Hi.

Lemma exchange_pending_spatial_bar active owner Hi s :
  persistent_models active s (exchange_pending active owner Hi)
    (A.Spatial (A.Pure BTrue) (A.Barrier (EVal (Z.pos owner)))).
Proof.
  exists (exchange_pending active owner Hi),(exchange_bar active owner Hi); split.
  - split; [exact (proj1 (spatial_empty_right (proj1_sig (exchange_pending active owner Hi)))) |].
    intros i; cbn; unfold no_blocked; tauto.
  - split; [reflexivity |apply marked_emp_barrier,bare_resource_models].
Qed.

Lemma exchange_pending_not_temporal_bar active owner Hi s :
  ~ persistent_models active s (exchange_pending active owner Hi)
    (A.Temporal (A.Pure BTrue) (A.Barrier (EVal (Z.pos owner)))).
Proof.
  intros H; pose proof (assertion_barrier_suffix_buffer _ _ _ _ _ Hi H) as E.
  change (buffer_update empty_buffers owner [(1%positive,0%Z)] owner = []) in E.
  rewrite buffer_update_same in E; discriminate.
Qed.

Lemma exchange_mixed_temporal_write active owner Hi s :
  persistent_models active s (exchange_mixed active owner Hi)
    (A.Temporal (A.Pure BTrue) (A.LeadsTo (EVal 1%Z) (EVal (Z.pos owner)) (EVal 0%Z))).
Proof. apply owned_enqueue_temporal_post; [reflexivity |intros j Hne [v H]; contradiction]. Qed.

Lemma exchange_mixed_not_spatial_write active owner Hi s :
  ~ persistent_models active s (exchange_mixed active owner Hi)
    (A.Spatial (A.Pure BTrue) (A.LeadsTo (EVal 1%Z) (EVal (Z.pos owner)) (EVal 0%Z))).
Proof.
  intros (a & b & [Hsp Hmarks] & HP & HW).
  eapply assertion_spatial_write_cannot_mix; [exact Hsp |exact HW | |].
  - exists 0%Z; apply heap_update_same.
  - exists 0%Z; change (In (1%positive,0%Z) (buffer_update empty_buffers owner [(1%positive,0%Z)] owner)).
    rewrite buffer_update_same; left; reflexivity.
Qed.

(** Uniform inclusion between spatial and temporal conjunction would force
    the processor domain to be empty. No classical case split is used. *)
Theorem assertion_uniform_spatial_temporal_empty active :
  (forall p q, persistent_entails active (A.Spatial p q) (A.Temporal p q)) ->
  forall owner, ~ active owner.
Proof.
  intros H owner Hi; apply (exchange_pending_not_temporal_bar active owner Hi (fun _ => 0%Z)),H,
    exchange_pending_spatial_bar.
Qed.

Theorem assertion_uniform_temporal_spatial_empty active :
  (forall p q, persistent_entails active (A.Temporal p q) (A.Spatial p q)) ->
  forall owner, ~ active owner.
Proof.
  intros H owner Hi; apply (exchange_mixed_not_spatial_write active owner Hi (fun _ => 0%Z)),H,
    exchange_mixed_temporal_write.
Qed.

Lemma assertion_empty_domain_resource active : (forall i, ~ active i) -> forall r : resource active,
  generalized_equiv (proj1_sig r) empty_generalized.
Proof.
  intros Hnone r; destruct (proj2_sig r) as [[Hblocks Hbuffers] [Hmarks Hheap]].
  assert (Hnomarks : forall i, ~ complete (proj1_sig r) i) by (intros i H; apply (Hnone i),Hmarks,H).
  split.
  - split; [exact (Hheap Hnomarks) |]. split; [intros i; apply Hbuffers,Hnone |].
    intros i; split; [intros H; exfalso; apply (Hnone i),Hblocks,H |contradiction].
  - intros i; split; [intros H; exfalso; exact (Hnomarks i H) |contradiction].
Qed.

Lemma assertion_empty_domain_conjunction kind active p q s r : (forall i, ~ active i) ->
  (persistent_models active s r (assertion_conjunction kind p q) <->
    persistent_models active s r p /\ persistent_models active s r q).
Proof.
  intros Hnone.
  assert (Htransport : forall p a, persistent_models active s a p -> persistent_models active s r p).
  { intros f a H; apply (persistent_models_resource_equiv active f s (bare_resource active) r).
    - apply assertion_generalized_equiv_sym,assertion_empty_domain_resource,Hnone.
    - eapply persistent_models_resource_equiv; [apply assertion_empty_domain_resource,Hnone |exact H]. }
  assert (HE : empty_atom (proj1_sig r)).
  { pose proof (assertion_empty_domain_resource _ Hnone r) as [[Hh [Hb Hk]] Hm].
    split; [exact Hh |]. split; [exact Hb |intros i H; apply Hk in H; exact H]. }
  assert (Hsp : spatial (proj1_sig r) (proj1_sig r) (proj1_sig r)) by (apply assertion_empty_self_spatial,HE).
  assert (Htm : repaired_temporal active (proj1_sig r) (proj1_sig r) (proj1_sig r))
    by (apply assertion_spatial_empty_buffers_temporal; [exact Hsp |exact (proj1 (proj2 HE)) |exact (proj1 (proj2 HE))]).
  split.
  - destruct kind; intros H;
      [destruct H as (a & b & HS & HP & HQ) |destruct H as (a & b & HS & HP & HQ)
      |destruct H as [(a & b & HS & HP & HQ) HT]]; split; eapply Htransport; eassumption.
  - intros [HP HQ]; destruct kind; cbn [assertion_conjunction]; try (exists r,r; auto).
    split; exists r,r; auto.
Qed.

Theorem assertion_empty_domain_small_exchange bullet circle active p q t s r :
  (forall i, ~ active i) ->
  (persistent_models active s r (assertion_conjunction bullet p (assertion_conjunction circle q t)) <->
    persistent_models active s r (assertion_conjunction circle (assertion_conjunction bullet p q) t)) /\
  (persistent_models active s r (assertion_conjunction bullet (assertion_conjunction circle p q) t) <->
    persistent_models active s r (assertion_conjunction circle p (assertion_conjunction bullet q t))).
Proof.
  intros Hnone; repeat rewrite assertion_empty_domain_conjunction by exact Hnone; tauto.
Qed.

(** With emp as the middle formula, the literal premise always holds;
    either exchange conclusion would imply the missing connective inclusion. *)
Theorem assertion_emp_middle_exchange_countermodel bullet circle active p t s r :
  persistent_models active s r (assertion_conjunction bullet p t) ->
  ~ persistent_models active s r (assertion_conjunction circle p t) ->
  persistent_entails active (assertion_conjunction bullet p A.Emp) (assertion_conjunction circle p A.Emp) /\
  persistent_models active s r (assertion_conjunction bullet p (assertion_conjunction circle A.Emp t)) /\
  ~ persistent_models active s r (assertion_conjunction circle (assertion_conjunction bullet p A.Emp) t) /\
  persistent_models active s r (assertion_conjunction bullet (assertion_conjunction circle p A.Emp) t) /\
  ~ persistent_models active s r (assertion_conjunction circle p (assertion_conjunction bullet A.Emp t)).
Proof.
  intros HP Hnot.
  assert (HRintro : forall k f, persistent_entails active f (assertion_conjunction k f A.Emp))
    by (intros k f u a H; apply (proj2 (assertion_conjunction_unit_right k active f u a)),H).
  assert (HRelim : forall k f, persistent_entails active (assertion_conjunction k f A.Emp) f)
    by (intros k f u a H; apply (proj1 (assertion_conjunction_unit_right k active f u a)),H).
  assert (HLintro : forall k f, persistent_entails active f (assertion_conjunction k A.Emp f))
    by (intros k f u a H; apply (proj2 (assertion_conjunction_unit_left k active f u a)),H).
  assert (HLelim : forall k f, persistent_entails active (assertion_conjunction k A.Emp f) f)
    by (intros k f u a H; apply (proj1 (assertion_conjunction_unit_left k active f u a)),H).
  split; [intros u a H; exact (HRintro circle p u a (HRelim bullet p u a H)) |].
  split; [eapply assertion_conjunction_mono; [intros u a H; exact H |apply HLintro |exact HP] |].
  split; [intros H; apply Hnot; eapply assertion_conjunction_mono; [apply HRelim |intros u a HA; exact HA |exact H] |].
  split; [eapply assertion_conjunction_mono; [apply HRintro |intros u a H; exact H |exact HP] |].
  intros H; apply Hnot; eapply assertion_conjunction_mono; [intros u a HA; exact HA |apply HLelim |exact H].
Qed.

Theorem assertion_literal_exchange_spatial_refuted active owner (Hi : active owner) circle :
  circle = TemporalKind \/ circle = StrongKind ->
  ~ (forall p q t, persistent_entails active (A.Spatial p q) (assertion_conjunction circle p q) ->
    persistent_entails active (A.Spatial p (assertion_conjunction circle q t))
      (assertion_conjunction circle (A.Spatial p q) t)) /\
  ~ (forall p q t, persistent_entails active (A.Spatial p q) (assertion_conjunction circle p q) ->
    persistent_entails active (A.Spatial (assertion_conjunction circle p q) t)
      (assertion_conjunction circle p (A.Spatial q t))).
Proof.
  intros Hcircle.
  assert (Hnot : ~ persistent_models active (fun _ => 0%Z) (exchange_pending active owner Hi)
    (assertion_conjunction circle (A.Pure BTrue) (A.Barrier (EVal (Z.pos owner))))).
  { destruct Hcircle as [-> | ->]; [apply exchange_pending_not_temporal_bar
      |intros [_ H]; exact (exchange_pending_not_temporal_bar _ _ _ _ H)]. }
  destruct (assertion_emp_middle_exchange_countermodel SpatialKind circle active _ _ _ _
    (exchange_pending_spatial_bar active owner Hi (fun _ => 0%Z)) Hnot)
    as (Hprem & HL & HNL & HR & HNR).
  split; intros H; [apply HNL |apply HNR]; eapply H; eassumption.
Qed.

Theorem assertion_literal_exchange_temporal_refuted active owner (Hi : active owner) circle :
  circle = SpatialKind \/ circle = StrongKind ->
  ~ (forall p q t, persistent_entails active (A.Temporal p q) (assertion_conjunction circle p q) ->
    persistent_entails active (A.Temporal p (assertion_conjunction circle q t))
      (assertion_conjunction circle (A.Temporal p q) t)) /\
  ~ (forall p q t, persistent_entails active (A.Temporal p q) (assertion_conjunction circle p q) ->
    persistent_entails active (A.Temporal (assertion_conjunction circle p q) t)
      (assertion_conjunction circle p (A.Temporal q t))).
Proof.
  intros Hcircle.
  assert (Hnot : ~ persistent_models active (fun _ => 0%Z) (exchange_mixed active owner Hi)
    (assertion_conjunction circle (A.Pure BTrue) (A.LeadsTo (EVal 1%Z) (EVal (Z.pos owner)) (EVal 0%Z)))).
  { destruct Hcircle as [-> | ->]; [apply exchange_mixed_not_spatial_write
      |intros [H _]; exact (exchange_mixed_not_spatial_write _ _ _ _ H)]. }
  destruct (assertion_emp_middle_exchange_countermodel TemporalKind circle active _ _ _ _
    (exchange_mixed_temporal_write active owner Hi (fun _ => 0%Z)) Hnot)
    as (Hprem & HL & HNL & HR & HNR).
  split; intros H; [apply HNL |apply HNR]; eapply H; eassumption.
Qed.

Theorem assertion_uniform_incomparable_empty bullet circle active :
  (bullet = SpatialKind /\ (circle = TemporalKind \/ circle = StrongKind)) \/
  (bullet = TemporalKind /\ (circle = SpatialKind \/ circle = StrongKind)) ->
  (forall p q, persistent_entails active (assertion_conjunction bullet p q) (assertion_conjunction circle p q)) ->
  forall owner, ~ active owner.
Proof.
  intros [[-> [-> | ->]] |[-> [-> | ->]]] H.
  - apply assertion_uniform_spatial_temporal_empty,H.
  - apply assertion_uniform_spatial_temporal_empty; intros p q s r HP; exact (proj2 (H p q s r HP)).
  - apply assertion_uniform_temporal_spatial_empty,H.
  - apply assertion_uniform_temporal_spatial_empty; intros p q s r HP; exact (proj1 (H p q s r HP)).
Qed.

Theorem assertion_uniform_incomparable_exchange bullet circle active :
  (bullet = SpatialKind /\ (circle = TemporalKind \/ circle = StrongKind)) \/
  (bullet = TemporalKind /\ (circle = SpatialKind \/ circle = StrongKind)) ->
  (forall p q, persistent_entails active (assertion_conjunction bullet p q) (assertion_conjunction circle p q)) ->
  (forall p q t, persistent_entails active
    (assertion_conjunction bullet p (assertion_conjunction circle q t))
    (assertion_conjunction circle (assertion_conjunction bullet p q) t)) /\
  (forall p q t, persistent_entails active
    (assertion_conjunction bullet (assertion_conjunction circle p q) t)
    (assertion_conjunction circle p (assertion_conjunction bullet q t))).
Proof.
  intros Hkinds H; pose proof (assertion_uniform_incomparable_empty _ _ _ Hkinds H) as Hnone.
  split; intros p q t s r HP;
    [apply (proj1 (proj1 (assertion_empty_domain_small_exchange bullet circle active p q t s r Hnone)))
    |apply (proj1 (proj2 (assertion_empty_domain_small_exchange bullet circle active p q t s r Hnone)))]; exact HP.
Qed.

Lemma assertion_enqueue_spatial active s local p actor loc value (Hi : active actor) :
  persistent_models active s local p -> ~ memory_domain (resource_memory active local) loc ->
  persistent_models active s (owned_enqueue_resource active local actor loc value Hi)
    (A.Spatial p (A.LeadsTo (EVal (Z.pos loc)) (EVal (Z.pos actor)) (EVal value))).
Proof.
  intros HP Hfresh; exists local,(pending_write_resource active actor loc value Hi); split.
  - split; [split |intros i; cbn; unfold no_blocked; tauto].
    + split.
      * intros address Hlocal [[v Hheap] |[i [v Hbuf]]]; [discriminate |].
        change (In (address,v) (buffer_update empty_buffers actor [(loc,value)] i)) in Hbuf.
        unfold buffer_update in Hbuf; destruct (Pos.eq_dec i actor); [|contradiction].
        destruct Hbuf as [E |H]; [inversion E; subst; exact (Hfresh Hlocal) |contradiction].
      * intros i _ H; contradiction.
    + split; [intros; reflexivity |]. split.
      * intros i; cbn [owned_enqueue_resource pending_write_resource proj1_sig underlying enqueue buffers pending_write_memory].
        unfold buffer_update; destruct (Pos.eq_dec i actor); subst; [apply interleaves_app |].
        change (interleaves (buffers (resource_memory active local) i) [] (buffers (resource_memory active local) i)).
        rewrite <- (app_nil_r (buffers (resource_memory active local) i)) at 2; apply interleaves_app.
      * intros i; cbn; unfold no_blocked; tauto.
  - split; [exact HP |]. split; [exact Hi |left].
    split; [intros; reflexivity |]. split; [intros; reflexivity |intros i H; contradiction].
Qed.
