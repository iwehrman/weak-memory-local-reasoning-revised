From Stdlib Require Import List ZArith.
From WMLR Require Import Expressions Machine BufferRelations Separation StableCompatibility
  RepairedSeparation SpatialExchange Assertions AssertionSemantics ConcreteAssertions PersistentAssertions
  PersistentRules TemporalSafety RegionalResources OwnedResources OwnedHeapResources OwnedAcceptance
  ExecutionExamples OwnedContainerEntailments AssertionAlgebra AssertionBarrierAlgebra
  AssertionWriteAlgebra AssertionAlgebraCounterexamples AssertionExchange AssertionExchangeRight.
Import ListNotations.

(** T8 with strong-temporal outside and temporal inside. The witness has
    two allocated cells, one pending write and just processor 1's mark. *)
Lemma assertion_strong_write_single_mark_heap_empty active owner loc value s r p :
  (forall i, complete (proj1_sig r) i -> i = owner) ->
  buffer_domain (buffers (resource_memory active r) owner) loc ->
  persistent_models active s r
    (A.strong_temporal (A.LeadsTo (EVal (Z.pos loc)) (EVal (Z.pos owner)) (EVal value)) p) ->
  forall address, shared_heap (resource_memory active r) address = None.
Proof.
  intros Hmarks Hpending [(a & b & [Hsp Hspmarks] & HW & HP) HT].
  assert (Habsent : shared_heap (resource_memory active r) loc = None).
  { destruct (shared_heap (resource_memory active r) loc) as [v|] eqn:E; [|reflexivity].
    exfalso; eapply assertion_spatial_write_cannot_mix with (a := proj1_sig b) (b := proj1_sig a).
    - exact (proj1 (spatial_comm _ _ _ (conj Hsp Hspmarks))).
    - exact HW.
    - exists v; exact E.
    - exact Hpending. }
  destruct HT as (c & d & [_ [[Hcompat [Hheap [Hbuffers Hblocks]]] [Hbefore Hunion]]] & HC & HD).
  destruct HC as [_ [[Hch [Hcb Hck]] |[Hch [Hcb Hck]]]].
  - assert (Hnone : forall i, ~ complete (proj1_sig d) i).
    { intros i Hi; assert (E : i = owner) by (apply Hmarks,Hunion; right; exact Hi).
      subst i; specialize (Hbefore owner Hi); rewrite Hcb,buffer_update_same in Hbefore; discriminate. }
    pose proof (proj2 (proj2 (proj2_sig d)) Hnone) as Hdh.
    intros address; unfold resource_memory; rewrite Hheap; unfold heap_override; rewrite Hdh,Hch; reflexivity.
  - specialize (Hheap loc); unfold resource_memory in Habsent; rewrite Habsent in Hheap.
    unfold heap_override in Hheap; rewrite Hch,heap_update_same in Hheap.
    destruct (shared_heap (underlying (proj1_sig d)) loc); discriminate.
Qed.

Definition exchange_temporal_right_heap : resource two_processors.
Proof.
  refine (exist _ (Generalized
    (Memory (heap_update (heap_update empty_heap 1%positive 0%Z) 2%positive 0%Z)
      empty_buffers no_blocked) (fun i => i = 1%positive)) _).
  split; [split; [intros i H; contradiction |intros; reflexivity] |].
  split; [intros i ->; left; reflexivity |].
  intros Hnone loc; exfalso; apply (Hnone 1%positive); reflexivity.
Defined.

Definition exchange_temporal_right_whole := owned_enqueue_resource two_processors
  exchange_temporal_right_heap 1%positive 1%positive 0%Z (or_introl eq_refl).

Lemma exchange_temporal_right_spatial :
  spatial (proj1_sig algebra_whole) (proj1_sig exchange_right_cell)
    (proj1_sig exchange_temporal_right_whole).
Proof.
  split; [split |intros i; cbn; tauto].
  - split.
    + intros loc Hleft Hright; apply acceptance_cell_domain in Hright; subst loc.
      destruct Hleft as [[v H] |[i [v H]]]; [discriminate |].
      change (In (2%positive,v) (buffer_update empty_buffers 1%positive [(1%positive,0%Z)] i)) in H.
      unfold buffer_update in H; destruct (Pos.eq_dec i 1%positive);
        [destruct H; [discriminate |contradiction] |contradiction].
    + intros i H; contradiction.
  - split.
    + intros loc; change (heap_update (heap_update empty_heap 1%positive 0%Z) 2%positive 0%Z loc =
        heap_override (heap_update empty_heap 1%positive 0%Z) (heap_update empty_heap 2%positive 0%Z) loc).
      unfold heap_update,heap_override,empty_heap; destruct (Pos.eq_dec loc 2%positive); reflexivity.
    + split.
      * intros i; change (interleaves (buffer_update empty_buffers 1%positive [(1%positive,0%Z)] i) []
          (buffer_update empty_buffers 1%positive [(1%positive,0%Z)] i)).
        apply interleaves_comm; exact (interleaves_app [] _).
      * intros i; cbn; unfold no_blocked; tauto.
Qed.

Lemma exchange_temporal_right_temporal :
  repaired_temporal two_processors (proj1_sig algebra_heap) (proj1_sig exchange_right_first)
    (proj1_sig exchange_temporal_right_whole).
Proof.
  assert (Hstable : stable_compatible two_processors
    (resource_memory two_processors algebra_heap) (resource_memory two_processors exchange_right_first)).
  { split; [intros i H; contradiction |]. split;
      [intros i _ loc [v H]; contradiction |intros i j _ _ _ loc [v H]; contradiction]. }
  split; [exact Hstable |]. split.
  - split; [apply stable_implies_printed_compatible,Hstable |]. split.
    + exact (proj1 (proj2 (proj1 exchange_temporal_right_spatial))).
    + split; [intros; reflexivity |intros i; cbn; unfold no_blocked; tauto].
  - split; [intros; reflexivity |intros i; cbn; tauto].
Qed.

Lemma exchange_temporal_right_heap_double_write s :
  persistent_models two_processors s algebra_heap (A.Temporal algebra_W algebra_W).
Proof.
  assert (HW : persistent_models two_processors s algebra_heap (A.Temporal algebra_W algebra_Q)).
  { eapply assertion_write_barrier_from_shape with (loc := 1%positive) (owner := 1%positive);
      [reflexivity |reflexivity |left; reflexivity |].
    split; [intros; reflexivity |]. split; [intros; reflexivity |]. split; [intros i H; exact H |reflexivity]. }
  apply (proj2 (assertion_successive_writes_collapse two_processors (EVal 1%Z) (EVal 1%Z)
    (EVal 0%Z) (EVal 0%Z) s algebra_heap)) in HW.
  eapply assertion_barrier_suffix_elim; exact HW.
Qed.

Theorem assertion_exchange_strong_temporal_right_model s :
  persistent_models two_processors s exchange_temporal_right_whole
    (A.strong_temporal (A.Temporal algebra_W algebra_W) algebra_P).
Proof.
  split.
  - exists algebra_whole,exchange_right_cell; split; [apply exchange_temporal_right_spatial |].
    split; [|reflexivity]. apply owned_enqueue_temporal_post.
    + split; [left; reflexivity |right]. split; [intros; reflexivity |].
      split; [intros; reflexivity |]. split; [intros i H; exact H |reflexivity].
    + intros i Hne [v H]; contradiction.
  - exists algebra_heap,exchange_right_first; split; [apply exchange_temporal_right_temporal |].
    split; [apply exchange_temporal_right_heap_double_write |reflexivity].
Qed.

Theorem assertion_exchange_strong_temporal_right_not_model s :
  ~ persistent_models two_processors s exchange_temporal_right_whole
    (A.Temporal algebra_W (A.strong_temporal algebra_W algebra_P)).
Proof.
  intros (a & b & [_ [[Hcompat [Hheap [Hbuffers Hblocks]]] [Hbefore Hmarks]]] & HW & Hinner).
  assert (Hbmarks : forall i, complete (proj1_sig b) i -> i = 1%positive).
  { intros i Hi; apply (proj2 (Hmarks i)); right; exact Hi. }
  assert (Hbcell : shared_heap (resource_memory two_processors b) 2%positive = Some 0%Z).
  { destruct HW as [_ [[Hh _] |[Hh _]]]; specialize (Hheap 2%positive);
      change (Some 0%Z = heap_override (shared_heap (underlying (proj1_sig a)))
        (shared_heap (underlying (proj1_sig b))) 2%positive) in Hheap;
      unfold heap_override in Hheap; rewrite Hh in Hheap;
      destruct (shared_heap (underlying (proj1_sig b)) 2%positive) eqn:E;
      try discriminate; unfold resource_memory; congruence. }
  destruct HW as [_ [[Hh [Hb HK]] |[Hh [Hb HK]]]].
  - assert (Hnone : forall i, ~ complete (proj1_sig b) i).
    { intros i Hi; pose proof (Hbmarks i Hi); subst i.
      specialize (Hbefore 1%positive Hi); rewrite Hb,buffer_update_same in Hbefore; discriminate. }
    pose proof (proj2 (proj2 (proj2_sig b)) Hnone 2%positive) as E.
    change (shared_heap (resource_memory two_processors b) 2%positive = None) in E.
    rewrite E in Hbcell; discriminate.
  - assert (Hpending : buffer_domain (buffers (resource_memory two_processors b) 1%positive) 1%positive).
    { exists 0%Z; specialize (Hbuffers 1%positive); rewrite Hb in Hbuffers.
      change ([(1%positive,0%Z)] = buffers (resource_memory two_processors b) 1%positive) in Hbuffers.
      rewrite <- Hbuffers; left; reflexivity. }
    pose proof (assertion_strong_write_single_mark_heap_empty two_processors 1%positive 1%positive 0%Z
      s b algebra_P Hbmarks Hpending Hinner 2%positive) as E; rewrite E in Hbcell; discriminate.
Qed.

Theorem assertion_small_exchange_strong_temporal_right_refuted :
  (forall p q, persistent_entails two_processors (A.strong_temporal p q) (A.Temporal p q)) /\
  ~ persistent_entails two_processors
    (A.strong_temporal (A.Temporal algebra_W algebra_W) algebra_P)
    (A.Temporal algebra_W (A.strong_temporal algebra_W algebra_P)).
Proof.
  split; [apply assertion_strong_entails_temporal |].
  intros H; apply (assertion_exchange_strong_temporal_right_not_model (fun _ => 0%Z)),H,
    assertion_exchange_strong_temporal_right_model.
Qed.
