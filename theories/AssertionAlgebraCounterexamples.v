From Stdlib Require Import List ZArith.
From WMLR Require Import Expressions Machine BufferRelations Separation StableCompatibility
  RepairedSeparation Assertions AssertionSemantics ConcreteAssertions PersistentAssertions
  PersistentRules TemporalSafety TemporalFence RegionalResources ExecutionExamples
  OwnershipProtocol OwnedSafety OwnedAdequacy OwnedResources OwnedHeapResources OwnedAcceptance OwnedContainerEntailments
  AssertionUnits AssertionAlgebra.
Import ListNotations.

(** E3 countermodel: one address, one value and one buffered write. *)
Definition algebra_bar := mark_processor two_processors (bare_resource two_processors)
  1%positive (or_introl eq_refl).
Definition algebra_heap := acceptance_cell 1%positive 0%Z 1%positive (or_introl eq_refl).
Definition algebra_pending := owned_enqueue_resource two_processors algebra_bar
  1%positive 1%positive 0%Z (or_introl eq_refl).
Definition algebra_whole := owned_enqueue_resource two_processors algebra_heap
  1%positive 1%positive 0%Z (or_introl eq_refl).
Definition algebra_P := A.Pure BTrue.
Definition algebra_Q := A.Barrier (EVal 1%Z).
Definition algebra_W := A.LeadsTo (EVal 1%Z) (EVal 1%Z) (EVal 0%Z).
Definition algebra_R := A.Or A.Emp algebra_W.

Lemma algebra_bar_models s : persistent_models two_processors s algebra_bar algebra_Q.
Proof. apply marked_emp_barrier, bare_resource_models. Qed.

Lemma algebra_bar_inner_models s :
  persistent_models two_processors s algebra_bar (A.strong_temporal algebra_Q algebra_R).
Proof.
  eapply assertion_conjunction_mono with (kind := StrongKind) (p := algebra_Q) (q := A.Emp).
  - intros t r H; exact H.
  - intros t r H; left; exact H.
  - apply (proj2 (assertion_unit_strong_right _ _ _ _)),algebra_bar_models.
Qed.

Lemma algebra_pending_inner_models s :
  persistent_models two_processors s algebra_pending (A.strong_temporal algebra_Q algebra_R).
Proof.
  assert (H : persistent_models two_processors s algebra_pending (A.Temporal algebra_Q algebra_W)).
  { apply owned_enqueue_temporal_post; [apply algebra_bar_models |intros j Hne [v H]; contradiction]. }
  destruct H as (a & b & Htm & HQ & HW); split; exists a,b; split.
  - apply (assertion_temporal_empty_left_spatial two_processors); [exact (proj1 HQ) |exact Htm].
  - split; [exact HQ |right; exact HW].
  - exact Htm.
  - split; [exact HQ |right; exact HW].
Qed.

Lemma algebra_whole_spatial_bar :
  spatial (proj1_sig algebra_whole) (proj1_sig algebra_bar) (proj1_sig algebra_whole).
Proof.
  split; [exact (proj1 (spatial_empty_right (proj1_sig algebra_whole))) |].
  intros i; change (i = 1%positive <-> i = 1%positive \/ False \/ i = 1%positive); tauto.
Qed.

Lemma algebra_heap_pending_temporal :
  repaired_temporal two_processors (proj1_sig algebra_heap) (proj1_sig algebra_pending)
    (proj1_sig algebra_whole).
Proof.
  assert (Hstable : stable_compatible two_processors
    (resource_memory two_processors algebra_heap) (resource_memory two_processors algebra_pending)).
  { split; [intros i H; contradiction |]. split;
      [intros i _ loc [v H]; contradiction |intros i j _ _ _ loc [v H]; contradiction]. }
  split; [exact Hstable |]. split.
  - split; [apply stable_implies_printed_compatible,Hstable |].
    split; [intros; reflexivity |]. split; [intros; reflexivity |intros i; cbn; tauto].
  - split; [intros; reflexivity |].
    intros i; change (i = 1%positive <-> i = 1%positive \/ False \/ i = 1%positive); tauto.
Qed.

Theorem assertion_strong_associativity_right_model s :
  persistent_models two_processors s algebra_whole
    (A.strong_temporal algebra_P (A.strong_temporal algebra_Q algebra_R)).
Proof.
  split.
  - exists algebra_whole,algebra_bar; split; [apply algebra_whole_spatial_bar |].
    split; [reflexivity |apply algebra_bar_inner_models].
  - exists algebra_heap,algebra_pending; split; [apply algebra_heap_pending_temporal |].
    split; [reflexivity |apply algebra_pending_inner_models].
Qed.

Lemma assertion_strong_associativity_left_spatial_not_model s :
  ~ persistent_models two_processors s algebra_whole
    (A.Spatial (A.strong_temporal algebra_P algebra_Q) algebra_R).
Proof.
  intros (a & b & [[Hdis [Hheap [Hbuffers Hblocks]]] Hmarks] & [_ Hbar] & HR).
  assert (Ha : buffers (resource_memory two_processors a) 1%positive = []).
  { eapply assertion_barrier_suffix_buffer; [left; reflexivity |exact Hbar]. }
  specialize (Hbuffers 1%positive); change (interleaves
    (buffers (resource_memory two_processors a) 1%positive)
    (buffers (resource_memory two_processors b) 1%positive) [(1%positive,0%Z)]) in Hbuffers.
  rewrite Ha in Hbuffers; apply interleaves_nil_left in Hbuffers.
  destruct HR as [[Hh [Hb Hk]] |[_ [[Hh [Hb Hk]] |[Hh [Hb Hk]]]]].
  - rewrite Hb in Hbuffers; discriminate.
  - apply (proj1 Hdis 1%positive).
    + left; exists 0%Z; specialize (Hheap 1%positive).
      change (Some 0%Z = heap_override (shared_heap (resource_memory two_processors a))
        (shared_heap (resource_memory two_processors b)) 1%positive) in Hheap.
      unfold heap_override in Hheap; rewrite Hh in Hheap; symmetry; exact Hheap.
    + right; exists 1%positive,0%Z.
      change (In (1%positive,0%Z) (buffers (resource_memory two_processors b) 1%positive)).
      rewrite <- Hbuffers; left; reflexivity.
  - rewrite Hb in Hbuffers; discriminate.
Qed.

Theorem assertion_strong_associativity_left_not_model s :
  ~ persistent_models two_processors s algebra_whole
    (A.strong_temporal (A.strong_temporal algebra_P algebra_Q) algebra_R).
Proof. intros [H _]; exact (assertion_strong_associativity_left_spatial_not_model s H). Qed.

Theorem assertion_associativity_countermodel_environment mode s :
  owned_environment two_processors mode A.Emp s algebra_whole empty_memory
    (empty_resource_value two_processors) (resource_memory two_processors algebra_whole) PoolFree.
Proof.
  apply owned_empty_frame_intro.
  - exact (proj1 (empty_generalized_well_formed two_processors)).
  - exact (proj1 (spatial_empty_left (proj1_sig algebra_whole))).
  - split; [intros i H; exact H |apply protocol_empty_satisfies].
Qed.

Corollary assertion_strong_associativity_refuted :
  ~ persistent_entails two_processors
    (A.strong_temporal algebra_P (A.strong_temporal algebra_Q algebra_R))
    (A.strong_temporal (A.strong_temporal algebra_P algebra_Q) algebra_R).
Proof.
  intros H; apply (assertion_strong_associativity_left_not_model (fun _ => 0%Z)),H,
    assertion_strong_associativity_right_model.
Qed.

(** T7 with both schematic connectives equal to strong-temporal. Even the
    stronger uniform inclusion premise is reflexivity for this instance. *)
Corollary assertion_small_exchange_strong_refuted :
  (forall p q, persistent_entails two_processors (A.strong_temporal p q) (A.strong_temporal p q)) /\
  ~ persistent_entails two_processors
    (A.strong_temporal algebra_P (A.strong_temporal algebra_Q algebra_R))
    (A.strong_temporal (A.strong_temporal algebra_P algebra_Q) algebra_R).
Proof. split; [intros p q s r H; exact H |apply assertion_strong_associativity_refuted]. Qed.

(** E6 countermodel: no heap, no buffers, no marks. Opposite lock atoms
    have disjoint blocked bits when there are exactly two processors. *)
Definition algebra_lock_resource owner (Hi : two_processors owner) : resource two_processors.
Proof.
  refine (exist _ (Generalized (Memory empty_heap empty_buffers (blocked_except two_processors owner))
    no_blocked) _).
  split; [split; [intros i [H _]; exact H |intros; reflexivity] |].
  split; [intros i H; contradiction |intros; reflexivity].
Defined.

Definition algebra_both_blocked : resource two_processors.
Proof.
  refine (exist _ (Generalized (Memory empty_heap empty_buffers two_processors) no_blocked) _).
  split; [split; [auto |intros; reflexivity] |].
  split; [intros i H; contradiction |intros; reflexivity].
Defined.

Lemma algebra_lock_models owner Hi s :
  persistent_models two_processors s (algebra_lock_resource owner Hi) (A.Lock (EVal (Z.pos owner))).
Proof. split; [intros; reflexivity |]. split; [intros; reflexivity |split; [exact Hi |intros; reflexivity]]. Qed.

Lemma algebra_lock_split :
  spatial (proj1_sig (algebra_lock_resource 1%positive (or_introl eq_refl)))
    (proj1_sig (algebra_lock_resource 2%positive (or_intror eq_refl))) (proj1_sig algebra_both_blocked) /\
  repaired_temporal two_processors (proj1_sig (algebra_lock_resource 1%positive (or_introl eq_refl)))
    (proj1_sig (algebra_lock_resource 2%positive (or_intror eq_refl))) (proj1_sig algebra_both_blocked).
Proof.
  assert (Hcompat : spatial_compatible
    (resource_memory two_processors (algebra_lock_resource 1%positive (or_introl eq_refl)))
    (resource_memory two_processors (algebra_lock_resource 2%positive (or_intror eq_refl)))).
  { split.
    - intros loc [[v H] |[i [v H]]]; discriminate || contradiction.
    - intros i [[-> | ->] H1] [H2 Hne]; contradiction. }
  assert (Hblocks : forall i, two_processors i <->
    blocked_except two_processors 1%positive i \/ blocked_except two_processors 2%positive i).
  { intros i; unfold blocked_except; split.
    - intros [-> | ->]; [right |left]; split; [left; reflexivity |discriminate |right; reflexivity |discriminate].
    - intros [[H _] |[H _]]; exact H. }
  split.
  - split; [split; [exact Hcompat |] |intros i; cbn; tauto].
    split; [intros; reflexivity |]. split; [intros; constructor |exact Hblocks].
  - split; [apply spatial_compatible_stable,Hcompat |]. split.
    + split; [apply spatial_compatible_temporal,Hcompat |].
      split; [intros; reflexivity |]. split; [intros; reflexivity |exact Hblocks].
    + split; [intros; reflexivity |intros i; cbn; tauto].
Qed.

Theorem assertion_lock_multiplication_model kind s :
  persistent_models two_processors s algebra_both_blocked
    (assertion_conjunction kind (A.Lock (EVal 1%Z)) (A.Lock (EVal 2%Z))).
Proof.
  assert (Hsp : persistent_models two_processors s algebra_both_blocked
    (A.Spatial (A.Lock (EVal 1%Z)) (A.Lock (EVal 2%Z)))).
  { exists (algebra_lock_resource 1%positive (or_introl eq_refl)),
      (algebra_lock_resource 2%positive (or_intror eq_refl));
      split; [exact (proj1 algebra_lock_split) |split; apply algebra_lock_models]. }
  assert (Htm : persistent_models two_processors s algebra_both_blocked
    (A.Temporal (A.Lock (EVal 1%Z)) (A.Lock (EVal 2%Z)))).
  { exists (algebra_lock_resource 1%positive (or_introl eq_refl)),
      (algebra_lock_resource 2%positive (or_intror eq_refl));
      split; [exact (proj2 algebra_lock_split) |split; apply algebra_lock_models]. }
  destruct kind; cbn; tauto.
Qed.

Corollary assertion_lock_multiplication_refuted kind :
  ~ persistent_entails two_processors
    (assertion_conjunction kind (A.Lock (EVal 1%Z)) (A.Lock (EVal 2%Z))) (A.Pure BFalse).
Proof.
  intros H; specialize (H (fun _ => 0%Z) algebra_both_blocked
    (assertion_lock_multiplication_model kind (fun _ => 0%Z))); discriminate.
Qed.

Theorem assertion_lock_countermodel_not_lock_complete :
  ~ lock_complete two_processors (resource_memory two_processors algebra_both_blocked).
Proof.
  intros [Hfree |[owner [Hi Hheld]]].
  - apply (Hfree 1%positive); left; reflexivity.
  - apply (proj1 (Hheld owner)) in Hi; destruct Hi as [_ Hne]; contradiction.
Qed.

Theorem assertion_lock_countermodel_no_environment mode invariant s pool frame whole phase :
  ~ owned_environment two_processors mode invariant s algebra_both_blocked pool frame whole phase.
Proof.
  intros Henv; pose proof (fun i => owned_blocked_union _ _ _ _ _ _ _ _ _ i Henv) as Hblocks.
  destruct Henv as [_ _ _ _ Hstatus]; destruct phase as [|owner]; cbn [pool_status] in Hstatus.
  - destruct Hstatus as [Hfree Hpool]; apply (Hfree 1%positive),Hblocks.
    right; right; left; reflexivity.
  - destruct Hstatus as [[Hi Hheld] Hpool].
    assert (Hblocked : blocked whole owner) by (apply Hblocks; right; right; exact Hi).
    apply Hheld in Hblocked; destruct Hblocked as [_ Hne]; contradiction.
Qed.

(** Both countermodels also refute the laws in the printed interpretation.
    They are not introduced by future-aware wands or stable compatibility. *)
Theorem assertion_strong_associativity_printed_right_model s :
  models two_processors s algebra_whole
    (A.strong_temporal algebra_P (A.strong_temporal algebra_Q algebra_R)).
Proof.
  apply assertion_wand_free_in_printed; [repeat split; exact I |apply assertion_strong_associativity_right_model].
Qed.

Theorem assertion_strong_associativity_printed_left_not_model s :
  ~ models two_processors s algebra_whole
    (A.strong_temporal (A.strong_temporal algebra_P algebra_Q) algebra_R).
Proof.
  intros [(a & b & [[Hdis [Hheap [Hbuffers Hblocks]]] Hmarks] & [_ Hbar] & HR) _].
  assert (Ha : buffers (resource_memory two_processors a) 1%positive = []).
  { destruct Hbar as (c & d & [[_ [_ [Hb _]]] [Hbefore _]] & HP & HE & [Hno |Hmark]).
    - exfalso; apply Hno; left; reflexivity.
    - unfold resource_memory; rewrite Hb, Hbefore by exact Hmark.
      rewrite (proj1 (proj2 HE) 1%positive); reflexivity. }
  specialize (Hbuffers 1%positive); change (interleaves
    (buffers (resource_memory two_processors a) 1%positive)
    (buffers (resource_memory two_processors b) 1%positive) [(1%positive,0%Z)]) in Hbuffers.
  rewrite Ha in Hbuffers; apply interleaves_nil_left in Hbuffers.
  destruct HR as [[Hh [Hb Hk]] |[_ [[Hh [Hb Hk]] |[Hh [Hb Hk]]]]].
  - rewrite Hb in Hbuffers; discriminate.
  - apply (proj1 Hdis 1%positive).
    + left; exists 0%Z; specialize (Hheap 1%positive).
      change (Some 0%Z = heap_override (shared_heap (resource_memory two_processors a))
        (shared_heap (resource_memory two_processors b)) 1%positive) in Hheap.
      unfold heap_override in Hheap; rewrite Hh in Hheap; symmetry; exact Hheap.
    + right; exists 1%positive,0%Z.
      change (In (1%positive,0%Z) (buffers (resource_memory two_processors b) 1%positive)).
      rewrite <- Hbuffers; left; reflexivity.
  - rewrite Hb in Hbuffers; discriminate.
Qed.

Theorem assertion_lock_multiplication_printed_model kind s :
  models two_processors s algebra_both_blocked
    (assertion_conjunction kind (A.Lock (EVal 1%Z)) (A.Lock (EVal 2%Z))).
Proof.
  apply assertion_wand_free_in_printed; [destruct kind; repeat split; exact I |apply assertion_lock_multiplication_model].
Qed.
