From Stdlib Require Import List ZArith.
From WMLR Require Import Expressions Machine BufferRelations Separation StableCompatibility RepairedSeparation
  Assertions AssertionSemantics ConcreteAssertions PersistentAssertions PersistentRules
  TemporalSafety RegionalResources OwnershipHeap OwnedRules ExecutionExamples OwnedContainerEntailments
  AssertionAlgebra AssertionAlgebraCounterexamples AssertionLockAlgebra AssertionExchange.
Import ListNotations.

Definition exchange_temporal_token := acquired_resource two_processors algebra_bar 1%positive.
Definition exchange_temporal_pending := acquired_resource two_processors algebra_pending 1%positive.
Definition exchange_temporal_whole := acquired_resource two_processors algebra_whole 1%positive.
Definition exchange_temporal_lock := A.Lock (EVal 1%Z).
Definition exchange_temporal_Q := A.Or exchange_temporal_lock algebra_W.
Definition exchange_temporal_R := A.Or algebra_Q exchange_temporal_lock.

Lemma exchange_temporal_token_inner s :
  persistent_models two_processors s exchange_temporal_token (A.Temporal exchange_temporal_Q exchange_temporal_R).
Proof.
  eapply container_temporal_mono with (p := exchange_temporal_lock) (q := algebra_Q);
    [intros t r H; left; exact H |intros t r H; left; exact H |].
  apply owned_barrier_suffix_intro; [left; reflexivity | |reflexivity |right; reflexivity].
  split; [intros; reflexivity |]. split; [intros; reflexivity |].
  split; [left; reflexivity |intros; reflexivity].
Qed.

Lemma exchange_temporal_pending_inner s :
  persistent_models two_processors s exchange_temporal_pending (A.Temporal exchange_temporal_Q exchange_temporal_R).
Proof.
  eapply container_temporal_mono with (p := algebra_W) (q := exchange_temporal_lock);
    [intros t r H; right; exact H |intros t r H; right; exact H |].
  apply assertion_temporal_lock_right_spatial,container_spatial_comm.
  apply acquire_marked_payload; [left; reflexivity |intros i H; exact H |].
  split; [left; reflexivity |left]. split; [intros; reflexivity |].
  split; [intros; reflexivity |intros i H; contradiction].
Qed.

Lemma exchange_temporal_spatial :
  spatial (proj1_sig algebra_whole) (proj1_sig exchange_temporal_token) (proj1_sig exchange_temporal_whole).
Proof.
  split; [split |intros i; cbn; unfold no_blocked; tauto].
  - split.
    + intros loc _ [[v H] |[i [v H]]]; discriminate || contradiction.
    + intros i H; contradiction.
  - split; [intros; reflexivity |]. split.
    + intros i; apply interleaves_comm; exact (interleaves_app [] (buffers (resource_memory two_processors algebra_whole) i)).
    + intros i; cbn; unfold no_blocked; tauto.
Qed.

Theorem assertion_exchange_strong_temporal_left_model s :
  persistent_models two_processors s exchange_temporal_whole
    (A.strong_temporal algebra_P (A.Temporal exchange_temporal_Q exchange_temporal_R)).
Proof.
  split.
  - exists algebra_whole,exchange_temporal_token; split; [apply exchange_temporal_spatial |].
    split; [reflexivity |apply exchange_temporal_token_inner].
  - exists algebra_heap,exchange_temporal_pending; split.
    + apply temporal_acquire_recompose; [intros i H; exact H |apply algebra_heap_pending_temporal].
    + split; [reflexivity |apply exchange_temporal_pending_inner].
Qed.

Theorem assertion_exchange_strong_temporal_left_not_model s :
  ~ persistent_models two_processors s exchange_temporal_whole
    (A.Temporal (A.strong_temporal algebra_P exchange_temporal_Q) exchange_temporal_R).
Proof.
  intros (a & b & Htm & Hinner & [HB |HL]).
  - assert (E : buffers (resource_memory two_processors exchange_temporal_whole) 1%positive = []).
    { eapply assertion_barrier_suffix_buffer with (p := A.strong_temporal algebra_P exchange_temporal_Q);
        [left; reflexivity |exists a,b; auto]. }
    discriminate.
  - destruct HL as [Hbh [Hbb [Hi Hbheld]]].
    destruct Htm as [[Hdis Hrest] [[Hcompat [Hheap [Hbuffers Hblocks]]] [Hbefore Hmarks]]].
    destruct Hinner as [(c & d & [[Hcd [Hch [Hcb Hck]]] Ginner] & HP & [HD |HW]) Hother].
    + apply (Hdis 2%positive).
      * apply Hck; right; destruct HD as [_ [_ [_ HDheld]]]; apply HDheld.
        split; [right; reflexivity |discriminate].
      * apply Hbheld; split; [right; reflexivity |discriminate].
    + eapply assertion_spatial_write_cannot_mix with (a := proj1_sig c) (b := proj1_sig d)
        (whole := underlying (proj1_sig a)) (loc := 1%positive) (owner := 1%positive) (value := 0%Z).
      * split; [exact Hcd |split; [exact Hch |split; assumption]].
      * exact HW.
      * exists 0%Z; specialize (Hheap 1%positive).
        change (Some 0%Z = heap_override (shared_heap (underlying (proj1_sig a)))
          (shared_heap (underlying (proj1_sig b))) 1%positive) in Hheap.
        unfold heap_override in Hheap; rewrite Hbh in Hheap; symmetry; exact Hheap.
      * exists 0%Z; specialize (Hbuffers 1%positive); rewrite Hbb,app_nil_r in Hbuffers.
        change ([(1%positive,0%Z)] = buffers (underlying (proj1_sig a)) 1%positive) in Hbuffers.
        rewrite <- Hbuffers; left; reflexivity.
  Unshelve. all: try assumption.
Qed.

Theorem assertion_small_exchange_strong_temporal_left_refuted :
  (forall p q, persistent_entails two_processors (A.strong_temporal p q) (A.Temporal p q)) /\
  ~ persistent_entails two_processors
    (A.strong_temporal algebra_P (A.Temporal exchange_temporal_Q exchange_temporal_R))
    (A.Temporal (A.strong_temporal algebra_P exchange_temporal_Q) exchange_temporal_R).
Proof.
  split; [apply assertion_strong_entails_temporal |].
  intros H; apply (assertion_exchange_strong_temporal_left_not_model (fun _ => 0%Z)),H,
    assertion_exchange_strong_temporal_left_model.
Qed.
