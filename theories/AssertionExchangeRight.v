From Stdlib Require Import List ZArith.
From WMLR Require Import Expressions Machine BufferRelations Separation StableCompatibility
  RepairedSeparation SpatialExchange Assertions AssertionSemantics ConcreteAssertions PersistentAssertions
  PersistentRules TemporalSafety RegionalResources ExecutionExamples OwnedResources OwnedHeapResources
  OwnedAcceptance OwnedContainerEntailments AssertionResourceEquivalence AssertionUnits AssertionAlgebra
  AssertionAlgebraCounterexamples AssertionExchange.
Import ListNotations.

(** The second associativity direction and T8 with spatial/strong inside. *)
Definition exchange_right_cell := acceptance_cell 2%positive 0%Z 1%positive (or_introl eq_refl).
Definition exchange_right_first := owned_enqueue_resource two_processors exchange_right_cell
  1%positive 1%positive 0%Z (or_introl eq_refl).
Definition exchange_right_foreign := owned_enqueue_resource two_processors exchange_right_cell
  2%positive 2%positive 0%Z (or_intror eq_refl).
Definition exchange_right_whole := owned_enqueue_resource two_processors exchange_right_first
  2%positive 2%positive 0%Z (or_intror eq_refl).
Definition exchange_right_alternate := owned_enqueue_resource two_processors exchange_right_foreign
  1%positive 1%positive 0%Z (or_introl eq_refl).
Definition exchange_right_Q := algebra_W.
Definition exchange_right_W := A.LeadsTo (EVal 2%Z) (EVal 2%Z) (EVal 0%Z).
Definition exchange_right_R := A.Or algebra_Q exchange_right_W.

Lemma exchange_right_cell_fresh : ~ memory_domain (resource_memory two_processors exchange_right_cell) 1%positive.
Proof. intros H; apply acceptance_cell_domain in H; discriminate. Qed.

Lemma exchange_right_foreign_fresh : ~ memory_domain (resource_memory two_processors exchange_right_foreign) 1%positive.
Proof.
  intros [[v H] |[i [v H]]]; [discriminate |].
  change (In (1%positive,v) (buffer_update empty_buffers 2%positive [(2%positive,0%Z)] i)) in H.
  unfold buffer_update in H; destruct (Pos.eq_dec i 2%positive); [destruct H; [discriminate |contradiction] |contradiction].
Qed.

Lemma exchange_right_alternate_equiv :
  generalized_equiv (proj1_sig exchange_right_alternate) (proj1_sig exchange_right_whole).
Proof.
  split; [split; [intros; reflexivity |] |intros; reflexivity]. split; [|intros; reflexivity].
  intros i; cbn [exchange_right_alternate exchange_right_whole exchange_right_foreign exchange_right_first
    owned_enqueue_resource proj1_sig underlying resource_memory enqueue buffers].
  unfold buffer_update; destruct (Pos.eq_dec i 1%positive), (Pos.eq_dec i 2%positive); subst;
    try congruence; reflexivity.
Qed.

Lemma exchange_right_first_inner s :
  persistent_models two_processors s exchange_right_first (A.strong_temporal algebra_P exchange_right_Q).
Proof.
  split.
  - apply assertion_enqueue_spatial; [reflexivity |apply exchange_right_cell_fresh].
  - apply owned_enqueue_temporal_post; [reflexivity |intros i Hne [v H]; contradiction].
Qed.

Lemma exchange_right_whole_inner s :
  persistent_models two_processors s exchange_right_whole (A.strong_temporal algebra_P exchange_right_Q).
Proof.
  apply (persistent_models_resource_equiv _ _ _ exchange_right_alternate); [apply exchange_right_alternate_equiv |].
  split.
  - apply assertion_enqueue_spatial; [reflexivity |apply exchange_right_foreign_fresh].
  - apply owned_enqueue_temporal_post; [reflexivity |].
    intros i Hne Hdom; apply exchange_right_foreign_fresh; right; exists i; exact Hdom.
Qed.

Lemma exchange_right_whole_bar :
  spatial (proj1_sig exchange_right_whole) (proj1_sig algebra_bar) (proj1_sig exchange_right_whole).
Proof.
  split; [exact (proj1 (spatial_empty_right (proj1_sig exchange_right_whole))) |].
  intros i; change (i = 1%positive <-> i = 1%positive \/ False \/ i = 1%positive); tauto.
Qed.

Theorem assertion_strong_associativity_left_model s :
  persistent_models two_processors s exchange_right_whole
    (A.strong_temporal (A.strong_temporal algebra_P exchange_right_Q) exchange_right_R).
Proof.
  split.
  - exists exchange_right_whole,algebra_bar; split; [apply exchange_right_whole_bar |].
    split; [apply exchange_right_whole_inner |left; apply algebra_bar_models].
  - eapply container_temporal_mono with (q := exchange_right_W);
      [intros t r H; exact H |intros t r H; right; exact H |].
    apply owned_enqueue_temporal_post; [apply exchange_right_first_inner |].
    intros i Hne [v H]; change (In (2%positive,v) (buffer_update empty_buffers 1%positive [(1%positive,0%Z)] i)) in H.
    unfold buffer_update in H; destruct (Pos.eq_dec i 1%positive); [destruct H; [discriminate |contradiction] |contradiction].
Qed.

Theorem assertion_exchange_strong_spatial_right_not_model s :
  ~ persistent_models two_processors s exchange_right_whole
    (A.Spatial algebra_P (A.strong_temporal exchange_right_Q exchange_right_R)).
Proof.
  intros (outer & inner & [Hout Gout] & HP &
    (a & b & [Hinner Ginner] & HQ & HR) & HT).
  destruct HR as [HB |HW].
  - pose proof (proj1 HB) as [Hbh [Hbb Hbk]].
    destruct Hinner as [Hcompat [Hh [Hb Hk]]].
    destruct HQ as [Hi [Hpending |Hflushed]].
    + destruct Hpending as [Hah [Hab Hak]].
      assert (HemptyHeap : forall loc, shared_heap (underlying (proj1_sig inner)) loc = None).
      { intros loc; rewrite Hh; unfold heap_override; rewrite Hbh,Hah; reflexivity. }
      assert (Hbuf : forall i, buffers (underlying (proj1_sig inner)) i =
        buffer_update empty_buffers 1%positive [(1%positive,0%Z)] i).
      { intros i; specialize (Hb i); rewrite Hbb in Hb; apply interleaves_nil_right in Hb; rewrite Hb; apply Hab. }
      destruct HT as (c & d & Htm & HC & [HD |HD]).
      * assert (E : buffers (resource_memory two_processors inner) 1%positive = []).
        { eapply assertion_barrier_suffix_buffer with (p := exchange_right_Q);
            [left; reflexivity |exists c,d; split; [exact Htm |split; [exact HC |exact HD]]]. }
        unfold resource_memory in E; rewrite Hbuf,buffer_update_same in E; discriminate.
      * destruct Htm as [_ [[_ [Hheap [Hbuffers Hblocks]]] _]].
        destruct HD as [_ [[Hdh [Hdb Hdk]] |[Hdh [Hdb Hdk]]]].
        -- specialize (Hbuffers 2%positive); rewrite Hbuf,Hdb,buffer_update_same in Hbuffers.
           cbn [buffer_update empty_buffers] in Hbuffers.
           symmetry in Hbuffers; apply app_eq_nil in Hbuffers; destruct Hbuffers as [_ Hbad]; discriminate.
        -- specialize (Hheap 2%positive); rewrite HemptyHeap in Hheap.
           unfold heap_override in Hheap; rewrite Hdh,heap_update_same in Hheap; discriminate.
    + destruct Hflushed as [Hah [Hab HK]].
      destruct Hout as [_ [Hheap Hrest]]; specialize (Hheap 1%positive).
      change (None = heap_override (shared_heap (underlying (proj1_sig outer)))
        (shared_heap (underlying (proj1_sig inner))) 1%positive) in Hheap.
      unfold heap_override in Hheap; rewrite Hh in Hheap.
      unfold heap_override in Hheap; rewrite Hbh,Hah,heap_update_same in Hheap; discriminate.
  - destruct (proj1 (memory_spatial_associative _ _ _ _)
      (ex_intro _ (underlying (proj1_sig inner)) (conj Hinner Hout))) as (combined & Hcombined & Hfinal).
    eapply assertion_spatial_write_cannot_mix with (a := Generalized combined no_blocked)
      (b := proj1_sig b) (loc := 2%positive) (owner := 2%positive) (value := 0%Z).
    + exact Hfinal.
    + exact HW.
    + exists 0%Z; reflexivity.
    + exists 0%Z; left; reflexivity.
Qed.

Corollary assertion_strong_associativity_right_not_model s :
  ~ persistent_models two_processors s exchange_right_whole
    (A.strong_temporal algebra_P (A.strong_temporal exchange_right_Q exchange_right_R)).
Proof. intros [H _]; exact (assertion_exchange_strong_spatial_right_not_model s H). Qed.

Theorem assertion_small_exchange_strong_right_refuted :
  ~ persistent_entails two_processors
    (A.strong_temporal (A.strong_temporal algebra_P exchange_right_Q) exchange_right_R)
    (A.strong_temporal algebra_P (A.strong_temporal exchange_right_Q exchange_right_R)).
Proof.
  intros H; apply (assertion_strong_associativity_right_not_model (fun _ => 0%Z)),H,
    assertion_strong_associativity_left_model.
Qed.

Theorem assertion_small_exchange_strong_spatial_right_refuted :
  (forall p q, persistent_entails two_processors (A.strong_temporal p q) (A.Spatial p q)) /\
  ~ persistent_entails two_processors
    (A.strong_temporal (A.Spatial algebra_P exchange_right_Q) exchange_right_R)
    (A.Spatial algebra_P (A.strong_temporal exchange_right_Q exchange_right_R)).
Proof.
  split; [apply assertion_strong_entails_spatial |]. intros H.
  apply (assertion_exchange_strong_spatial_right_not_model (fun _ => 0%Z)),H.
  eapply assertion_conjunction_mono with (kind := StrongKind);
    [apply assertion_strong_entails_spatial |intros t r HP; exact HP |apply assertion_strong_associativity_left_model].
Qed.
