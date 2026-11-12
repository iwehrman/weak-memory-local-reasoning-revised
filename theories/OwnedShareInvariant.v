From Stdlib Require Import List ZArith.
From WMLR Require Import Expressions Languages Machine BufferRelations Separation RepairedSeparation
  Assertions AssertionSemantics ConcreteAssertions PersistentAssertions TemporalSafety
  InvariantFragment AssertionAlgebra.
Import ListNotations.

(** An inhabited fragment model either supplies a mark witness, or has an
    empty heap. This constructive alternative avoids excluded middle on the
    mark set when restoring an invariant after a change of stack. *)
Lemma invariant_model_mark_or_empty p : invariant_fragment p ->
  forall active s (r : resource active), persistent_models active s r p ->
  (exists i, complete (proj1_sig r) i) \/
  (forall loc, shared_heap (resource_memory active r) loc = None).
Proof.
  induction 1; intros active s r Hmodel.
  - right; exact (proj1 Hmodel).
  - destruct (writer_points_to_shape _ _ _ _ _ Hmodel) as (loc & owner & _ & _ & _ & _ & _ & Hmark).
    left; eauto.
  - destruct Hmodel as (a & b & [Hsp Hmarks] & Ha & Hb).
    destruct (IHinvariant_fragment1 _ _ _ Ha) as [[i Hi] |Hea];
      [left; exists i; apply Hmarks; auto |].
    destruct (IHinvariant_fragment2 _ _ _ Hb) as [[i Hi] |Heb];
      [left; exists i; apply Hmarks; auto |].
    right; intros loc; rewrite (proj1 (proj2 Hsp)); unfold heap_override.
    change (shared_heap (resource_memory active a) loc) with (shared_heap (underlying (proj1_sig a)) loc) in Hea.
    change (shared_heap (resource_memory active b) loc) with (shared_heap (underlying (proj1_sig b)) loc) in Heb.
    rewrite Hea,Heb; reflexivity.
  - destruct Hmodel as [Hmodel |Hmodel];
      [exact (IHinvariant_fragment1 active s r Hmodel) |exact (IHinvariant_fragment2 active s r Hmodel)].
  - destruct Hmodel as [v Hmodel]; apply (IHinvariant_fragment _ _ _ Hmodel).
  - apply (IHinvariant_fragment _ _ _ (proj2 Hmodel)).
Qed.

Lemma invariant_empty_model p : invariant_fragment p ->
  forall active s (r target : resource active), persistent_models active s r p ->
  (forall loc, shared_heap (resource_memory active r) loc = None) ->
  empty_atom (proj1_sig target) -> persistent_models active s target p.
Proof.
  induction 1; intros active s r target Hmodel Hheap Hempty.
  - exact Hempty.
  - destruct (writer_points_to_shape _ _ _ _ _ Hmodel) as (loc & owner & _ & _ & Hcell & _).
    specialize (Hheap loc); rewrite Hcell,heap_update_same in Hheap; discriminate.
  - destruct Hmodel as (a & b & [Hsp _] & Ha & Hb).
    assert (HE : (forall loc, shared_heap (resource_memory active a) loc = None) /\
                 (forall loc, shared_heap (resource_memory active b) loc = None)).
    { destruct Hsp as [_ [Hout _]]; split; intros loc; specialize (Hheap loc).
      all: rewrite Hout in Hheap; unfold heap_override in Hheap;
        destruct (shared_heap (underlying (proj1_sig b)) loc) eqn:Eb; try discriminate.
      - exact Hheap.
      - exact Eb. }
    exists target,target; split; [apply assertion_empty_self_spatial,Hempty |].
    split; [exact (IHinvariant_fragment1 active s a target Ha (proj1 HE) Hempty)
      |exact (IHinvariant_fragment2 active s b target Hb (proj2 HE) Hempty)].
  - destruct Hmodel; [left; eapply IHinvariant_fragment1 |right; eapply IHinvariant_fragment2]; eassumption.
  - destruct Hmodel as [v Hmodel]; exists v; eapply IHinvariant_fragment; eassumption.
  - split; [exact (proj1 Hmodel) |]. eapply IHinvariant_fragment; [exact (proj2 Hmodel) |exact Hheap |exact Hempty].
Qed.

Lemma invariant_restore_marks active invariant s t (r : resource active) :
  invariant_fragment invariant -> persistent_models active s r invariant ->
  persistent_full_satisfies active t (resource_memory active r) invariant ->
  persistent_models active t r invariant.
Proof.
  intros Hfragment Hbefore (full & Efull & Hafter).
  destruct (invariant_model_mark_or_empty _ Hfragment _ _ _ Hbefore) as [Hmarks |Hempty].
  - eapply invariant_fragment_remark; [exact Hfragment | |exact Hmarks |exact Hafter].
    unfold resource_memory at 1; rewrite Efull; reflexivity.
  - eapply invariant_empty_model; [exact Hfragment |exact Hafter | |].
    + unfold resource_memory at 1; rewrite Efull; exact Hempty.
    + split; [exact Hempty |exact (invariant_fragment_shape _ Hfragment _ _ _ Hbefore)].
Qed.
