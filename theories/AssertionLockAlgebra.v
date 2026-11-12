From Stdlib Require Import List ZArith.
From WMLR Require Import Expressions Machine BufferRelations Separation StableCompatibility
  RepairedSeparation Assertions AssertionSemantics ConcreteAssertions PersistentAssertions
  PersistentRules TemporalSafety OwnedContainerEntailments AssertionAlgebra AssertionBarrierAlgebra.
Import ListNotations.

Definition assertion_erase_marks active (r : resource active)
    (Hheap : forall loc, shared_heap (resource_memory active r) loc = None) : resource active.
Proof.
  refine (exist _ (Generalized (resource_memory active r) no_blocked) _).
  split; [exact (proj1 (proj2_sig r)) |].
  split; [intros i H; contradiction |intros; apply Hheap].
Defined.

Lemma assertion_lock_shape active s r annotation :
  persistent_models active s r (A.Lock annotation) ->
  (forall loc, shared_heap (resource_memory active r) loc = None) /\
  (forall i, buffers (resource_memory active r) i = []).
Proof.
  intros HL; change (lock_atom active (eval_expr s annotation) (proj1_sig r)) in HL.
  destruct (eval_expr s annotation); try contradiction; destruct HL as [Hh [Hb Hheld]]; auto.
Qed.

Lemma assertion_temporal_bufferless_right_spatial active a b r :
  (forall loc, shared_heap (underlying b) loc = None) ->
  (forall i, buffers (underlying b) i = []) -> repaired_temporal active a b r -> spatial a b r.
Proof.
  intros Hbh Hbb [[Hdis Hstable] [[_ [Hh [Hb Hk]]] [_ Hmarks]]]; split; [|exact Hmarks].
  split; [split; [|exact Hdis] |].
  - intros loc _ [[v H] |[i [v H]]]; [rewrite Hbh in H; discriminate |rewrite Hbb in H; contradiction].
  - split; [exact Hh |]. split; [|exact Hk].
    intros i; rewrite Hb,Hbb; apply interleaves_app.
Qed.

Lemma assertion_temporal_bufferless_left_spatial active a b r :
  (forall loc, shared_heap (underlying a) loc = None) ->
  (forall i, buffers (underlying a) i = []) -> repaired_temporal active a b r -> spatial a b r.
Proof.
  intros Hah Hab [[Hdis Hstable] [[_ [Hh [Hb Hk]]] [_ Hmarks]]]; split; [|exact Hmarks].
  split; [split; [|exact Hdis] |].
  - intros loc [[v H] |[i [v H]]] _; [rewrite Hah in H; discriminate |rewrite Hab in H; contradiction].
  - split; [exact Hh |]. split; [|exact Hk].
    intros i; rewrite Hb,Hab; apply interleaves_app.
Qed.

(** A lock can be placed last temporally by assigning its optional marks
    to P. Preservation of P uses the full-grammar mark-extension theorem. *)
Theorem assertion_temporal_lock_right_spatial active p annotation s r :
  persistent_models active s r (A.Temporal p (A.Lock annotation)) <->
  persistent_models active s r (A.Spatial p (A.Lock annotation)).
Proof.
  split.
  - intros (a & b & Htm & HP & HL); exists a,b; split; [|auto].
    destruct (assertion_lock_shape _ _ _ _ HL) as [Hh Hb].
    exact (assertion_temporal_bufferless_right_spatial active (proj1_sig a) (proj1_sig b) (proj1_sig r) Hh Hb Htm).
  - intros (a & b & [[Hcompat [Hheap [Hbuffers Hblocks]]] Hmarks] & HP & HL).
    destruct (assertion_lock_shape _ _ _ _ HL) as [Hh Hb].
    exists (assertion_add_marks active a b),(assertion_erase_marks active b Hh); split.
    + split; [apply spatial_compatible_stable,Hcompat |]. split.
      * split; [apply spatial_compatible_temporal,Hcompat |]. split; [exact Hheap |].
        split; [|exact Hblocks]. intros i; change (buffers (resource_memory active r) i =
          buffers (resource_memory active a) i ++ buffers (resource_memory active b) i).
        specialize (Hbuffers i); change (interleaves (buffers (resource_memory active a) i)
          (buffers (resource_memory active b) i) (buffers (resource_memory active r) i)) in Hbuffers.
        rewrite Hb,app_nil_r; rewrite Hb in Hbuffers; apply interleaves_nil_right,Hbuffers.
      * split; [intros i H; contradiction |]. intros i.
        change (complete (proj1_sig r) i <->
          (complete (proj1_sig a) i \/ complete (proj1_sig b) i) \/ False).
        rewrite (Hmarks i); tauto.
    + split; [apply assertion_models_add_marks,HP |exact HL].
Qed.

Theorem assertion_temporal_lock_left_spatial active p annotation s r :
  persistent_models active s r (A.Temporal (A.Lock annotation) p) <->
  persistent_models active s r (A.Spatial (A.Lock annotation) p).
Proof.
  split; intros (a & b & Hsplit & HL & HP); exists a,b; split; [|auto | |auto].
  - destruct (assertion_lock_shape _ _ _ _ HL) as [Hh Hb].
    exact (assertion_temporal_bufferless_left_spatial active (proj1_sig a) (proj1_sig b) (proj1_sig r) Hh Hb Hsplit).
  - destruct (assertion_lock_shape _ _ _ _ HL) as [Hh Hb].
    destruct Hsplit as [[Hcompat [Hheap [Hbuffers Hblocks]]] Hmarks].
    split; [apply spatial_compatible_stable,Hcompat |]. split.
    + split; [apply spatial_compatible_temporal,Hcompat |]. split; [exact Hheap |].
      split; [|exact Hblocks]. intros i; change (buffers (resource_memory active r) i =
        buffers (resource_memory active a) i ++ buffers (resource_memory active b) i).
      specialize (Hbuffers i); change (interleaves (buffers (resource_memory active a) i)
        (buffers (resource_memory active b) i) (buffers (resource_memory active r) i)) in Hbuffers.
      rewrite Hb; rewrite Hb in Hbuffers; apply interleaves_nil_left,Hbuffers.
    + split; [intros; apply Hb |exact Hmarks].
Qed.

(** E5, all three conjunctions, arbitrary expressions and assertions. *)
Theorem assertion_lock_symmetric kind active p annotation s r :
  persistent_models active s r (assertion_conjunction kind p (A.Lock annotation)) <->
  persistent_models active s r (assertion_conjunction kind (A.Lock annotation) p).
Proof.
  destruct kind; cbn [assertion_conjunction].
  - apply assertion_spatial_commutative.
  - rewrite assertion_temporal_lock_right_spatial,assertion_temporal_lock_left_spatial.
    apply assertion_spatial_commutative.
  - change ((persistent_models active s r (A.Spatial p (A.Lock annotation)) /\
      persistent_models active s r (A.Temporal p (A.Lock annotation))) <->
      (persistent_models active s r (A.Spatial (A.Lock annotation) p) /\
      persistent_models active s r (A.Temporal (A.Lock annotation) p))).
    rewrite assertion_temporal_lock_right_spatial,assertion_temporal_lock_left_spatial.
    rewrite assertion_spatial_commutative; reflexivity.
Qed.
