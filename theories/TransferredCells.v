From Stdlib Require Import List ZArith.
From WMLR Require Import Expressions Languages Machine BufferRelations Separation StableCompatibility
  RepairedSeparation GeneralizedFlushing Assertions AssertionSemantics ConcreteAssertions PersistentAssertions
  Safety HeapRules OwnershipProtocol OwnershipHeap TemporalSafety TemporalFence RegionalResources.
Import ListNotations.

(** An existing-language abbreviation: a flushed cell with completeness for
    its named processor, rather than the all-processor points-to abbreviation. *)
Definition processor_cell owner loc v := A.Temporal
  (A.LeadsTo (EVal (Z.pos loc)) (EVal (Z.pos owner)) (EVal v))
  (A.Barrier (EVal (Z.pos owner))).

Lemma processor_cell_from_shape active owner s (r : resource active) loc v :
  active owner ->
  (forall address, shared_heap (resource_memory active r) address = heap_update empty_heap loc v address) ->
  (forall i, buffers (resource_memory active r) i = []) -> lock_free (resource_memory active r) ->
  complete (proj1_sig r) owner -> persistent_models active s r (processor_cell owner loc v).
Proof.
  intros Hi Hheap Hbuffers Hfree Hmark.
  exists r, (mark_processor active (bare_resource active) owner Hi); split.
  - split.
    + apply spatial_compatible_stable; exact (proj1 (proj1 (spatial_empty_right (proj1_sig r)))).
    + split.
      * exact (proj1 (temporal_empty_right active (proj1_sig r))).
      * split.
        -- intros i _; apply Hbuffers.
        -- intros i; change (complete (proj1_sig r) i <-> complete (proj1_sig r) i \/ False \/ i = owner).
           split; [auto |intros [H |[H | ->]]; [exact H |contradiction |exact Hmark]].
  - split.
    + split; [exact Hi |]. right; split; [exact Hheap |]. split; [exact Hbuffers |]. split; assumption.
    + apply marked_emp_barrier, bare_resource_models.
Qed.

Lemma processor_cell_shape active owner s (r : resource active) loc v : active owner ->
  persistent_models active s r (processor_cell owner loc v) ->
  (forall address, shared_heap (resource_memory active r) address = heap_update empty_heap loc v address) /\
  (forall i, buffers (resource_memory active r) i = []) /\ lock_free (resource_memory active r) /\
  complete (proj1_sig r) owner.
Proof.
  intros Hi (a & b & [_ [[_ [Hheap [Hbuffers Hblocked]]] [Hbefore Hmarks]]] &
    [_ [Hpending |Hflushed]] & [Hbh [Hbb Hbk]] & [Hinactive |Hbmark]); try contradiction.
  - destruct Hpending as [_ [Hab _]]. specialize (Hbefore owner Hbmark).
    rewrite Hab, buffer_update_same in Hbefore; discriminate.
  - destruct Hflushed as [Hah [Hab [Hak Ham]]].
    split.
    + intros address; unfold resource_memory; rewrite Hheap; unfold heap_override; rewrite Hbh; apply Hah.
    + split.
      * intros i; unfold resource_memory; rewrite Hbuffers, Hab, Hbb; reflexivity.
      * split.
        -- intros i H; apply Hblocked in H; destruct H; [apply (Hak i) |apply (Hbk i)]; assumption.
        -- apply Hmarks; auto.
Qed.

Lemma processor_cell_fresh owner loc v x : ~ In x (A.fv (processor_cell owner loc v)).
Proof. intros H; exact H. Qed.

Lemma processor_cell_active active owner s r loc v :
  persistent_models active s r (processor_cell owner loc v) -> active owner.
Proof. intros (a & b & Htm & [Hi Ha] & Hb); exact Hi. Qed.

(** Reuse a physical cell but retain ONLY previously private marks plus the
    issuing processor's fence mark. No protected completeness is copied. *)
Definition imported_cell_resource active owner (Hi : active owner) (local : resource active) cell
    (Hwf : memory_well_formed active cell) : resource active.
Proof.
  refine (exist _ (Generalized cell (fun i => complete (proj1_sig local) i \/ i = owner)) _).
  split; [exact Hwf |]. split.
  - intros i [H | ->]; [exact (proj1 (proj2 (proj2_sig local)) i H) |exact Hi].
  - intros H address; exfalso; apply (H owner); right; reflexivity.
Defined.
