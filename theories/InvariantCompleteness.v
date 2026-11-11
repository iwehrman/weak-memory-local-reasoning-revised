From Stdlib Require Import List ZArith.
From WMLR Require Import Expressions Languages Machine BufferRelations Separation OperationalSemantics
  Assertions AssertionSemantics ConcreteAssertions RepairedAssertions PersistentAssertions Safety HeapRules
  OwnershipProtocol OwnershipHeap TemporalSafety TemporalFence RegionalResources RegionalSafety RegionalCalculus.
Import ListNotations.

Lemma cell_resource_complete active s (r : resource active) loc v :
  persistent_models active s r (cell_assertion loc v) -> forall i, active i -> complete (proj1_sig r) i.
Proof.
  intros H; apply (proj1 (persistent_wand_free_unchanged _ _ _ _ (cell_assertion_wand_free loc v))) in H.
  destruct (repaired_points_to_requires_flushed _ _ _ _ _ H) as (address & owner & _ & _ & _ & Hcomplete).
  exact Hcomplete.
Qed.

(** Completeness in a spatially owned cell can also be assigned to an empty
    sibling, without changing the combined resource. This is an entailment
    of the current assertion interpretation, not a new logical axiom. *)
Theorem cell_emp_entails_barrier active loc v i : active i ->
  regional_entails active (A.Spatial (cell_assertion loc v) A.Emp)
    (A.Spatial (cell_assertion loc v) (A.Barrier (EVal (Z.pos i)))).
Proof.
  intros Hi s out (cell & rest & [Hmemory Hmarks] & Hcell & Hemp).
  exists cell, (mark_processor active rest i Hi). split.
  - split; [exact Hmemory |]. intros j.
    change (complete (proj1_sig out) j <-> complete (proj1_sig cell) j \/ complete (proj1_sig rest) j \/ j = i).
    rewrite (Hmarks j). split; [tauto |]. intros [H |[H | ->]]; [auto |auto |].
    left; exact (cell_resource_complete _ _ _ _ _ Hcell i Hi).
  - split; [exact Hcell |apply marked_emp_barrier, Hemp].
Qed.

Lemma owned_entails active owner pre post : regional_entails active pre post ->
  regional_entails active (owned_assertion owner pre) (owned_assertion owner post).
Proof.
  intros H s r (token & payload & Hsp & Htoken & HP).
  exists token, payload; split; [exact Hsp |]. split; [exact Htoken |apply H, HP].
Qed.

Definition regional_roundtrip owner := Concurrent.Seq
  (Concurrent.Prim Concurrent.Lock (EVal (Z.pos owner)))
  (Concurrent.Prim Concurrent.Unlock (EVal (Z.pos owner))).

Theorem regional_roundtrip_derivable active owner invariant pre :
  regional_derivation active owner invariant Closed pre (regional_roundtrip owner) Closed pre.
Proof. eapply RegionalSequence; [apply RegionalAcquire |apply RegionalRelease]. Qed.

(** The acquiring processor need not be the processor in the barrier.
    This exposes a conflict with unrestricted temporal framing across imports. *)
Theorem regional_roundtrip_barrier_derivable active owner loc v i : active i ->
  regional_derivation active owner (cell_assertion loc v) Closed A.Emp (regional_roundtrip owner)
    Closed (A.Barrier (EVal (Z.pos i))).
Proof.
  intros Hi. eapply RegionalSequence; [apply RegionalAcquire |].
  eapply RegionalConsequence.
  - apply owned_entails, cell_emp_entails_barrier, Hi.
  - apply RegionalRelease.
  - intros s r H; exact H.
Qed.

Lemma temporal_barrier_resource_empty active s (r : resource active) past i : active i ->
  persistent_models active s r (A.Temporal past (A.Barrier (EVal (Z.pos i)))) ->
  buffers (resource_memory active r) i = [].
Proof.
  intros Hi (a & b & [_ [[_ [_ [Hb _]]] [Hbefore _]]] & _ & Hempty & Hmark).
  destruct Hmark as [Hnot |Hmark]; [contradiction |].
  unfold resource_memory; rewrite Hb, (Hbefore i Hmark), (proj1 (proj2 Hempty) i); reflexivity.
Qed.
