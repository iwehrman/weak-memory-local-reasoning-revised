From Stdlib Require Import List ZArith.
From WMLR Require Import Expressions Languages OperationalSemantics Assertions AssertionSemantics
  PersistentAssertions PersistentRules GeneralizedFlushing Specifications OwnedSafety OwnedCalculus
  OwnedFenceExamples OwnedContainerEntailments AssertionUnits AssertionAlgebra.
Import ListNotations.

(** Independent classification of the dissertation's derived axioms.
    These are derivations in the existing calculus, not new constructors.
    A right temporal wand is written [TemporalWandRight conclusion suffix]. *)
Lemma alternative_temporal_wand_elim active post suffix :
  persistent_entails active (A.Temporal (A.TemporalWandRight post suffix) suffix) post.
Proof.
  intros s r (a & b & Htm & HW & HB).
  exact (HW a (GeneralizedRefl _ _) b r HB Htm).
Qed.

Theorem owned_derive_fence_backward active invariant mode post annotation :
  owned_derivation active invariant mode
    (A.TemporalWandRight post (A.Barrier annotation))
    (C.Prim (C.Common S.Fence) annotation) post.
Proof.
  eapply OwnedConsequence; [intros s r H; exact H |apply owned_derive_fence_after
    |apply alternative_temporal_wand_elim].
Qed.

(** LOCK-G retains the invariant explicitly. Temporal framing of acquisition
    is available in overlap mode; weakening also gives disjoint validity. *)
Theorem owned_derive_lock_after active invariant mode pre owner :
  owned_derivation active invariant mode pre (C.Prim C.Lock (EVal (Z.pos owner)))
    (A.Temporal pre (A.Temporal (A.Spatial (A.Lock (EVal (Z.pos owner))) invariant)
      (A.Barrier (EVal (Z.pos owner))))).
Proof.
  destruct mode; [|apply OwnedWeaken]; eapply OwnedConsequence with (pre' := A.Temporal pre A.Emp).
  - intros s r H; apply (proj2 (assertion_unit_temporal_right _ _ _ _)),H.
  - apply OwnedFrameTM; [apply OwnedLock |intros x H; contradiction].
  - intros s r H; exact H.
  - intros s r H; apply (proj2 (assertion_unit_temporal_right _ _ _ _)),H.
  - apply OwnedFrameTM; [apply OwnedLock |intros x H; contradiction].
  - intros s r H; exact H.
Qed.

Theorem owned_derive_lock_backward active invariant mode post owner :
  owned_derivation active invariant mode
    (A.TemporalWandRight post
      (A.Temporal (A.Spatial (A.Lock (EVal (Z.pos owner))) invariant)
        (A.Barrier (EVal (Z.pos owner)))))
    (C.Prim C.Lock (EVal (Z.pos owner))) post.
Proof.
  eapply OwnedConsequence; [intros s r H; exact H |apply owned_derive_lock_after
    |apply alternative_temporal_wand_elim].
Qed.

Theorem owned_derive_unlock_after_empty active pre owner :
  owned_derivation active A.Emp DisjointMode
    (A.Spatial pre (A.Lock (EVal (Z.pos owner))))
    (C.Prim C.Unlock (EVal (Z.pos owner)))
    (A.Temporal pre (A.Barrier (EVal (Z.pos owner)))).
Proof.
  eapply OwnedConsequence; [apply container_spatial_comm |apply OwnedUnlock |intros s r H; exact H].
  intros s r H; apply (proj2 (assertion_unit_spatial_left _ _ _ _)),H.
Qed.

Theorem owned_derive_unlock_backward_empty active post owner :
  owned_derivation active A.Emp DisjointMode
    (A.Spatial (A.TemporalWandRight post (A.Barrier (EVal (Z.pos owner))))
      (A.Lock (EVal (Z.pos owner))))
    (C.Prim C.Unlock (EVal (Z.pos owner))) post.
Proof.
  eapply OwnedConsequence; [intros s r H; exact H |apply owned_derive_unlock_after_empty
    |apply alternative_temporal_wand_elim].
Qed.

Theorem owned_derive_lock_empty_strong active mode owner :
  owned_derivation active A.Emp mode A.Emp (C.Prim C.Lock (EVal (Z.pos owner)))
    (A.Spatial (A.Lock (EVal (Z.pos owner))) (A.Barrier (EVal (Z.pos owner)))).
Proof.
  eapply OwnedConsequence; [intros s r H; exact H |apply OwnedLock |].
  intros s r H; apply assertion_lock_barrier_temporal_spatial.
  eapply container_temporal_mono; [|intros t a HB; exact HB |exact H].
  intros t a HL; apply (proj1 (assertion_unit_spatial_right _ _ _ _)),HL.
Qed.

Theorem owned_derive_unlock_empty_strong active owner :
  owned_derivation active A.Emp DisjointMode (A.Lock (EVal (Z.pos owner)))
    (C.Prim C.Unlock (EVal (Z.pos owner))) (A.Barrier (EVal (Z.pos owner))).
Proof.
  eapply OwnedConsequence with (pre' := A.Spatial A.Emp (A.Lock (EVal (Z.pos owner)))).
  - intros s r H; apply (proj2 (assertion_unit_spatial_left _ _ _ _)),H.
  - apply owned_derive_unlock_after_empty.
  - intros s r H; apply (proj1 (assertion_unit_temporal_left _ _ _ _)),H.
Qed.

(** The replacement for LOCKED/ATOMIC keeps the body under the SAME
    invariant. It cannot import an arbitrary proof under invariant emp.
    The entailment is exactly the already-proved transferring UNLOCK premise. *)
Theorem owned_derive_locked_wrapper active invariant pre body returned post owner :
  owned_derivation active invariant DisjointMode
    (A.Temporal pre (A.Temporal (A.Spatial (A.Lock (EVal (Z.pos owner))) invariant)
      (A.Barrier (EVal (Z.pos owner))))) body
    (A.Spatial (A.Lock (EVal (Z.pos owner))) returned) ->
  persistent_entails active (A.Temporal returned (A.Barrier (EVal (Z.pos owner))))
    (A.Spatial invariant post) ->
  owned_derivation active invariant DisjointMode pre
    (C.Seq (C.Prim C.Lock (EVal (Z.pos owner)))
      (C.Seq body (C.Prim C.Unlock (EVal (Z.pos owner))))) post.
Proof.
  intros Hbody Hrestore; eapply OwnedSequence; [apply owned_derive_lock_after |].
  eapply OwnedSequence; [exact Hbody |apply OwnedUnlock,Hrestore].
Qed.
