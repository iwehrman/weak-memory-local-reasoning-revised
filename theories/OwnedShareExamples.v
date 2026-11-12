From Stdlib Require Import List ZArith.
From WMLR Require Import Expressions Languages Machine Separation OperationalSemantics
  Assertions AssertionSemantics PersistentAssertions AssertionUnits TemporalSafety InvariantFragment
  ExecutionExamples OwnedSafety OwnedStructural OwnedFraming OwnedAcceptance OwnedContainer OwnedContainerDerivation
  OwnedContainerTrace OwnedShareAdequacy OwnedShare.
Import ListNotations.

(** The already derived ownership-transfer container, now under emp.
    SHARE is a semantic theorem; no program constructor is added. *)
Theorem owned_container_share_valid :
  owned_valid two_processors DisjointMode A.Emp container_invariant container_program container_invariant.
Proof.
  eapply owned_consequence_valid with (pre' := A.Spatial container_invariant A.Emp)
    (post' := A.Spatial container_invariant A.Emp).
  - intros s r H; apply (proj2 (assertion_unit_spatial_right _ _ _ _)),H.
  - apply owned_share_derivation_valid; [exact acceptance_two_active |exact container_invariant_fragment
      |apply invariant_assertion_lock_free,InvariantEmp |apply invariant_assertion_lock_free,InvariantEmp
      |exact container_core_derived].
  - intros s r H; apply (proj1 (assertion_unit_spatial_right _ _ _ _)),H.
Qed.

Theorem owned_container_share_framed_valid :
  owned_valid two_processors DisjointMode A.Emp (A.Spatial container_foreign container_invariant)
    container_program (A.Spatial container_foreign container_invariant).
Proof.
  apply owned_spatial_frame_valid; [exact owned_container_share_valid |intros x _ H; contradiction].
Qed.

Theorem owned_container_share_inhabited s :
  persistent_models two_processors s (container_full_pool 7%Z) container_invariant.
Proof. apply container_full_pool_models. Qed.
