From Stdlib Require Import ZArith.
From WMLR Require Import Expressions Languages Assertions AssertionSemantics PersistentAssertions
  OwnershipProtocol OwnershipHeap RegionalResources RegionalSafety.

(** A bounded calculus for the marked region model. Frame constructors are
    deliberately absent until their compatibility with transfer is established. *)
Inductive regional_derivation active owner invariant : ownership_phase -> A.assertion ->
    Concurrent.command -> ownership_phase -> A.assertion -> Prop :=
| RegionalSkip phase p annotation : regional_derivation active owner invariant phase p
    (Concurrent.skip annotation) phase p
| RegionalAcquire p : regional_derivation active owner invariant Closed p
    (Concurrent.Prim Concurrent.Lock (EVal (Z.pos owner))) Open
    (owned_assertion owner (A.Spatial invariant p))
| RegionalRelease q : regional_derivation active owner invariant Open (owned_assertion owner (A.Spatial invariant q))
    (Concurrent.Prim Concurrent.Unlock (EVal (Z.pos owner))) Closed q
| RegionalSequence start pre first middle mid second finish post :
    regional_derivation active owner invariant start pre first middle mid ->
    regional_derivation active owner invariant middle mid second finish post ->
    regional_derivation active owner invariant start pre (Concurrent.Seq first second) finish post
| RegionalConsequence start pre pre' command finish post' post :
    regional_entails active pre pre' ->
    regional_derivation active owner invariant start pre' command finish post' ->
    regional_entails active post' post ->
    regional_derivation active owner invariant start pre command finish post.

Theorem regional_calculus_sound active owner invariant start pre command finish post :
  regional_derivation active owner invariant start pre command finish post ->
  regional_valid active owner invariant start pre command finish post.
Proof.
  induction 1.
  - intros s local region Hr HP n; apply regional_skip_safe; assumption.
  - apply regional_acquire_valid.
  - apply regional_release_valid.
  - eapply regional_sequence_valid; eassumption.
  - eapply regional_consequence_valid; eassumption.
Qed.
