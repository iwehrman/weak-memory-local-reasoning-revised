From Stdlib Require Import List ZArith.
From WMLR Require Import Expressions Machine BufferRelations Separation RepairedSeparation
  Assertions AssertionSemantics PersistentAssertions PersistentRules TemporalSafety
  ExecutionExamples OwnedContainerEntailments AssertionAlgebra AssertionUnits
  AssertionAlgebraCounterexamples AssertionExchange.
Import ListNotations.

(** T7 with strong-temporal outside and spatial inside. The same one-cell
    countermodel as associativity suffices. *)
Theorem assertion_exchange_strong_spatial_left_model s :
  persistent_models two_processors s algebra_whole
    (A.strong_temporal algebra_P (A.Spatial algebra_Q algebra_R)).
Proof.
  eapply assertion_conjunction_mono with (kind := StrongKind);
    [intros t r H; exact H |apply assertion_strong_entails_spatial |apply assertion_strong_associativity_right_model].
Qed.

Theorem assertion_exchange_strong_spatial_left_refuted :
  (forall p q, persistent_entails two_processors (A.strong_temporal p q) (A.Spatial p q)) /\
  ~ persistent_entails two_processors
    (A.strong_temporal algebra_P (A.Spatial algebra_Q algebra_R))
    (A.Spatial (A.strong_temporal algebra_P algebra_Q) algebra_R).
Proof.
  split; [apply assertion_strong_entails_spatial |].
  intros H; apply (assertion_strong_associativity_left_spatial_not_model (fun _ => 0%Z)),H,
    assertion_exchange_strong_spatial_left_model.
Qed.

(** T9's full exchange law fails in the same small resource. This witness
    was minimized from the search candidate using the proved emp units. *)
Theorem assertion_full_exchange_left_model s :
  persistent_models two_processors s algebra_whole
    (A.strong_temporal (A.Spatial algebra_P A.Emp) (A.Spatial algebra_Q algebra_R)).
Proof.
  eapply assertion_conjunction_mono with (kind := StrongKind).
  - intros t r H; apply (proj2 (assertion_unit_spatial_right _ _ _ _)),H.
  - intros t r H; exact H.
  - apply assertion_exchange_strong_spatial_left_model.
Qed.

Theorem assertion_full_exchange_right_not_model s :
  ~ persistent_models two_processors s algebra_whole
    (A.Spatial (A.strong_temporal algebra_P algebra_Q) (A.strong_temporal A.Emp algebra_R)).
Proof.
  intros H; apply (assertion_strong_associativity_left_spatial_not_model s).
  eapply container_spatial_mono; [intros t r HP; exact HP | |exact H].
  intros t r HP; apply (proj1 (assertion_unit_strong_left _ _ _ _)),HP.
Qed.

Corollary assertion_full_exchange_refuted :
  ~ persistent_entails two_processors
    (A.strong_temporal (A.Spatial algebra_P A.Emp) (A.Spatial algebra_Q algebra_R))
    (A.Spatial (A.strong_temporal algebra_P algebra_Q) (A.strong_temporal A.Emp algebra_R)).
Proof.
  intros H; apply (assertion_full_exchange_right_not_model (fun _ => 0%Z)),H,assertion_full_exchange_left_model.
Qed.
