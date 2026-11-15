From Stdlib Require Import List ZArith.
From WMLR Require Import Expressions Languages Machine Separation OperationalSemantics Assertions AssertionSemantics
  PersistentAssertions PersistentRules AssertionSubstitution Specifications Safety TemporalSafety
  InvariantFragment BufferedPoolCandidate BufferedPoolRules BufferedPoolStructural BufferedPoolPrimitives
  BufferedPoolFraming BufferedPoolParallel BufferedPoolAdequacy.
Import ListNotations.

(** A separate calculus for lock-free commands with disjoint external frames.
    The invariant fragment is a standing soundness hypothesis. Atomic access
    has the approved semantic one-step premise; no constructor assumes safety
    or validity. This judgment has no lock or temporal-frame constructor. *)
Inductive buffered_derivation active J : A.assertion -> C.command -> A.assertion -> Prop :=
| BufferedSkip P annotation : buffered_derivation active J P (C.skip annotation) P
| BufferedAtomic P p annotation Q : buffered_atomic_premise active J P p annotation Q ->
    buffered_derivation active J P (C.Prim (C.Common p) annotation) Q
| BufferedAssign Q x rhs annotation : ~ In x (A.fv J) ->
    buffered_derivation active J (assertion_subst x rhs Q) (C.Prim (C.Common (S.Assign x rhs)) annotation) Q
| BufferedAssume P condition annotation :
    buffered_derivation active J (A.Or (A.Pure (BNot condition)) P)
      (C.Prim (C.Common (S.Assume condition)) annotation) P
| BufferedAssert P condition annotation :
    buffered_derivation active J (A.And (A.Pure condition) P)
      (C.Prim (C.Common (S.Assert condition)) annotation) P
| BufferedLoad address value annotation x : ~ In x (A.fv J) -> ~ In x (expr_fv address ++ expr_fv value) ->
    buffered_derivation active J (writer_points_to address value) (C.Prim (C.Common (S.Load x address)) annotation)
      (A.And (writer_points_to address value) (A.Pure (BEq (EVar x) value)))
| BufferedStore address old value annotation :
    buffered_derivation active J (writer_points_to address old) (C.Prim (C.Common (S.Store address value)) annotation)
      (A.Temporal (writer_points_to address old) (A.LeadsTo address annotation value))
| BufferedFence annotation : buffered_derivation active J A.Emp (C.Prim (C.Common S.Fence) annotation) (A.Barrier annotation)
| BufferedSequence P M Q first second :
    buffered_derivation active J P first M -> buffered_derivation active J M second Q ->
    buffered_derivation active J P (C.Seq first second) Q
| BufferedConsequence P P' c Q' Q : persistent_entails active P P' ->
    buffered_derivation active J P' c Q' -> persistent_entails active Q' Q -> buffered_derivation active J P c Q
| BufferedDisjunction P P' c Q : buffered_derivation active J P c Q -> buffered_derivation active J P' c Q ->
    buffered_derivation active J (A.Or P P') c Q
| BufferedChoice P left right Q : buffered_derivation active J P left Q -> buffered_derivation active J P right Q ->
    buffered_derivation active J P (C.Choice left right) Q
| BufferedLoop P body : buffered_derivation active J P body P -> buffered_derivation active J P (C.Loop body) P
| BufferedExists P c Q x : ~ In x (A.fv J) -> ~ In x (C.fv c) -> ~ In x (A.fv Q) ->
    buffered_derivation active J P c Q -> buffered_derivation active J (A.Exists x P) c Q
| BufferedFrame P c Q R : buffered_derivation active J P c Q -> frame_variable_condition c R ->
    buffered_derivation active J (A.Spatial R P) c (A.Spatial R Q)
| BufferedParallel LP left LQ RP right RQ :
    buffered_derivation active J LP left LQ -> buffered_derivation active J RP right RQ ->
    parallel_variable_condition (Build_concurrent_specification J LP left LQ) (Build_concurrent_specification J RP right RQ) ->
    frame_variable_condition left J -> frame_variable_condition right J ->
    buffered_derivation active J (A.Spatial LP RP) (C.Parallel left right) (A.Spatial LQ RQ).

Theorem buffered_calculus_sound active J : buffered_invariant_fragment J ->
  forall P c Q, buffered_derivation active J P c Q -> buffered_valid active J P c Q.
Proof.
  intros Hfragment P c Q Hderive; induction Hderive.
  - apply buffered_skip_valid,Hfragment.
  - apply buffered_atomic_valid; assumption.
  - apply buffered_assignment_valid; assumption.
  - apply buffered_assume_valid,Hfragment.
  - apply buffered_assert_valid,Hfragment.
  - apply buffered_private_load_valid; assumption.
  - apply buffered_private_store_valid,Hfragment.
  - apply buffered_private_fence_valid,Hfragment.
  - eapply buffered_sequence_valid; eassumption.
  - eapply buffered_consequence_valid; eassumption.
  - apply buffered_disjunction_valid; assumption.
  - apply buffered_choice_valid; assumption.
  - apply buffered_loop_valid; assumption.
  - apply buffered_exists_valid; assumption.
  - apply buffered_spatial_frame_valid; assumption.
  - apply buffered_parallel_valid; assumption.
Qed.

Theorem buffered_derivation_adequacy active J : buffered_invariant_fragment J ->
  forall P c Q, buffered_derivation active J P c Q ->
  forall n s whole last t final local pool,
    persistent_models active s local P -> persistent_full_satisfies active s pool J ->
    memory_spatial pool (resource_memory active local) whole -> lock_free whole ->
    execution active n c s whole last t final ->
    ~ abort active last (State t final) /\
    (terminal last -> exists local' pool', memory_spatial pool' (resource_memory active local') final /\
      lock_free final /\ persistent_full_satisfies active t pool' J /\ persistent_models active t local' Q).
Proof.
  intros Hfragment P c Q Hderive; apply buffered_valid_adequacy; [exact Hfragment |].
  apply buffered_calculus_sound; assumption.
Qed.
