From Stdlib Require Import List ZArith.
From WMLR Require Import Expressions Languages Machine Separation OperationalSemantics
  Assertions AssertionSemantics Specifications PersistentAssertions PersistentRules AssertionSubstitution
  Safety TemporalSafety InvariantFragment LockRepresentation OwnedSafety OwnedAdequacy OwnedResources OwnedRules
  OwnedFraming OwnedParallel OwnedStructural OwnedPrimitives OwnedHeap OwnedExists.
Import ListNotations.

(** The active calculus. Constructors contain syntactic side conditions and
    assertion entailments only; none assumes command safety or validity.
    The invariant fragment and two active processors are standing hypotheses
    of soundness, not repeated premises of rule applications. *)
Inductive owned_derivation active invariant : ownership_mode -> A.assertion -> C.command -> A.assertion -> Prop :=
| OwnedSkip mode pre annotation :
    owned_derivation active invariant mode pre (C.skip annotation) pre
| OwnedAssign mode post x rhs annotation : ~ In x (A.fv invariant) ->
    owned_derivation active invariant mode (assertion_subst x rhs post)
      (C.Prim (C.Common (S.Assign x rhs)) annotation) post
| OwnedAssume mode pre condition annotation :
    owned_derivation active invariant mode (A.Or (A.Pure (BNot condition)) pre)
      (C.Prim (C.Common (S.Assume condition)) annotation) pre
| OwnedAssert mode pre condition annotation :
    owned_derivation active invariant mode (A.And (A.Pure condition) pre)
      (C.Prim (C.Common (S.Assert condition)) annotation) pre
| OwnedLoad mode address value annotation tail x :
    ~ In x (A.fv invariant) ->
    ~ In x (expr_fv address ++ expr_fv annotation ++ expr_fv value ++ A.fv tail) ->
    owned_derivation active invariant mode (A.strong_temporal (A.LeadsTo address annotation value) tail)
      (C.Prim (C.Common (S.Load x address)) annotation)
      (A.And (A.strong_temporal (A.LeadsTo address annotation value) tail) (A.Pure (BEq (EVar x) value)))
| OwnedStore mode address old value annotation tail :
    owned_derivation active invariant mode (A.strong_temporal (A.LeadsTo address annotation old) tail)
      (C.Prim (C.Common (S.Store address value)) annotation)
      (A.Temporal (A.strong_temporal (A.LeadsTo address annotation old) tail) (A.LeadsTo address annotation value))
| OwnedLoadAny mode address value annotation tail x :
    ~ In x (A.fv invariant) -> ~ In x (expr_fv address ++ expr_fv value ++ A.fv tail) ->
    owned_derivation active invariant mode (A.strong_temporal (writer_points_to address value) tail)
      (C.Prim (C.Common (S.Load x address)) annotation)
      (A.And (A.strong_temporal (writer_points_to address value) tail) (A.Pure (BEq (EVar x) value)))
| OwnedStoreAny mode address old value annotation tail :
    owned_derivation active invariant mode (A.strong_temporal (writer_points_to address old) tail)
      (C.Prim (C.Common (S.Store address value)) annotation)
      (A.Temporal (A.strong_temporal (writer_points_to address old) tail) (A.LeadsTo address annotation value))
| OwnedFence mode annotation :
    owned_derivation active invariant mode A.Emp
      (C.Prim (C.Common S.Fence) annotation) (A.Barrier annotation)
| OwnedLock mode owner :
    owned_derivation active invariant mode A.Emp (C.Prim C.Lock (EVal (Z.pos owner)))
      (A.Temporal (A.Spatial (A.Lock (EVal (Z.pos owner))) invariant) (A.Barrier (EVal (Z.pos owner))))
| OwnedUnlock pre post owner :
    persistent_entails active (A.Temporal pre (A.Barrier (EVal (Z.pos owner)))) (A.Spatial invariant post) ->
    owned_derivation active invariant DisjointMode (A.Spatial (A.Lock (EVal (Z.pos owner))) pre)
      (C.Prim C.Unlock (EVal (Z.pos owner))) post
| OwnedSequence mode pre middle post first second :
    owned_derivation active invariant mode pre first middle ->
    owned_derivation active invariant mode middle second post ->
    owned_derivation active invariant mode pre (C.Seq first second) post
| OwnedConsequence mode pre pre' command post' post :
    persistent_entails active pre pre' ->
    owned_derivation active invariant mode pre' command post' ->
    persistent_entails active post' post ->
    owned_derivation active invariant mode pre command post
| OwnedDisjunction mode pre pre' command post :
    owned_derivation active invariant mode pre command post ->
    owned_derivation active invariant mode pre' command post ->
    owned_derivation active invariant mode (A.Or pre pre') command post
| OwnedChoice mode pre left right post :
    owned_derivation active invariant mode pre left post ->
    owned_derivation active invariant mode pre right post ->
    owned_derivation active invariant mode pre (C.Choice left right) post
| OwnedLoop mode pre body :
    owned_derivation active invariant mode pre body pre ->
    owned_derivation active invariant mode pre (C.Loop body) pre
| OwnedExists mode pre command post x :
    ~ In x (A.fv invariant) -> ~ In x (C.fv command) -> ~ In x (A.fv post) ->
    owned_derivation active invariant mode pre command post ->
    owned_derivation active invariant mode (A.Exists x pre) command post
| OwnedFrameSP mode pre command post frame :
    owned_derivation active invariant mode pre command post -> frame_variable_condition command frame ->
    owned_derivation active invariant mode (A.Spatial frame pre) command (A.Spatial frame post)
| OwnedFrameTM pre command post frame :
    owned_derivation active invariant OverlapMode pre command post -> frame_variable_condition command frame ->
    owned_derivation active invariant OverlapMode (A.Temporal frame pre) command (A.Temporal frame post)
| OwnedParallel mode left_pre left left_post right_pre right right_post :
    owned_derivation active invariant mode left_pre left left_post ->
    owned_derivation active invariant mode right_pre right right_post ->
    parallel_variable_condition (Build_concurrent_specification invariant left_pre left left_post)
      (Build_concurrent_specification invariant right_pre right right_post) ->
    frame_variable_condition left invariant -> frame_variable_condition right invariant ->
    owned_derivation active invariant mode (A.Spatial left_pre right_pre)
      (C.Parallel left right) (A.Spatial left_post right_post)
| OwnedWeaken pre command post :
    owned_derivation active invariant OverlapMode pre command post ->
    owned_derivation active invariant DisjointMode pre command post.

Theorem owned_calculus_sound active invariant :
  invariant_fragment invariant -> two_active_processors active ->
  forall mode pre command post, owned_derivation active invariant mode pre command post ->
  owned_valid active mode invariant pre command post.
Proof.
  intros Hfragment Htwo mode pre command post Hderive; induction Hderive.
  - apply owned_skip_valid.
  - apply owned_assignment_valid, H.
  - apply owned_assume_valid.
  - apply owned_assert_valid.
  - apply owned_load_valid; assumption.
  - apply owned_store_valid.
  - apply owned_load_any_writer_valid; assumption.
  - apply owned_store_any_writer_valid.
  - apply owned_fence_valid.
  - apply owned_lock_valid; assumption.
  - apply owned_unlock_valid; assumption.
  - eapply owned_sequence_valid; eassumption.
  - eapply owned_consequence_valid; eassumption.
  - apply owned_disjunction_valid; assumption.
  - apply owned_choice_valid; assumption.
  - apply owned_loop_valid; assumption.
  - apply owned_exists_valid; assumption.
  - apply owned_spatial_frame_valid; assumption.
  - apply owned_temporal_frame_valid; assumption.
  - apply owned_parallel_valid; assumption.
  - apply owned_valid_overlap_disjoint; assumption.
Qed.

(** Operational soundness from a concrete free-pool start. There is no
    semantic validity premise, external-frame premise, or leftover mode test. *)
Theorem owned_derivation_adequacy active invariant :
  invariant_fragment invariant -> two_active_processors active ->
  forall mode pre command post, owned_derivation active invariant mode pre command post ->
  forall n s whole last t final local pool,
    persistent_models active s local pre ->
    persistent_full_satisfies active s pool invariant -> lock_free whole ->
    memory_spatial pool (resource_memory active local) whole ->
    execution active n command s whole last t final ->
    ~ abort active last (State t final) /\
    (terminal last -> exists local' pool',
      memory_spatial pool' (resource_memory active local') final /\
      persistent_models active t local' post /\
      ((lock_free final /\ persistent_full_satisfies active t pool' invariant) \/
        exists owner, lock_held active (resource_memory active local') owner /\ pool' = empty_memory)).
Proof.
  intros Hfragment Htwo mode pre command post Hderive n s whole last t final local pool HP HJ Hfree Hsp Hrun.
  eapply owned_valid_adequacy; [exact Htwo |exact Hfragment
    |apply owned_calculus_sound; eassumption |exact HP |exact HJ |exact Hfree |exact Hsp |exact Hrun].
Qed.
