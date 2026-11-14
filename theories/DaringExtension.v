From Stdlib Require Import List ZArith.
From WMLR Require Import Expressions Languages Machine Separation OperationalSemantics
  Assertions AssertionSemantics Specifications PersistentAssertions PersistentRules AssertionSubstitution
  Safety TemporalSafety InvariantFragment LockRepresentation OwnedSafety OwnedAdequacy OwnedResources OwnedRules
  OwnedFraming OwnedParallel OwnedStructural OwnedPrimitives OwnedHeap OwnedExists OwnedCalculus.
Import ListNotations.

(** Stage 1 only: the 21 existing rule schemas, plus the original
    DARING-LOAD. This extension is deliberately UNSOUND. The invariant is
    an index so the new rule's premise can use the empty invariant. *)
Inductive daring_load_extension active : A.assertion -> ownership_mode -> A.assertion -> C.command -> A.assertion -> Prop :=
| DaringSkip invariant mode pre annotation :
    daring_load_extension active invariant mode pre (C.skip annotation) pre
| DaringAssign invariant mode post x rhs annotation : ~ In x (A.fv invariant) ->
    daring_load_extension active invariant mode (assertion_subst x rhs post)
      (C.Prim (C.Common (S.Assign x rhs)) annotation) post
| DaringAssume invariant mode pre condition annotation :
    daring_load_extension active invariant mode (A.Or (A.Pure (BNot condition)) pre)
      (C.Prim (C.Common (S.Assume condition)) annotation) pre
| DaringAssert invariant mode pre condition annotation :
    daring_load_extension active invariant mode (A.And (A.Pure condition) pre)
      (C.Prim (C.Common (S.Assert condition)) annotation) pre
| DaringLoad invariant mode address value annotation tail x :
    ~ In x (A.fv invariant) ->
    ~ In x (expr_fv address ++ expr_fv annotation ++ expr_fv value ++ A.fv tail) ->
    daring_load_extension active invariant mode (A.strong_temporal (A.LeadsTo address annotation value) tail)
      (C.Prim (C.Common (S.Load x address)) annotation)
      (A.And (A.strong_temporal (A.LeadsTo address annotation value) tail) (A.Pure (BEq (EVar x) value)))
| DaringStore invariant mode address old value annotation tail :
    daring_load_extension active invariant mode (A.strong_temporal (A.LeadsTo address annotation old) tail)
      (C.Prim (C.Common (S.Store address value)) annotation)
      (A.Temporal (A.strong_temporal (A.LeadsTo address annotation old) tail) (A.LeadsTo address annotation value))
| DaringLoadAny invariant mode address value annotation tail x :
    ~ In x (A.fv invariant) -> ~ In x (expr_fv address ++ expr_fv value ++ A.fv tail) ->
    daring_load_extension active invariant mode (A.strong_temporal (writer_points_to address value) tail)
      (C.Prim (C.Common (S.Load x address)) annotation)
      (A.And (A.strong_temporal (writer_points_to address value) tail) (A.Pure (BEq (EVar x) value)))
| DaringStoreAny invariant mode address old value annotation tail :
    daring_load_extension active invariant mode (A.strong_temporal (writer_points_to address old) tail)
      (C.Prim (C.Common (S.Store address value)) annotation)
      (A.Temporal (A.strong_temporal (writer_points_to address old) tail) (A.LeadsTo address annotation value))
| DaringFence invariant mode annotation :
    daring_load_extension active invariant mode A.Emp
      (C.Prim (C.Common S.Fence) annotation) (A.Barrier annotation)
| DaringLock invariant mode owner :
    daring_load_extension active invariant mode A.Emp (C.Prim C.Lock (EVal (Z.pos owner)))
      (A.Temporal (A.Spatial (A.Lock (EVal (Z.pos owner))) invariant) (A.Barrier (EVal (Z.pos owner))))
| DaringUnlock invariant pre post owner :
    persistent_entails active (A.Temporal pre (A.Barrier (EVal (Z.pos owner)))) (A.Spatial invariant post) ->
    daring_load_extension active invariant DisjointMode (A.Spatial (A.Lock (EVal (Z.pos owner))) pre)
      (C.Prim C.Unlock (EVal (Z.pos owner))) post
| DaringSequence invariant mode pre middle post first second :
    daring_load_extension active invariant mode pre first middle ->
    daring_load_extension active invariant mode middle second post ->
    daring_load_extension active invariant mode pre (C.Seq first second) post
| DaringConsequence invariant mode pre pre' command post' post :
    persistent_entails active pre pre' ->
    daring_load_extension active invariant mode pre' command post' ->
    persistent_entails active post' post ->
    daring_load_extension active invariant mode pre command post
| DaringDisjunction invariant mode pre pre' command post :
    daring_load_extension active invariant mode pre command post ->
    daring_load_extension active invariant mode pre' command post ->
    daring_load_extension active invariant mode (A.Or pre pre') command post
| DaringChoice invariant mode pre left right post :
    daring_load_extension active invariant mode pre left post ->
    daring_load_extension active invariant mode pre right post ->
    daring_load_extension active invariant mode pre (C.Choice left right) post
| DaringLoop invariant mode pre body :
    daring_load_extension active invariant mode pre body pre ->
    daring_load_extension active invariant mode pre (C.Loop body) pre
| DaringExists invariant mode pre command post x :
    ~ In x (A.fv invariant) -> ~ In x (C.fv command) -> ~ In x (A.fv post) ->
    daring_load_extension active invariant mode pre command post ->
    daring_load_extension active invariant mode (A.Exists x pre) command post
| DaringFrameSP invariant mode pre command post frame :
    daring_load_extension active invariant mode pre command post -> frame_variable_condition command frame ->
    daring_load_extension active invariant mode (A.Spatial frame pre) command (A.Spatial frame post)
| DaringFrameTM invariant pre command post frame :
    daring_load_extension active invariant OverlapMode pre command post -> frame_variable_condition command frame ->
    daring_load_extension active invariant OverlapMode (A.Temporal frame pre) command (A.Temporal frame post)
| DaringParallel invariant mode left_pre left left_post right_pre right right_post :
    daring_load_extension active invariant mode left_pre left left_post ->
    daring_load_extension active invariant mode right_pre right right_post ->
    parallel_variable_condition (Build_concurrent_specification invariant left_pre left left_post)
      (Build_concurrent_specification invariant right_pre right right_post) ->
    frame_variable_condition left invariant -> frame_variable_condition right invariant ->
    daring_load_extension active invariant mode (A.Spatial left_pre right_pre)
      (C.Parallel left right) (A.Spatial left_post right_post)
| DaringWeaken invariant pre command post :
    daring_load_extension active invariant OverlapMode pre command post ->
    daring_load_extension active invariant DisjointMode pre command post
| DaringLoadRule invariant mode pre post address annotation x :
    daring_load_extension active A.Emp mode (A.Spatial invariant pre)
      (C.Prim (C.Common (S.Load x address)) annotation) (A.Spatial invariant post) ->
    daring_load_extension active invariant mode pre
      (C.Prim (C.Common (S.Load x address)) annotation) post.

(** The old calculus embeds without changing any constructor or hypothesis. *)
Theorem daring_load_embeds_owned active invariant mode pre command post :
  owned_derivation active invariant mode pre command post ->
  daring_load_extension active invariant mode pre command post.
Proof.
  induction 1; econstructor; eassumption.
Qed.
