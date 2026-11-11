From Stdlib Require Import List ZArith.
From WMLR Require Import Expressions Languages Assertions AssertionSemantics Specifications
  HeapRules OwnershipProtocol OwnershipHeap OwnershipCalculus RegionalSafety SeparatedSafety SeparatedRules SeparatedHeap.

(** Two assertion positions, with componentwise consequence. The existing
    bounded protected calculus supplies heap operations and invariant transfer.
    No constructor assumes validity, safety, or the conclusion of framing. *)
Inductive separated_derivation active owner invariant : ownership_phase ->
    A.assertion -> A.assertion -> Concurrent.command -> ownership_phase -> A.assertion -> A.assertion -> Prop :=
| SeparateProtected start protected_pre private_assertion command finish protected_post :
    ownership_derivation active owner invariant start protected_pre command finish protected_post ->
    frame_variable_condition command private_assertion ->
    separated_derivation active owner invariant start protected_pre private_assertion command finish protected_post private_assertion
| SeparateFence phase protected_assertion i :
    separated_derivation active owner invariant phase protected_assertion A.Emp
      (Concurrent.Prim (Concurrent.Common Sequential.Fence) (EVal (Z.pos i)))
      phase protected_assertion (A.Barrier (EVal (Z.pos i)))
| SeparateLoad phase protected_assertion loc v x :
    ~ In x (A.fv invariant) -> ~ In x (A.fv protected_assertion) ->
    separated_derivation active owner invariant phase protected_assertion (cell_assertion loc v)
      (Concurrent.Prim (Concurrent.Common (Sequential.Load x (EVal (Z.pos loc)))) (EVal (Z.pos owner)))
      phase protected_assertion (A.And (cell_assertion loc v) (A.Pure (BEq (EVar x) (EVal v))))
| SeparateSequence start protected_pre pre first middle protected_mid mid second finish protected_post post :
    separated_derivation active owner invariant start protected_pre pre first middle protected_mid mid ->
    separated_derivation active owner invariant middle protected_mid mid second finish protected_post post ->
    separated_derivation active owner invariant start protected_pre pre (Concurrent.Seq first second) finish protected_post post
| SeparateConsequence start protected_pre pre protected_pre' pre' command finish protected_post' post' protected_post post :
    regional_entails active protected_pre protected_pre' -> regional_entails active pre pre' ->
    separated_derivation active owner invariant start protected_pre' pre' command finish protected_post' post' ->
    regional_entails active protected_post' protected_post -> regional_entails active post' post ->
    separated_derivation active owner invariant start protected_pre pre command finish protected_post post
| SeparateFrameTM start protected_pre pre command finish protected_post post frame :
    separated_derivation active owner invariant start protected_pre pre command finish protected_post post ->
    frame_variable_condition command frame ->
    separated_derivation active owner invariant start protected_pre (A.Temporal frame pre) command finish
      protected_post (A.Temporal frame post).

Theorem separated_calculus_sound active owner invariant start protected_pre pre command finish protected_post post :
  separated_derivation active owner invariant start protected_pre pre command finish protected_post post ->
  separated_valid active owner invariant start protected_pre pre command finish protected_post post.
Proof.
  induction 1.
  - apply separated_protocol_valid; [apply ownership_calculus_sound |]; assumption.
  - apply separated_fence_valid.
  - apply separated_load_cell_valid; assumption.
  - eapply separated_sequence_valid; eassumption.
  - eapply separated_consequence_valid; eassumption.
  - apply separated_temporal_frame_valid; assumption.
Qed.
