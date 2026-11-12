From Stdlib Require Import List ZArith.
From WMLR Require Import Expressions Languages Machine Separation OperationalSemantics
  Assertions AssertionSemantics Specifications PersistentAssertions PersistentRules AssertionSubstitution
  Safety TemporalSafety RegionalResources InvariantFragment OwnedSafety OwnedHeap OwnedCalculus
  OwnedContainerEntailments.
Import ListNotations.

Lemma owned_derive_load_cell active invariant mode address value annotation x :
  ~ In x (A.fv invariant) -> ~ In x (expr_fv address ++ expr_fv value) ->
  owned_derivation active invariant mode (writer_points_to address value)
    (C.Prim (C.Common (S.Load x address)) annotation)
    (A.And (writer_points_to address value) (A.Pure (BEq (EVar x) value))).
Proof.
  intros HJ Hfresh; eapply OwnedConsequence.
  - intros s r H; apply persistent_strong_emp_right, H.
  - apply OwnedLoadAny; [exact HJ |cbn [A.fv]; rewrite app_nil_r; exact Hfresh].
  - intros s r [[Hsp Htm] Hb]; split; [|exact Hb].
    eapply container_spatial_emp_elim; [cbn [writer_points_to wand_free]; tauto |exact Hsp].
Qed.

Lemma owned_derive_store_cell active invariant mode address old value annotation :
  owned_derivation active invariant mode (writer_points_to address old)
    (C.Prim (C.Common (S.Store address value)) annotation)
    (A.Temporal (writer_points_to address old) (A.LeadsTo address annotation value)).
Proof.
  eapply OwnedConsequence.
  - intros s r H; apply persistent_strong_emp_right, H.
  - apply OwnedStoreAny.
  - eapply container_temporal_mono; [|intros s r H; exact H].
    intros s r [Hsp Htm]; eapply container_spatial_emp_elim;
      [cbn [writer_points_to wand_free]; tauto |exact Hsp].
Qed.

Lemma owned_derive_assign_from active invariant mode pre post x rhs annotation :
  ~ In x (A.fv invariant) ->
  (forall s r, persistent_models active s r pre ->
    persistent_models active (update s x (eval_expr s rhs)) r post) ->
  owned_derivation active invariant mode pre (C.Prim (C.Common (S.Assign x rhs)) annotation) post.
Proof.
  intros Hfresh Hpost; eapply OwnedConsequence; [|apply OwnedAssign, Hfresh |intros s r H; exact H].
  intros s r H; apply (proj2 (persistent_assertion_subst _ _ _ _ _ _)), Hpost, H.
Qed.

Lemma owned_derive_while active invariant mode pre condition annotation body :
  owned_derivation active invariant mode (A.And pre (A.Pure condition)) body pre ->
  owned_derivation active invariant mode pre (C.while_do annotation condition body)
    (A.And pre (A.Pure (BNot condition))).
Proof.
  intros Hbody; unfold C.while_do; eapply OwnedSequence with (middle := pre).
  - apply OwnedLoop; eapply OwnedSequence; [|exact Hbody].
    eapply OwnedConsequence; [|apply OwnedAssume |intros s r H; exact H].
    intros s r HP; destruct (eval_bexpr s condition) eqn:E; [right; split; assumption |left; change (negb (eval_bexpr s condition) = true); rewrite E; reflexivity].
  - eapply OwnedConsequence; [|apply OwnedAssume |intros s r H; exact H].
    intros s r HP; destruct (eval_bexpr s condition) eqn:E.
    + left; change (negb (negb (eval_bexpr s condition)) = true); rewrite E; reflexivity.
    + right; split; [exact HP |change (negb (eval_bexpr s condition) = true); rewrite E; reflexivity].
Qed.

Lemma owned_derive_unlock_false active invariant owner :
  owned_derivation active invariant DisjointMode (A.Pure BFalse)
    (C.Prim C.Unlock (EVal (Z.pos owner))) (A.Pure BFalse).
Proof.
  eapply OwnedConsequence with (pre' := A.Spatial (A.Lock (EVal (Z.pos owner))) (A.Pure BFalse)).
  - intros s r H; discriminate H.
  - apply OwnedUnlock; intros s r (a & b & Htm & Hfalse & Hbar); discriminate Hfalse.
  - intros s r H; exact H.
Qed.
