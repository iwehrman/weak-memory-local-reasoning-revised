From Stdlib Require Import List ZArith.
From WMLR Require Import Expressions Languages Machine OperationalSemantics Assertions AssertionSemantics
  Specifications InvariantFragment OwnedSafety OwnedCalculus OwnedDerivedRules
  AssertionDerivation AssertionDerivedRules AssertionRearrangements AssertionClientRules OwnedAssertionRules.
Import ListNotations.

(** Program proof trees with assertion-derivation premises throughout. *)
Lemma owned_assertion_frame_right active invariant mode pre command post frame :
  owned_derivation active invariant mode pre command post -> frame_variable_condition command frame ->
  owned_derivation active invariant mode (A.Spatial pre frame) command (A.Spatial post frame).
Proof.
  intros HD HF; eapply owned_assertion_consequence
    with (pre' := A.Spatial frame pre) (post' := A.Spatial frame post);
    [apply AssertSpatialComm |apply OwnedFrameSP; assumption |apply AssertSpatialComm].
Qed.

Lemma owned_assertion_pure_frame active invariant mode pre command post b :
  owned_derivation active invariant mode pre command post -> frame_variable_condition command (A.Pure b) ->
  owned_derivation active invariant mode (A.And pre (A.Pure b)) command (A.And post (A.Pure b)).
Proof.
  intros HD HF; eapply owned_assertion_consequence;
    [apply assert_derive_pure_frame_intro | |apply assert_derive_pure_frame_elim].
  apply OwnedFrameSP; [exact HD |].
  unfold frame_variable_condition in *; cbn [A.fv]; rewrite app_nil_r; exact HF.
Qed.

Lemma owned_assertion_fence_after active invariant mode pre annotation :
  owned_derivation active invariant mode pre (C.Prim (C.Common S.Fence) annotation)
    (A.Temporal pre (A.Barrier annotation)).
Proof.
  destruct mode; [|apply OwnedWeaken];
    eapply owned_assertion_consequence with (pre' := A.Temporal pre A.Emp);
    [apply (AssertUnitRight active SepTemporal Backward)
    |apply OwnedFrameTM; [apply OwnedFence |intros x H; contradiction]
    |apply AssertRefl
    |apply (AssertUnitRight active SepTemporal Backward)
    |apply OwnedFrameTM; [apply OwnedFence |intros x H; contradiction]
    |apply AssertRefl].
Qed.

Theorem owned_assertion_store_fence active invariant mode address old value annotation :
  owned_derivation active invariant mode (writer_points_to address old)
    (C.Seq (C.Prim (C.Common (S.Store address value)) annotation)
      (C.Prim (C.Common S.Fence) annotation)) (writer_points_to address value).
Proof.
  eapply OwnedSequence; [apply owned_derive_store_cell |].
  eapply owned_assertion_consequence;
    [apply AssertRefl |apply owned_assertion_fence_after |apply assert_derive_cell_write_drained].
Qed.

Lemma owned_assertion_load_spatial active invariant mode address value annotation x frame :
  ~ In x (A.fv invariant) -> ~ In x (expr_fv address ++ expr_fv value ++ A.fv frame) ->
  owned_derivation active invariant mode (A.Spatial frame (writer_points_to address value))
    (C.Prim (C.Common (S.Load x address)) annotation)
    (A.And (A.Spatial frame (writer_points_to address value)) (A.Pure (BEq (EVar x) value))).
Proof.
  intros HJ Hfresh; rewrite !in_app_iff in Hfresh.
  eapply owned_assertion_consequence; [apply AssertRefl | |].
  - apply OwnedFrameSP.
    + apply owned_derive_load_cell; [exact HJ |rewrite in_app_iff; tauto].
    + intros y Hy; cbn in Hy; destruct Hy as [<- |H]; [tauto |contradiction].
  - apply (AssertPureSeparateRight active SepSpatial Forward).
Qed.
