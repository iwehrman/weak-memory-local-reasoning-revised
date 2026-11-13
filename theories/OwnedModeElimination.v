From Stdlib Require Import List.
From WMLR Require Import Languages Assertions AssertionSemantics Specifications
  InvariantFragment OwnedSafety OwnedCalculus.
Module C := Concurrent.

(** Inspect the whole syntax, including unreachable branches and loop
    bodies. This guard concerns derivation replay, not reachability. *)
Fixpoint unlock_free (command : C.command) : Prop :=
  match command with
  | C.Prim C.Unlock _ => False
  | C.Prim _ _ => True
  | C.Seq first second | C.Choice first second | C.Parallel first second =>
      unlock_free first /\ unlock_free second
  | C.Loop body => unlock_free body
  end.

Theorem owned_derivation_unlock_free_overlap active invariant mode pre command post :
  owned_derivation active invariant mode pre command post -> unlock_free command ->
  owned_derivation active invariant OverlapMode pre command post.
Proof.
  intros Hderive; induction Hderive; cbn [unlock_free]; intros Hfree;
    try contradiction;
    try solve [econstructor; eauto; tauto].
  - eapply OwnedSequence; [apply IHHderive1 |apply IHHderive2]; tauto.
  - apply IHHderive,Hfree.
Qed.

Theorem owned_derivation_overlap_unlock_free active invariant mode pre command post :
  owned_derivation active invariant mode pre command post ->
  mode = OverlapMode -> unlock_free command.
Proof.
  intros Hderive; induction Hderive; cbn [unlock_free]; intros E;
    try discriminate; intuition.
  exact I.
Qed.

Corollary owned_overlap_derivable_iff_unlock_free active invariant pre command post :
  owned_derivation active invariant DisjointMode pre command post ->
  (owned_derivation active invariant OverlapMode pre command post <-> unlock_free command).
Proof.
  intros HD; split.
  - intros HO; eapply owned_derivation_overlap_unlock_free; [exact HO |reflexivity].
  - intros Hfree; eapply owned_derivation_unlock_free_overlap; eassumption.
Qed.

Theorem owned_derive_temporal_frame_unlock_free active invariant pre command post frame :
  owned_derivation active invariant DisjointMode pre command post ->
  unlock_free command -> frame_variable_condition command frame ->
  owned_derivation active invariant DisjointMode (A.Temporal frame pre) command (A.Temporal frame post).
Proof.
  intros HD Hfree Hvariables; apply OwnedWeaken,OwnedFrameTM; [|exact Hvariables].
  eapply owned_derivation_unlock_free_overlap; eassumption.
Qed.

Corollary owned_temporal_frame_unlock_free_valid active invariant pre command post frame :
  invariant_fragment invariant -> two_active_processors active ->
  owned_derivation active invariant DisjointMode pre command post ->
  unlock_free command -> frame_variable_condition command frame ->
  owned_valid active DisjointMode invariant (A.Temporal frame pre) command (A.Temporal frame post).
Proof.
  intros HJ Htwo HD Hfree HV; apply owned_calculus_sound; [exact HJ |exact Htwo |].
  apply owned_derive_temporal_frame_unlock_free; assumption.
Qed.
