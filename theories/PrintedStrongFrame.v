From Stdlib Require Import List ZArith.
From WMLR Require Import Expressions Languages Machine BufferRelations Separation Assertions AssertionSemantics
  ConcreteAssertions Safety Specifications ExecutionExamples PrintedDerivations PrintedPointsToDerivations.
Import ListNotations.

(** Queue 5.4: the independent-witness pattern in the PRINTED calculus.
    This extends the reviewed four-rule subset only by printed FRAME-STM.
    Its premise uses INV donation in place of the repaired transferring
    release. No FRAME-TM instance is used in the derivation below. *)
Inductive printed_with_stm active : A.assertion -> A.assertion -> Concurrent.command -> A.assertion -> Prop :=
| PrintedCore J P c Q : printed active J P c Q -> printed_with_stm active J P c Q
| PrintedFrameSTM J P c Q R :
    printed_with_stm active J P c Q -> frame_variable_condition c R ->
    printed_with_stm active J (A.strong_temporal R P) c (A.strong_temporal R Q).

Definition printed_stm_invariant := A.Or A.Emp (printed_cell X 7%Z).
Definition printed_stm_frame := A.Or A.Emp (printed_cell X 5%Z).
Definition printed_stm_pre := A.Spatial (printed_cell X 7%Z) (lockA P1).
Definition printed_stm_post := A.Spatial A.Emp (lockA P1).

Theorem printed_stm_donation_derivation :
  printed_with_stm two_processors printed_stm_invariant
    (A.strong_temporal printed_stm_frame printed_stm_pre) (skip1 P1)
    (A.strong_temporal printed_stm_frame printed_stm_post).
Proof.
  apply PrintedFrameSTM; [|apply skip_frame_condition].
  apply PrintedCore,PInv; eapply PCons;
    [apply printed_points_donate |apply PSkip |apply entails_refl].
Qed.

Lemma printed_stm_initial_models s :
  full_satisfies two_processors s held7 (A.strong_temporal printed_stm_frame printed_stm_pre).
Proof.
  destruct (printed_points_held7_pre s) as (r & Er & HP).
  exists r; split; [exact Er |]. split.
  - exists (empty_resource_value two_processors),r; split; [apply spatial_empty_left |].
    split; [left |exact HP]; repeat split; simpl; auto; intros i H; exact H.
  - pose proof (printed_points_invent two_processors X 5%Z 7%Z P1 s r HP)
      as (a & b & Htm & HA & HB).
    exists a,b; split; [exact Htm |split; [right; exact HA |exact HB]].
Qed.

Lemma printed_stm_final_impossible s :
  ~ full_satisfies two_processors s held7 (A.strong_temporal printed_stm_frame printed_stm_post).
Proof.
  intros (r & Er & Hsp & a & b & Htm & [HA |HA] & HB).
  - destruct HA as [Hah Harest]; destruct HB as (e & l & Hsp' & HE & HL).
    destruct HE as [Heh Herest]; destruct (lock_elim _ _ _ _ HL) as [Hlh Hlrest].
    pose proof (proj1 (spatial_parts _ _ _ Hsp')) as Hbh.
    pose proof (proj1 (temporal_parts _ _ _ _ Htm)) as Hrh.
    unfold hp in Hrh,Hbh,Hlh.
    specialize (Hrh X); unfold heap_override in Hrh; rewrite Hbh in Hrh.
    unfold heap_override in Hrh; rewrite Hlh,Heh,Hah in Hrh.
    rewrite Er in Hrh; cbn in Hrh; discriminate.
  - apply (printed_points_held7_not_post s); exists r; split; [exact Er |].
    apply (printed_points_unit two_processors X 5%Z P1 s r).
    exists a,b; split; [exact Htm |split; assumption].
Qed.

Theorem printed_strong_frame_counterexample :
  printed_with_stm two_processors printed_stm_invariant
    (A.strong_temporal printed_stm_frame printed_stm_pre) (skip1 P1)
    (A.strong_temporal printed_stm_frame printed_stm_post) /\
  (forall s, full_satisfies two_processors s held7
      (A.strong_temporal printed_stm_frame printed_stm_pre) /\
    ~ full_satisfies two_processors s held7
      (A.strong_temporal printed_stm_frame printed_stm_post)) /\
  ~ valid_specification two_processors printed_stm_invariant
    (A.strong_temporal printed_stm_frame printed_stm_pre) (skip1 P1)
    (A.strong_temporal printed_stm_frame printed_stm_post).
Proof.
  split; [apply printed_stm_donation_derivation |]. split.
  - intros; split; [apply printed_stm_initial_models |apply printed_stm_final_impossible].
  - apply (skip_needs_post _ _ _ _ _ (fun _ => 0%Z) held7);
      [apply printed_stm_initial_models |apply printed_stm_final_impossible].
Qed.
