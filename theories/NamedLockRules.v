From Stdlib Require Import List ZArith.
From WMLR Require Import Expressions Languages Machine OperationalSemantics Assertions AssertionSemantics
  Specifications InvariantFragment OwnedSafety OwnedCalculus OwnedDerivedRules AssertionDerivation
  AssertionDerivedRules AssertionRearrangements AssertionClientRules OwnedAssertionRules OwnedClientRules
  OwnedLoopRules MessagePassingAssertions NamedLockSyntax NamedLockAssertions.
Import ListNotations.

Lemma nl_load_held_derived active pool actor flag x tail value :
  ~ In x (A.fv pool) -> ~ In x (A.fv tail) ->
  owned_derivation active pool DisjointMode (nl_held actor (A.Spatial (nl_cell flag value) tail))
    (nl_load actor flag x)
    (A.And (nl_held actor (A.Spatial (nl_cell flag value) tail)) (A.Pure (nl_is x value))).
Proof.
  intros HJ Htail; eapply owned_assertion_consequence.
  - apply assert_derive_spatial_swap.
  - apply owned_assertion_load_spatial; [exact HJ |exact Htail].
  - apply assert_derive_and_mono; [apply assert_derive_spatial_restore |apply AssertRefl].
Qed.

Theorem nl_attempt_derived active pool actor flag x invariant rest :
  assertion_derivation active pool (A.Spatial (nl_component flag invariant) rest) ->
  assertion_derivation active (A.Spatial (nl_component flag invariant) rest) pool ->
  ~ In x (A.fv pool) -> ~ In x (A.fv invariant ++ A.fv rest) ->
  owned_derivation active pool DisjointMode A.Emp (nl_attempt actor flag x) (nl_loop_invariant x invariant).
Proof.
  intros Hout Hin HJ HF; rewrite in_app_iff in HF.
  eapply OwnedSequence with (middle := nl_cases actor flag invariant rest).
  - eapply owned_assertion_consequence; [apply AssertRefl |apply OwnedLock |].
    eapply AssertTrans; [apply assert_derive_barrier_suffix |].
    eapply AssertTrans; [apply (AssertSeparateMono active SepSpatial); [apply AssertRefl |exact Hout] |apply nl_assert_cases].
  - eapply OwnedSequence with (middle := nl_read_cases actor flag x invariant rest).
    + apply OwnedDisjunction.
      * eapply owned_assertion_consequence; [apply AssertRefl |apply nl_load_held_derived |apply AssertOrLeft];
          [exact HJ |cbn [A.fv]; rewrite in_app_iff; tauto].
      * eapply owned_assertion_consequence; [apply AssertRefl |apply nl_load_held_derived |apply AssertOrRight]; tauto.
    + apply OwnedChoice.
      * eapply OwnedSequence.
        -- eapply owned_assertion_consequence; [apply nl_assert_select_zero |apply OwnedAssume |apply AssertRefl].
        -- eapply owned_assertion_consequence; [apply AssertRefl | |apply AssertOrLeft].
           apply owned_assertion_pure_frame; [|intros y H; contradiction].
           eapply OwnedSequence.
           ++ apply OwnedFrameSP; [|intros y H; contradiction].
              apply owned_assertion_frame_right; [apply owned_derive_store_cell |intros y H; contradiction].
           ++ apply owned_assertion_unlock,nl_assert_take_donation,Hin.
      * eapply OwnedSequence.
        -- eapply owned_assertion_consequence; [apply nl_assert_select_not_zero |apply OwnedAssume |apply AssertRefl].
        -- eapply owned_assertion_consequence; [apply AssertRefl | |apply AssertOrRight].
           apply owned_assertion_pure_frame; [apply owned_assertion_unlock; eapply nl_assert_retry_donation; exact Hin |intros y H; contradiction].
Qed.

Theorem nl_acquire_derived active pool actor flag x invariant rest :
  assertion_derivation active pool (A.Spatial (nl_component flag invariant) rest) ->
  assertion_derivation active (A.Spatial (nl_component flag invariant) rest) pool ->
  ~ In x (A.fv pool) -> ~ In x (A.fv invariant ++ A.fv rest) ->
  owned_derivation active pool DisjointMode A.Emp (nl_acquire actor flag x) invariant.
Proof.
  intros Hout Hin HJ HF; eapply OwnedSequence with (middle := nl_loop_invariant x invariant).
  - eapply owned_assertion_consequence; [apply AssertRefl |apply owned_assertion_set_emp,HJ |apply AssertOrRight].
  - eapply owned_assertion_consequence; [apply AssertRefl |apply owned_assertion_while |apply nl_assert_loop_finish].
    eapply owned_assertion_consequence; [apply nl_assert_loop_continue |eapply nl_attempt_derived; eassumption |apply AssertRefl].
Qed.

Theorem nl_release_derived active pool actor flag invariant rest :
  assertion_derivation active pool (A.Spatial (nl_component flag invariant) rest) ->
  assertion_derivation active (A.Spatial (nl_component flag invariant) rest) pool ->
  assertion_derivation active (A.Spatial invariant invariant) (A.Pure BFalse) ->
  owned_derivation active pool DisjointMode invariant (nl_release actor flag) A.Emp.
Proof.
  intros Hout Hin Hex; eapply OwnedSequence with
    (middle := nl_held actor (A.Spatial (nl_cell flag 1%Z) (A.Spatial invariant rest))).
  - eapply owned_assertion_consequence; [apply (AssertUnitRight active SepSpatial Backward) | |].
    + apply OwnedFrameSP; [apply OwnedLock |intros x H; contradiction].
    + apply mp_assert_acquire.
      eapply AssertTrans; [apply (AssertSeparateMono active SepSpatial); [apply AssertRefl |exact Hout]
        |apply nl_assert_release_payload,Hex].
  - eapply OwnedSequence.
    + apply OwnedFrameSP; [|intros x H; contradiction].
      apply owned_assertion_frame_right; [apply owned_derive_store_cell |intros x H; contradiction].
    + apply owned_assertion_unlock,nl_assert_return_donation,Hin.
Qed.

(** The selected component is exposed by proof trees, not by changing the
    invariant in the program judgment. The remainder contains every other
    component, including any repeated list entries. *)
Theorem nl_pool_focus active locks flag invariant : In (flag,invariant) locks ->
  exists rest,
    (forall x, In x (A.fv invariant ++ A.fv rest) -> In x (A.fv (nl_pool locks))) /\
    assertion_derivation active (nl_pool locks) (A.Spatial (nl_component flag invariant) rest) /\
    assertion_derivation active (A.Spatial (nl_component flag invariant) rest) (nl_pool locks).
Proof.
  induction locks as [|[head HI] tail IH]; cbn [In]; [contradiction |intros [E |Hin]].
  - inversion E; subst; exists (nl_pool tail); split.
    + intros x H; cbn [nl_pool A.fv]; rewrite nl_component_fv; exact H.
    + split; apply AssertRefl.
  - destruct (IH Hin) as (rest & HF & Hout & Hback).
    exists (A.Spatial (nl_component head HI) rest); split.
    + intros x H; cbn [nl_pool A.fv] in *; rewrite nl_component_fv in *.
      apply in_app_iff in H; apply in_app_iff; destruct H as [H |H].
      * right; apply HF,in_or_app; left; exact H.
      * apply in_app_iff in H; destruct H as [H |H]; [left; exact H |].
        right; apply HF,in_or_app; right; exact H.
    + split.
      * eapply AssertTrans; [apply (AssertSeparateMono active SepSpatial); [apply AssertRefl |exact Hout]
          |apply assert_derive_spatial_rotate].
      * eapply AssertTrans; [apply assert_derive_spatial_rotate |].
        apply (AssertSeparateMono active SepSpatial); [apply AssertRefl |exact Hback].
Qed.

Theorem named_lock_acquire_family active locks flag invariant actor x :
  In (flag,invariant) locks -> ~ In x (A.fv (nl_pool locks)) ->
  owned_derivation active (nl_pool locks) DisjointMode A.Emp (nl_acquire actor flag x) invariant.
Proof.
  intros Hin Hfresh; destruct (nl_pool_focus active locks flag invariant Hin) as (rest & HF & Hout & Hback).
  eapply nl_acquire_derived; [exact Hout |exact Hback |exact Hfresh |intros H; apply Hfresh,HF,H].
Qed.

Theorem named_lock_release_family active locks flag invariant actor : In (flag,invariant) locks ->
  assertion_derivation active (A.Spatial invariant invariant) (A.Pure BFalse) ->
  owned_derivation active (nl_pool locks) DisjointMode invariant (nl_release actor flag) A.Emp.
Proof.
  intros Hin Hex; destruct (nl_pool_focus active locks flag invariant Hin) as (rest & HF & Hout & Hback).
  eapply nl_release_derived; eassumption.
Qed.
