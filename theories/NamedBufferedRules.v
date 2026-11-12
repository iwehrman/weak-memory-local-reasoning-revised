From Stdlib Require Import List ZArith.
From WMLR Require Import Expressions Languages Machine OperationalSemantics Assertions AssertionSemantics
  Specifications InvariantFragment OwnedSafety OwnedCalculus OwnedDerivedRules AssertionDerivation
  AssertionDerivedRules AssertionRearrangements AssertionClientRules OwnedAssertionRules OwnedClientRules
  OwnedLoopRules OwnedRetryRules MessagePassingAssertions NamedLockSyntax NamedLockAssertions
  NamedLockRules NamedBufferedAssertions.
Import ListNotations.

Lemma nl_acquire_cases_retained active pool actor flag invariant rest retained :
  assertion_derivation active pool (A.Spatial (nl_component flag invariant) rest) ->
  owned_derivation active pool DisjointMode retained (nl_acquire_global actor)
    (nl_cases actor flag invariant (A.Spatial retained rest)).
Proof.
  intros Hout; eapply owned_assertion_consequence;
    [apply (AssertUnitRight active SepSpatial Backward) | |].
  - apply OwnedFrameSP; [apply OwnedLock |intros x H; contradiction].
  - eapply AssertTrans; [apply mp_assert_acquire |apply nl_assert_cases].
    eapply AssertTrans; [apply (AssertSeparateMono active SepSpatial); [apply AssertRefl |exact Hout]
      |apply assert_derive_spatial_rotate].
Qed.

Lemma nl_read_cases_derived active pool actor flag x invariant rest :
  ~ In x (A.fv pool) -> ~ In x (A.fv invariant) -> ~ In x (A.fv rest) ->
  owned_derivation active pool DisjointMode (nl_cases actor flag invariant rest) (nl_load actor flag x)
    (nl_read_cases actor flag x invariant rest).
Proof.
  intros HJ HI HR; apply OwnedDisjunction.
  - eapply owned_assertion_consequence; [apply AssertRefl |apply nl_load_held_derived |apply AssertOrLeft];
      [exact HJ |cbn [A.fv]; rewrite in_app_iff; tauto].
  - eapply owned_assertion_consequence; [apply AssertRefl |apply nl_load_held_derived |apply AssertOrRight]; assumption.
Qed.

Theorem nl_attempt_retained_derived active pool actor flag x invariant rest retained :
  assertion_derivation active pool (A.Spatial (nl_component flag invariant) rest) ->
  assertion_derivation active (A.Spatial (nl_component flag invariant) rest) pool ->
  ~ In x (A.fv pool) -> ~ In x (A.fv invariant) -> ~ In x (A.fv rest) -> ~ In x (A.fv retained) ->
  owned_derivation active pool DisjointMode retained (nl_attempt actor flag x)
    (retry_assertion x retained (A.Spatial invariant (A.Temporal retained (A.Barrier (EVal (Z.pos actor)))))).
Proof.
  intros Hout Hin HJ HI HR HF; eapply OwnedSequence; [apply nl_acquire_cases_retained,Hout |].
  eapply OwnedSequence.
  - apply nl_read_cases_derived; [exact HJ |exact HI |cbn [A.fv]; rewrite in_app_iff; tauto].
  - apply OwnedChoice.
    + eapply OwnedSequence.
      * eapply owned_assertion_consequence; [apply nl_assert_select_zero |apply OwnedAssume |apply AssertRefl].
      * eapply owned_assertion_consequence; [apply AssertRefl | |apply AssertOrLeft].
        apply owned_assertion_pure_frame; [|intros y H; contradiction].
        eapply OwnedSequence.
        -- apply OwnedFrameSP; [|intros y H; contradiction].
           apply owned_assertion_frame_right; [apply owned_derive_store_cell |intros y H; contradiction].
        -- apply owned_assertion_unlock,nl_assert_take_retained,Hin.
    + eapply OwnedSequence.
      * eapply owned_assertion_consequence; [apply nl_assert_select_not_zero |apply OwnedAssume |apply AssertRefl].
      * eapply owned_assertion_consequence; [apply AssertRefl | |apply AssertOrRight].
        apply owned_assertion_pure_frame; [|intros y H; contradiction].
        apply owned_assertion_unlock; eapply nl_assert_retry_retained; exact Hin.
Qed.

Theorem named_lock_acquire_retained_family active locks flag invariant actor x retained :
  In (flag,invariant) locks -> ~ In x (A.fv (nl_pool locks)) -> ~ In x (A.fv retained) ->
  owned_derivation active (nl_pool locks) DisjointMode retained (nl_acquire actor flag x)
    (A.Spatial invariant (A.Temporal retained (A.Barrier (EVal (Z.pos actor))))).
Proof.
  intros Hin HJ HR; destruct (nl_pool_focus active locks flag invariant Hin) as (rest & HF & Hout & Hback).
  apply owned_assertion_retry; [exact HJ |exact HR |].
  eapply nl_attempt_retained_derived; [exact Hout |exact Hback |exact HJ | | |exact HR].
  - intros H; apply HJ,HF,in_or_app; left; exact H.
  - intros H; apply HJ,HF,in_or_app; right; exact H.
Qed.

Theorem nl_release_buffered_derived active pool actor flag invariant rest retained :
  assertion_derivation active pool (A.Spatial (nl_component flag invariant) rest) ->
  assertion_derivation active (A.Spatial (nl_component flag invariant) rest) pool ->
  assertion_derivation active (A.Temporal retained (A.Barrier (EVal (Z.pos actor)))) invariant ->
  assertion_derivation active (A.Spatial invariant invariant) (A.Pure BFalse) ->
  owned_derivation active pool DisjointMode retained (nl_release actor flag) A.Emp.
Proof.
  intros Hout Hin HC Hex; eapply OwnedSequence; [apply nl_acquire_cases_retained,Hout |].
  apply OwnedDisjunction.
  - eapply OwnedSequence.
    + apply OwnedFrameSP; [|intros x H; contradiction].
      apply owned_assertion_frame_right; [apply owned_derive_store_cell |intros x H; contradiction].
    + apply owned_assertion_unlock; eapply nl_assert_buffered_return_closed; eassumption.
  - eapply OwnedSequence.
    + apply OwnedFrameSP; [|intros x H; contradiction].
      apply owned_assertion_frame_right; [apply owned_derive_store_cell |intros x H; contradiction].
    + apply owned_assertion_unlock; eapply nl_assert_buffered_return_open; eassumption.
Qed.

Theorem named_lock_release_buffered_family active locks flag invariant actor retained : In (flag,invariant) locks ->
  assertion_derivation active (A.Temporal retained (A.Barrier (EVal (Z.pos actor)))) invariant ->
  assertion_derivation active (A.Spatial invariant invariant) (A.Pure BFalse) ->
  owned_derivation active (nl_pool locks) DisjointMode retained (nl_release actor flag) A.Emp.
Proof.
  intros Hin HC Hex; destruct (nl_pool_focus active locks flag invariant Hin) as (rest & HF & Hout & Hback).
  eapply nl_release_buffered_derived; eassumption.
Qed.
