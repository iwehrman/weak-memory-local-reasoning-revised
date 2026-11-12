From Stdlib Require Import List ZArith.
From WMLR Require Import Expressions Languages Machine OperationalSemantics Assertions AssertionSemantics
  Specifications InvariantFragment OwnedSafety OwnedCalculus OwnedDerivedRules
  AssertionDerivation AssertionDerivedRules AssertionRearrangements AssertionClientRules
  OwnedAssertionRules OwnedClientRules MessagePassingSyntax MessagePassingAssertions.
Import ListNotations.

Theorem mp_sender_derived active t r :
  owned_derivation active (mp_invariant t r) DisjointMode (mp_token t) mp_sender A.Emp.
Proof.
  eapply OwnedSequence with (middle := mp_held 1%positive (A.Spatial (mp_data 0%Z) (mp_token t))).
  - eapply owned_assertion_consequence;
      [apply (AssertUnitRight active SepSpatial Backward) | |apply mp_assert_acquire,mp_assert_sender_payload].
    apply OwnedFrameSP; [apply OwnedLock |intros x H; contradiction].
  - eapply OwnedSequence.
    + apply OwnedFrameSP; [|intros x H; contradiction].
      apply owned_assertion_frame_right; [apply owned_derive_store_cell |intros x H; contradiction].
    + apply owned_assertion_unlock,mp_assert_sender_release.
Qed.

Lemma mp_load_held_derived active t r tail v : ~ In 0 (A.fv tail) ->
  owned_derivation active (mp_invariant t r) DisjointMode (mp_held 2%positive (A.Spatial (mp_data v) tail))
    mp_load (A.And (mp_held 2%positive (A.Spatial (mp_data v) tail)) (A.Pure (mp_guard v))).
Proof.
  intros Htail; eapply owned_assertion_consequence.
  - apply assert_derive_spatial_swap.
  - apply owned_assertion_load_spatial.
    + rewrite mp_invariant_fv; cbn; intuition discriminate.
    + change (~ In 0 (1 :: A.fv tail)); cbn; intuition discriminate.
  - apply assert_derive_and_mono; [apply assert_derive_spatial_restore |apply AssertRefl].
Qed.

Lemma mp_load_cases_derived active t r :
  owned_derivation active (mp_invariant t r) DisjointMode (mp_load_cases t r) mp_load (mp_read_cases t r).
Proof.
  apply OwnedDisjunction.
  - eapply owned_assertion_consequence; [apply AssertRefl |apply mp_load_held_derived |apply AssertOrLeft].
    rewrite mp_token_fv; cbn; tauto.
  - eapply owned_assertion_consequence; [apply AssertRefl |apply mp_load_held_derived |apply AssertOrRight].
    cbn [A.fv]; rewrite !mp_token_fv; cbn; tauto.
Qed.

Lemma mp_release_cases_derived active t r :
  owned_derivation active (mp_invariant t r) DisjointMode (mp_read_cases t r)
    (mp_release 2%positive) (mp_received r 1%Z).
Proof.
  apply OwnedDisjunction.
  - eapply owned_assertion_consequence; [apply AssertRefl | |apply AssertOrLeft].
    apply owned_assertion_pure_frame; [apply owned_assertion_unlock,mp_assert_release_zero |intros x H; contradiction].
  - eapply owned_assertion_consequence; [apply AssertRefl | |apply AssertOrRight].
    apply owned_assertion_pure_frame; [apply owned_assertion_unlock,mp_assert_release_one |intros x H; contradiction].
Qed.

Lemma mp_tail_derived active t r :
  owned_derivation active (mp_invariant t r) DisjointMode (mp_received r 1%Z) mp_tail (mp_received r 2%Z).
Proof.
  apply OwnedChoice.
  - eapply OwnedSequence.
    + eapply owned_assertion_consequence; [apply mp_assert_select_one |apply OwnedAssume |apply AssertRefl].
    + eapply owned_assertion_consequence; [apply AssertRefl | |apply AssertOrRight].
      apply owned_assertion_pure_frame; [apply owned_assertion_store_fence |intros x H; contradiction].
  - eapply OwnedSequence.
    + eapply owned_assertion_consequence; [apply mp_assert_select_not_one |apply OwnedAssume |apply AssertRefl].
    + eapply owned_assertion_consequence; [apply AssertRefl |apply OwnedSkip |apply AssertOrLeft].
Qed.

Theorem mp_receiver_derived active t r :
  owned_derivation active (mp_invariant t r) DisjointMode (mp_token r) mp_receiver (mp_received r 2%Z).
Proof.
  eapply OwnedSequence with (middle := mp_load_cases t r).
  - eapply owned_assertion_consequence;
      [apply (AssertUnitRight active SepSpatial Backward) | |apply mp_assert_receiver_acquire].
    apply OwnedFrameSP; [apply OwnedLock |intros x H; contradiction].
  - eapply OwnedSequence; [apply mp_load_cases_derived |].
    eapply OwnedSequence; [apply mp_release_cases_derived |apply mp_tail_derived].
Qed.

Theorem mp_parallel_derived active t r :
  owned_derivation active (mp_invariant t r) DisjointMode (A.Spatial (mp_token t) (mp_token r))
    mp_program (mp_received r 2%Z).
Proof.
  eapply owned_assertion_consequence; [apply AssertRefl | |apply (AssertUnitLeft active SepSpatial Forward)].
  apply OwnedParallel; [apply mp_sender_derived |apply mp_receiver_derived | | |].
  - split.
    + intros x Hfv Hmod; change (In x (C.modifies mp_receiver)) in Hmod.
      rewrite mp_receiver_modifies in Hmod; destruct Hmod as [<- |H]; [|contradiction].
      cbn [branch_fv concurrent_pre concurrent_program concurrent_post] in Hfv.
      cbn [mp_sender mp_acquire mp_store mp_release mp_address C.fv C.primitive_fv S.primitive_fv expr_fv A.fv] in Hfv.
      cbn in Hfv; intuition discriminate.
    + intros x Hfv Hmod; change (In x (C.modifies mp_sender)) in Hmod.
      rewrite mp_sender_modifies in Hmod; contradiction.
  - intros x H; rewrite mp_sender_modifies in H; contradiction.
  - intros x H; rewrite mp_receiver_modifies in H; destruct H as [<- |H]; [|contradiction].
    rewrite mp_invariant_fv; cbn; intuition discriminate.
Qed.
