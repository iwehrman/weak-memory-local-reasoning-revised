From Stdlib Require Import List ZArith.
From WMLR Require Import Expressions Languages Machine OperationalSemantics Assertions AssertionSemantics
  Specifications InvariantFragment OwnedSafety OwnedCalculus OwnedDerivedRules AssertionDerivation
  AssertionDerivedRules AssertionRearrangements OwnedAssertionRules OwnedClientRules OwnedLoopRules
  OwnedRetryRules CellFamilies RegionRules NamedLockSyntax NamedLockRules NamedBufferedRules
  MailboxSyntax MailboxAssertions.
Import ListNotations.

Lemma mailbox_publish_derived active items old :
  owned_derivation active (nl_pool (mailbox_locks items)) DisjointMode
    (A.Spatial (mailbox_flag old) (cell_family items))
    (C.Seq (mailbox_store 1%positive 1%Z) (nl_release 1%positive 1%positive)) A.Emp.
Proof.
  eapply OwnedSequence.
  - apply owned_assertion_frame_right; [apply owned_derive_store_cell |intros x H; contradiction].
  - apply named_lock_release_buffered_family with (invariant := mailbox_invariant items).
    + left; reflexivity.
    + apply mailbox_assert_publish_complete.
    + apply mailbox_exclusive.
Qed.

Theorem mailbox_producer_derived active items :
  owned_derivation active (nl_pool (mailbox_locks items)) DisjointMode
    (cell_family (zero_items items)) (mailbox_producer items) A.Emp.
Proof.
  eapply OwnedSequence; [apply fill_region_derived |].
  eapply OwnedSequence.
  - eapply owned_assertion_consequence; [apply AssertRefl | |apply mailbox_assert_producer_acquired].
    apply named_lock_acquire_retained_family; [left; reflexivity
      |rewrite mailbox_pool_fv; tauto |rewrite history_family_fv; tauto].
  - apply OwnedDisjunction; apply mailbox_publish_derived.
Qed.

Lemma mailbox_read_derived active items :
  owned_derivation active (nl_pool (mailbox_locks items)) DisjointMode (mailbox_invariant items)
    (nl_load 2%positive 2%positive 1) (mailbox_read_cases items).
Proof.
  apply OwnedDisjunction.
  - eapply owned_assertion_consequence; [apply AssertRefl |apply owned_derive_load_cell |apply AssertOrLeft];
      [rewrite mailbox_pool_fv; tauto |cbn; tauto].
  - eapply owned_assertion_consequence; [apply AssertSpatialComm | |].
    + apply owned_assertion_load_spatial; [rewrite mailbox_pool_fv; tauto |cbn [expr_fv]; rewrite cell_family_fv; tauto].
    + eapply AssertTrans; [apply assert_derive_and_mono; [apply AssertSpatialComm |apply AssertRefl] |apply AssertOrRight].
Qed.

Lemma mailbox_take_yes_derived active items :
  owned_derivation active (nl_pool (mailbox_locks items)) DisjointMode
    (A.Spatial (mailbox_flag 1%Z) (cell_family items)) mailbox_take_yes
    (retry_assertion 1 A.Emp (cell_family items)).
Proof.
  eapply OwnedSequence.
  - apply owned_assertion_frame_right; [apply owned_derive_store_cell |intros x H; contradiction].
  - eapply OwnedSequence with (middle := cell_family items).
    + eapply owned_assertion_consequence; [apply AssertRefl | |apply (AssertUnitLeft active SepSpatial Forward)].
      apply owned_assertion_frame_right; [|intros x H; contradiction].
      apply named_lock_release_buffered_family with (invariant := mailbox_invariant items).
      * left; reflexivity.
      * apply mailbox_assert_withdraw_complete.
      * apply mailbox_exclusive.
    + eapply owned_assertion_consequence; [apply AssertRefl |apply owned_assertion_set_frame |apply AssertOrLeft];
        [rewrite mailbox_pool_fv; tauto |rewrite cell_family_fv; tauto].
Qed.

Lemma mailbox_take_no_derived active items :
  owned_derivation active (nl_pool (mailbox_locks items)) DisjointMode (mailbox_flag 0%Z) mailbox_take_no
    (retry_assertion 1 A.Emp (cell_family items)).
Proof.
  eapply OwnedSequence with (middle := A.Emp).
  - eapply owned_assertion_consequence; [apply AssertOrLeft | |apply AssertRefl].
    apply named_lock_release_family; [left; reflexivity |apply mailbox_exclusive].
  - eapply owned_assertion_consequence; [apply AssertRefl |apply owned_assertion_set_emp |apply AssertOrRight].
    rewrite mailbox_pool_fv; tauto.
Qed.

Theorem mailbox_attempt_derived active items :
  owned_derivation active (nl_pool (mailbox_locks items)) DisjointMode A.Emp mailbox_attempt
    (retry_assertion 1 A.Emp (cell_family items)).
Proof.
  eapply OwnedSequence; [apply named_lock_acquire_family;
    [left; reflexivity |rewrite mailbox_pool_fv; tauto] |].
  eapply OwnedSequence; [apply mailbox_read_derived |].
  apply OwnedChoice.
  - eapply OwnedSequence; [|apply mailbox_take_yes_derived].
    eapply owned_assertion_consequence; [apply mailbox_assert_select_one |apply OwnedAssume |apply AssertRefl].
  - eapply OwnedSequence; [|apply mailbox_take_no_derived].
    eapply owned_assertion_consequence; [apply mailbox_assert_select_not_one |apply OwnedAssume |apply AssertRefl].
Qed.

Theorem mailbox_consumer_derived active items :
  owned_derivation active (nl_pool (mailbox_locks items)) DisjointMode A.Emp (mailbox_consumer items) (cell_family items).
Proof.
  eapply OwnedSequence.
  - apply owned_assertion_retry; [rewrite mailbox_pool_fv; tauto |cbn; tauto |apply mailbox_attempt_derived].
  - apply read_region_derived; rewrite mailbox_pool_fv; tauto.
Qed.

Theorem mailbox_parallel_derived active items :
  owned_derivation active (nl_pool (mailbox_locks items)) DisjointMode
    (cell_family (zero_items items)) (mailbox_program items) (cell_family items).
Proof.
  eapply owned_assertion_consequence; [apply (AssertUnitRight active SepSpatial Backward)
    | |apply (AssertUnitLeft active SepSpatial Forward)].
  apply OwnedParallel; [apply mailbox_producer_derived |apply mailbox_consumer_derived | | |].
  - split.
    + intros x HF HM.
      change (In x (A.fv (cell_family (zero_items items)) ++ C.fv (mailbox_producer items) ++ [])) in HF.
      change (In x (C.modifies (mailbox_consumer items))) in HM.
      rewrite cell_family_fv in HF; cbn [app] in HF; rewrite app_nil_r in HF.
      apply mailbox_producer_fv in HF; subst x; apply mailbox_consumer_modifies in HM; intuition discriminate.
    + intros x HF HM.
      change (In x (C.fv (mailbox_consumer items) ++ A.fv (cell_family items))) in HF.
      change (In x (C.modifies (mailbox_producer items))) in HM.
      rewrite cell_family_fv,app_nil_r in HF.
      apply mailbox_consumer_fv in HF; rewrite mailbox_producer_modifies in HM; cbn in HM; intuition congruence.
  - intros x HM HF; rewrite mailbox_pool_fv in HF; contradiction.
  - intros x HM HF; rewrite mailbox_pool_fv in HF; contradiction.
Qed.

Theorem mailbox_parallel_valid active items : two_active_processors active ->
  owned_valid active DisjointMode (nl_pool (mailbox_locks items))
    (cell_family (zero_items items)) (mailbox_program items) (cell_family items).
Proof. intros Htwo; apply owned_calculus_sound; [apply mailbox_pool_fragment |exact Htwo |apply mailbox_parallel_derived]. Qed.
