From Stdlib Require Import List ZArith.
From WMLR Require Import Expressions Machine Assertions AssertionSemantics InvariantFragment
  AssertionDerivation AssertionDerivedRules AssertionRearrangements.
Import ListNotations.

Lemma assert_derive_and_comm active p q :
  assertion_derivation active (A.And p q) (A.And q p).
Proof. apply AssertAndIntro; [apply AssertAndRight |apply AssertAndLeft]. Qed.

Lemma assert_derive_separate_pure_left active kind b p :
  assertion_derivation active (separate kind (A.Pure b) p) (A.Pure b).
Proof.
  eapply AssertTrans with (q := separate kind (A.And (A.Pure b) (A.Pure BTrue)) p).
  - apply AssertSeparateMono; [apply AssertAndIntro; [apply AssertRefl |apply AssertTrue] |apply AssertRefl].
  - eapply AssertTrans; [apply (AssertPureSeparateLeft active kind Forward) |apply AssertAndLeft].
Qed.

Lemma assert_derive_separate_pure_right active kind b p :
  assertion_derivation active (separate kind p (A.Pure b)) (A.Pure b).
Proof.
  eapply AssertTrans with (q := separate kind p (A.And (A.Pure BTrue) (A.Pure b))).
  - apply AssertSeparateMono; [apply AssertRefl |apply AssertAndIntro; [apply AssertTrue |apply AssertRefl]].
  - eapply AssertTrans; [apply (AssertPureSeparateRight active kind Forward) |apply AssertAndRight].
Qed.

Lemma assert_derive_spatial_rotate active p q r :
  assertion_derivation active (A.Spatial p (A.Spatial q r)) (A.Spatial q (A.Spatial p r)).
Proof.
  eapply AssertTrans; [apply (AssertAssociative active SepSpatial Backward) |].
  eapply AssertTrans; [apply (AssertSeparateMono active SepSpatial);
    [apply AssertSpatialComm |apply AssertRefl] |apply (AssertAssociative active SepSpatial Forward)].
Qed.

Lemma assert_derive_cell_write_drained active address old annotation value :
  assertion_derivation active
    (A.Temporal (A.Temporal (writer_points_to address old) (A.LeadsTo address annotation value))
      (A.Barrier annotation)) (writer_points_to address value).
Proof.
  eapply AssertTrans; [apply (AssertBarrierDistribute active SepTemporal Forward) |].
  eapply AssertTrans; [apply (AssertSeparateMono active SepTemporal);
    [apply assert_derive_barrier_suffix |apply assert_derive_drained_write_cell] |apply AssertCellOverwrite].
Qed.

Lemma assert_derive_pure_frame_intro active p b :
  assertion_derivation active (A.And p (A.Pure b)) (A.Spatial (A.And (A.Pure b) A.Emp) p).
Proof.
  eapply AssertTrans; [apply assert_derive_and_comm |].
  eapply AssertTrans; [apply assert_derive_and_mono;
    [apply AssertRefl |apply (AssertUnitLeft active SepSpatial Backward)]
    |apply (AssertPureSeparateLeft active SepSpatial Backward)].
Qed.

Lemma assert_derive_pure_frame_elim active p b :
  assertion_derivation active (A.Spatial (A.And (A.Pure b) A.Emp) p) (A.And p (A.Pure b)).
Proof.
  eapply AssertTrans; [apply (AssertPureSeparateLeft active SepSpatial Forward) |].
  eapply AssertTrans; [apply assert_derive_and_mono;
    [apply AssertRefl |apply (AssertUnitLeft active SepSpatial Forward)] |apply assert_derive_and_comm].
Qed.
