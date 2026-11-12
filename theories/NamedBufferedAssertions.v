From Stdlib Require Import List ZArith.
From WMLR Require Import Expressions Machine Assertions AssertionSemantics InvariantFragment
  AssertionDerivation AssertionDerivedRules AssertionRearrangements AssertionClientRules NamedLockSyntax.
Import ListNotations.

Lemma nl_assert_distribute_three active p q r annotation :
  assertion_derivation active (A.Temporal (A.Spatial p (A.Spatial q r)) (A.Barrier annotation))
    (A.Spatial (A.Temporal p (A.Barrier annotation))
      (A.Spatial (A.Temporal q (A.Barrier annotation)) (A.Temporal r (A.Barrier annotation)))).
Proof.
  eapply AssertTrans; [apply (AssertBarrierDistribute active SepSpatial Forward) |].
  apply (AssertSeparateMono active SepSpatial); [apply AssertRefl |apply (AssertBarrierDistribute active SepSpatial Forward)].
Qed.

Lemma nl_assert_take_retained active actor flag invariant rest pool retained :
  assertion_derivation active (A.Spatial (nl_component flag invariant) rest) pool ->
  assertion_derivation active
    (A.Temporal (A.Spatial (A.Temporal (nl_cell flag 0%Z)
      (A.LeadsTo (EVal (Z.pos flag)) (EVal (Z.pos actor)) (EVal 1%Z)))
      (A.Spatial invariant (A.Spatial retained rest))) (A.Barrier (EVal (Z.pos actor))))
    (A.Spatial pool (A.Spatial invariant (A.Temporal retained (A.Barrier (EVal (Z.pos actor)))))).
Proof.
  intros HP; eapply AssertTrans; [apply (AssertBarrierDistribute active SepSpatial Forward) |].
  eapply AssertTrans with (q := A.Spatial (nl_cell flag 1%Z)
    (A.Spatial invariant (A.Spatial (A.Temporal retained (A.Barrier (EVal (Z.pos actor)))) rest))).
  - apply (AssertSeparateMono active SepSpatial); [apply assert_derive_cell_write_drained |].
    eapply AssertTrans; [apply nl_assert_distribute_three |].
    apply (AssertSeparateMono active SepSpatial); [apply assert_derive_barrier_suffix |].
    apply (AssertSeparateMono active SepSpatial); [apply AssertRefl |apply assert_derive_barrier_suffix].
  - eapply AssertTrans; [apply (AssertSeparateMono active SepSpatial); [apply AssertRefl |] |].
    + eapply AssertTrans; [apply (AssertSeparateMono active SepSpatial); [apply AssertRefl |apply AssertSpatialComm] |].
      apply assert_derive_spatial_rotate.
    + eapply AssertTrans; [apply (AssertAssociative active SepSpatial Backward) |].
      apply (AssertSeparateMono active SepSpatial); [|apply AssertRefl].
      eapply AssertTrans; [apply (AssertSeparateMono active SepSpatial); [apply AssertOrRight |apply AssertRefl] |exact HP].
Qed.

Lemma nl_assert_retry_retained active actor flag invariant rest pool retained :
  assertion_derivation active (A.Spatial (nl_component flag invariant) rest) pool ->
  assertion_derivation active
    (A.Temporal (A.Spatial (nl_cell flag 1%Z) (A.Spatial retained rest)) (A.Barrier (EVal (Z.pos actor))))
    (A.Spatial pool retained).
Proof.
  intros HP; eapply AssertTrans; [apply assert_derive_barrier_suffix |].
  eapply AssertTrans; [apply (AssertSeparateMono active SepSpatial); [apply AssertRefl |apply AssertSpatialComm] |].
  eapply AssertTrans; [apply (AssertAssociative active SepSpatial Backward) |].
  apply (AssertSeparateMono active SepSpatial); [|apply AssertRefl].
  eapply AssertTrans; [apply (AssertSeparateMono active SepSpatial); [apply AssertOrRight |apply AssertRefl] |exact HP].
Qed.

Lemma nl_assert_buffered_return_open active actor flag invariant rest pool retained :
  assertion_derivation active (A.Temporal retained (A.Barrier (EVal (Z.pos actor)))) invariant ->
  assertion_derivation active (A.Spatial (nl_component flag invariant) rest) pool ->
  assertion_derivation active
    (A.Temporal (A.Spatial (A.Temporal (nl_cell flag 1%Z)
      (A.LeadsTo (EVal (Z.pos flag)) (EVal (Z.pos actor)) (EVal 0%Z)))
      (A.Spatial retained rest)) (A.Barrier (EVal (Z.pos actor))))
    (A.Spatial pool A.Emp).
Proof.
  intros HC HP; eapply AssertTrans; [apply nl_assert_distribute_three |].
  eapply AssertTrans with (q := A.Spatial (nl_cell flag 0%Z) (A.Spatial invariant rest)).
  - apply (AssertSeparateMono active SepSpatial); [apply assert_derive_cell_write_drained |].
    apply (AssertSeparateMono active SepSpatial); [exact HC |apply assert_derive_barrier_suffix].
  - eapply AssertTrans; [apply (AssertAssociative active SepSpatial Backward) |].
    eapply AssertTrans; [apply (AssertSeparateMono active SepSpatial); [apply AssertOrLeft |apply AssertRefl] |].
    eapply AssertTrans; [exact HP |apply (AssertUnitRight active SepSpatial Backward)].
Qed.

Lemma nl_assert_buffered_return_closed active actor flag invariant rest pool retained :
  assertion_derivation active (A.Temporal retained (A.Barrier (EVal (Z.pos actor)))) invariant ->
  assertion_derivation active (A.Spatial invariant invariant) (A.Pure BFalse) ->
  assertion_derivation active
    (A.Temporal (A.Spatial (A.Temporal (nl_cell flag 0%Z)
      (A.LeadsTo (EVal (Z.pos flag)) (EVal (Z.pos actor)) (EVal 0%Z)))
      (A.Spatial invariant (A.Spatial retained rest))) (A.Barrier (EVal (Z.pos actor))))
    (A.Spatial pool A.Emp).
Proof.
  intros HC Hex; eapply AssertTrans; [apply (AssertBarrierDistribute active SepSpatial Forward) |].
  eapply AssertTrans with (q := A.Spatial (nl_cell flag 0%Z) (A.Spatial invariant (A.Spatial invariant rest))).
  - apply (AssertSeparateMono active SepSpatial); [apply assert_derive_cell_write_drained |].
    eapply AssertTrans; [apply nl_assert_distribute_three |].
    apply (AssertSeparateMono active SepSpatial); [apply assert_derive_barrier_suffix |].
    apply (AssertSeparateMono active SepSpatial); [exact HC |apply assert_derive_barrier_suffix].
  - eapply AssertTrans with (q := A.Spatial (nl_cell flag 0%Z) (A.Spatial (A.Pure BFalse) rest)).
    + apply (AssertSeparateMono active SepSpatial); [apply AssertRefl |].
      eapply AssertTrans; [apply (AssertAssociative active SepSpatial Backward) |].
      apply (AssertSeparateMono active SepSpatial); [exact Hex |apply AssertRefl].
    + eapply AssertTrans with (q := A.Spatial (nl_cell flag 0%Z) (A.Pure BFalse)).
      * apply (AssertSeparateMono active SepSpatial); [apply AssertRefl |apply (assert_derive_separate_pure_left active SepSpatial)].
      * eapply AssertTrans; [apply (assert_derive_separate_pure_right active SepSpatial) |apply AssertFalse].
Qed.
