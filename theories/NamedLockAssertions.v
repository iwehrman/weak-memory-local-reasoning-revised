From Stdlib Require Import List ZArith Bool.
From WMLR Require Import Expressions Machine Assertions AssertionSemantics InvariantFragment
  AssertionDerivation AssertionDerivedRules AssertionRearrangements AssertionClientRules
  OwnedLoopRules NamedLockSyntax.
Import ListNotations.

Lemma nl_assert_cases active actor flag invariant rest :
  assertion_derivation active (nl_held actor (A.Spatial (nl_component flag invariant) rest))
    (nl_cases actor flag invariant rest).
Proof.
  eapply AssertTrans; [apply (AssertSeparateMono active SepSpatial);
    [apply AssertRefl |apply (AssertOrSeparateLeft active SepSpatial Forward)] |].
  eapply AssertTrans; [apply (AssertOrSeparateRight active SepSpatial Forward) |].
  apply assert_derive_or_mono; [|apply AssertRefl].
  apply (AssertSeparateMono active SepSpatial); [apply AssertRefl |apply (AssertAssociative active SepSpatial Forward)].
Qed.

Lemma nl_assert_take_donation active actor flag invariant rest pool :
  assertion_derivation active (A.Spatial (nl_component flag invariant) rest) pool ->
  assertion_derivation active
    (A.Temporal (A.Spatial (A.Temporal (nl_cell flag 0%Z)
      (A.LeadsTo (EVal (Z.pos flag)) (EVal (Z.pos actor)) (EVal 1%Z)))
      (A.Spatial invariant rest)) (A.Barrier (EVal (Z.pos actor))))
    (A.Spatial pool invariant).
Proof.
  intros HP; eapply AssertTrans; [apply (AssertBarrierDistribute active SepSpatial Forward) |].
  eapply AssertTrans with (q := A.Spatial (nl_cell flag 1%Z) (A.Spatial invariant rest)).
  - apply (AssertSeparateMono active SepSpatial); [apply assert_derive_cell_write_drained |apply assert_derive_barrier_suffix].
  - eapply AssertTrans; [apply (AssertSeparateMono active SepSpatial);
      [apply AssertRefl |apply AssertSpatialComm] |].
    eapply AssertTrans; [apply (AssertAssociative active SepSpatial Backward) |].
    apply (AssertSeparateMono active SepSpatial); [|apply AssertRefl].
    eapply AssertTrans; [apply (AssertSeparateMono active SepSpatial); [apply AssertOrRight |apply AssertRefl] |exact HP].
Qed.

Lemma nl_assert_retry_donation active actor flag invariant rest pool :
  assertion_derivation active (A.Spatial (nl_component flag invariant) rest) pool ->
  assertion_derivation active
    (A.Temporal (A.Spatial (nl_cell flag 1%Z) rest) (A.Barrier (EVal (Z.pos actor))))
    (A.Spatial pool A.Emp).
Proof.
  intros HP; eapply AssertTrans; [apply assert_derive_barrier_suffix |].
  eapply AssertTrans; [apply (AssertSeparateMono active SepSpatial); [apply AssertOrRight |apply AssertRefl] |].
  eapply AssertTrans; [exact HP |apply (AssertUnitRight active SepSpatial Backward)].
Qed.

Lemma nl_assert_release_payload active flag invariant rest :
  assertion_derivation active (A.Spatial invariant invariant) (A.Pure BFalse) ->
  assertion_derivation active (A.Spatial invariant (A.Spatial (nl_component flag invariant) rest))
    (A.Spatial (nl_cell flag 1%Z) (A.Spatial invariant rest)).
Proof.
  intros Hex; eapply AssertTrans; [apply (AssertSeparateMono active SepSpatial);
    [apply AssertRefl |apply (AssertOrSeparateLeft active SepSpatial Forward)] |].
  eapply AssertTrans; [apply (AssertOrSeparateRight active SepSpatial Forward) |].
  apply assert_derive_or_elim; [|apply assert_derive_spatial_rotate].
  eapply AssertTrans; [apply (AssertSeparateMono active SepSpatial);
    [apply AssertRefl |apply (AssertAssociative active SepSpatial Forward)] |].
  eapply AssertTrans; [apply assert_derive_spatial_rotate |].
  eapply AssertTrans with (q := A.Spatial (nl_cell flag 0%Z) (A.Spatial (A.Pure BFalse) rest)).
  - apply (AssertSeparateMono active SepSpatial); [apply AssertRefl |].
    eapply AssertTrans; [apply (AssertAssociative active SepSpatial Backward) |].
    apply (AssertSeparateMono active SepSpatial); [exact Hex |apply AssertRefl].
  - eapply AssertTrans with (q := A.Pure BFalse); [|apply AssertFalse].
    eapply AssertTrans with (q := A.Spatial (nl_cell flag 0%Z) (A.Pure BFalse)).
    + apply (AssertSeparateMono active SepSpatial); [apply AssertRefl |apply (assert_derive_separate_pure_left active SepSpatial)].
    + apply (assert_derive_separate_pure_right active SepSpatial).
Qed.

Lemma nl_assert_return_donation active actor flag invariant rest pool :
  assertion_derivation active (A.Spatial (nl_component flag invariant) rest) pool ->
  assertion_derivation active
    (A.Temporal (A.Spatial (A.Temporal (nl_cell flag 1%Z)
      (A.LeadsTo (EVal (Z.pos flag)) (EVal (Z.pos actor)) (EVal 0%Z)))
      (A.Spatial invariant rest)) (A.Barrier (EVal (Z.pos actor))))
    (A.Spatial pool A.Emp).
Proof.
  intros HP; eapply AssertTrans; [apply (AssertBarrierDistribute active SepSpatial Forward) |].
  eapply AssertTrans with (q := A.Spatial (nl_cell flag 0%Z) (A.Spatial invariant rest)).
  - apply (AssertSeparateMono active SepSpatial); [apply assert_derive_cell_write_drained |apply assert_derive_barrier_suffix].
  - eapply AssertTrans; [apply (AssertAssociative active SepSpatial Backward) |].
    eapply AssertTrans; [apply (AssertSeparateMono active SepSpatial); [apply AssertOrLeft |apply AssertRefl] |].
    eapply AssertTrans; [exact HP |apply (AssertUnitRight active SepSpatial Backward)].
Qed.

Lemma nl_assert_select_zero active x p q :
  assertion_derivation active (A.Or (A.And p (A.Pure (nl_is x 0%Z))) (A.And q (A.Pure (nl_is x 1%Z))))
    (A.Or (A.Pure (BNot (nl_is x 0%Z))) (A.And p (A.Pure (nl_is x 0%Z)))).
Proof.
  apply assert_derive_or_elim; [apply AssertOrRight |].
  eapply AssertTrans; [apply AssertAndRight |].
  eapply AssertTrans; [|apply AssertOrLeft].
  apply assert_derive_pure_implication; intros s H; cbn [nl_is eval_bexpr eval_expr] in *.
  apply Z.eqb_eq in H; rewrite H; reflexivity.
Qed.

Lemma nl_assert_select_not_zero active x p q :
  assertion_derivation active (A.Or (A.And p (A.Pure (nl_is x 0%Z))) (A.And q (A.Pure (nl_is x 1%Z))))
    (A.Or (A.Pure (BNot (BNot (nl_is x 0%Z)))) (A.And q (A.Pure (nl_is x 1%Z)))).
Proof.
  apply assert_derive_or_elim; [|apply AssertOrRight].
  eapply AssertTrans; [apply AssertAndRight |].
  eapply AssertTrans; [|apply AssertOrLeft].
  apply assert_derive_pure_implication; intros s H.
  change (negb (negb (eval_bexpr s (nl_is x 0%Z))) = true); rewrite H; reflexivity.
Qed.

Lemma nl_assert_loop_continue active x invariant :
  assertion_derivation active (A.And (nl_loop_invariant x invariant) (A.Pure (nl_is x 1%Z))) A.Emp.
Proof.
  eapply AssertTrans; [apply assert_derive_and_comm |]; apply AssertOrCases.
  - eapply AssertTrans with (q := A.Pure BFalse); [|apply AssertFalse].
    eapply assert_derive_boolean_clash with (b := nl_is x 1%Z) (c := nl_is x 0%Z).
    + apply AssertAndLeft.
    + eapply AssertTrans; [apply AssertAndRight |apply AssertAndRight].
    + intros s H1 H0; cbn [nl_is eval_bexpr eval_expr] in *.
      apply Z.eqb_eq in H1; rewrite H1 in H0; discriminate.
  - eapply AssertTrans; [apply AssertAndRight |apply AssertAndLeft].
Qed.

Lemma nl_assert_loop_finish active x invariant :
  assertion_derivation active (A.And (nl_loop_invariant x invariant) (A.Pure (BNot (nl_is x 1%Z)))) invariant.
Proof.
  eapply AssertTrans; [apply assert_derive_and_comm |]; apply AssertOrCases.
  - eapply AssertTrans; [apply AssertAndRight |apply AssertAndLeft].
  - eapply AssertTrans with (q := A.Pure BFalse); [|apply AssertFalse].
    eapply assert_derive_boolean_clash with (b := BNot (nl_is x 1%Z)) (c := nl_is x 1%Z).
    + apply AssertAndLeft.
    + eapply AssertTrans; [apply AssertAndRight |apply AssertAndRight].
    + intros s Hn H; change (negb (eval_bexpr s (nl_is x 1%Z)) = true) in Hn; rewrite H in Hn; discriminate.
Qed.
