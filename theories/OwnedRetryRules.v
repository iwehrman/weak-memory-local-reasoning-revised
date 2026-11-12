From Stdlib Require Import List ZArith Bool.
From WMLR Require Import Expressions Languages Machine OperationalSemantics Assertions AssertionSemantics
  Specifications OwnedSafety OwnedCalculus AssertionDerivation AssertionDerivedRules AssertionRearrangements
  AssertionClientRules OwnedAssertionRules OwnedClientRules OwnedLoopRules NamedLockSyntax.
Import ListNotations.

Definition retry_assertion x pre post := A.Or (A.And post (A.Pure (nl_is x 0%Z)))
  (A.And pre (A.Pure (nl_is x 1%Z))).

Lemma owned_assertion_set_frame active invariant mode pre x value annotation :
  ~ In x (A.fv invariant) -> ~ In x (A.fv pre) ->
  owned_derivation active invariant mode pre (C.Prim (C.Common (S.Assign x (EVal value))) annotation)
    (A.And pre (A.Pure (nl_is x value))).
Proof.
  intros HJ HF; eapply owned_assertion_consequence; [apply (AssertUnitRight active SepSpatial Backward) | |].
  - apply OwnedFrameSP; [apply owned_assertion_set_emp,HJ |].
    intros y Hy; cbn in Hy; destruct Hy as [<- |H]; [exact HF |contradiction].
  - eapply AssertTrans; [apply (AssertPureSeparateRight active SepSpatial Forward) |].
    apply assert_derive_and_mono; [apply (AssertUnitRight active SepSpatial Forward) |apply AssertRefl].
Qed.

Lemma retry_assert_continue active x pre post :
  assertion_derivation active (A.And (retry_assertion x pre post) (A.Pure (nl_is x 1%Z))) pre.
Proof.
  eapply AssertTrans; [apply assert_derive_and_comm |]; apply AssertOrCases.
  - eapply AssertTrans with (q := A.Pure BFalse); [|apply AssertFalse].
    eapply assert_derive_boolean_clash with (b := nl_is x 1%Z) (c := nl_is x 0%Z).
    + apply AssertAndLeft.
    + eapply AssertTrans; [apply AssertAndRight |apply AssertAndRight].
    + intros s H1 H0; cbn [nl_is eval_bexpr eval_expr] in *; apply Z.eqb_eq in H1; rewrite H1 in H0; discriminate.
  - eapply AssertTrans; [apply AssertAndRight |apply AssertAndLeft].
Qed.

Lemma retry_assert_finish active x pre post :
  assertion_derivation active (A.And (retry_assertion x pre post) (A.Pure (BNot (nl_is x 1%Z)))) post.
Proof.
  eapply AssertTrans; [apply assert_derive_and_comm |]; apply AssertOrCases.
  - eapply AssertTrans; [apply AssertAndRight |apply AssertAndLeft].
  - eapply AssertTrans with (q := A.Pure BFalse); [|apply AssertFalse].
    eapply assert_derive_boolean_clash with (b := BNot (nl_is x 1%Z)) (c := nl_is x 1%Z).
    + apply AssertAndLeft.
    + eapply AssertTrans; [apply AssertAndRight |apply AssertAndRight].
    + intros s Hn H; change (negb (eval_bexpr s (nl_is x 1%Z)) = true) in Hn; rewrite H in Hn; discriminate.
Qed.

Theorem owned_assertion_retry active invariant mode pre post actor x attempt :
  ~ In x (A.fv invariant) -> ~ In x (A.fv pre) ->
  owned_derivation active invariant mode pre attempt (retry_assertion x pre post) ->
  owned_derivation active invariant mode pre
    (C.Seq (C.Prim (C.Common (S.Assign x (EVal 1%Z))) (EVal (Z.pos actor)))
      (C.while_do (EVal (Z.pos actor)) (nl_is x 1%Z) attempt)) post.
Proof.
  intros HJ HF HD; eapply OwnedSequence with (middle := retry_assertion x pre post).
  - eapply owned_assertion_consequence; [apply AssertRefl |apply owned_assertion_set_frame; assumption |apply AssertOrRight].
  - eapply owned_assertion_consequence; [apply AssertRefl |apply owned_assertion_while |apply retry_assert_finish].
    eapply owned_assertion_consequence; [apply retry_assert_continue |exact HD |apply AssertRefl].
Qed.
