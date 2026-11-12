From Stdlib Require Import List ZArith Bool.
From WMLR Require Import Expressions Languages Machine OperationalSemantics Assertions AssertionSemantics
  AssertionSubstitution InvariantFragment OwnedSafety OwnedCalculus AssertionDerivation
  AssertionDerivedRules AssertionRearrangements AssertionClientRules OwnedAssertionRules.
Import ListNotations.

Lemma assert_derive_boolean_clash active p b c :
  assertion_derivation active p (A.Pure b) -> assertion_derivation active p (A.Pure c) ->
  (forall s, eval_bexpr s b = true -> eval_bexpr s c = true -> False) ->
  assertion_derivation active p (A.Pure BFalse).
Proof.
  intros HB HC Hfalse; eapply AssertTrans with (q := pure_assumptions [b;c]).
  - apply AssertAndIntro; [exact HB |apply AssertAndIntro; [exact HC |apply AssertTrue]].
  - apply AssertPure; intros s HS; exfalso; apply (Hfalse s); apply HS; cbn; auto.
Qed.

Lemma owned_assertion_assume active invariant mode pre condition annotation :
  owned_derivation active invariant mode pre (C.Prim (C.Common (S.Assume condition)) annotation)
    (A.And pre (A.Pure condition)).
Proof.
  eapply owned_assertion_consequence; [|apply OwnedAssume |apply AssertRefl].
  apply AssertPureCases with (b := condition).
  - apply AssertOrRight.
  - eapply AssertTrans; [apply AssertAndRight |apply AssertOrLeft].
Qed.

Theorem owned_assertion_while active invariant mode pre condition annotation body :
  owned_derivation active invariant mode (A.And pre (A.Pure condition)) body pre ->
  owned_derivation active invariant mode pre (C.while_do annotation condition body)
    (A.And pre (A.Pure (BNot condition))).
Proof.
  intros HD; eapply OwnedSequence; [apply OwnedLoop; eapply OwnedSequence
    |apply owned_assertion_assume]; [apply owned_assertion_assume |exact HD].
Qed.

Lemma owned_assertion_set_emp active invariant mode x value annotation : ~ In x (A.fv invariant) ->
  owned_derivation active invariant mode A.Emp (C.Prim (C.Common (S.Assign x (EVal value))) annotation)
    (A.And A.Emp (A.Pure (BEq (EVar x) (EVal value)))).
Proof.
  intros HF; eapply owned_assertion_consequence; [|apply OwnedAssign,HF |apply AssertRefl].
  unfold assertion_subst; cbn [substitute_assertion substitute_expression substitute_boolean].
  destruct (Nat.eq_dec x x); [|contradiction].
  apply AssertAndIntro; [apply AssertRefl |apply assert_derive_pure_fact].
  intros s; apply Z.eqb_refl.
Qed.
