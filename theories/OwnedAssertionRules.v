From Stdlib Require Import ZArith.
From WMLR Require Import Expressions Languages Machine OperationalSemantics Assertions AssertionSemantics
  AssertionDerivation AssertionDerivedRules AssertionSoundness OwnedSafety OwnedCalculus.

(** Derived interfaces to the unchanged 21-constructor program calculus.
    Clients supply assertion proof trees, not semantic entailments. *)
Theorem owned_assertion_consequence active invariant mode pre pre' command post' post :
  assertion_derivation active pre pre' ->
  owned_derivation active invariant mode pre' command post' ->
  assertion_derivation active post' post ->
  owned_derivation active invariant mode pre command post.
Proof.
  intros Hpre Hcommand Hpost; eapply OwnedConsequence;
    [apply assertion_derivation_sound; exact Hpre |exact Hcommand
    |apply assertion_derivation_sound; exact Hpost].
Qed.

Theorem owned_assertion_unlock active invariant pre post owner :
  assertion_derivation active (A.Temporal pre (A.Barrier (EVal (Z.pos owner)))) (A.Spatial invariant post) ->
  owned_derivation active invariant DisjointMode (A.Spatial (A.Lock (EVal (Z.pos owner))) pre)
    (C.Prim C.Unlock (EVal (Z.pos owner))) post.
Proof. intros H; apply OwnedUnlock,assertion_derivation_sound,H. Qed.

(** A small integration derivation, before the separate 4C container
    checkpoint. Both assertion obligations use only the new interface. *)
Theorem owned_assertion_return_invariant active invariant owner :
  owned_derivation active invariant DisjointMode
    (A.Spatial (A.Lock (EVal (Z.pos owner))) invariant)
    (C.Prim C.Unlock (EVal (Z.pos owner))) A.Emp.
Proof.
  apply owned_assertion_unlock; eapply AssertTrans;
    [apply assert_derive_barrier_suffix |apply (AssertUnitRight active SepSpatial Backward)].
Qed.

Theorem owned_assertion_lock_round_trip active invariant owner :
  owned_derivation active invariant DisjointMode A.Emp
    (C.Seq (C.Prim C.Lock (EVal (Z.pos owner))) (C.Prim C.Unlock (EVal (Z.pos owner)))) A.Emp.
Proof.
  eapply OwnedSequence; [apply OwnedLock |].
  eapply owned_assertion_consequence;
    [apply assert_derive_barrier_suffix |apply owned_assertion_return_invariant |apply AssertRefl].
Qed.
