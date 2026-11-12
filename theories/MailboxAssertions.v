From Stdlib Require Import List ZArith Bool.
From WMLR Require Import Expressions Machine Assertions AssertionSemantics InvariantFragment
  AssertionDerivation AssertionDerivedRules AssertionRearrangements AssertionClientRules CellFamilies
  RegionRules NamedLockSyntax MailboxSyntax.
Import ListNotations.

Lemma assert_derive_exclusive_extensions active p q a b :
  assertion_derivation active (A.Spatial p q) (A.Pure BFalse) ->
  assertion_derivation active (A.Spatial (A.Spatial p a) (A.Spatial q b)) (A.Pure BFalse).
Proof.
  intros Hex; eapply AssertTrans; [apply (AssertAssociative active SepSpatial Forward) |].
  eapply AssertTrans; [apply (AssertSeparateMono active SepSpatial); [apply AssertRefl |apply assert_derive_spatial_rotate] |].
  eapply AssertTrans; [apply (AssertAssociative active SepSpatial Backward) |].
  eapply AssertTrans with (q := A.Spatial (A.Pure BFalse) (A.Spatial a b)).
  - apply (AssertSeparateMono active SepSpatial); [exact Hex |apply AssertRefl].
  - apply (assert_derive_separate_pure_left active SepSpatial).
Qed.

Theorem mailbox_exclusive active items :
  assertion_derivation active (A.Spatial (mailbox_invariant items) (mailbox_invariant items)) (A.Pure BFalse).
Proof.
  eapply AssertTrans; [apply (AssertOrSeparateLeft active SepSpatial Forward) |].
  apply assert_derive_or_elim; eapply AssertTrans; [apply (AssertOrSeparateRight active SepSpatial Forward) | |
    apply (AssertOrSeparateRight active SepSpatial Forward) |]; apply assert_derive_or_elim.
  - apply assert_derive_cells_exclusive.
  - eapply AssertTrans; [apply (AssertAssociative active SepSpatial Backward) |].
    eapply AssertTrans with (q := A.Spatial (A.Pure BFalse) (cell_family items)).
    + apply (AssertSeparateMono active SepSpatial); [apply assert_derive_cells_exclusive |apply AssertRefl].
    + apply (assert_derive_separate_pure_left active SepSpatial).
  - eapply AssertTrans; [apply AssertSpatialComm |].
    eapply AssertTrans; [apply (AssertAssociative active SepSpatial Backward) |].
    eapply AssertTrans with (q := A.Spatial (A.Pure BFalse) (cell_family items)).
    + apply (AssertSeparateMono active SepSpatial); [apply assert_derive_cells_exclusive |apply AssertRefl].
    + apply (assert_derive_separate_pure_left active SepSpatial).
  - apply assert_derive_exclusive_extensions,assert_derive_cells_exclusive.
Qed.

Lemma mailbox_assert_producer_acquired active items :
  assertion_derivation active (A.Spatial (mailbox_invariant items)
    (A.Temporal (history_family 1%positive items) (A.Barrier (EVal 1%Z))))
    (A.Or (A.Spatial (mailbox_flag 0%Z) (cell_family items)) (A.Spatial (mailbox_flag 1%Z) (cell_family items))).
Proof.
  eapply AssertTrans; [apply (AssertSeparateMono active SepSpatial); [apply AssertRefl |apply history_family_complete] |].
  eapply AssertTrans; [apply (AssertOrSeparateLeft active SepSpatial Forward) |].
  apply assert_derive_or_mono; [apply AssertRefl |].
  eapply AssertTrans; [apply (AssertAssociative active SepSpatial Forward) |].
  apply (AssertSeparateMono active SepSpatial); [apply AssertRefl |apply cell_family_contraction].
Qed.

Lemma mailbox_assert_publish_complete active items old :
  assertion_derivation active
    (A.Temporal (A.Spatial (A.Temporal (mailbox_flag old)
      (A.LeadsTo (EVal 2%Z) (EVal 1%Z) (EVal 1%Z))) (cell_family items)) (A.Barrier (EVal 1%Z)))
    (mailbox_invariant items).
Proof.
  eapply AssertTrans; [apply (AssertBarrierDistribute active SepSpatial Forward) |].
  eapply AssertTrans; [apply (AssertSeparateMono active SepSpatial);
    [apply assert_derive_cell_write_drained |apply assert_derive_barrier_suffix] |apply AssertOrRight].
Qed.

Lemma mailbox_assert_withdraw_complete active items :
  assertion_derivation active
    (A.Temporal (A.Temporal (mailbox_flag 1%Z) (A.LeadsTo (EVal 2%Z) (EVal 2%Z) (EVal 0%Z)))
      (A.Barrier (EVal 2%Z))) (mailbox_invariant items).
Proof. eapply AssertTrans; [apply assert_derive_cell_write_drained |apply AssertOrLeft]. Qed.

Lemma mailbox_assert_select_one active items : assertion_derivation active (mailbox_read_cases items)
  (A.Or (A.Pure (BNot (nl_is 1 1%Z))) (A.Spatial (mailbox_flag 1%Z) (cell_family items))).
Proof.
  apply assert_derive_or_elim.
  - eapply AssertTrans; [apply AssertAndRight |].
    eapply AssertTrans; [|apply AssertOrLeft].
    apply assert_derive_pure_implication; intros s H; cbn [nl_is eval_bexpr eval_expr] in *.
    apply Z.eqb_eq in H; rewrite H; reflexivity.
  - eapply AssertTrans; [apply AssertAndLeft |apply AssertOrRight].
Qed.

Lemma mailbox_assert_select_not_one active items : assertion_derivation active (mailbox_read_cases items)
  (A.Or (A.Pure (BNot (BNot (nl_is 1 1%Z)))) (mailbox_flag 0%Z)).
Proof.
  apply assert_derive_or_elim.
  - eapply AssertTrans; [apply AssertAndLeft |apply AssertOrRight].
  - eapply AssertTrans; [apply AssertAndRight |].
    eapply AssertTrans; [|apply AssertOrLeft].
    apply assert_derive_pure_implication; intros s H.
    change (negb (negb (eval_bexpr s (nl_is 1 1%Z))) = true); rewrite H; reflexivity.
Qed.
