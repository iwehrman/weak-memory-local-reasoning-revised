From Stdlib Require Import List ZArith.
From WMLR Require Import Expressions Languages Machine OperationalSemantics Assertions AssertionSemantics
  Specifications InvariantFragment AssertionCellSubstitution OwnedSafety OwnedCalculus OwnedDerivedRules
  AssertionDerivation AssertionDerivedRules AssertionRearrangements AssertionClientRules OwnedAssertionRules
  OwnedClientRules CellFamilies.
Import ListNotations.

Definition zero_items (items : list (location * Z)) := map (fun item => (fst item,0%Z)) items.
Definition cell_history actor loc value := A.Temporal (concrete_cell loc 0%Z)
  (A.LeadsTo (EVal (Z.pos loc)) (EVal (Z.pos actor)) (EVal value)).
Fixpoint history_family actor (items : list (location * Z)) : A.assertion :=
  match items with [] => A.Emp |(loc,value)::rest => A.Spatial (cell_history actor loc value) (history_family actor rest) end.
Fixpoint fill_region actor (items : list (location * Z)) : C.command :=
  match items with [] => C.skip (EVal (Z.pos actor)) |(loc,value)::rest =>
    C.Seq (C.Prim (C.Common (S.Store (EVal (Z.pos loc)) (EVal value))) (EVal (Z.pos actor))) (fill_region actor rest) end.
Fixpoint read_region actor x (items : list (location * Z)) : C.command :=
  match items with [] => C.skip (EVal (Z.pos actor)) |(loc,value)::rest =>
    C.Seq (C.Prim (C.Common (S.Load x (EVal (Z.pos loc)))) (EVal (Z.pos actor))) (read_region actor x rest) end.

Lemma cell_history_fv actor loc value : A.fv (cell_history actor loc value) = [].
Proof. cbn [cell_history A.fv]; unfold concrete_cell; rewrite assertion_writer_cell_fv; reflexivity. Qed.

Lemma history_family_fv actor items : A.fv (history_family actor items) = [].
Proof. induction items as [|[loc value] rest IH]; [reflexivity |cbn [history_family A.fv]; rewrite cell_history_fv,IH; reflexivity]. Qed.

Theorem history_family_complete active actor items :
  assertion_derivation active (A.Temporal (history_family actor items) (A.Barrier (EVal (Z.pos actor)))) (cell_family items).
Proof.
  induction items as [|[loc value] rest IH]; [apply assert_derive_barrier_suffix |].
  eapply AssertTrans; [apply (AssertBarrierDistribute active SepSpatial Forward) |].
  apply (AssertSeparateMono active SepSpatial); [apply assert_derive_cell_write_drained |exact IH].
Qed.

Theorem cell_family_contraction active items :
  assertion_derivation active (A.Spatial (cell_family items) (cell_family items)) (cell_family items).
Proof.
  destruct items as [|[loc value] rest]; [apply (AssertUnitLeft active SepSpatial Forward) |].
  eapply AssertTrans; [apply cell_family_exclusive |apply AssertFalse].
Qed.

Theorem fill_region_derived active invariant mode actor items :
  owned_derivation active invariant mode (cell_family (zero_items items)) (fill_region actor items) (history_family actor items).
Proof.
  induction items as [|[loc value] rest IH]; [apply OwnedSkip |].
  eapply OwnedSequence.
  - apply owned_assertion_frame_right; [apply owned_derive_store_cell |intros x H; contradiction].
  - apply OwnedFrameSP; [exact IH |intros x HM HF; rewrite cell_history_fv in HF; contradiction].
Qed.

Theorem read_region_derived active invariant mode actor x items : ~ In x (A.fv invariant) ->
  owned_derivation active invariant mode (cell_family items) (read_region actor x items) (cell_family items).
Proof.
  intros HJ; induction items as [|[loc value] rest IH]; [apply OwnedSkip |].
  eapply OwnedSequence with (middle := cell_family ((loc,value)::rest)).
  - eapply owned_assertion_consequence; [apply AssertRefl | |].
    + apply owned_assertion_frame_right.
      * apply owned_derive_load_cell; [exact HJ |cbn; tauto].
      * intros y HM HF; rewrite cell_family_fv in HF; contradiction.
    + apply (AssertSeparateMono active SepSpatial); [apply AssertAndLeft |apply AssertRefl].
  - apply OwnedFrameSP; [exact IH |].
    intros y HM HF; unfold concrete_cell in HF; rewrite assertion_writer_cell_fv in HF; exact HF.
Qed.

Lemma fill_region_modifies actor items : C.modifies (fill_region actor items) = [].
Proof. induction items as [|[loc value] rest IH]; [reflexivity |exact IH]. Qed.

Lemma fill_region_fv actor items : C.fv (fill_region actor items) = [].
Proof. induction items as [|[loc value] rest IH]; [reflexivity |exact IH]. Qed.

Lemma read_region_modifies actor x items y : In y (C.modifies (read_region actor x items)) -> y = x.
Proof. induction items as [|[loc value] rest IH]; cbn; [contradiction |intros [H |H]; [symmetry; exact H |apply IH,H]]. Qed.

Lemma read_region_fv actor x items y : In y (C.fv (read_region actor x items)) -> y = x.
Proof. induction items as [|[loc value] rest IH]; cbn; [contradiction |intros [H |H]; [symmetry; exact H |apply IH,H]]. Qed.
