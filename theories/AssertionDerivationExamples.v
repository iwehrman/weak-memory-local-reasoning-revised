From Stdlib Require Import List ZArith.
From WMLR Require Import Expressions Machine Assertions AssertionSemantics AssertionSubstitution
  InvariantFragment AssertionDerivation AssertionCellSubstitution AssertionDerivedRules.
Import ListNotations.

(** Substitution must rename writer 1 to 2 when the value inserted is the
    free variable 1. A literal substitution without freshening would bind
    that value accidentally. *)
Example assertion_cell_substitution_capture_regression :
  assertion_subst 0 (EVar 1) (writer_points_to (EVal 1%Z) (EVar 0)) =
  A.Exists 2 (cell_body (EVal 1%Z) (EVar 2) (EVar 1)).
Proof. reflexivity. Qed.

Example assertion_cell_hiding_capture_regression active :
  assertion_derivation active (writer_points_to (EVal 1%Z) (EVar 1))
    (A.Exists 0 (writer_points_to (EVal 1%Z) (EVar 0))).
Proof. apply assert_derive_cell_value_hiding; cbn; tauto. Qed.

(** The first cell's default hidden writer is the second cell's free
    value name. Exclusion must rename before moving the quantifiers. *)
Example assertion_cell_exclusion_capture_regression active :
  assertion_derivation active
    (A.Spatial (writer_points_to (EVal 1%Z) (EVar 0)) (writer_points_to (EVal 1%Z) (EVar 1)))
    (A.Pure BFalse).
Proof. apply assert_derive_cells_exclusive. Qed.

(** The history's bound value name may occur freely in the writer
    annotation outside its scope. No annotation-freshness premise is used. *)
Example assertion_history_annotation_regression active :
  assertion_derivation active
    (A.Temporal
      (A.Temporal (A.Exists 0 (writer_points_to (EVal 1%Z) (EVar 0)))
        (A.LeadsTo (EVal 1%Z) (EVar 0) (EVal 9%Z))) (A.Barrier (EVar 0)))
    (writer_points_to (EVal 1%Z) (EVal 9%Z)).
Proof. apply assert_derive_drained_history; cbn; tauto. Qed.
