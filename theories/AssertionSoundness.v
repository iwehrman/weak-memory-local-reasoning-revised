From Stdlib Require Import List ZArith.
From WMLR Require Import Expressions Machine Separation Assertions AssertionSemantics
  PersistentAssertions PersistentRules AssertionDerivation AssertionLogicalRules
  AssertionAlgebra AssertionBarrierAlgebra AssertionLockAlgebra AssertionWriteAlgebra
  AssertionCellAlgebra.

Lemma assertion_equivalence_direction active direction p q :
  (forall s r, persistent_models active s r p <-> persistent_models active s r q) ->
  persistent_entails active (assertion_source direction p q) (assertion_target direction p q).
Proof. intros H; destruct direction; intros s r HP; [apply (proj1 (H s r)) |apply (proj2 (H s r))]; exact HP. Qed.

(** All 47 approved constructors, with no global domain, invariant,
    wand-free or mode assumption. The pure oracle remains boolean-only. *)
Theorem assertion_derivation_sound active p q :
  assertion_derivation active p q -> persistent_entails active p q.
Proof.
  intros H; induction H.
  - apply assertion_rule_refl.
  - eapply assertion_rule_trans; eassumption.
  - apply assertion_rule_true.
  - apply assertion_rule_false.
  - apply assertion_rule_and_intro; assumption.
  - apply assertion_rule_and_left.
  - apply assertion_rule_and_right.
  - apply assertion_rule_or_left.
  - apply assertion_rule_or_right.
  - apply assertion_rule_or_cases; assumption.
  - apply assertion_rule_exists_intro.
  - apply assertion_rule_exists_elim; assumption.
  - apply assertion_rule_forall_intro; assumption.
  - apply assertion_rule_forall_elim.
  - apply assertion_rule_substitute; assumption.
  - apply assertion_rule_pure; assumption.
  - apply (assertion_rule_pure_cases active p b q); assumption.
  - apply assertion_rule_equality.
  - destruct kind; [apply (assertion_conjunction_mono SpatialKind) |apply (assertion_conjunction_mono TemporalKind)]; assumption.
  - apply assertion_equivalence_direction; intros s r; destruct kind;
      [apply (assertion_conjunction_unit_left SpatialKind) |apply (assertion_conjunction_unit_left TemporalKind)].
  - apply assertion_equivalence_direction; intros s r; destruct kind;
      [apply (assertion_conjunction_unit_right SpatialKind) |apply (assertion_conjunction_unit_right TemporalKind)].
  - apply assertion_equivalence_direction; intros s a; destruct kind;
      [apply assertion_spatial_associative |apply assertion_temporal_associative].
  - intros s r HP; apply (proj1 (assertion_spatial_commutative _ _ _ _ _)),HP.
  - apply assertion_equivalence_direction,assertion_rule_or_separate_left.
  - apply assertion_equivalence_direction,assertion_rule_or_separate_right.
  - apply assertion_equivalence_direction,assertion_rule_exists_separate_left,H.
  - apply assertion_equivalence_direction,assertion_rule_exists_separate_right,H.
  - apply assertion_equivalence_direction,assertion_rule_pure_separate_left.
  - apply assertion_equivalence_direction,assertion_rule_pure_separate_right.
  - apply persistent_spatial_wand_adjoint,IHassertion_derivation.
  - apply persistent_spatial_wand_adjoint,IHassertion_derivation.
  - apply persistent_temporal_wand_left_adjoint,IHassertion_derivation.
  - apply persistent_temporal_wand_left_adjoint,IHassertion_derivation.
  - apply persistent_temporal_wand_right_adjoint,IHassertion_derivation.
  - apply persistent_temporal_wand_right_adjoint,IHassertion_derivation.
  - apply assertion_barrier_entails_emp.
  - apply assertion_equivalence_direction; intros s r; destruct kind;
      [apply (assertion_barrier_idempotent SpatialKind) |apply (assertion_barrier_idempotent TemporalKind)].
  - apply assertion_equivalence_direction; intros s r; destruct kind;
      [apply assertion_barrier_distributes_spatial |apply assertion_barrier_distributes_temporal].
  - intros s r HP; exact (proj1 (proj2 (assertion_strong_barrier_temporal _ _ _ _ _) HP)).
  - apply assertion_equivalence_direction,assertion_temporal_lock_right_spatial.
  - apply assertion_equivalence_direction,assertion_temporal_lock_left_spatial.
  - apply (assertion_lock_multiplication_common_blocker SpatialKind active first second blocker); assumption.
  - intros s r HP; apply (proj1 (assertion_spatial_writes_exclusive active address first second old next s r)),HP.
  - apply assertion_equivalence_direction,assertion_successive_writes_collapse.
  - apply assertion_points_to_write_active,H.
  - intros s r [Hne HP]; split; [exact Hne |]. destruct direction.
    + apply (proj1 (assertion_cells_separate _ _ _ _ _ _ _ Hne)),HP.
    + apply (proj2 (assertion_cells_separate _ _ _ _ _ _ _ Hne)),HP.
  - apply assertion_cell_overwrite.
Qed.
