From Stdlib Require Import List ZArith.
From WMLR Require Import Expressions Languages Machine BufferRelations Separation RepairedSeparation
  OperationalSemantics ProgramSteps ExecutionExamples Assertions AssertionSemantics ConcreteAssertions
  RepairedAssertions PersistentAssertions PersistentRules Safety Specifications PrivateOwnership
  TemporalSafety TemporalFence RegionalResources InvariantFragment OwnedSafety OwnedResources
  OwnedRules OwnedFraming OwnedStructural OwnedPrimitives OwnedHeap OwnedAcceptance
  StrongTemporalCounterexample OwnedContainerEntailments OwnedContainer OwnedCalculus OwnedDerivedRules.
Import ListNotations.

(** Derivation trees for checkpoint 10. No constructor accepts semantic validity. *)

Lemma container_read_flag_derived mode tail v : ~ In 0 (A.fv tail) ->
  owned_derivation two_processors container_invariant mode (container_held (A.Spatial (container_flag v) tail))
    container_load_flag (A.And (container_held (A.Spatial (container_flag v) tail)) (A.Pure (container_guard v))).
Proof.
  intros Hfresh; eapply OwnedConsequence.
  - apply container_held_swap.
  - apply OwnedFrameSP.
    + apply owned_derive_load_cell; [apply container_invariant_closed |intros H; contradiction].
    + intros x Hx; cbn [container_load_flag load_command C.modifies] in Hx.
      destruct Hx as [E |Hfalse]; [subst x |contradiction]. exact Hfresh.
  - intros s r H; apply container_spatial_pure in H; destruct H as [H Hb].
    split; [apply container_held_restore, H |exact Hb].
Qed.

Lemma container_read_cases_derived mode p q : ~ In 0 (A.fv p) -> ~ In 0 (A.fv q) ->
  owned_derivation two_processors container_invariant mode (container_cases p q) container_load_flag (container_read_cases p q).
Proof.
  intros Hp Hq; apply OwnedDisjunction.
  - eapply OwnedConsequence; [intros s r H; exact H |apply container_read_flag_derived, Hp |intros s r H; left; exact H].
  - eapply OwnedConsequence; [intros s r H; exact H |apply container_read_flag_derived, Hq |intros s r H; right; exact H].
Qed.

Lemma container_select_one_derived mode p q : ~ In 0 (A.fv p) -> ~ In 0 (A.fv q) ->
  owned_derivation two_processors container_invariant mode (container_cases p q) (container_select 1%Z)
    (container_held (A.Spatial (container_flag 1%Z) q)).
Proof.
  intros Hp Hq; eapply OwnedSequence; [apply container_read_cases_derived; assumption |].
  eapply OwnedConsequence; [|apply OwnedAssume |intros s r H; exact H].
  intros s r [[H Hb] |[H Hb]]; [left |right; exact H].
  change (Z.eqb (s 0) 0%Z = true) in Hb; apply Z.eqb_eq in Hb.
  change (negb (Z.eqb (s 0) 1%Z) = true); rewrite Hb; reflexivity.
Qed.

Lemma container_select_zero_derived mode p q : ~ In 0 (A.fv p) -> ~ In 0 (A.fv q) ->
  owned_derivation two_processors container_invariant mode (container_cases p q) (container_select 0%Z)
    (container_held (A.Spatial (container_flag 0%Z) p)).
Proof.
  intros Hp Hq; eapply OwnedSequence; [apply container_read_cases_derived; assumption |].
  eapply OwnedConsequence; [|apply OwnedAssume |intros s r H; exact H].
  intros s r [[H Hb] |[H Hb]]; [right; exact H |left].
  change (Z.eqb (s 0) 1%Z = true) in Hb; apply Z.eqb_eq in Hb.
  change (negb (Z.eqb (s 0) 0%Z) = true); rewrite Hb; reflexivity.
Qed.

Lemma container_store_known_derived mode loc old value :
  owned_derivation two_processors container_invariant mode (container_cell loc old)
    (store_command 1%positive loc value) (container_history loc 1%positive value).
Proof.
  eapply OwnedConsequence; [intros s r H; exact H |apply owned_derive_store_cell |].
  apply container_temporal_mono; [apply container_cell_some |intros s r H; exact H].
Qed.

Lemma container_expression_cell_some active loc expression :
  persistent_entails active (writer_points_to (EVal (Z.pos loc)) expression) (container_some_cell loc).
Proof.
  intros s r H; apply container_some_cell_models; exists (eval_expr s expression).
  destruct (writer_points_to_shape _ _ _ _ _ H) as (address & owner & E & Hi & Hheap & Hbuffers & Hfree & Hmark).
  cbn in E; inversion E; subst address.
  eapply writer_points_to_from_shape with (loc := loc) (owner := owner); try eassumption; reflexivity.
Qed.

Lemma container_store_some_derived mode loc value :
  owned_derivation two_processors container_invariant mode (container_some_cell loc)
    (store_command 1%positive loc value) (container_history loc 1%positive value).
Proof.
  apply OwnedExists.
  - apply container_invariant_closed.
  - intros H; contradiction.
  - cbn [container_history container_some_cell container_write writer_points_to A.fv expr_fv fresh]; tauto.
  - eapply OwnedConsequence; [intros s r H; exact H |apply owned_derive_store_cell |].
    apply container_temporal_mono; [apply container_expression_cell_some |intros s r H; exact H].
Qed.


Lemma container_store_flag_derived mode tail old value :
  owned_derivation two_processors container_invariant mode (container_held (A.Spatial (container_flag old) tail))
    (store_command 1%positive 1%positive value) (container_held (A.Spatial (container_flag_history value) tail)).
Proof.
  eapply OwnedConsequence; [apply container_held_swap | |apply container_held_restore].
  apply OwnedFrameSP; [apply container_store_known_derived |intros x H; contradiction].
Qed.

Theorem container_remove_derived :
  owned_derivation two_processors container_invariant DisjointMode A.Emp container_remove container_item.
Proof.
  eapply OwnedSequence with (middle := container_cases A.Emp container_item).
  - eapply OwnedConsequence; [intros s r H; exact H | |apply container_first_acquire_entails].
    apply OwnedLock.
  - eapply OwnedSequence.
    + apply container_select_one_derived; cbn [container_item container_some_cell writer_points_to A.fv expr_fv fresh]; tauto.
    + eapply OwnedSequence; [apply container_store_flag_derived |].
      apply OwnedUnlock, container_remove_unlock_entails.
Qed.

Theorem container_return_derived :
  owned_derivation two_processors container_invariant DisjointMode container_private_history container_return A.Emp.
Proof.
  eapply OwnedSequence with (middle := container_cases (container_cell 2%positive 9%Z) container_item).
  - apply OwnedWeaken.
    eapply OwnedConsequence; [intros s r H; apply temporal_emp_right_intro, H | |apply container_reacquire_entails].
    apply OwnedFrameTM; [|intros x H; contradiction].
    apply OwnedLock.
  - eapply OwnedSequence.
    + apply container_select_zero_derived;
        cbn [container_item container_some_cell container_cell writer_points_to A.fv expr_fv fresh]; tauto.
    + eapply OwnedSequence; [apply container_store_flag_derived |].
      apply OwnedUnlock, container_return_unlock_entails.
Qed.

Theorem container_core_derived :
  owned_derivation two_processors container_invariant DisjointMode A.Emp container_program A.Emp.
Proof.
  eapply OwnedSequence; [apply container_remove_derived |].
  eapply OwnedSequence; [apply container_store_some_derived |apply container_return_derived].
Qed.

Theorem owned_container_derived :
  owned_derivation two_processors container_invariant DisjointMode container_foreign container_program container_foreign.
Proof.
  eapply OwnedConsequence; [intros s r H; apply persistent_spatial_emp_right, H | |].
  - apply OwnedFrameSP; [apply container_core_derived |intros x _ H; contradiction].
  - apply container_spatial_emp_elim; exact I.
Qed.
