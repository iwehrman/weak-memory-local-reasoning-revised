From Stdlib Require Import List ZArith.
From WMLR Require Import Expressions Languages Machine BufferRelations Separation RepairedSeparation
  OperationalSemantics ExecutionExamples Assertions AssertionSemantics ConcreteAssertions RepairedAssertions
  PersistentAssertions PersistentRules AssertionSubstitution Safety Specifications TemporalSafety RegionalResources
  InvariantFragment OwnedSafety OwnedHeap OwnedCalculus OwnedDerivedRules StrongTemporalCounterexample
  OwnedContainerEntailments OwnedContainer OwnedContainerDerivation.
Import ListNotations.

Definition container_done value := BEq (EVar 1) (EVal value).
Definition container_retry_invariant pre post :=
  A.Or (A.And pre (A.Pure (container_done 0%Z))) (A.And post (A.Pure (container_done 1%Z))).
Definition container_set_done value := C.Prim (C.Common (S.Assign 1 (EVal value))) (EVal 1%Z).
Definition container_retry attempt := C.Seq (container_set_done 0%Z)
  (C.while_do (EVal 1%Z) (container_done 0%Z) attempt).

Lemma container_models_update active p s r x value :
  ~ In x (A.fv p) -> persistent_models active s r p -> persistent_models active (update s x value) r p.
Proof.
  intros Hfresh HP; apply (proj1 (future_satisfies_agrees _ _ p s (update s x value)
    (agrees_update_irrelevant _ _ _ _ Hfresh) r)), HP.
Qed.

Lemma container_set_retry_derived mode pre post : ~ In 1 (A.fv pre) ->
  owned_derivation two_processors container_invariant mode pre (container_set_done 0%Z)
    (container_retry_invariant pre post).
Proof.
  intros Hfresh; apply owned_derive_assign_from; [apply container_invariant_closed |].
  intros s r HP; left; split; [apply container_models_update; assumption |reflexivity].
Qed.

Lemma container_set_finished_derived mode pre post : ~ In 1 (A.fv post) ->
  owned_derivation two_processors container_invariant mode post (container_set_done 1%Z)
    (container_retry_invariant pre post).
Proof.
  intros Hfresh; apply owned_derive_assign_from; [apply container_invariant_closed |].
  intros s r HP; right; split; [apply container_models_update; assumption |reflexivity].
Qed.

Lemma container_retry_derived mode pre post attempt : ~ In 1 (A.fv pre) ->
  owned_derivation two_processors container_invariant mode pre attempt (container_retry_invariant pre post) ->
  owned_derivation two_processors container_invariant mode pre (container_retry attempt) post.
Proof.
  intros Hfresh Hattempt; eapply OwnedSequence; [apply container_set_retry_derived, Hfresh |].
  eapply OwnedConsequence; [intros s r H; exact H |apply owned_derive_while |].
  - eapply OwnedConsequence; [|exact Hattempt |intros s r H; exact H].
    intros s r [[ [HP Hz] |[HQ Ho] ] Hguard]; [exact HP |].
    change (Z.eqb (s 1) 1%Z = true) in Ho; apply Z.eqb_eq in Ho.
    change (Z.eqb (s 1) 0%Z = true) in Hguard; rewrite Ho in Hguard; discriminate.
  - intros s r [[ [HP Hz] |[HQ Ho] ] Hguard]; [|exact HQ].
    change (negb (Z.eqb (s 1) 0%Z) = true) in Hguard.
    change (Z.eqb (s 1) 0%Z = true) in Hz; rewrite Hz in Hguard; discriminate.
Qed.

Lemma container_empty_release_derived :
  owned_derivation two_processors container_invariant DisjointMode
    (container_held (A.Spatial (container_flag 0%Z) A.Emp)) container_release A.Emp.
Proof.
  apply OwnedUnlock; intros s r H.
  apply persistent_spatial_emp_right; left.
  apply container_spatial_emp_elim; [cbn [container_flag container_cell writer_points_to wand_free]; tauto |].
  eapply stm_wand_free_barrier_elim;
    [cbn [container_flag container_cell writer_points_to wand_free]; tauto |exact H].
Qed.

Definition container_take_success := C.Seq (store_command 1%positive 1%positive 0%Z)
  (C.Seq container_release (container_set_done 1%Z)).
Definition container_take_failure := C.Seq container_release (container_set_done 0%Z).
Definition container_take_attempt := C.Seq container_acquire
  (C.Seq container_load_flag (C.if_then_else (EVal 1%Z) (container_guard 1%Z)
    container_take_success container_take_failure)).
Definition container_retry_take := container_retry container_take_attempt.

Theorem container_take_attempt_derived :
  owned_derivation two_processors container_invariant DisjointMode A.Emp container_take_attempt
    (container_retry_invariant A.Emp container_item).
Proof.
  eapply OwnedSequence with (middle := container_cases A.Emp container_item).
  - eapply OwnedConsequence; [intros s r H; exact H |apply OwnedLock |apply container_first_acquire_entails].
  - eapply OwnedSequence; [apply container_read_cases_derived;
      cbn [container_item container_some_cell writer_points_to A.fv expr_fv fresh]; tauto |].
    apply OwnedChoice.
    + eapply OwnedSequence with (middle := container_held (A.Spatial (container_flag 1%Z) container_item)).
      * eapply OwnedConsequence; [|apply OwnedAssume |intros s r H; exact H].
        intros s r [[HP Hb] |[HQ Hb]]; [left |right; exact HQ].
        change (Z.eqb (s 0) 0%Z = true) in Hb; apply Z.eqb_eq in Hb.
        change (negb (Z.eqb (s 0) 1%Z) = true); rewrite Hb; reflexivity.
      * eapply OwnedSequence; [apply container_store_flag_derived |].
        eapply OwnedSequence; [apply OwnedUnlock, container_remove_unlock_entails |].
        apply container_set_finished_derived; cbn [container_item container_some_cell writer_points_to A.fv expr_fv fresh]; tauto.
    + eapply OwnedSequence with (middle := container_held (A.Spatial (container_flag 0%Z) A.Emp)).
      * eapply OwnedConsequence; [|apply OwnedAssume |intros s r H; exact H].
        intros s r [[HP Hb] |[HQ Hb]]; [right; exact HP |left].
        change (Z.eqb (s 0) 1%Z = true) in Hb.
        change (negb (negb (Z.eqb (s 0) 1%Z)) = true); rewrite Hb; reflexivity.
      * eapply OwnedSequence; [apply container_empty_release_derived |].
        apply container_set_retry_derived; intros H; contradiction.
Qed.

Theorem container_retry_take_derived :
  owned_derivation two_processors container_invariant DisjointMode A.Emp container_retry_take container_item.
Proof. apply container_retry_derived; [intros H; contradiction |apply container_take_attempt_derived]. Qed.

Lemma container_history_heap active s r loc owner value :
  persistent_models active s r (container_history loc owner value) ->
  exists old, shared_heap (resource_memory active r) loc = Some old.
Proof.
  intros (a & b & [_ [[_ [Hheap _]] _]] & HA & [_ [HB |HB]]);
    apply container_some_cell_models in HA; destruct HA as [old HA];
    destruct (container_cell_shape _ _ _ _ _ HA) as (writer & Hi & Hah & _).
  - destruct HB as [Hbh _]; exists old; unfold resource_memory; rewrite Hheap.
    unfold heap_override; rewrite Hbh, Hah; apply heap_update_same.
  - destruct HB as [Hbh _]; exists value; unfold resource_memory; rewrite Hheap.
    unfold heap_override; rewrite Hbh, heap_update_same; reflexivity.
Qed.

Lemma container_item_history_disjoint s r :
  ~ persistent_models two_processors s r (A.Spatial container_item container_private_history).
Proof.
  intros (a & b & [[[Hdisjoint _] _] _] & HA & HB).
  apply container_some_cell_models in HA; destruct HA as [value HA].
  destruct (container_cell_shape _ _ _ _ _ HA) as (owner & Hi & Hheap & _).
  destruct (container_history_heap _ _ _ _ _ _ HB) as [old Hold].
  apply (Hdisjoint 2%positive); left; [exists value; rewrite Hheap; apply heap_update_same |exists old; exact Hold].
Qed.

(** Spatial framing retains disjoint ownership at reacquisition. Thus a full
    pool containing x is incompatible with the still privately owned x. *)
Lemma container_retry_acquire_entails :
  persistent_entails two_processors
    (A.Spatial container_private_history (A.Temporal (container_held container_invariant) (A.Barrier (EVal 1%Z))))
    (container_held (A.Spatial (container_flag 0%Z) container_private_history)).
Proof.
  intros s r H.
  assert (Hplain : persistent_models two_processors s r (A.Spatial container_private_history (container_held container_invariant))).
  { eapply container_spatial_mono; [intros t a Ha; exact Ha | |exact H].
    intros t a Ha; eapply stm_wand_free_barrier_elim;
      [cbn [container_held container_token container_invariant container_flag container_cell container_item container_some_cell writer_points_to wand_free]; tauto |exact Ha]. }
  apply container_spatial_comm in Hplain; apply container_spatial_assoc in Hplain.
  destruct Hplain as (token & payload & Hsp & Htoken & shared & private & Hinner & [HJ |HJ] & HP).
  - exists token,payload; split; [exact Hsp |]. split; [exact Htoken |exists shared,private; auto].
  - assert (Hfull : persistent_models two_processors s payload
      (A.Spatial (A.Spatial (container_flag 1%Z) container_item) container_private_history)).
    { exists shared,private; auto. }
    apply container_spatial_assoc in Hfull; destruct Hfull as (flag & rest & Hrest & HF & HX).
    exfalso; exact (container_item_history_disjoint s rest HX).
Qed.

Lemma container_retry_return_unlock_entails :
  persistent_entails two_processors
    (A.Temporal (A.Spatial (container_flag_history 1%Z) container_private_history) (A.Barrier (EVal 1%Z)))
    (A.Spatial container_invariant A.Emp).
Proof.
  intros s r H; apply (container_barrier_spatial two_processors (container_flag_history 1%Z) container_private_history 1%positive) in H;
    [|left; reflexivity |cbn [container_flag_history container_history container_some_cell container_write writer_points_to wand_free]; tauto
     |cbn [container_private_history container_history container_some_cell container_write writer_points_to wand_free]; tauto].
  apply persistent_spatial_emp_right; right.
  eapply container_spatial_mono; [| |exact H].
  - apply container_history_complete; left; reflexivity.
  - intros t a Ha; apply container_cell_some with (value := 9%Z).
    eapply container_history_complete; [left; reflexivity |exact Ha].
Qed.

Definition container_put_success := C.Seq (store_command 1%positive 1%positive 1%Z)
  (C.Seq container_release (container_set_done 1%Z)).
Definition container_put_failure := C.Seq container_release (container_set_done 0%Z).
Definition container_put_attempt := C.Seq container_acquire
  (C.Seq container_load_flag (C.if_then_else (EVal 1%Z) (container_guard 0%Z)
    container_put_success container_put_failure)).
Definition container_retry_put := container_retry container_put_attempt.

Theorem container_put_attempt_derived :
  owned_derivation two_processors container_invariant DisjointMode container_private_history container_put_attempt
    (container_retry_invariant container_private_history A.Emp).
Proof.
  eapply OwnedSequence with (middle := container_held (A.Spatial (container_flag 0%Z) container_private_history)).
  - eapply OwnedConsequence; [intros s r H; apply persistent_spatial_emp_right, H | |apply container_retry_acquire_entails].
    apply OwnedFrameSP; [apply OwnedLock |intros x H; contradiction].
  - eapply OwnedSequence; [apply container_read_flag_derived;
      cbn [container_private_history container_history container_some_cell container_write writer_points_to A.fv expr_fv fresh]; tauto |].
    apply OwnedChoice.
    + eapply OwnedSequence with (middle := container_held (A.Spatial (container_flag 0%Z) container_private_history)).
      * eapply OwnedConsequence; [|apply OwnedAssume |intros s r H; exact H].
        intros s r [HP Hb]; right; exact HP.
      * eapply OwnedSequence; [apply container_store_flag_derived |].
        eapply OwnedSequence; [apply OwnedUnlock, container_retry_return_unlock_entails |].
        apply container_set_finished_derived; intros H; contradiction.
    + eapply OwnedSequence with (middle := A.Pure BFalse).
      * eapply OwnedConsequence; [|apply OwnedAssume |intros s r H; exact H].
        intros s r [HP Hb]; left.
        change (Z.eqb (s 0) 0%Z = true) in Hb.
        change (negb (negb (Z.eqb (s 0) 0%Z)) = true); rewrite Hb; reflexivity.
      * eapply OwnedSequence; [apply owned_derive_unlock_false |].
        apply owned_derive_assign_from; [apply container_invariant_closed |intros s r H; discriminate H].
Qed.

Theorem container_retry_put_derived :
  owned_derivation two_processors container_invariant DisjointMode container_private_history container_retry_put A.Emp.
Proof.
  apply container_retry_derived; [|apply container_put_attempt_derived].
  cbn [container_private_history container_history container_some_cell container_write writer_points_to A.fv expr_fv fresh]; tauto.
Qed.

Definition retrying_container_program := C.Seq container_retry_take
  (C.Seq (store_command 1%positive 2%positive 9%Z) container_retry_put).

Theorem container_retry_core_derived :
  owned_derivation two_processors container_invariant DisjointMode A.Emp retrying_container_program A.Emp.
Proof.
  eapply OwnedSequence; [apply container_retry_take_derived |].
  eapply OwnedSequence; [apply container_store_some_derived |apply container_retry_put_derived].
Qed.

Theorem owned_retrying_container_derived :
  owned_derivation two_processors container_invariant DisjointMode container_foreign retrying_container_program container_foreign.
Proof.
  eapply OwnedConsequence; [intros s r H; apply persistent_spatial_emp_right, H | |].
  - apply OwnedFrameSP; [apply container_retry_core_derived |intros x _ H; contradiction].
  - apply container_spatial_emp_elim; exact I.
Qed.
