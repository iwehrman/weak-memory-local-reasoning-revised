From Stdlib Require Import List ZArith.
From WMLR Require Import Expressions Languages Machine BufferRelations Separation OperationalSemantics
  ExecutionExamples Assertions AssertionSemantics PersistentAssertions Safety TemporalSafety
  InvariantFragment OwnedSafety OwnedCalculus OwnedAcceptance OwnedDerivedRules AssertionDerivation
  AssertionDerivedRules AssertionSoundness OwnedAssertionRules OwnedClientRules CellFamilies
  OwnedContainerTrace NamedLockSyntax NamedLockRules NamedLockTrace.
Import ListNotations.

Theorem named_lock_family_valid active locks flag invariant actor x :
  Forall (fun item => invariant_fragment (snd item)) locks -> two_active_processors active ->
  In (flag,invariant) locks -> ~ In x (A.fv (nl_pool locks)) ->
  assertion_derivation active (A.Spatial invariant invariant) (A.Pure BFalse) ->
  owned_valid active DisjointMode (nl_pool locks) A.Emp (nl_acquire actor flag x) invariant /\
  owned_valid active DisjointMode (nl_pool locks) invariant (nl_release actor flag) A.Emp.
Proof.
  intros Hfr Htwo Hin HF Hex; split; apply owned_calculus_sound;
    [apply nl_pool_fragment,Hfr |exact Htwo |apply named_lock_acquire_family; assumption
    |apply nl_pool_fragment,Hfr |exact Htwo |apply named_lock_release_family; assumption].
Qed.

Definition nl_two_locks : nl_family := [(1%positive,nl_cell 2%positive 7%Z);(3%positive,nl_cell 4%positive 9%Z)].
Definition nl_two_items := [(1%positive,0%Z);(2%positive,7%Z);(3%positive,0%Z);(4%positive,9%Z)].
Definition nl_two_initial := cell_memory nl_two_items.
Definition nl_nested := C.Seq (nl_acquire 1%positive 1%positive 0)
  (C.Seq (nl_acquire 1%positive 3%positive 0)
    (C.Seq (nl_release 1%positive 3%positive) (nl_release 1%positive 1%positive))).

Lemma nl_two_pool_closed : A.fv (nl_pool nl_two_locks) = [].
Proof. cbn [nl_two_locks nl_pool A.fv]; rewrite !nl_component_fv,!nl_cell_fv; reflexivity. Qed.

Theorem named_lock_nested_derived :
  owned_derivation two_processors (nl_pool nl_two_locks) DisjointMode A.Emp nl_nested A.Emp.
Proof.
  eapply OwnedSequence with (middle := nl_cell 2%positive 7%Z).
  - apply named_lock_acquire_family; [left; reflexivity |rewrite nl_two_pool_closed; tauto].
  - eapply OwnedSequence with (middle := A.Spatial (nl_cell 2%positive 7%Z) (nl_cell 4%positive 9%Z)).
    + eapply owned_assertion_consequence; [apply (AssertUnitRight two_processors SepSpatial Backward) | |apply AssertRefl].
      apply OwnedFrameSP.
      * apply named_lock_acquire_family; [right; left; reflexivity |rewrite nl_two_pool_closed; tauto].
      * intros x HM HF; rewrite nl_cell_fv in HF; contradiction.
    + eapply OwnedSequence with (middle := nl_cell 2%positive 7%Z).
      * eapply owned_assertion_consequence; [apply AssertRefl | |apply (AssertUnitRight two_processors SepSpatial Forward)].
        apply OwnedFrameSP.
        -- apply named_lock_release_family; [right; left; reflexivity |apply assert_derive_cells_exclusive].
        -- intros x H; contradiction.
      * apply named_lock_release_family; [left; reflexivity |apply assert_derive_cells_exclusive].
Qed.

Lemma nl_two_initial_assertion active : assertion_derivation active (cell_family nl_two_items) (nl_pool nl_two_locks).
Proof.
  eapply AssertTrans; [apply (AssertAssociative active SepSpatial Backward) |].
  apply (AssertSeparateMono active SepSpatial); [apply AssertOrLeft |].
  eapply AssertTrans; [apply (AssertAssociative active SepSpatial Backward) |].
  apply (AssertSeparateMono active SepSpatial); [apply AssertOrLeft |apply AssertRefl].
Qed.

Theorem named_lock_two_initial_inhabited s :
  persistent_full_satisfies two_processors s nl_two_initial (nl_pool nl_two_locks) /\
  lock_free nl_two_initial /\ (forall i, buffers nl_two_initial i = []) /\
  shared_heap nl_two_initial 1%positive = Some 0%Z /\ shared_heap nl_two_initial 3%positive = Some 0%Z /\
  shared_heap nl_two_initial 2%positive = Some 7%Z /\ shared_heap nl_two_initial 4%positive = Some 9%Z.
Proof.
  split.
  - exists (cell_resource two_processors 1%positive (or_introl eq_refl) nl_two_items); split; [reflexivity |].
    apply (assertion_derivation_sound _ _ _ (nl_two_initial_assertion two_processors)).
    apply cell_family_models; repeat constructor; cbn; intuition discriminate.
  - split; [intros i H; exact H |]; repeat split; intros; reflexivity.
Qed.

Definition nl_two_first := nl_write_final two_processors 1%positive 1%positive 1%Z nl_two_initial.
Definition nl_two_both := nl_write_final two_processors 1%positive 3%positive 1%Z nl_two_first.
Definition nl_two_second_returned := nl_write_final two_processors 1%positive 3%positive 0%Z nl_two_both.
Definition nl_two_final := nl_write_final two_processors 1%positive 1%positive 0%Z nl_two_second_returned.
Definition nl_after_first s := update (update s 0 1%Z) 0 0%Z.
Definition nl_after_both s := nl_after_first (nl_after_first s).

Theorem named_lock_nested_trace s : execution two_processors 59 nl_nested s nl_two_initial halt (nl_after_both s) nl_two_final.
Proof.
  change 59 with (22 + S 36); eapply container_execution_sequence with (middle := nl_two_first) (t := nl_after_first s).
  - apply named_lock_acquire_success_trace; [left; reflexivity |reflexivity |reflexivity].
  - change 36 with (22 + S 13); eapply container_execution_sequence with (middle := nl_two_both) (t := nl_after_both s).
    + apply named_lock_acquire_success_trace; [left; reflexivity |reflexivity |reflexivity].
    + change 13 with (6 + S 6); eapply container_execution_sequence with (middle := nl_two_second_returned).
      * apply named_lock_release_trace; [left; reflexivity |reflexivity |reflexivity].
      * apply named_lock_release_trace; [left; reflexivity |reflexivity |reflexivity].
Qed.

Theorem named_lock_nested_state :
  shared_heap nl_two_both 1%positive = Some 1%Z /\ shared_heap nl_two_both 3%positive = Some 1%Z /\
  lock_free nl_two_both /\
  shared_heap nl_two_final 1%positive = Some 0%Z /\ shared_heap nl_two_final 3%positive = Some 0%Z /\
  shared_heap nl_two_final 2%positive = Some 7%Z /\ shared_heap nl_two_final 4%positive = Some 9%Z /\
  (forall i, buffers nl_two_final i = []) /\ lock_free nl_two_final.
Proof.
  split; [reflexivity |split; [reflexivity |split; [intros i H; exact H |]]].
  repeat split; try reflexivity; try (intros i H; exact H).
  intros i; unfold nl_two_final,nl_two_second_returned,nl_two_both,nl_two_first,nl_write_final.
  cbn [release flush_write enqueue acquire buffers]; unfold buffer_update; destruct (Pos.eq_dec i 1%positive); reflexivity.
Qed.

Theorem named_lock_nested_all_runs s n last t final :
  execution two_processors n nl_nested s nl_two_initial last t final ->
  ~ abort two_processors last (State t final) /\
  (terminal last -> exists local pool,
    memory_spatial pool (resource_memory two_processors local) final /\
    persistent_models two_processors t local A.Emp /\
    lock_free final /\ persistent_full_satisfies two_processors t pool (nl_pool nl_two_locks)).
Proof.
  intros HR; assert (HF : invariant_fragment (nl_pool nl_two_locks)) by (repeat constructor).
  assert (HE : persistent_models two_processors s (empty_resource_value two_processors) A.Emp).
  { split; [intros; reflexivity |split; [intros; reflexivity |intros i H; exact H]]. }
  destruct (named_lock_two_initial_inhabited s) as [HJ [HK Hrest]].
  pose proof (proj1 (spatial_empty_right (Generalized nl_two_initial no_blocked))) as HS.
  destruct (owned_derivation_adequacy two_processors (nl_pool nl_two_locks) HF acceptance_two_active
    DisjointMode _ _ _ named_lock_nested_derived n s _ last t final
    (empty_resource_value two_processors) nl_two_initial HE HJ HK HS HR) as [Hsafe Hdone].
  split; [exact Hsafe |intros HT].
  destruct (Hdone HT) as (local & pool & Hsplit & HP & [[Hfree Hpool] |[owner [[Hi Hheld] Ep]]]).
  - exists local,pool; auto.
  - exfalso; destruct HP as [_ [_ Hfree]].
    destruct Hi as [-> | ->]; [apply (Hfree 2%positive) |apply (Hfree 1%positive)];
      apply Hheld; split; [right; reflexivity |discriminate |left; reflexivity |discriminate].
Qed.
