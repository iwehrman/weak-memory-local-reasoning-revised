From Stdlib Require Import List ZArith Lia.
From WMLR Require Import Expressions Languages Machine BufferRelations Separation RepairedSeparation
  OperationalSemantics ExecutionExamples Assertions AssertionSemantics ConcreteAssertions PersistentAssertions
  Safety GeneralizedFlushing SpatialExchange TemporalSafety RegionalResources InvariantFragment InvariantFragmentExamples PrivateOwnership
  OwnedSafety OwnedAdequacy OwnedResources OwnedAcceptance OwnedContainerEntailments OwnedContainer
  OwnedContainerTrace OwnedCalculus OwnedContainerDerivation OwnedRetryContainer OwnedExecution.
Import ListNotations.

Lemma container_done_trace s memory value :
  execution two_processors 1 (container_set_done value) s memory halt (update s 1 value) memory.
Proof.
  eapply ExecuteNext; [|constructor]. eapply StepPrimitive; [reflexivity |].
  apply PrimitiveAssign; left; reflexivity.
Qed.

Lemma container_if_true_trace n condition yes no s initial t final :
  eval_bexpr s condition = true -> execution two_processors n yes s initial halt t final ->
  execution two_processors (n + 3) (C.if_then_else (EVal 1%Z) condition yes no) s initial halt t final.
Proof.
  intros Hb Hrun; replace (n + 3) with (S (1 + S n)) by lia.
  eapply ExecuteNext; [apply StepChoiceLeft |]. eapply container_execution_sequence; [|exact Hrun].
  eapply ExecuteNext; [|constructor]. eapply StepPrimitive; [reflexivity |].
  apply PrimitiveAssume; [left; reflexivity |exact Hb].
Qed.

Lemma container_if_false_trace n condition yes no s initial t final :
  eval_bexpr s condition = false -> execution two_processors n no s initial halt t final ->
  execution two_processors (n + 3) (C.if_then_else (EVal 1%Z) condition yes no) s initial halt t final.
Proof.
  intros Hb Hrun; replace (n + 3) with (S (1 + S n)) by lia.
  eapply ExecuteNext; [apply StepChoiceRight |]. eapply container_execution_sequence; [|exact Hrun].
  eapply ExecuteNext; [|constructor]. eapply StepPrimitive; [reflexivity |].
  apply PrimitiveAssume; [left; reflexivity |cbn; rewrite Hb; reflexivity].
Qed.

Lemma container_loop_one_trace n attempt s initial t final :
  s 1 = 0%Z -> execution two_processors n attempt s initial halt t final ->
  execution two_processors (n + 7)
    (C.Loop (C.Seq (C.Prim (C.Common (S.Assume (container_done 0%Z))) (EVal 1%Z)) attempt))
    s initial halt t final.
Proof.
  intros Hz Hrun; replace (n + 7) with (S (S ((1 + S n) + S 2))) by lia.
  eapply ExecuteNext; [apply StepLoop |]. eapply ExecuteNext; [apply StepChoiceRight |].
  eapply container_execution_sequence.
  - eapply container_execution_sequence; [|exact Hrun].
    eapply ExecuteNext; [|constructor]. eapply StepPrimitive; [reflexivity |].
    apply PrimitiveAssume; [left; reflexivity |change (Z.eqb (s 1) 0%Z = true); rewrite Hz; reflexivity].
  - eapply ExecuteNext; [apply StepLoop |]. eapply ExecuteNext; [apply StepChoiceLeft |constructor].
Qed.

Lemma container_retry_one_trace n attempt s initial t final :
  execution two_processors n attempt (update s 1 0%Z) initial halt t final -> t 1 = 1%Z ->
  execution two_processors (n + 11) (container_retry attempt) s initial halt t final.
Proof.
  intros Hrun Ho; replace (n + 11) with (1 + S ((n + 7) + S 1)) by lia.
  eapply container_execution_sequence; [apply container_done_trace |].
  eapply container_execution_sequence; [apply container_loop_one_trace; [apply update_same |exact Hrun] |].
  eapply ExecuteNext; [|constructor]. eapply StepPrimitive; [reflexivity |].
  apply PrimitiveAssume; [left; reflexivity |change (negb (Z.eqb (t 1) 0%Z) = true); rewrite Ho; reflexivity].
Qed.

Lemma container_take_success_trace s :
  execution two_processors 13 container_take_attempt s container_initial halt
    (update (update s 0 1%Z) 1 1%Z) container_removed.
Proof.
  change 13 with (1 + S 11); eapply container_execution_sequence with (t := s) (middle := container_first_held).
  - eapply ExecuteNext; [|constructor]. eapply StepPrimitive; [reflexivity |].
    apply PrimitiveLock; [left; reflexivity |reflexivity |intros i H; exact H].
  - change 11 with (1 + S 9); eapply container_execution_sequence with (t := update s 0 1%Z) (middle := container_first_held).
    + eapply ExecuteNext; [|constructor]. eapply StepPrimitive; [reflexivity |].
      apply PrimitiveLoad; [left; reflexivity |intros [_ H]; apply H; reflexivity |reflexivity].
    + change 9 with (6 + 3); apply container_if_true_trace; [reflexivity |].
      change 6 with (2 + S 3); eapply container_execution_sequence with (middle := container_remove_flushed).
      * eapply ExecuteNext; [eapply StepPrimitive; [reflexivity |] |].
        -- eapply PrimitiveStore with (previous := 1%Z); [left; reflexivity |reflexivity |reflexivity].
        -- eapply ExecuteNext; [apply StepFlush; apply FlushWrite with (i := 1%positive);
            [left; reflexivity |intros [_ H]; apply H; reflexivity |reflexivity] |constructor].
      * change 3 with (1 + S 1); eapply container_execution_sequence; [|apply container_done_trace].
        eapply ExecuteNext; [|constructor]. eapply StepPrimitive; [reflexivity |].
        apply PrimitiveUnlock; [left; reflexivity |reflexivity |split; [left; reflexivity |intros i; reflexivity]].
Qed.

Lemma container_put_success_trace s :
  execution two_processors 14 container_put_attempt s container_private_pending halt
    (update (update s 0 0%Z) 1 1%Z) container_final.
Proof.
  change 14 with (2 + S 11); eapply container_execution_sequence with (t := s) (middle := container_second_held).
  - eapply ExecuteNext; [apply StepFlush; apply FlushWrite with (i := 1%positive);
      [left; reflexivity |intros H; exact H |reflexivity] |].
    eapply ExecuteNext; [|constructor]. eapply StepPrimitive; [reflexivity |].
    apply PrimitiveLock; [left; reflexivity |reflexivity |intros i H; exact H].
  - change 11 with (1 + S 9); eapply container_execution_sequence with (t := update s 0 0%Z) (middle := container_second_held).
    + eapply ExecuteNext; [|constructor]. eapply StepPrimitive; [reflexivity |].
      apply PrimitiveLoad; [left; reflexivity |intros [_ H]; apply H; reflexivity |reflexivity].
    + change 9 with (6 + 3); apply container_if_true_trace; [reflexivity |].
      change 6 with (2 + S 3); eapply container_execution_sequence with (middle := container_return_flushed).
      * eapply ExecuteNext; [eapply StepPrimitive; [reflexivity |] |].
        -- eapply PrimitiveStore with (previous := 0%Z); [left; reflexivity |reflexivity |reflexivity].
        -- eapply ExecuteNext; [apply StepFlush; apply FlushWrite with (i := 1%positive);
            [left; reflexivity |intros [_ H]; apply H; reflexivity |reflexivity] |constructor].
      * change 3 with (1 + S 1); eapply container_execution_sequence; [|apply container_done_trace].
        eapply ExecuteNext; [|constructor]. eapply StepPrimitive; [reflexivity |].
        apply PrimitiveUnlock; [left; reflexivity |reflexivity |split; [left; reflexivity |intros i; reflexivity]].
Qed.

Definition container_retry_take_stack s := update (update (update s 1 0%Z) 0 1%Z) 1 1%Z.
Definition container_retry_final_stack s := update (update (update (container_retry_take_stack s) 1 0%Z) 0 0%Z) 1 1%Z.

Theorem owned_retrying_container_trace s :
  execution two_processors 52 retrying_container_program s container_initial halt
    (container_retry_final_stack s) container_final.
Proof.
  change 52 with (24 + S 27); eapply container_execution_sequence with (t := container_retry_take_stack s) (middle := container_removed).
  - change 24 with (13 + 11); apply container_retry_one_trace; [apply container_take_success_trace |reflexivity].
  - change 27 with (1 + S 25); eapply container_execution_sequence with (middle := container_private_pending).
    + eapply ExecuteNext; [|constructor]. eapply StepPrimitive; [reflexivity |].
      eapply PrimitiveStore with (previous := 7%Z); [left; reflexivity |reflexivity |reflexivity].
    + change 25 with (14 + 11); apply container_retry_one_trace; [apply container_put_success_trace |reflexivity].
Qed.

(** An empty pool exercises the failure branch, including release. This is
    an actual machine execution, not a vacuous consequence from false. *)
Definition container_retry_empty := Memory (heap_update empty_heap 1%positive 0%Z)
  (buffer_update empty_buffers 2%positive [(3%positive,17%Z)]) no_blocked.

Definition container_empty_pool_resource := container_heap_resource two_processors
  (container_full_pool 7%Z) 1%positive (or_introl eq_refl) 1%positive 0%Z.

Lemma container_retry_empty_environment s :
  owned_environment two_processors DisjointMode container_invariant s (bare_resource two_processors)
    (resource_memory two_processors container_empty_pool_resource) checkpoint_foreign_pending container_retry_empty PoolFree.
Proof.
  assert (Hsp : memory_spatial (resource_memory two_processors container_empty_pool_resource)
    (resource_memory two_processors checkpoint_foreign_pending) container_retry_empty).
  { split.
    - split; [|intros i H _; exact H]. intros loc Hpool Hforeign.
      apply container_heap_domain in Hpool; subst loc.
      destruct Hforeign as [[v H] |[i [v H]]]; [discriminate |].
      change (In (1%positive,v) (buffer_update empty_buffers 2%positive [(3%positive,17%Z)] i)) in H.
      unfold buffer_update in H; destruct (Pos.eq_dec i 2%positive); [|contradiction].
      destruct H as [E |H]; [discriminate E |contradiction].
    - split; [intros loc; reflexivity |]. split; [intros i; apply interleaves_app |intros i; cbn; unfold no_blocked; tauto]. }
  constructor.
  - exact (proj1 (proj2_sig container_empty_pool_resource)).
  - eapply raw_spatial_well_formed; [exact (proj1 (proj2_sig container_empty_pool_resource))
      |exact (proj1 (proj2_sig checkpoint_foreign_pending)) |exact Hsp].
  - exists checkpoint_foreign_pending; split; [apply repaired_empty_right |exact Hsp].
  - intros loc _ [[v H] |[i [v H]]]; discriminate || contradiction.
  - split; [intros i H; exact H |]. exists container_empty_pool_resource; split; [reflexivity |].
    left; apply container_heap_models.
Qed.

Theorem container_take_failure_trace s :
  execution two_processors 10 container_take_attempt s container_retry_empty halt
    (update (update s 0 0%Z) 1 0%Z) container_retry_empty.
Proof.
  change 10 with (1 + S 8); eapply container_execution_sequence with (t := s)
    (middle := acquire two_processors container_retry_empty 1%positive).
  - eapply ExecuteNext; [|constructor]. eapply StepPrimitive; [reflexivity |].
    apply PrimitiveLock; [left; reflexivity |reflexivity |intros i H; exact H].
  - change 8 with (1 + S 6); eapply container_execution_sequence with (t := update s 0 0%Z)
      (middle := acquire two_processors container_retry_empty 1%positive).
    + eapply ExecuteNext; [|constructor]. eapply StepPrimitive; [reflexivity |].
      apply PrimitiveLoad; [left; reflexivity |intros [_ H]; apply H; reflexivity |reflexivity].
    + change 6 with (3 + 3); apply container_if_false_trace; [reflexivity |].
      change 3 with (1 + S 1); eapply container_execution_sequence; [|apply container_done_trace].
      eapply ExecuteNext; [|constructor]. eapply StepPrimitive; [reflexivity |].
      apply PrimitiveUnlock; [left; reflexivity |reflexivity |split; [left; reflexivity |intros i; reflexivity]].
Qed.

Lemma container_execution_append active n m c s initial middle t intermediate last u final :
  execution active n c s initial middle t intermediate -> execution active m middle t intermediate last u final ->
  execution active (n + m) c s initial last u final.
Proof. intros Hfirst Hsecond; induction Hfirst; cbn; [exact Hsecond |econstructor; eauto]. Qed.

Lemma container_execution_prefix active n first second s initial last t final :
  execution active n first s initial last t final ->
  execution active n (C.Seq first second) s initial (C.Seq last second) t final.
Proof. induction 1; [constructor |econstructor; [apply StepSeq; eassumption |exact IHexecution]]. Qed.

Definition container_take_loop := C.Loop (C.Seq
  (C.Prim (C.Common (S.Assume (container_done 0%Z))) (EVal 1%Z)) container_take_attempt).

Theorem container_failed_iteration_retries s : s 1 = 0%Z ->
  execution two_processors 15 container_take_loop s container_retry_empty container_take_loop
    (update (update s 0 0%Z) 1 0%Z) container_retry_empty.
Proof.
  intros Hz; eapply ExecuteNext; [apply StepLoop |]. eapply ExecuteNext; [apply StepChoiceRight |].
  change 13 with (12 + 1); eapply container_execution_append.
  - apply container_execution_prefix; change 12 with (1 + S 10); eapply container_execution_sequence;
      [|apply container_take_failure_trace].
    eapply ExecuteNext; [|constructor]. eapply StepPrimitive; [reflexivity |].
    apply PrimitiveAssume; [left; reflexivity |change (Z.eqb (s 1) 0%Z = true); rewrite Hz; reflexivity].
  - eapply ExecuteNext; [apply StepSeqDone |constructor].
Qed.

Theorem container_two_failed_iterations s : s 1 = 0%Z ->
  execution two_processors 30 container_take_loop s container_retry_empty container_take_loop
    (update (update (update (update s 0 0%Z) 1 0%Z) 0 0%Z) 1 0%Z) container_retry_empty /\
  lock_free container_retry_empty /\ buffers container_retry_empty 2%positive = [(3%positive,17%Z)].
Proof.
  intros Hz; split.
  - change 30 with (15 + 15); eapply container_execution_append;
      apply container_failed_iteration_retries; [exact Hz |reflexivity].
  - split; [intros i H; exact H |reflexivity].
Qed.

Theorem owned_retrying_container_all_runs_safe s n last t final :
  execution two_processors n retrying_container_program s container_initial last t final ->
  ~ abort two_processors last (State t final) /\
  (terminal last -> exists local pool,
    memory_spatial pool (resource_memory two_processors local) final /\
    persistent_models two_processors t local container_foreign /\
    ((lock_free final /\ persistent_full_satisfies two_processors t pool container_invariant) \/
      exists owner, lock_held two_processors (resource_memory two_processors local) owner /\ pool = empty_memory)).
Proof.
  intros Hrun; destruct (owned_container_initial s) as [HP [HJ [Henv [Hf [Hx Hfree]]]]].
  eapply owned_derivation_adequacy; [apply container_invariant_fragment |apply acceptance_two_active
    |apply owned_retrying_container_derived |exact HP |exact HJ |exact Hfree |apply container_initial_split |exact Hrun].
Qed.

Lemma container_core_initial_environment s :
  owned_environment two_processors DisjointMode container_invariant s (bare_resource two_processors)
    (container_pool_memory 7%Z) checkpoint_foreign_pending container_initial PoolFree.
Proof.
  destruct (owned_container_initial s) as [HP [HJ [Henv [_ [_ Hfree]]]]].
  constructor.
  - exact (owned_pool_wf _ _ _ _ _ _ _ _ _ Henv).
  - exact (owned_whole_wf _ _ _ _ _ _ _ _ _ Henv).
  - exists checkpoint_foreign_pending; split; [apply repaired_empty_right |apply container_initial_split].
  - intros loc _ [[v H] |[i [v H]]]; discriminate || contradiction.
  - split; assumption.
Qed.

Theorem owned_container_completed_restores s n last t final :
  execution two_processors n container_program s container_initial last t final ->
  terminal last -> exists pool frame,
    resource_future two_processors checkpoint_foreign_pending frame /\
    memory_spatial pool (resource_memory two_processors frame) final /\
    lock_free final /\ persistent_full_satisfies two_processors t pool container_invariant.
Proof.
  intros Hrun Hterminal; eapply (proj2 (owned_emp_derivation_restores _ _
    container_invariant_fragment acceptance_two_active _ _ container_core_derived
    n s container_initial last t final (bare_resource two_processors) (container_pool_memory 7%Z)
    checkpoint_foreign_pending PoolFree (bare_resource_models _ _) (fun i H => H)
    (container_core_initial_environment s) Hrun)), Hterminal.
Qed.

Theorem owned_retrying_container_completed_restores s n last t final :
  execution two_processors n retrying_container_program s container_initial last t final ->
  terminal last -> exists pool frame,
    resource_future two_processors checkpoint_foreign_pending frame /\
    memory_spatial pool (resource_memory two_processors frame) final /\
    lock_free final /\ persistent_full_satisfies two_processors t pool container_invariant.
Proof.
  intros Hrun Hterminal; eapply (proj2 (owned_emp_derivation_restores _ _
    container_invariant_fragment acceptance_two_active _ _ container_retry_core_derived
    n s container_initial last t final (bare_resource two_processors) (container_pool_memory 7%Z)
    checkpoint_foreign_pending PoolFree (bare_resource_models _ _) (fun i H => H)
    (container_core_initial_environment s) Hrun)), Hterminal.
Qed.
