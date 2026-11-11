From Stdlib Require Import List ZArith.
From WMLR Require Import Expressions Languages Machine BufferRelations Separation FrameDecomposition
  OperationalSemantics ExecutionExamples Assertions AssertionSemantics PersistentAssertions Safety HeapRules
  OwnershipProtocol OwnershipHeap OwnershipExamples PrivateOwnership PrivateRules PrivateHeap PrivateCalculus.
Import ListNotations.

Definition retained_cell := Memory (heap_update empty_heap 2%positive 11%Z) empty_buffers no_blocked.
Definition retained_assertion := cell_assertion 2%positive 11%Z.
Definition private_initial := Memory
  (heap_override (shared_heap (protocol_cell 7%Z)) (shared_heap retained_cell)) empty_buffers no_blocked.

Lemma retained_cell_models s : persistent_full_satisfies two_processors s retained_cell retained_assertion.
Proof.
  apply (persistent_cell_from_shape two_processors 1%positive);
    [exact two_processor_cases |left; reflexivity |intros; reflexivity |intros; reflexivity |intros i H; exact H].
Qed.

Lemma private_initial_split : memory_spatial (protocol_cell 7%Z) retained_cell private_initial.
Proof.
  split.
  - split.
    + intros loc [[v Hv] |[i [v Hv]]] [[w Hw] |[j [w Hw]]]; try contradiction.
      cbn [protocol_cell retained_cell shared_heap] in Hv, Hw. unfold heap_update in Hv, Hw.
      destruct (Pos.eq_dec loc 1%positive); [subst loc; discriminate |discriminate].
    + intros i H _; exact H.
  - split; [intros; reflexivity |]. split; [intros; constructor |intros i; simpl; unfold no_blocked; tauto].
Qed.

Lemma private_initial_environment s : private_environment two_processors 1%positive protected_seven
  Closed s retained_cell private_initial empty_memory private_initial.
Proof.
  assert (Hboth : persistent_full_satisfies two_processors s private_initial (A.Spatial protected_seven retained_assertion)).
  { eapply full_spatial_intro; [apply private_initial_split |apply protocol_cell_models |apply retained_cell_models]. }
  pose proof (proj1 (persistent_full_well_formed _ _ _ _ Hboth)) as Hwf.
  constructor.
  - split; [exact (proj1 (persistent_full_well_formed _ _ _ _ (retained_cell_models s))) |].
    split; [exact Hwf |]. split; [intros i H; exact H |].
    exists (protocol_cell 7%Z); split; [apply protocol_cell_models |apply private_initial_split].
  - exact (proj1 (empty_generalized_well_formed two_processors)).
  - exact Hwf.
  - intros i H; exact H.
  - exact (proj1 (spatial_empty_left (Generalized private_initial two_processors))).
Qed.

Definition read_private := Concurrent.Prim (Concurrent.Common (Sequential.Load 0 (EVal 2%Z))) (EVal 1%Z).
Definition private_restore_program := Concurrent.Seq restore_using_unlock_fence read_private.
Definition private_final_assertion := A.And retained_assertion (A.Pure (BEq (EVar 0) (EVal 11%Z))).

Theorem private_restore_derivable : private_derivation two_processors 1%positive protected_seven
  Closed retained_assertion private_restore_program Closed private_final_assertion.
Proof.
  unfold private_restore_program. eapply PrivateSequence.
  - unfold restore_using_unlock_fence. eapply PrivateSequence; [apply PrivateAcquire |].
    eapply PrivateSequence; [apply PrivateStore |].
    eapply PrivateSequence; [apply PrivateFence |].
    eapply PrivateSequence; [apply PrivateStore |]. apply PrivateReleaseBuffered; reflexivity.
  - apply PrivateLoad, cell_assertion_fresh.
Qed.

Theorem private_restore_no_abort s frame whole n last t final :
  private_environment two_processors 1%positive protected_seven Closed s retained_cell private_initial frame whole ->
  execution two_processors n private_restore_program s whole last t final -> ~ abort two_processors last (State t final).
Proof.
  intros Henv Hrun. eapply private_execution_no_abort; [exact Hrun | |exact Henv].
  apply (private_calculus_sound _ _ _ _ _ _ _ _ private_restore_derivable);
    [exact (private_region_ok _ _ _ _ _ _ _ _ _ Henv) |apply retained_cell_models].
Qed.

Lemma spatial_heap_value a b out loc v : memory_spatial a b out -> shared_heap b loc = Some v ->
  shared_heap out loc = Some v.
Proof. intros [_ [Hheap _]] Hcell; rewrite Hheap; unfold heap_override; rewrite Hcell; reflexivity. Qed.

Theorem private_restore_all_terminating_runs s frame whole n last t final :
  private_environment two_processors 1%positive protected_seven Closed s retained_cell private_initial frame whole ->
  execution two_processors n private_restore_program s whole last t final -> terminal last ->
  lock_free final /\ shared_heap final 1%positive = Some 7%Z /\
    shared_heap final 2%positive = Some 11%Z /\ t 0 = 11%Z.
Proof.
  intros Henv Hrun Hlast.
  assert (Hsafe : private_safe two_processors 1%positive protected_seven (S n)
    private_restore_program s Closed retained_cell private_initial Closed private_final_assertion).
  { apply (private_calculus_sound _ _ _ _ _ _ _ _ private_restore_derivable);
      [exact (private_region_ok _ _ _ _ _ _ _ _ _ Henv) |apply retained_cell_models]. }
  destruct (private_execution_closed_post _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hrun Hsafe Henv Hlast)
    as [local [pool [region [frame' [Hinner [Houter [_ [Hfree [HJ HQ]]]]]]]]].
  destruct (persistent_cell_shape _ _ _ _ _ HJ) as [Hshared _].
  destruct HQ as [r [Er [Hprivate Hvalue]]].
  assert (HQ : persistent_full_satisfies two_processors t local retained_assertion) by (exists r; auto).
  destruct (persistent_cell_shape _ _ _ _ _ HQ) as [Hretained _].
  split; [exact Hfree |]. split.
  - eapply spatial_heap_value; [exact Houter |]. eapply spatial_heap_value;
      [apply memory_spatial_comm, Hinner |exact Hshared].
  - split.
    + eapply spatial_heap_value; [exact Houter |]. eapply spatial_heap_value; eassumption.
    + change (Z.eqb (t 0) 11%Z = true) in Hvalue; apply Z.eqb_eq, Hvalue.
Qed.

Lemma execution_append active n m c s initial middle t intermediate last u final :
  execution active n c s initial middle t intermediate -> execution active m middle t intermediate last u final ->
  execution active (n + m) c s initial last u final.
Proof. intros Hfirst Hsecond; induction Hfirst; simpl; [exact Hsecond |econstructor; eauto]. Qed.

Lemma execution_sequence_prefix active n first second s initial last t final :
  execution active n first s initial last t final ->
  execution active n (Concurrent.Seq first second) s initial (Concurrent.Seq last second) t final.
Proof. induction 1; [constructor |econstructor; [apply StepSeq; eassumption |exact IHexecution]]. Qed.

Definition private_held := acquire two_processors private_initial 1%positive.
Definition private_pending_nine := enqueue private_held 1%positive 1%positive 9%Z.
Definition private_flushed_nine := flush_write private_pending_nine 1%positive 1%positive 9%Z [].
Definition private_pending_seven := enqueue private_flushed_nine 1%positive 1%positive 7%Z.
Definition private_flushed_seven := flush_write private_pending_seven 1%positive 1%positive 7%Z [].
Definition private_released := release private_flushed_seven.

Example private_critical_trace : execution two_processors 11 restore_using_unlock_fence protocol_stack private_initial
  halt protocol_stack private_released.
Proof.
  unfold restore_using_unlock_fence. eapply ExecuteNext with
    (next := Concurrent.Seq halt (Concurrent.Seq (owner_store 9%Z)
      (Concurrent.Seq owner_fence (Concurrent.Seq (owner_store 7%Z) owner_release)))) (middle := private_held).
  - apply StepSeq. eapply StepPrimitive; [reflexivity |]. apply PrimitiveLock;
      [left; reflexivity |reflexivity |intros i H; exact H].
  - eapply ExecuteNext; [apply StepSeqDone |]. eapply ExecuteNext with
      (next := Concurrent.Seq halt (Concurrent.Seq owner_fence (Concurrent.Seq (owner_store 7%Z) owner_release)))
      (middle := private_pending_nine).
    + apply StepSeq. eapply StepPrimitive; [reflexivity |]. eapply PrimitiveStore with (previous := 7%Z);
        [left; reflexivity |reflexivity |reflexivity].
    + eapply ExecuteNext; [apply StepSeqDone |]. eapply ExecuteNext with (middle := private_flushed_nine).
      * apply StepFlush. eapply FlushWrite with (i := 1%positive);
          [left; reflexivity |intros [_ H]; apply H; reflexivity |reflexivity].
      * eapply ExecuteNext with (next := Concurrent.Seq halt (Concurrent.Seq (owner_store 7%Z) owner_release)).
        -- apply StepSeq. eapply StepPrimitive; [reflexivity |]. apply PrimitiveFence; [left; reflexivity |reflexivity].
        -- eapply ExecuteNext; [apply StepSeqDone |]. eapply ExecuteNext with
             (next := Concurrent.Seq halt owner_release) (middle := private_pending_seven).
           ++ apply StepSeq. eapply StepPrimitive; [reflexivity |]. eapply PrimitiveStore with (previous := 9%Z);
                [left; reflexivity |reflexivity |reflexivity].
           ++ eapply ExecuteNext; [apply StepSeqDone |]. eapply ExecuteNext with (middle := private_flushed_seven).
              ** apply StepFlush. eapply FlushWrite with (i := 1%positive);
                   [left; reflexivity |intros [_ H]; apply H; reflexivity |reflexivity].
              ** eapply ExecuteNext; [|constructor]. eapply StepPrimitive; [reflexivity |]. apply PrimitiveUnlock;
                   [left; reflexivity |reflexivity |split; [left; reflexivity |intros i; reflexivity]].
Qed.

Example private_restore_trace : execution two_processors 13 private_restore_program protocol_stack private_initial
  halt (update protocol_stack 0 11%Z) private_released.
Proof.
  change (execution two_processors (11 + 2) private_restore_program protocol_stack private_initial
    halt (update protocol_stack 0 11%Z) private_released).
  eapply execution_append.
  - apply execution_sequence_prefix, private_critical_trace.
  - eapply ExecuteNext; [apply StepSeqDone |]. eapply ExecuteNext; [|constructor].
    eapply StepPrimitive; [reflexivity |]. apply PrimitiveLoad;
      [left; reflexivity |intros H; exact H |reflexivity].
Qed.

Theorem private_alias_rejected s region :
  ~ private_region two_processors 1%positive protected_seven Closed s (protocol_cell 11%Z) region.
Proof.
  intros [_ [_ [_ [pool [HJ [[Hd _] _]]]]]].
  destruct (persistent_cell_shape _ _ _ _ _ HJ) as [Hheap _].
  apply (Hd 1%positive); left; [exists 7%Z; exact Hheap |exists 11%Z; reflexivity].
Qed.
