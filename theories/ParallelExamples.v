From Stdlib Require Import List ZArith.
From WMLR Require Import Expressions Languages Machine BufferRelations Separation FrameDecomposition
  OperationalSemantics ExecutionExamples Assertions AssertionSemantics PersistentAssertions Safety HeapRules
  OwnershipProtocol OwnershipHeap OwnershipExamples PrivateOwnership PrivateRules PrivateHeap PrivateCalculus
  PrivateExamples SpatialExchange ThreadProgress SharedViews ParallelOwnership.
Import ListNotations.

Definition right_cell := Memory (heap_update empty_heap 3%positive 13%Z) empty_buffers no_blocked.
Definition right_assertion := cell_assertion 3%positive 13%Z.
Definition parallel_initial := Memory
  (heap_override (shared_heap right_cell) (shared_heap private_initial)) empty_buffers no_blocked.

Lemma right_cell_models s : persistent_full_satisfies two_processors s right_cell right_assertion.
Proof.
  apply (persistent_cell_from_shape two_processors 2%positive);
    [exact two_processor_cases |right; reflexivity |intros; reflexivity |intros; reflexivity |intros i H; exact H].
Qed.

(** A concrete terminating schedule accompanies the universal safety result.
    The intermediate write is flushed, so the invariant really is broken
    inside each critical section, rather than only hidden in a buffer. *)
Definition restore_result active owner temporary initial :=
  release (flush_write
    (enqueue (flush_write (enqueue (acquire active initial owner) owner 1%positive temporary)
      owner 1%positive temporary []) owner 1%positive 7%Z) owner 1%positive 7%Z []).

Lemma restore_result_empty active owner temporary initial :
  (forall i, buffers initial i = []) -> forall i, buffers (restore_result active owner temporary initial) i = [].
Proof.
  intros Hempty i. unfold restore_result; cbn [release flush_write enqueue acquire buffers].
  unfold buffer_update. destruct (Pos.eq_dec i owner); [reflexivity |apply Hempty].
Qed.

Lemma restore_result_cell active owner temporary initial :
  shared_heap (restore_result active owner temporary initial) 1%positive = Some 7%Z.
Proof. apply heap_update_same. Qed.

Lemma parallel_initial_split : memory_spatial right_cell private_initial parallel_initial.
Proof.
  split.
  - split.
    + intros loc [[v Hv] |[i [v Hv]]] [[w Hw] |[j [w Hw]]]; try contradiction.
      cbn [right_cell shared_heap] in Hv. unfold heap_update in Hv.
      destruct (Pos.eq_dec loc 3%positive); [subst loc; discriminate |discriminate].
    + intros i H _; exact H.
  - split; [intros; reflexivity |]. split; [intros; constructor |intros i; simpl; unfold no_blocked; tauto].
Qed.

Lemma parallel_initial_environment s : private_environment two_processors 1%positive protected_seven
  Closed s retained_cell private_initial right_cell parallel_initial.
Proof.
  pose proof (private_initial_environment s) as Henv. constructor.
  - exact (private_region_ok _ _ _ _ _ _ _ _ _ Henv).
  - exact (proj1 (persistent_full_well_formed _ _ _ _ (right_cell_models s))).
  - eapply raw_spatial_well_formed;
      [exact (proj1 (persistent_full_well_formed _ _ _ _ (right_cell_models s))) |
      exact (private_whole_wf _ _ _ _ _ _ _ _ _ Henv) |apply parallel_initial_split].
  - intros i H; exact H.
  - apply parallel_initial_split.
Qed.

Definition lock_for owner := Concurrent.Prim Concurrent.Lock (EVal (Z.pos owner)).
Definition unlock_for owner := Concurrent.Prim Concurrent.Unlock (EVal (Z.pos owner)).
Definition store_for owner v := Concurrent.Prim
  (Concurrent.Common (Sequential.Store (EVal 1%Z) (EVal v))) (EVal (Z.pos owner)).
Definition fence_for owner := Concurrent.Prim (Concurrent.Common Sequential.Fence) (EVal (Z.pos owner)).
Definition restore_for owner temporary := Concurrent.Seq (lock_for owner)
  (Concurrent.Seq (store_for owner temporary)
    (Concurrent.Seq (fence_for owner) (Concurrent.Seq (store_for owner 7%Z) (unlock_for owner)))).

Lemma restore_for_memory_only owner temporary : memory_only (restore_for owner temporary).
Proof. intros x; simpl; tauto. Qed.

Theorem restore_for_derivable active owner temporary p : private_derivation active owner protected_seven
  Closed p (restore_for owner temporary) Closed p.
Proof.
  unfold restore_for. eapply PrivateSequence; [apply PrivateAcquire |].
  eapply PrivateSequence; [apply PrivateStore |]. eapply PrivateSequence; [apply PrivateFence |].
  eapply PrivateSequence; [apply PrivateStore |]. apply PrivateReleaseBuffered; reflexivity.
Qed.

Definition competing_restorers := Concurrent.Parallel (restore_for 1%positive 9%Z) (restore_for 2%positive 5%Z).

Theorem competing_restorers_no_abort s n last t final :
  execution two_processors n competing_restorers s parallel_initial last t final ->
  ~ abort two_processors last (State t final).
Proof.
  intros Hrun. eapply (proj1 (private_parallel_memory_only_rule two_processors 1%positive 2%positive
    protected_seven retained_assertion retained_assertion right_assertion right_assertion
    _ _ _ _ _ _ _ ltac:(discriminate) (restore_for_memory_only _ _) (restore_for_memory_only _ _)
    (restore_for_derivable _ _ _ _) (restore_for_derivable _ _ _ _)
    (parallel_initial_environment s) (retained_cell_models s) (right_cell_models s) _ _ _ _ Hrun)).
Qed.

Theorem competing_restorers_all_terminating_runs s n last t final :
  execution two_processors n competing_restorers s parallel_initial last t final -> terminal last ->
  lock_free final /\ shared_heap final 1%positive = Some 7%Z /\
    shared_heap final 2%positive = Some 11%Z /\ shared_heap final 3%positive = Some 13%Z.
Proof.
  intros Hrun Hlast.
  destruct (proj2 (private_parallel_memory_only_rule two_processors 1%positive 2%positive
    protected_seven retained_assertion retained_assertion right_assertion right_assertion
    _ _ _ _ _ _ _ ltac:(discriminate) (restore_for_memory_only _ _) (restore_for_memory_only _ _)
    (restore_for_derivable _ _ _ _) (restore_for_derivable _ _ _ _)
    (parallel_initial_environment s) (retained_cell_models s) (right_cell_models s) _ _ _ _ Hrun) Hlast)
    as [pool [combined [Hpool [HJ [HQ Hfree]]]]].
  destruct (full_spatial_elim _ _ _ _ _ HQ) as [a [b [Hab [Ha Hb]]]].
  destruct (persistent_cell_shape _ _ _ _ _ HJ) as [Hshared _].
  destruct (persistent_cell_shape _ _ _ _ _ Ha) as [Hleft _].
  destruct (persistent_cell_shape _ _ _ _ _ Hb) as [Hright _].
  split; [exact Hfree |]. split.
  - eapply spatial_heap_value; [apply memory_spatial_comm, Hpool |exact Hshared].
  - split; eapply spatial_heap_value; [exact Hpool | |exact Hpool |].
    + eapply spatial_heap_value; [apply memory_spatial_comm, Hab |exact Hleft].
    + eapply spatial_heap_value; eassumption.
Qed.

Theorem restore_for_trace active owner temporary s initial :
  active owner -> lock_free initial -> (forall i, buffers initial i = []) ->
  shared_heap initial 1%positive = Some 7%Z ->
  execution active 11 (restore_for owner temporary) s initial halt s (restore_result active owner temporary initial).
Proof.
  intros Hi Hfree Hempty Hcell.
  set (locked := acquire active initial owner).
  set (pending := enqueue locked owner 1%positive temporary).
  set (flushed := flush_write pending owner 1%positive temporary []).
  set (pending' := enqueue flushed owner 1%positive 7%Z).
  set (flushed' := flush_write pending' owner 1%positive 7%Z []).
  unfold restore_for. eapply ExecuteNext with
    (next := Concurrent.Seq halt (Concurrent.Seq (store_for owner temporary)
      (Concurrent.Seq (fence_for owner) (Concurrent.Seq (store_for owner 7%Z) (unlock_for owner)))))
    (middle := locked).
  - apply StepSeq. eapply StepPrimitive; [reflexivity |]. apply PrimitiveLock; [exact Hi |apply Hempty |exact Hfree].
  - eapply ExecuteNext; [apply StepSeqDone |]. eapply ExecuteNext with
      (next := Concurrent.Seq halt (Concurrent.Seq (fence_for owner)
        (Concurrent.Seq (store_for owner 7%Z) (unlock_for owner)))) (middle := pending).
    + apply StepSeq. eapply StepPrimitive; [reflexivity |]. eapply PrimitiveStore with (previous := 7%Z);
        [exact Hi |reflexivity |].
      unfold local_read; cbn [locked acquire buffers shared_heap]; rewrite Hempty; exact Hcell.
    + eapply ExecuteNext; [apply StepSeqDone |]. eapply ExecuteNext with (middle := flushed).
      * apply StepFlush. eapply FlushWrite with (i := owner);
          [exact Hi |intros [_ H]; apply H; reflexivity |].
        cbn [pending enqueue locked acquire buffers]; rewrite buffer_update_same, Hempty; reflexivity.
      * eapply ExecuteNext with (next := Concurrent.Seq halt (Concurrent.Seq (store_for owner 7%Z) (unlock_for owner))).
        -- apply StepSeq. eapply StepPrimitive; [reflexivity |]. apply PrimitiveFence; [exact Hi |].
           apply buffer_update_same.
        -- eapply ExecuteNext; [apply StepSeqDone |]. eapply ExecuteNext with
             (next := Concurrent.Seq halt (unlock_for owner)) (middle := pending').
           ++ apply StepSeq. eapply StepPrimitive; [reflexivity |]. eapply PrimitiveStore with (previous := temporary);
                [exact Hi |reflexivity |].
              unfold local_read; cbn [flushed flush_write buffers shared_heap]; rewrite buffer_update_same.
              apply heap_update_same.
           ++ eapply ExecuteNext; [apply StepSeqDone |]. eapply ExecuteNext with (middle := flushed').
              ** apply StepFlush. eapply FlushWrite with (i := owner);
                   [exact Hi |intros [_ H]; apply H; reflexivity |].
                 cbn [pending' enqueue flushed flush_write buffers]; rewrite !buffer_update_same; reflexivity.
              ** eapply ExecuteNext; [|constructor]. eapply StepPrimitive; [reflexivity |]. apply PrimitiveUnlock;
                   [exact Hi |apply buffer_update_same |split; [exact Hi |intros i; reflexivity]].
Qed.

Lemma execution_parallel_left active n first second s initial last t final :
  execution active n first s initial last t final ->
  execution active n (Concurrent.Parallel first second) s initial (Concurrent.Parallel last second) t final.
Proof. induction 1; [constructor |econstructor; [apply StepParallelLeft; eassumption |exact IHexecution]]. Qed.

Lemma execution_parallel_right active n first second s initial last t final :
  execution active n second s initial last t final ->
  execution active n (Concurrent.Parallel first second) s initial (Concurrent.Parallel first last) t final.
Proof. induction 1; [constructor |econstructor; [apply StepParallelRight; eassumption |exact IHexecution]]. Qed.

Definition left_then_right_result := restore_result two_processors 2%positive 5%Z
  (restore_result two_processors 1%positive 9%Z parallel_initial).
Definition right_then_left_result := restore_result two_processors 1%positive 9%Z
  (restore_result two_processors 2%positive 5%Z parallel_initial).

Example competing_restorers_left_first : execution two_processors 23 competing_restorers protocol_stack parallel_initial
  halt protocol_stack left_then_right_result.
Proof.
  change (execution two_processors (11 + 12) competing_restorers protocol_stack parallel_initial
    halt protocol_stack left_then_right_result). eapply execution_append.
  - apply execution_parallel_left, restore_for_trace;
      [left; reflexivity |intros i H; exact H |intros; reflexivity |reflexivity].
  - eapply ExecuteNext; [apply StepParallelLeftDone |]. apply restore_for_trace;
      [right; reflexivity |intros i H; exact H |apply restore_result_empty; intros; reflexivity |apply restore_result_cell].
Qed.

Example competing_restorers_right_first : execution two_processors 23 competing_restorers protocol_stack parallel_initial
  halt protocol_stack right_then_left_result.
Proof.
  change (execution two_processors (11 + 12) competing_restorers protocol_stack parallel_initial
    halt protocol_stack right_then_left_result). eapply execution_append.
  - apply execution_parallel_right, restore_for_trace;
      [right; reflexivity |intros i H; exact H |intros; reflexivity |reflexivity].
  - eapply ExecuteNext; [apply StepParallelRightDone |]. apply restore_for_trace;
      [left; reflexivity |intros i H; exact H |apply restore_result_empty; intros; reflexivity |apply restore_result_cell].
Qed.

Definition contended_memory := flush_write
  (enqueue (acquire two_processors parallel_initial 1%positive) 1%positive 1%positive 9%Z)
  1%positive 1%positive 9%Z [].
Definition contended_left := Concurrent.Seq (fence_for 1%positive)
  (Concurrent.Seq (store_for 1%positive 7%Z) (unlock_for 1%positive)).

Example competing_restorers_contended : execution two_processors 5 competing_restorers protocol_stack parallel_initial
  (Concurrent.Parallel contended_left (restore_for 2%positive 5%Z)) protocol_stack contended_memory.
Proof.
  apply execution_parallel_left. unfold restore_for.
  eapply ExecuteNext with (next := Concurrent.Seq halt (Concurrent.Seq (store_for 1%positive 9%Z) contended_left))
    (middle := acquire two_processors parallel_initial 1%positive).
  - apply StepSeq. eapply StepPrimitive; [reflexivity |]. apply PrimitiveLock;
      [left; reflexivity |reflexivity |intros i H; exact H].
  - eapply ExecuteNext; [apply StepSeqDone |].
    eapply ExecuteNext with (next := Concurrent.Seq halt contended_left)
      (middle := enqueue (acquire two_processors parallel_initial 1%positive) 1%positive 1%positive 9%Z).
    + apply StepSeq. eapply StepPrimitive; [reflexivity |]. eapply PrimitiveStore with (previous := 7%Z);
        [left; reflexivity |reflexivity |reflexivity].
    + eapply ExecuteNext; [apply StepSeqDone |]. eapply ExecuteNext; [|constructor].
      apply StepFlush. eapply FlushWrite with (i := 1%positive);
        [left; reflexivity |intros [_ H]; apply H; reflexivity |reflexivity].
Qed.

Example contended_value_and_blocking : shared_heap contended_memory 1%positive = Some 9%Z /\
  blocked contended_memory 2%positive.
Proof. split; [reflexivity |split; [right; reflexivity |discriminate]]. Qed.

Example contended_waiter_cannot_acquire s final :
  ~ primitive_step two_processors Concurrent.Lock 2%positive (State s contended_memory) final.
Proof.
  intros Hstep; inversion Hstep; subst.
  match goal with H : lock_free contended_memory |- _ =>
    exact (H 2%positive (proj2 contended_value_and_blocking)) end.
Qed.
