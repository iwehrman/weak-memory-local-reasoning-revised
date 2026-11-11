From Stdlib Require Import List ZArith.
From WMLR Require Import Expressions Languages Machine BufferRelations Separation FrameDecomposition
  OperationalSemantics ExecutionExamples Assertions AssertionSemantics PersistentAssertions Safety HeapRules
  OwnershipProtocol OwnershipRules OwnershipHeap OwnershipCalculus.
Import ListNotations.

Definition protocol_stack : stack := fun _ => 0%Z.

Definition protocol_cell v := Memory (heap_update empty_heap 1%positive v) empty_buffers no_blocked.

Lemma two_processor_cases i : ~ two_processors i \/ two_processors i.
Proof.
  unfold two_processors. destruct (Pos.eq_dec i 1%positive), (Pos.eq_dec i 2%positive); tauto.
Qed.

Lemma protocol_cell_models s v :
  persistent_full_satisfies two_processors s (protocol_cell v) (cell_assertion 1%positive v).
Proof.
  apply (persistent_cell_from_shape two_processors 1%positive).
  - exact two_processor_cases.
  - left; reflexivity.
  - intros; reflexivity.
  - intros; reflexivity.
  - intros i H; exact H.
Qed.

Definition owner_acquire := Concurrent.Prim Concurrent.Lock (EVal 1%Z).
Definition owner_release := Concurrent.Prim Concurrent.Unlock (EVal 1%Z).
Definition owner_store v := Concurrent.Prim (Concurrent.Common (Sequential.Store (EVal 1%Z) (EVal v))) (EVal 1%Z).
Definition owner_fence := Concurrent.Prim (Concurrent.Common Sequential.Fence) (EVal 1%Z).
Definition restore_tail := Concurrent.Seq owner_fence owner_release.
Definition restore_write := Concurrent.Seq (owner_store 7%Z) restore_tail.
Definition restore_middle := Concurrent.Seq owner_fence restore_write.
Definition restore_body := Concurrent.Seq (owner_store 9%Z) restore_middle.
Definition restore_program := Concurrent.Seq owner_acquire restore_body.
Definition protected_seven := cell_assertion 1%positive 7%Z.

Theorem restore_program_derivable : ownership_derivation two_processors 1%positive protected_seven
  Closed A.Emp restore_program Closed A.Emp.
Proof.
  unfold restore_program, restore_body, restore_middle, restore_write, restore_tail.
  eapply OwnSequence; [apply OwnAcquire |].
  eapply OwnSequence; [apply OwnStore |].
  eapply OwnSequence; [apply OwnFence |].
  eapply OwnSequence; [apply OwnStore |].
  eapply OwnSequence; [apply OwnFence |apply OwnRelease].
Qed.

Definition restore_using_unlock_fence := Concurrent.Seq owner_acquire
  (Concurrent.Seq (owner_store 9%Z) (Concurrent.Seq owner_fence (Concurrent.Seq (owner_store 7%Z) owner_release))).

Theorem restore_using_unlock_fence_derivable : ownership_derivation two_processors 1%positive protected_seven
  Closed A.Emp restore_using_unlock_fence Closed A.Emp.
Proof.
  unfold restore_using_unlock_fence.
  eapply OwnSequence; [apply OwnAcquire |].
  eapply OwnSequence; [apply OwnStore |].
  eapply OwnSequence; [apply OwnFence |].
  eapply OwnSequence; [apply OwnStore |]. apply OwnReleaseBuffered; reflexivity.
Qed.

Lemma protocol_cell_initial_environment s : protocol_environment two_processors 1%positive protected_seven
  Closed s (protocol_cell 7%Z) empty_memory (protocol_cell 7%Z).
Proof.
  constructor.
  - split; [exact (proj1 (persistent_full_well_formed _ _ _ _ (protocol_cell_models s 7%Z))) |].
    split; [intros i H; exact H |apply protocol_cell_models].
  - exact (proj1 (empty_generalized_well_formed two_processors)).
  - exact (proj1 (persistent_full_well_formed _ _ _ _ (protocol_cell_models s 7%Z))).
  - intros i H; exact H.
  - exact (proj1 (spatial_empty_left (Generalized (protocol_cell 7%Z) two_processors))).
Qed.

(** This covers every ordinary execution and every spatial external frame,
    not just the concrete schedule exhibited below. *)
Theorem restore_program_no_abort s frame whole n last t final :
  protocol_environment two_processors 1%positive protected_seven Closed s (protocol_cell 7%Z) frame whole ->
  execution two_processors n restore_program s whole last t final -> ~ abort two_processors last (State t final).
Proof.
  intros Henv Hrun. eapply protocol_execution_no_abort; [exact Hrun | |exact Henv].
  apply (ownership_calculus_sound _ _ _ _ _ _ _ _ restore_program_derivable);
    [exact (protocol_region_ok _ _ _ _ _ _ _ _ Henv) |apply protocol_empty_satisfies].
Qed.

Theorem restore_program_all_terminating_runs s frame whole n last t final :
  protocol_environment two_processors 1%positive protected_seven Closed s (protocol_cell 7%Z) frame whole ->
  execution two_processors n restore_program s whole last t final -> terminal last ->
  lock_free final /\ shared_heap final 1%positive = Some 7%Z.
Proof.
  intros Henv Hrun Hlast.
  assert (Hsafe : protocol_safe two_processors 1%positive protected_seven (S n)
    restore_program s Closed (protocol_cell 7%Z) Closed A.Emp).
  { apply (ownership_calculus_sound _ _ _ _ _ _ _ _ restore_program_derivable);
      [exact (protocol_region_ok _ _ _ _ _ _ _ _ Henv) |apply protocol_empty_satisfies]. }
  destruct (protocol_execution_closed_post _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hrun Hsafe Henv Hlast)
    as [pool [frame' [Hsep [_ [Hfree [Hinv _]]]]]].
  split; [exact Hfree |]. destruct (persistent_cell_shape _ _ _ _ _ Hinv) as [Hcell _].
  rewrite (proj1 (proj2 Hsep)); unfold heap_override; rewrite Hcell; reflexivity.
Qed.

Definition held_seven := acquire two_processors (protocol_cell 7%Z) 1%positive.
Definition pending_nine := enqueue held_seven 1%positive 1%positive 9%Z.
Definition flushed_nine := flush_write pending_nine 1%positive 1%positive 9%Z [].
Definition pending_seven := enqueue flushed_nine 1%positive 1%positive 7%Z.
Definition flushed_seven := flush_write pending_seven 1%positive 1%positive 7%Z [].
Definition restored_release := release flushed_seven.

Example restore_program_trace : execution two_processors 13 restore_program protocol_stack (protocol_cell 7%Z)
  halt protocol_stack restored_release.
Proof.
  unfold restore_program. eapply ExecuteNext with (next := Concurrent.Seq halt restore_body) (middle := held_seven).
  - apply StepSeq. eapply StepPrimitive; [reflexivity |]. apply PrimitiveLock;
      [left; reflexivity |reflexivity |intros i H; exact H].
  - eapply ExecuteNext; [apply StepSeqDone |]. unfold restore_body.
    eapply ExecuteNext with (next := Concurrent.Seq halt restore_middle) (middle := pending_nine).
    + apply StepSeq. eapply StepPrimitive; [reflexivity |]. eapply PrimitiveStore with (previous := 7%Z);
        [left; reflexivity |reflexivity |reflexivity].
    + eapply ExecuteNext; [apply StepSeqDone |].
      eapply ExecuteNext with (middle := flushed_nine).
      * apply StepFlush. eapply FlushWrite with (i := 1%positive);
          [left; reflexivity |intros [_ H]; apply H; reflexivity |reflexivity].
      * unfold restore_middle. eapply ExecuteNext with (next := Concurrent.Seq halt restore_write).
        -- apply StepSeq. eapply StepPrimitive; [reflexivity |]. apply PrimitiveFence;
             [left; reflexivity |reflexivity].
        -- eapply ExecuteNext; [apply StepSeqDone |]. unfold restore_write.
           eapply ExecuteNext with (next := Concurrent.Seq halt restore_tail) (middle := pending_seven).
           ++ apply StepSeq. eapply StepPrimitive; [reflexivity |]. eapply PrimitiveStore with (previous := 9%Z);
                [left; reflexivity |reflexivity |reflexivity].
           ++ eapply ExecuteNext; [apply StepSeqDone |].
              eapply ExecuteNext with (middle := flushed_seven).
              ** apply StepFlush. eapply FlushWrite with (i := 1%positive);
                   [left; reflexivity |intros [_ H]; apply H; reflexivity |reflexivity].
              ** unfold restore_tail. eapply ExecuteNext with (next := Concurrent.Seq halt owner_release).
                 --- apply StepSeq. eapply StepPrimitive; [reflexivity |]. apply PrimitiveFence;
                       [left; reflexivity |reflexivity].
                 --- eapply ExecuteNext; [apply StepSeqDone |]. eapply ExecuteNext.
                     +++ eapply StepPrimitive; [reflexivity |]. apply PrimitiveUnlock;
                           [left; reflexivity |reflexivity |split; [left; reflexivity |intros i; reflexivity]].
                     +++ constructor.
Qed.

Example intermediate_invariant_broken s :
  ~ persistent_full_satisfies two_processors s (release flushed_nine) protected_seven.
Proof.
  intros H. destruct (persistent_cell_shape _ _ _ _ _ H) as [Hcell _]. discriminate.
Qed.

Example pending_restore_then_unlock : execution two_processors 2 owner_release protocol_stack pending_seven
  halt protocol_stack restored_release.
Proof.
  eapply ExecuteNext with (middle := flushed_seven).
  - apply StepFlush. eapply FlushWrite with (i := 1%positive);
      [left; reflexivity |intros [_ H]; apply H; reflexivity |reflexivity].
  - eapply ExecuteNext; [|constructor]. eapply StepPrimitive; [reflexivity |]. apply PrimitiveUnlock;
      [left; reflexivity |reflexivity |split; [left; reflexivity |intros i; reflexivity]].
Qed.

(** The repaired semantics rejects release with a wrong protected value,
    even though the machine instruction itself is enabled. *)
Theorem unrestored_release_invalid :
  ~ protocol_valid two_processors 1%positive protected_seven Open
    (owned_assertion 1%positive (cell_assertion 1%positive 9%Z)) owner_release Closed A.Emp.
Proof.
  intros Hvalid.
  set (region := acquire two_processors (protocol_cell 9%Z) 1%positive).
  assert (Hr : protocol_region two_processors 1%positive protected_seven Open protocol_stack region).
  { split.
    - apply acquire_well_formed. exact (proj1 (persistent_full_well_formed _ _ _ _ (protocol_cell_models protocol_stack 9%Z))).
    - split; [left; reflexivity |intros i; reflexivity]. }
  assert (Henv : protocol_environment two_processors 1%positive protected_seven Open protocol_stack region empty_memory region).
  { constructor; [exact Hr |exact (proj1 (empty_generalized_well_formed two_processors)) |exact (proj1 Hr) | |].
    - intros i H; exact H.
    - exact (proj1 (spatial_empty_left (Generalized region two_processors))). }
  assert (Hp : protocol_assertion two_processors Open protocol_stack region
    (owned_assertion 1%positive (cell_assertion 1%positive 9%Z))).
  { apply acquire_exposes_invariant;
      [left; reflexivity |intros i H; exact H |apply protocol_cell_models]. }
  assert (Hrun : execution two_processors 1 owner_release protocol_stack region halt protocol_stack (release region)).
  { eapply ExecuteNext; [|constructor]. eapply StepPrimitive; [reflexivity |]. apply PrimitiveUnlock;
      [left; reflexivity |reflexivity |exact (proj2 Hr)]. }
  destruct (protocol_execution_closed_post _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hrun
    (Hvalid _ _ Hr Hp 2) Henv ltac:(eexists; reflexivity))
    as [pool [frame [Hsep [_ [_ [Hinv _]]]]]].
  destruct (persistent_cell_shape _ _ _ _ _ Hinv) as [Hcell _].
  pose proof (proj1 (proj2 Hsep) 1%positive) as Hheap.
  unfold heap_override in Hheap; rewrite Hcell in Hheap. discriminate.
Qed.
