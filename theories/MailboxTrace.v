From Stdlib Require Import List ZArith Lia.
From WMLR Require Import Expressions Languages Machine BufferRelations Separation OperationalSemantics
  Assertions AssertionSemantics PersistentAssertions Safety TemporalSafety PrivateExamples ParallelExamples OwnedContainerTrace CellFamilies RegionRules NamedLockSyntax
  NamedLockTrace MailboxSyntax MailboxAdequacy.
Import ListNotations.

Lemma mailbox_sequence_to active n m first second s initial t middle last u final :
  execution active n first s initial halt t middle -> execution active m second t middle last u final ->
  execution active (n + S m) (C.Seq first second) s initial last u final.
Proof.
  intros Hfirst Hsecond; remember halt as terminal eqn:E in Hfirst.
  induction Hfirst; subst; cbn; [eapply ExecuteNext; [apply StepSeqDone |exact Hsecond] |].
  eapply ExecuteNext; [apply StepSeq; exact H |apply IHHfirst; assumption || reflexivity].
Qed.

Definition mb_items := [(3%positive,7%Z);(4%positive,9%Z)].
Definition mb_initial := mailbox_initial mb_items 5%positive.
Definition mb_fill_first := enqueue mb_initial 1%positive 3%positive 7%Z.
Definition mb_filled := enqueue mb_fill_first 1%positive 4%positive 9%Z.
Definition mb_flush_first := flush_write mb_filled 1%positive 3%positive 7%Z [(4%positive,9%Z)].
Definition mb_flushed := flush_write mb_flush_first 1%positive 4%positive 9%Z [].
Definition mb_producer_acquired := nl_write_final mailbox_active 1%positive 1%positive 1%Z mb_flushed.
Definition mb_publish_pending := enqueue mb_producer_acquired 1%positive 2%positive 1%Z.
Definition mb_publish_flushed := flush_write mb_publish_pending 1%positive 2%positive 1%Z [].
Definition mb_producer_final := nl_write_final mailbox_active 1%positive 1%positive 0%Z mb_publish_flushed.
Definition mb_consumer_acquired := nl_write_final mailbox_active 2%positive 1%positive 1%Z mb_producer_final.
Definition mb_take_pending := enqueue mb_consumer_acquired 2%positive 2%positive 0%Z.
Definition mb_take_flushed := flush_write mb_take_pending 2%positive 2%positive 0%Z [].
Definition mb_final := nl_write_final mailbox_active 2%positive 1%positive 0%Z mb_take_flushed.
Definition mb_acquired_stack x s := update (update s x 1%Z) x 0%Z.
Definition mb_taken_stack s := update (update (mb_acquired_stack 1 s) 1 1%Z) 1 0%Z.
Definition mb_consumer_stack s := update (update (mb_taken_stack (update s 1 1%Z)) 2 7%Z) 2 9%Z.

Lemma mb_fill_trace s : execution mailbox_active 4 (fill_region 1%positive mb_items) s mb_initial halt s mb_filled.
Proof.
  eapply ExecuteNext.
  - apply StepSeq; eapply StepPrimitive; [reflexivity |].
    eapply PrimitiveStore with (previous := 0%Z); [left; reflexivity |reflexivity |reflexivity].
  - eapply ExecuteNext; [apply StepSeqDone |]. eapply ExecuteNext.
    + apply StepSeq; eapply StepPrimitive; [reflexivity |].
      eapply PrimitiveStore with (previous := 0%Z); [left; reflexivity |reflexivity |reflexivity].
    + eapply ExecuteNext; [apply StepSeqDone |constructor].
Qed.

Lemma mb_acquire_after_fill_trace s : execution mailbox_active 24 (nl_acquire 1%positive 1%positive 0)
  s mb_filled halt (mb_acquired_stack 0 s) mb_producer_acquired.
Proof.
  eapply ExecuteNext.
  - apply StepFlush; apply FlushWrite with (i := 1%positive) (address := 3%positive) (v := 7%Z) (rest := [(4%positive,9%Z)]);
      [left; reflexivity |intros H; exact H |reflexivity].
  - eapply ExecuteNext.
    + apply StepFlush; apply FlushWrite with (i := 1%positive) (address := 4%positive) (v := 9%Z) (rest := []);
        [left; reflexivity |intros H; exact H |reflexivity].
    + apply named_lock_acquire_success_trace; [left; reflexivity |reflexivity |reflexivity].
Qed.

Lemma mb_publish_release_trace s : execution mailbox_active 7 (nl_release 1%positive 1%positive)
  s mb_publish_pending halt s mb_producer_final.
Proof.
  eapply ExecuteNext.
  - apply StepFlush; apply FlushWrite with (i := 1%positive) (address := 2%positive) (v := 1%Z) (rest := []);
      [left; reflexivity |intros H; exact H |reflexivity].
  - apply named_lock_release_trace; [left; reflexivity |reflexivity |reflexivity].
Qed.

Theorem mailbox_producer_trace s : execution mailbox_active 39 (mailbox_producer mb_items)
  s mb_initial halt (mb_acquired_stack 0 s) mb_producer_final.
Proof.
  change 39 with (4 + S 34); eapply container_execution_sequence; [apply mb_fill_trace |].
  change 34 with (24 + S 9); eapply container_execution_sequence; [apply mb_acquire_after_fill_trace |].
  change 9 with (1 + S 7); eapply container_execution_sequence with (middle := mb_publish_pending).
  - eapply ExecuteNext; [|constructor]. eapply StepPrimitive; [reflexivity |].
    eapply PrimitiveStore with (previous := 0%Z); [left; reflexivity |reflexivity |reflexivity].
  - apply mb_publish_release_trace.
Qed.

Lemma mb_take_release_trace s : execution mailbox_active 7 (nl_release 2%positive 1%positive)
  s mb_take_pending halt s mb_final.
Proof.
  eapply ExecuteNext.
  - apply StepFlush; apply FlushWrite with (i := 2%positive) (address := 2%positive) (v := 0%Z) (rest := []);
      [right; left; reflexivity |intros H; exact H |reflexivity].
  - apply named_lock_release_trace; [right; left; reflexivity |reflexivity |reflexivity].
Qed.

Theorem mailbox_take_success_trace s : execution mailbox_active 39 mailbox_attempt s mb_producer_final halt (mb_taken_stack s) mb_final.
Proof.
  change 39 with (22 + S 16); eapply container_execution_sequence with (middle := mb_consumer_acquired) (t := mb_acquired_stack 1 s).
  - apply named_lock_acquire_success_trace; [right; left; reflexivity |reflexivity |reflexivity].
  - change 16 with (1 + S 14); eapply container_execution_sequence with (middle := mb_consumer_acquired)
      (t := update (mb_acquired_stack 1 s) 1 1%Z).
    + eapply ExecuteNext; [|constructor]. eapply StepPrimitive; [reflexivity |].
      apply PrimitiveLoad; [right; left; reflexivity |intros H; exact H |reflexivity].
    + eapply ExecuteNext; [apply StepChoiceLeft |]. eapply ExecuteNext.
      * apply StepSeq; eapply StepPrimitive; [reflexivity |apply PrimitiveAssume; [right; left; reflexivity |reflexivity]].
      * eapply ExecuteNext; [apply StepSeqDone |]. change 11 with (1 + S 9).
        eapply container_execution_sequence with (middle := mb_take_pending).
        -- eapply ExecuteNext; [|constructor]. eapply StepPrimitive; [reflexivity |].
           eapply PrimitiveStore with (previous := 1%Z); [right; left; reflexivity |reflexivity |reflexivity].
        -- change 9 with (7 + S 1); eapply container_execution_sequence; [apply mb_take_release_trace |].
           eapply ExecuteNext; [|constructor]. eapply StepPrimitive; [reflexivity |apply PrimitiveAssign; right; left; reflexivity].
Qed.

Lemma mb_retry_success_trace s : execution mailbox_active 50 mailbox_retry s mb_producer_final halt
  (mb_taken_stack (update s 1 1%Z)) mb_final.
Proof.
  change 50 with (1 + S 48); eapply container_execution_sequence.
  - eapply ExecuteNext; [|constructor]. eapply StepPrimitive; [reflexivity |apply PrimitiveAssign; right; left; reflexivity].
  - change 48 with (46 + S 1); eapply container_execution_sequence.
    + change 46 with (39 + 7); apply nl_loop_one_trace;
        [right; left; reflexivity |reflexivity |apply mailbox_take_success_trace].
    + eapply ExecuteNext; [|constructor]. eapply StepPrimitive; [reflexivity |].
      apply PrimitiveAssume; [right; left; reflexivity |reflexivity].
Qed.

Lemma mb_private_reads_trace s : execution mailbox_active 4 (read_region 2%positive 2 mb_items) s mb_final
  (C.skip (EVal 2%Z)) (update (update s 2 7%Z) 2 9%Z) mb_final.
Proof.
  eapply ExecuteNext.
  - apply StepSeq; eapply StepPrimitive; [reflexivity |].
    apply PrimitiveLoad; [right; left; reflexivity |intros H; exact H |reflexivity].
  - eapply ExecuteNext; [apply StepSeqDone |]. eapply ExecuteNext.
    + apply StepSeq; eapply StepPrimitive; [reflexivity |].
      apply PrimitiveLoad; [right; left; reflexivity |intros H; exact H |reflexivity].
    + eapply ExecuteNext; [apply StepSeqDone |constructor].
Qed.

Theorem mailbox_consumer_trace s : execution mailbox_active 55 (mailbox_consumer mb_items) s mb_producer_final
  (C.skip (EVal 2%Z)) (mb_consumer_stack s) mb_final.
Proof. change 55 with (50 + S 4); eapply mailbox_sequence_to; [apply mb_retry_success_trace |apply mb_private_reads_trace]. Qed.

Theorem mailbox_parallel_trace s : execution mailbox_active 95 (mailbox_program mb_items) s mb_initial
  (C.skip (EVal 2%Z)) (mb_consumer_stack (mb_acquired_stack 0 s)) mb_final.
Proof.
  change 95 with (39 + 56); eapply execution_append; [apply execution_parallel_left,mailbox_producer_trace |].
  eapply ExecuteNext; [apply StepParallelLeftDone |apply mailbox_consumer_trace].
Qed.

Definition mb_failed_acquired := nl_write_final mailbox_active 2%positive 1%positive 1%Z mb_initial.
Definition mb_failed_final := nl_write_final mailbox_active 2%positive 1%positive 0%Z mb_failed_acquired.
Definition mb_failed_stack s := update (update (mb_acquired_stack 1 s) 1 0%Z) 1 1%Z.
Definition mailbox_retry_loop := C.Loop (C.Seq (C.Prim (C.Common (S.Assume (nl_is 1 1%Z))) (EVal 2%Z)) mailbox_attempt).

Theorem mailbox_take_failure_trace s : execution mailbox_active 36 mailbox_attempt s mb_initial halt (mb_failed_stack s) mb_failed_final.
Proof.
  change 36 with (22 + S 13); eapply container_execution_sequence with (middle := mb_failed_acquired) (t := mb_acquired_stack 1 s).
  - apply named_lock_acquire_success_trace; [right; left; reflexivity |reflexivity |reflexivity].
  - change 13 with (1 + S 11); eapply container_execution_sequence with (middle := mb_failed_acquired)
      (t := update (mb_acquired_stack 1 s) 1 0%Z).
    + eapply ExecuteNext; [|constructor]. eapply StepPrimitive; [reflexivity |].
      apply PrimitiveLoad; [right; left; reflexivity |intros H; exact H |reflexivity].
    + eapply ExecuteNext; [apply StepChoiceRight |]. eapply ExecuteNext.
      * apply StepSeq; eapply StepPrimitive; [reflexivity |apply PrimitiveAssume; [right; left; reflexivity |reflexivity]].
      * eapply ExecuteNext; [apply StepSeqDone |]. change 8 with (6 + S 1); eapply container_execution_sequence.
        -- apply named_lock_release_trace; [right; left; reflexivity |reflexivity |reflexivity].
        -- eapply ExecuteNext; [|constructor]. eapply StepPrimitive; [reflexivity |apply PrimitiveAssign; right; left; reflexivity].
Qed.

Theorem mailbox_failed_iteration_retries s : s 1 = 1%Z -> execution mailbox_active 41 mailbox_retry_loop s mb_initial
  mailbox_retry_loop (mb_failed_stack s) mb_failed_final.
Proof.
  intros Hx; eapply ExecuteNext; [apply StepLoop |]. eapply ExecuteNext; [apply StepChoiceRight |].
  change 39 with (38 + 1); eapply execution_append.
  - apply execution_sequence_prefix; change 38 with (1 + S 36); eapply container_execution_sequence.
    + eapply ExecuteNext; [|constructor]. eapply StepPrimitive; [reflexivity |apply PrimitiveAssume; [right; left; reflexivity |]].
      change (Z.eqb (s 1) 1%Z = true); rewrite Hx; reflexivity.
    + apply mailbox_take_failure_trace.
  - eapply ExecuteNext; [apply StepSeqDone |constructor].
Qed.

Definition nl_write_states active actor flag value m := [m; acquire active m actor;
  enqueue (acquire active m actor) actor flag value;
  flush_write (enqueue (acquire active m actor) actor flag value) actor flag value [];
  nl_write_final active actor flag value m].

Lemma nl_write_foreign_buffer active actor flag value m foreign : actor <> foreign ->
  Forall (fun out => buffers out foreign = buffers m foreign) (nl_write_states active actor flag value m).
Proof.
  intros Hne; unfold nl_write_states; repeat constructor; cbn [nl_write_final release flush_write enqueue acquire buffers];
    unfold buffer_update; destruct (Pos.eq_dec foreign actor); congruence.
Qed.

Definition mailbox_trace_memories :=
  [mb_initial; mb_fill_first; mb_filled; mb_flush_first; mb_flushed; mb_publish_pending;
   mb_publish_flushed; mb_take_pending; mb_take_flushed] ++
  nl_write_states mailbox_active 1%positive 1%positive 1%Z mb_flushed ++
  nl_write_states mailbox_active 1%positive 1%positive 0%Z mb_publish_flushed ++
  nl_write_states mailbox_active 2%positive 1%positive 1%Z mb_producer_final ++
  nl_write_states mailbox_active 2%positive 1%positive 0%Z mb_take_flushed ++
  nl_write_states mailbox_active 2%positive 1%positive 1%Z mb_initial ++
  nl_write_states mailbox_active 2%positive 1%positive 0%Z mb_failed_acquired.

Theorem mailbox_foreign_pending_throughout :
  Forall (fun m => buffers m 3%positive = [(5%positive,17%Z)]) mailbox_trace_memories.
Proof. unfold mailbox_trace_memories,nl_write_states; repeat constructor. Qed.

Theorem mailbox_trace_contents s :
  buffers mb_filled 1%positive = [(3%positive,7%Z);(4%positive,9%Z)] /\
  shared_heap mb_filled 3%positive = Some 0%Z /\ shared_heap mb_filled 4%positive = Some 0%Z /\
  shared_heap mb_final 1%positive = Some 0%Z /\ shared_heap mb_final 2%positive = Some 0%Z /\
  shared_heap mb_final 3%positive = Some 7%Z /\ shared_heap mb_final 4%positive = Some 9%Z /\
  buffers mb_final 1%positive = [] /\ buffers mb_final 2%positive = [] /\
  buffers mb_final 3%positive = [(5%positive,17%Z)] /\ lock_free mb_final /\
  mb_consumer_stack (mb_acquired_stack 0 s) 2 = 9%Z.
Proof. repeat split; try reflexivity; intros i H; exact H. Qed.

Theorem mailbox_example_all_runs s n last t final : execution mailbox_active n (mailbox_program mb_items) s mb_initial last t final ->
  ~ abort mailbox_active last (State t final) /\
  (terminal last -> exists local pool, memory_spatial pool (resource_memory mailbox_active local) final /\
    persistent_models mailbox_active t local (A.Spatial (mailbox_foreign 5%positive) (cell_family mb_items)) /\
    lock_free final /\ persistent_full_satisfies mailbox_active t pool (nl_pool (mailbox_locks mb_items))).
Proof. apply mailbox_all_runs; repeat constructor; cbn; intuition discriminate. Qed.
