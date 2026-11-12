From Stdlib Require Import List ZArith Lia.
From WMLR Require Import Expressions Languages Machine BufferRelations Separation OperationalSemantics
  ExecutionExamples Safety TemporalSafety PrivateExamples ParallelExamples HeapExtension
  MessagePassingSyntax MessagePassingResources MessagePassingAdequacy.
Import ListNotations.

Definition mp_sender_held loc := acquire two_processors (mp_initial loc) 1%positive.
Definition mp_sender_pending loc := enqueue (mp_sender_held loc) 1%positive loc 1%Z.
Definition mp_sender_flushed loc := flush_write (mp_sender_pending loc) 1%positive loc 1%Z [].
Definition mp_sender_final loc := release (mp_sender_flushed loc).
Definition mp_private_pending loc := enqueue (mp_sender_final loc) 2%positive loc 2%Z.
Definition mp_private_final loc := flush_write (mp_private_pending loc) 2%positive loc 2%Z [].

Lemma mp_sender_trace s loc : s 1 = Z.pos loc ->
  execution two_processors 6 mp_sender s (mp_initial loc) halt s (mp_sender_final loc).
Proof.
  intros E; eapply ExecuteNext.
  - apply StepSeq; eapply StepPrimitive; [reflexivity |].
    apply PrimitiveLock; [left; reflexivity |reflexivity |intros i H; exact H].
  - eapply ExecuteNext; [apply StepSeqDone |]. eapply ExecuteNext.
    + apply StepSeq; eapply StepPrimitive; [reflexivity |].
      eapply PrimitiveStore with (loc := loc) (previous := 0%Z); [left; reflexivity |exact E |].
      change (local_read (mp_sender_held loc) 1%positive (Z.pos loc) = Some 0%Z).
      cbn [local_read mp_sender_held acquire mp_initial mp_plain buffers empty_buffers buffer_lookup shared_heap].
      apply heap_update_same.
    + eapply ExecuteNext; [apply StepSeqDone |]. eapply ExecuteNext.
      * apply StepFlush; apply FlushWrite with (i := 1%positive) (address := loc) (v := 1%Z) (rest := []).
        -- left; reflexivity.
        -- intros [_ H]; apply H; reflexivity.
        -- change (buffer_update empty_buffers 1%positive [(loc,1%Z)] 1%positive = [(loc,1%Z)]).
           apply buffer_update_same.
      * eapply ExecuteNext; [|constructor]. eapply StepPrimitive; [reflexivity |].
        apply PrimitiveUnlock; [left; reflexivity |apply buffer_update_same
          |split; [left; reflexivity |intros i; reflexivity]].
Qed.

(** The six-step locked prefix leaves the same physical heap and buffers.
    The only stack change is the result register. *)
Lemma mp_receiver_prefix s loc h b value : s 1 = Z.pos loc -> h loc = Some value ->
  (forall i, b i = []) ->
  execution two_processors 6 mp_receiver s (Memory h b no_blocked)
    mp_tail (update s 0 value) (Memory h b no_blocked).
Proof.
  intros E HH HB; eapply ExecuteNext.
  - apply StepSeq; eapply StepPrimitive; [reflexivity |].
    apply PrimitiveLock; [right; reflexivity |apply HB |intros i H; exact H].
  - eapply ExecuteNext; [apply StepSeqDone |]. eapply ExecuteNext.
    + apply StepSeq; eapply StepPrimitive; [reflexivity |].
      apply PrimitiveLoad with (v := value); [right; reflexivity |intros [_ H]; apply H; reflexivity |].
      change (local_read (acquire two_processors (Memory h b no_blocked) 2%positive) 2%positive (s 1) = Some value).
      rewrite E; cbn [local_read acquire buffers shared_heap]; rewrite HB; exact HH.
    + eapply ExecuteNext; [apply StepSeqDone |]. eapply ExecuteNext.
      * apply StepSeq; eapply StepPrimitive; [reflexivity |].
        apply PrimitiveUnlock; [right; reflexivity |apply HB
          |split; [right; reflexivity |intros i; reflexivity]].
      * eapply ExecuteNext; [apply StepSeqDone |constructor].
Qed.

Lemma mp_tail_zero_trace s m : s 0 = 0%Z ->
  execution two_processors 3 mp_tail s m (C.skip (EVal 2%Z)) s m.
Proof.
  intros E; eapply ExecuteNext; [apply StepChoiceRight |]. eapply ExecuteNext.
  - apply StepSeq; eapply StepPrimitive; [reflexivity |].
    apply PrimitiveAssume; [right; reflexivity |change (negb (Z.eqb (s 0) 1%Z) = true); rewrite E; reflexivity].
  - eapply ExecuteNext; [apply StepSeqDone |constructor].
Qed.

Lemma mp_receiver_zero_trace s loc : s 1 = Z.pos loc ->
  execution two_processors 9 mp_receiver s (mp_initial loc) (C.skip (EVal 2%Z)) (update s 0 0%Z) (mp_initial loc).
Proof.
  intros E; change 9 with (6 + 3); eapply execution_append.
  - apply mp_receiver_prefix with (loc := loc); [exact E |apply heap_update_same |intros; reflexivity].
  - apply mp_tail_zero_trace,update_same.
Qed.

Theorem message_passing_zero_trace s loc : s 1 = Z.pos loc ->
  execution two_processors 16 mp_program s (mp_initial loc) halt
    (update s 0 0%Z) (mp_sender_final loc).
Proof.
  intros E; change 16 with (9 + 7); eapply execution_append.
  - apply execution_parallel_right,mp_receiver_zero_trace,E.
  - eapply ExecuteNext; [apply StepParallelRightDone |].
    apply mp_sender_trace; rewrite update_other by discriminate; exact E.
Qed.

Lemma mp_sender_final_shape loc : shared_heap (mp_sender_final loc) loc = Some 1%Z /\
  (forall i, buffers (mp_sender_final loc) i = []) /\ lock_free (mp_sender_final loc).
Proof.
  split; [apply heap_update_same |split; [|intros i H; exact H]].
  intros i; change (buffer_update (buffers (mp_sender_pending loc)) 1%positive [] i = []).
  unfold buffer_update; destruct (Pos.eq_dec i 1%positive) as [-> |Hne]; [reflexivity |].
  change (buffer_update empty_buffers 1%positive [(loc,1%Z)] i = []).
  rewrite buffer_update_other by exact Hne; reflexivity.
Qed.

Lemma mp_tail_one_pending_trace s loc : s 1 = Z.pos loc -> s 0 = 1%Z ->
  execution two_processors 4 mp_tail s (mp_sender_final loc) (C.Seq halt mp_fence)
    s (mp_private_pending loc).
Proof.
  intros E HV; eapply ExecuteNext; [apply StepChoiceLeft |]. eapply ExecuteNext.
  - apply StepSeq; eapply StepPrimitive; [reflexivity |].
    apply PrimitiveAssume; [right; reflexivity |change (Z.eqb (s 0) 1%Z = true); rewrite HV; reflexivity].
  - eapply ExecuteNext; [apply StepSeqDone |]. eapply ExecuteNext; [|constructor].
    apply StepSeq; eapply StepPrimitive; [reflexivity |].
    eapply PrimitiveStore with (loc := loc) (previous := 1%Z); [right; reflexivity |exact E |].
    change (local_read (mp_sender_final loc) 2%positive (Z.pos loc) = Some 1%Z).
    cbn [local_read]; rewrite (proj1 (proj2 (mp_sender_final_shape loc))).
    exact (proj1 (mp_sender_final_shape loc)).
Qed.

Theorem message_passing_one_pending_trace s loc : s 1 = Z.pos loc ->
  execution two_processors 17 mp_program s (mp_initial loc) (C.Seq halt mp_fence)
    (update s 0 1%Z) (mp_private_pending loc).
Proof.
  intros E; change 17 with (6 + 11); eapply execution_append.
  - apply execution_parallel_left,mp_sender_trace,E.
  - eapply ExecuteNext; [apply StepParallelLeftDone |].
    change 10 with (6 + 4); eapply execution_append.
    + apply mp_receiver_prefix with (loc := loc); [exact E |apply mp_sender_final_shape |apply mp_sender_final_shape].
    + apply mp_tail_one_pending_trace; [rewrite update_other by discriminate; exact E |apply update_same].
Qed.

Lemma mp_private_complete_trace s loc :
  execution two_processors 3 (C.Seq halt mp_fence) s (mp_private_pending loc)
    halt s (mp_private_final loc).
Proof.
  eapply ExecuteNext.
  - apply StepFlush; apply FlushWrite with (i := 2%positive) (address := loc) (v := 2%Z) (rest := []).
    + right; reflexivity.
    + intros H; exact H.
    + change (buffer_update (buffers (mp_sender_final loc)) 2%positive
        (buffers (mp_sender_final loc) 2%positive ++ [(loc,2%Z)]) 2%positive = [(loc,2%Z)]).
      rewrite buffer_update_same,(proj1 (proj2 (mp_sender_final_shape loc))); reflexivity.
  - eapply ExecuteNext; [apply StepSeqDone |]. eapply ExecuteNext; [|constructor].
    eapply StepPrimitive; [reflexivity |apply PrimitiveFence; [right; reflexivity |apply buffer_update_same]].
Qed.

Theorem message_passing_one_trace s loc : s 1 = Z.pos loc ->
  execution two_processors 20 mp_program s (mp_initial loc) halt
    (update s 0 1%Z) (mp_private_final loc).
Proof.
  intros E; change 20 with (17 + 3); eapply execution_append;
    [apply message_passing_one_pending_trace,E |apply mp_private_complete_trace].
Qed.

Theorem message_passing_private_write_pending loc :
  shared_heap (mp_private_pending loc) loc = Some 1%Z /\
  buffers (mp_private_pending loc) 2%positive = [(loc,2%Z)] /\
  lock_free (mp_private_pending loc) /\ shared_heap (mp_private_final loc) loc = Some 2%Z.
Proof.
  split; [apply mp_sender_final_shape |split].
  - change (buffer_update (buffers (mp_sender_final loc)) 2%positive
      (buffers (mp_sender_final loc) 2%positive ++ [(loc,2%Z)]) 2%positive = [(loc,2%Z)]).
    rewrite buffer_update_same,(proj1 (proj2 (mp_sender_final_shape loc))); reflexivity.
  - split; [intros i H; exact H |apply heap_update_same].
Qed.
