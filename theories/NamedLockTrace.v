From Stdlib Require Import List ZArith Lia.
From WMLR Require Import Expressions Languages Machine BufferRelations Separation OperationalSemantics
  Safety PrivateExamples OwnedContainerTrace NamedLockSyntax.
Import ListNotations.

Definition nl_write_final active actor flag value m := release
  (flush_write (enqueue (acquire active m actor) actor flag value) actor flag value []).

Lemma nl_global_write_trace active actor flag old value s h b : active actor ->
  b actor = [] -> h flag = Some old ->
  execution active 6 (C.Seq (nl_acquire_global actor)
    (C.Seq (nl_store actor flag value) (nl_release_global actor))) s (Memory h b no_blocked)
    halt s (nl_write_final active actor flag value (Memory h b no_blocked)).
Proof.
  intros Hi HB HH; eapply ExecuteNext.
  - apply StepSeq; eapply StepPrimitive; [reflexivity |apply PrimitiveLock; [exact Hi |exact HB |intros i H; exact H]].
  - eapply ExecuteNext; [apply StepSeqDone |]. eapply ExecuteNext.
    + apply StepSeq; eapply StepPrimitive; [reflexivity |].
      eapply PrimitiveStore with (loc := flag) (previous := old); [exact Hi |reflexivity |].
      cbn [local_read acquire buffers shared_heap eval_expr]; rewrite HB; exact HH.
    + eapply ExecuteNext; [apply StepSeqDone |]. eapply ExecuteNext.
      * apply StepFlush; apply FlushWrite with (i := actor) (address := flag) (v := value) (rest := []).
        -- exact Hi.
        -- intros [_ H]; apply H; reflexivity.
        -- cbn [enqueue buffers]; rewrite buffer_update_same; cbn [acquire buffers]; rewrite HB; reflexivity.
      * eapply ExecuteNext; [|constructor]. eapply StepPrimitive; [reflexivity |].
        apply PrimitiveUnlock; [exact Hi |apply buffer_update_same |split; [exact Hi |intros i; reflexivity]].
Qed.

Lemma nl_attempt_success_trace active actor flag x s h b : active actor ->
  b actor = [] -> h flag = Some 0%Z ->
  execution active 11 (nl_attempt actor flag x) s (Memory h b no_blocked)
    halt (update s x 0%Z) (nl_write_final active actor flag 1%Z (Memory h b no_blocked)).
Proof.
  intros Hi HB HH; eapply ExecuteNext.
  - apply StepSeq; eapply StepPrimitive; [reflexivity |apply PrimitiveLock; [exact Hi |exact HB |intros i H; exact H]].
  - eapply ExecuteNext; [apply StepSeqDone |]. eapply ExecuteNext.
    + apply StepSeq; eapply StepPrimitive; [reflexivity |].
      apply PrimitiveLoad with (v := 0%Z); [exact Hi |intros [_ H]; apply H; reflexivity |].
      cbn [local_read acquire buffers shared_heap eval_expr]; rewrite HB; exact HH.
    + eapply ExecuteNext; [apply StepSeqDone |]. eapply ExecuteNext; [apply StepChoiceLeft |]. eapply ExecuteNext.
      * apply StepSeq; eapply StepPrimitive; [reflexivity |apply PrimitiveAssume; [exact Hi |]].
        change (Z.eqb (update s x 0%Z x) 0%Z = true); rewrite update_same; reflexivity.
      * eapply ExecuteNext; [apply StepSeqDone |]. eapply ExecuteNext.
        -- apply StepSeq; eapply StepPrimitive; [reflexivity |].
           eapply PrimitiveStore with (loc := flag) (previous := 0%Z); [exact Hi |reflexivity |].
           cbn [local_read acquire buffers shared_heap]; rewrite HB; exact HH.
        -- eapply ExecuteNext; [apply StepSeqDone |]. eapply ExecuteNext.
           ++ apply StepFlush; apply FlushWrite with (i := actor) (address := flag) (v := 1%Z) (rest := []).
              ** exact Hi.
              ** intros [_ H]; apply H; reflexivity.
              ** cbn [enqueue buffers]; rewrite buffer_update_same; cbn [acquire buffers]; rewrite HB; reflexivity.
           ++ eapply ExecuteNext; [|constructor]. eapply StepPrimitive; [reflexivity |].
              apply PrimitiveUnlock; [exact Hi |apply buffer_update_same |split; [exact Hi |intros i; reflexivity]].
Qed.

Lemma nl_attempt_retry_trace active actor flag x s h b : active actor ->
  b actor = [] -> h flag = Some 1%Z ->
  execution active 8 (nl_attempt actor flag x) s (Memory h b no_blocked)
    halt (update s x 1%Z) (Memory h b no_blocked).
Proof.
  intros Hi HB HH; eapply ExecuteNext.
  - apply StepSeq; eapply StepPrimitive; [reflexivity |apply PrimitiveLock; [exact Hi |exact HB |intros i H; exact H]].
  - eapply ExecuteNext; [apply StepSeqDone |]. eapply ExecuteNext.
    + apply StepSeq; eapply StepPrimitive; [reflexivity |].
      apply PrimitiveLoad with (v := 1%Z); [exact Hi |intros [_ H]; apply H; reflexivity |].
      cbn [local_read acquire buffers shared_heap eval_expr]; rewrite HB; exact HH.
    + eapply ExecuteNext; [apply StepSeqDone |]. eapply ExecuteNext; [apply StepChoiceRight |]. eapply ExecuteNext.
      * apply StepSeq; eapply StepPrimitive; [reflexivity |apply PrimitiveAssume; [exact Hi |]].
        change (negb (Z.eqb (update s x 1%Z x) 0%Z) = true); rewrite update_same; reflexivity.
      * eapply ExecuteNext; [apply StepSeqDone |]. eapply ExecuteNext; [|constructor].
        eapply StepPrimitive; [reflexivity |].
        apply PrimitiveUnlock; [exact Hi |exact HB |split; [exact Hi |intros i; reflexivity]].
Qed.

Lemma nl_loop_one_trace active actor condition body n s initial t final : active actor ->
  eval_bexpr s condition = true -> execution active n body s initial halt t final ->
  execution active (n + 7) (C.Loop (C.Seq (C.Prim (C.Common (S.Assume condition)) (EVal (Z.pos actor))) body))
    s initial halt t final.
Proof.
  intros Hi Hb HR; replace (n + 7) with (S (S ((1 + S n) + S 2))) by lia.
  eapply ExecuteNext; [apply StepLoop |]. eapply ExecuteNext; [apply StepChoiceRight |].
  eapply container_execution_sequence.
  - eapply container_execution_sequence; [|exact HR]. eapply ExecuteNext; [|constructor].
    eapply StepPrimitive; [reflexivity |apply PrimitiveAssume; assumption].
  - eapply ExecuteNext; [apply StepLoop |]. eapply ExecuteNext; [apply StepChoiceLeft |constructor].
Qed.

Theorem named_lock_acquire_success_trace active actor flag x s h b : active actor ->
  b actor = [] -> h flag = Some 0%Z ->
  execution active 22 (nl_acquire actor flag x) s (Memory h b no_blocked)
    halt (update (update s x 1%Z) x 0%Z) (nl_write_final active actor flag 1%Z (Memory h b no_blocked)).
Proof.
  intros Hi HB HH; change 22 with (1 + S 20); eapply container_execution_sequence.
  - eapply ExecuteNext; [|constructor]. eapply StepPrimitive; [reflexivity |apply PrimitiveAssign,Hi].
  - change 20 with (18 + S 1); eapply container_execution_sequence.
    + change 18 with (11 + 7); apply nl_loop_one_trace; [exact Hi | |apply nl_attempt_success_trace; assumption].
      change (Z.eqb (update s x 1%Z x) 1%Z = true); rewrite update_same; reflexivity.
    + eapply ExecuteNext; [|constructor]. eapply StepPrimitive; [reflexivity |apply PrimitiveAssume; [exact Hi |]].
      change (negb (Z.eqb (update (update s x 1%Z) x 0%Z x) 1%Z) = true); rewrite update_same; reflexivity.
Qed.

Definition nl_retry_loop actor flag x := C.Loop (C.Seq
  (C.Prim (C.Common (S.Assume (nl_is x 1%Z))) (EVal (Z.pos actor))) (nl_attempt actor flag x)).

Theorem named_lock_retry_iteration_trace active actor flag x s h b : active actor ->
  b actor = [] -> h flag = Some 1%Z -> s x = 1%Z ->
  execution active 13 (nl_retry_loop actor flag x) s (Memory h b no_blocked)
    (nl_retry_loop actor flag x) (update s x 1%Z) (Memory h b no_blocked).
Proof.
  intros Hi HB HH Hx; eapply ExecuteNext; [apply StepLoop |]. eapply ExecuteNext; [apply StepChoiceRight |].
  change 11 with (10 + 1); eapply execution_append.
  - apply execution_sequence_prefix; change 10 with (1 + S 8); eapply container_execution_sequence.
    + eapply ExecuteNext; [|constructor]. eapply StepPrimitive; [reflexivity |apply PrimitiveAssume; [exact Hi |]].
      change (Z.eqb (s x) 1%Z = true); rewrite Hx; reflexivity.
    + apply nl_attempt_retry_trace; assumption.
  - eapply ExecuteNext; [apply StepSeqDone |constructor].
Qed.

Theorem named_lock_release_trace active actor flag s h b : active actor ->
  b actor = [] -> h flag = Some 1%Z ->
  execution active 6 (nl_release actor flag) s (Memory h b no_blocked)
    halt s (nl_write_final active actor flag 0%Z (Memory h b no_blocked)).
Proof. intros Hi HB HH; eapply nl_global_write_trace; eassumption. Qed.

Lemma nl_write_final_shape active actor flag value m : buffers m actor = [] ->
  (forall l, shared_heap (nl_write_final active actor flag value m) l = heap_update (shared_heap m) flag value l) /\
  (forall i, buffers (nl_write_final active actor flag value m) i = buffers m i) /\
  lock_free (nl_write_final active actor flag value m).
Proof.
  intros HB; split; [intros; reflexivity |split; [|intros i H; exact H]].
  intros i; cbn [nl_write_final release flush_write enqueue acquire buffers].
  unfold buffer_update; destruct (Pos.eq_dec i actor) as [-> |Hne]; [symmetry; exact HB |reflexivity].
Qed.
