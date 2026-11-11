From Stdlib Require Import List ZArith.
From WMLR Require Import Expressions Languages Machine OperationalSemantics.
Import ListNotations.

(** A two-processor instance with locations 1 and 2 initially allocated. *)
Definition two_processors (i : processor) : Prop := i = 1%positive \/ i = 2%positive.

Definition initial_heap : heap :=
  heap_update (heap_update empty_heap 1%positive 0%Z) 2%positive 0%Z.

Definition initial_memory : memory := Memory initial_heap empty_buffers no_blocked.
Definition initial_registers : stack := fun _ => (-1)%Z.
Definition initial_state : state := State initial_registers initial_memory.

Definition store_command (i loc : positive) (v : value) : C.command :=
  C.Prim (C.Common (S.Store (EVal (Z.pos loc)) (EVal v))) (EVal (Z.pos i)).

Definition load_command (i loc : positive) (target : ident) : C.command :=
  C.Prim (C.Common (S.Load target (EVal (Z.pos loc)))) (EVal (Z.pos i)).

(** The standard store-buffering litmus. Registers start at -1, so the
    zero results below require that both load commands actually execute. *)
Definition store_buffering : C.command :=
  C.Parallel
    (C.Seq (store_command 1%positive 1%positive 1%Z) (load_command 1%positive 2%positive 0))
    (C.Seq (store_command 2%positive 2%positive 1%Z) (load_command 2%positive 1%positive 1)).

Definition after_first_store : memory := enqueue initial_memory 1%positive 1%positive 1%Z.
Definition after_both_stores : memory := enqueue after_first_store 2%positive 2%positive 1%Z.
Definition after_first_load : stack := update initial_registers 0 0%Z.
Definition after_both_loads : stack := update after_first_load 1 0%Z.
Definition after_first_flush : memory :=
  flush_write after_both_stores 1%positive 1%positive 1%Z [].
Definition after_both_flushes : memory :=
  flush_write after_first_flush 2%positive 2%positive 1%Z [].
Definition store_buffering_final : state := State after_both_loads after_both_flushes.

Theorem store_buffering_trace :
  steps two_processors store_buffering initial_state halt store_buffering_final.
Proof.
  unfold store_buffering, initial_state, store_buffering_final.
  (* Processor 1 buffers its store. *)
  eapply StepsNext with
    (next := C.Parallel
      (C.Seq halt (load_command 1%positive 2%positive 0))
      (C.Seq (store_command 2%positive 2%positive 1%Z) (load_command 2%positive 1%positive 1)))
    (middle := State initial_registers after_first_store).
  { apply StepParallelLeft, StepSeq.
    eapply StepPrimitive; [reflexivity |].
    eapply PrimitiveStore with (previous := 0%Z);
      [left; reflexivity | reflexivity | reflexivity]. }
  (* Processor 2 buffers its store before either buffer flushes. *)
  eapply StepsNext with
    (next := C.Parallel (C.Seq halt (load_command 1%positive 2%positive 0))
      (C.Seq halt (load_command 2%positive 1%positive 1)))
    (middle := State initial_registers after_both_stores).
  { apply StepParallelRight, StepSeq.
    eapply StepPrimitive; [reflexivity |].
    eapply PrimitiveStore with (previous := 0%Z);
      [right; reflexivity | reflexivity | reflexivity]. }
  eapply StepsNext; [apply StepParallelLeft, StepSeqDone |].
  (* Processor 1 reads location 2 from the shared heap. *)
  eapply StepsNext with
    (next := C.Parallel halt (C.Seq halt (load_command 2%positive 1%positive 1)))
    (middle := State after_first_load after_both_stores).
  { apply StepParallelLeft. eapply StepPrimitive; [reflexivity |].
    apply PrimitiveLoad; [left; reflexivity | simpl; tauto | reflexivity]. }
  eapply StepsNext; [apply StepParallelRight, StepSeqDone |].
  (* Processor 2 also reads zero from the shared heap. *)
  eapply StepsNext with (next := C.Parallel halt halt)
    (middle := State after_both_loads after_both_stores).
  { apply StepParallelRight. eapply StepPrimitive; [reflexivity |].
    apply PrimitiveLoad; [right; reflexivity | simpl; tauto | reflexivity]. }
  eapply StepsNext; [apply StepParallelLeftDone |].
  (* Flushing remains possible after the commands finish. *)
  eapply StepsNext with (middle := State after_both_loads after_first_flush).
  { apply StepFlush. eapply FlushWrite with (i := 1%positive).
    - left; reflexivity.
    - simpl; tauto.
    - reflexivity. }
  eapply StepsNext with (middle := State after_both_loads after_both_flushes).
  { apply StepFlush. eapply FlushWrite with (i := 2%positive).
    - right; reflexivity.
    - simpl; tauto.
    - reflexivity. }
  constructor.
Qed.

Lemma store_buffering_final_buffers_empty i :
  buffers (memory_state store_buffering_final) i = [].
Proof.
  unfold store_buffering_final, after_both_flushes, after_first_flush,
    after_both_stores, after_first_store, initial_memory, flush_write, enqueue.
  cbn [memory_state buffers]. unfold buffer_update.
  destruct (Pos.eq_dec i 2%positive); destruct (Pos.eq_dec i 1%positive); reflexivity.
Qed.

Theorem store_buffering_zero_zero :
  exists final,
    steps two_processors store_buffering initial_state halt final /\
    registers final 0 = 0%Z /\ registers final 1 = 0%Z /\
    shared_heap (memory_state final) 1%positive = Some 1%Z /\
    shared_heap (memory_state final) 2%positive = Some 1%Z /\
    (forall i, buffers (memory_state final) i = []).
Proof.
  exists store_buffering_final. split; [apply store_buffering_trace |].
  repeat split; try reflexivity. apply store_buffering_final_buffers_empty.
Qed.

Example initial_memory_well_formed : memory_well_formed two_processors initial_memory.
Proof. split; simpl; [intros i H; contradiction | auto]. Qed.

Example initial_memory_lock_complete : lock_complete two_processors initial_memory.
Proof. left. intros i H; contradiction. Qed.

Example store_buffering_final_well_formed :
  memory_well_formed two_processors (memory_state store_buffering_final).
Proof.
  eapply steps_preserve_well_formed; [apply store_buffering_trace |].
  apply initial_memory_well_formed.
Qed.

Example store_buffering_final_lock_complete :
  lock_complete two_processors (memory_state store_buffering_final).
Proof.
  eapply steps_preserve_lock_complete; [apply store_buffering_trace |].
  apply initial_memory_lock_complete.
Qed.

(** A fence can execute only after the preceding store flushes. *)
Definition store_then_fence : C.command :=
  C.Seq (store_command 1%positive 1%positive 1%Z)
    (C.Prim (C.Common S.Fence) (EVal 1%Z)).

Example fence_waits_for_buffer :
  forall final, ~ primitive_step two_processors (C.Common S.Fence) 1%positive
    (State initial_registers after_first_store) final.
Proof. intros final Hstep. inversion Hstep. discriminate. Qed.

Theorem store_fence_trace :
  steps two_processors store_then_fence initial_state halt
    (State initial_registers (flush_write after_first_store 1%positive 1%positive 1%Z [])).
Proof.
  unfold store_then_fence, initial_state.
  eapply StepsNext with
    (next := C.Seq halt (C.Prim (C.Common S.Fence) (EVal 1%Z)))
    (middle := State initial_registers after_first_store).
  - apply StepSeq. eapply StepPrimitive; [reflexivity |].
    eapply PrimitiveStore with (previous := 0%Z); [left; reflexivity | reflexivity | reflexivity].
  - eapply StepsNext; [apply StepSeqDone |].
    eapply StepsNext with
      (middle := State initial_registers
        (flush_write after_first_store 1%positive 1%positive 1%Z [])).
    + apply StepFlush. eapply FlushWrite with (i := 1%positive).
      * left; reflexivity.
      * simpl; tauto.
      * reflexivity.
    + apply steps_one. eapply StepPrimitive; [reflexivity |].
      apply PrimitiveFence; [left; reflexivity | reflexivity].
Qed.

(** FIFO flush order and latest-write forwarding are different operations. *)
Definition repeated_writes : memory :=
  enqueue (enqueue initial_memory 1%positive 1%positive 3%Z) 1%positive 1%positive 4%Z.

Example fifo_flush_and_latest_read :
  let next := flush_write repeated_writes 1%positive 1%positive 3%Z [(1%positive, 4%Z)] in
  flush two_processors repeated_writes next /\
  shared_heap next 1%positive = Some 3%Z /\
  buffers next 1%positive = [(1%positive, 4%Z)] /\
  local_read next 1%positive 1%Z = Some 4%Z.
Proof.
  split.
  - eapply FlushWrite with (i := 1%positive); [left; reflexivity | simpl; tauto | reflexivity].
  - repeat split; reflexivity.
Qed.

Definition locked_memory : memory := acquire two_processors initial_memory 1%positive.
Definition blocked_store_memory : memory := enqueue locked_memory 2%positive 2%positive 7%Z.

Theorem lock_store_unlock_trace :
  let buffered := enqueue locked_memory 1%positive 1%positive 1%Z in
  let flushed := flush_write buffered 1%positive 1%positive 1%Z [] in
  steps two_processors (C.locked (EVal 1%Z) (store_command 1%positive 1%positive 1%Z))
    initial_state halt (State initial_registers (release flushed)).
Proof.
  cbn zeta. unfold C.locked, initial_state.
  eapply StepsNext with
    (next := C.Seq halt
      (C.Seq (store_command 1%positive 1%positive 1%Z) (C.Prim C.Unlock (EVal 1%Z))))
    (middle := State initial_registers locked_memory).
  { apply StepSeq. eapply StepPrimitive; [reflexivity |].
    apply PrimitiveLock; [left; reflexivity | reflexivity | intros i H; contradiction]. }
  eapply StepsNext; [apply StepSeqDone |].
  eapply StepsNext with
    (next := C.Seq halt (C.Prim C.Unlock (EVal 1%Z)))
    (middle := State initial_registers (enqueue locked_memory 1%positive 1%positive 1%Z)).
  { apply StepSeq. eapply StepPrimitive; [reflexivity |].
    eapply PrimitiveStore with (previous := 0%Z);
      [left; reflexivity | reflexivity | reflexivity]. }
  eapply StepsNext; [apply StepSeqDone |].
  eapply StepsNext with
    (middle := State initial_registers
      (flush_write (enqueue locked_memory 1%positive 1%positive 1%Z)
        1%positive 1%positive 1%Z [])).
  { apply StepFlush. eapply FlushWrite with (i := 1%positive).
    - left; reflexivity.
    - intros [_ Hneq]. apply Hneq; reflexivity.
    - reflexivity. }
  apply steps_one. eapply StepPrimitive; [reflexivity |].
  apply PrimitiveUnlock; [left; reflexivity | reflexivity |].
  split; [left; reflexivity | intros i; reflexivity].
Qed.

Example store_can_issue_while_blocked :
  blocked locked_memory 2%positive /\
  step two_processors (store_command 2%positive 2%positive 7%Z)
    (State initial_registers locked_memory) halt
    (State initial_registers blocked_store_memory).
Proof.
  split.
  - split; [right; reflexivity | discriminate].
  - eapply StepPrimitive; [reflexivity |].
    eapply PrimitiveStore with (previous := 0%Z); [right; reflexivity | reflexivity | reflexivity].
Qed.

Example blocked_load_waits_even_for_own_buffer :
  local_read blocked_store_memory 2%positive 2%Z = Some 7%Z /\
  (forall final, ~ primitive_step two_processors (C.Common (S.Load 0 (EVal 2%Z)))
    2%positive (State initial_registers blocked_store_memory) final) /\
  ~ primitive_abort two_processors (C.Common (S.Load 0 (EVal 2%Z)))
    2%positive (State initial_registers blocked_store_memory).
Proof.
  assert (Hblocked : blocked blocked_store_memory 2%positive).
  { split; [right; reflexivity | discriminate]. }
  split; [reflexivity |]. split.
  - intros final Hstep. inversion Hstep; subst. contradiction.
  - intros Habort. inversion Habort; subst. contradiction.
Qed.

Example blocked_buffer_cannot_flush :
  forall next, ~ flush two_processors blocked_store_memory next.
Proof.
  intros next Hflush. inversion Hflush as [m i address v rest Hi Hunblocked Hbuffer]; subst.
  destruct Hi as [-> | ->].
  - discriminate Hbuffer.
  - apply Hunblocked. split; [right; reflexivity | discriminate].
Qed.

Example lock_requires_flushed_buffer :
  forall final, ~ primitive_step two_processors C.Lock 1%positive
    (State initial_registers after_first_store) final.
Proof. intros final Hstep. inversion Hstep. discriminate. Qed.

Example unlock_requires_flushed_buffer :
  forall final, ~ primitive_step two_processors C.Unlock 1%positive
    (State initial_registers (enqueue locked_memory 1%positive 1%positive 1%Z)) final.
Proof. intros final Hstep. inversion Hstep. discriminate. Qed.

Example false_assumption_waits :
  (forall final, ~ primitive_step two_processors (C.Common (S.Assume BFalse))
    1%positive initial_state final) /\
  ~ primitive_abort two_processors (C.Common (S.Assume BFalse)) 1%positive initial_state.
Proof.
  split.
  - intros final Hstep. inversion Hstep. discriminate.
  - intros Habort. inversion Habort.
Qed.

Example assertion_fault_propagates_through_parallel :
  abort two_processors
    (C.Parallel (C.Prim (C.Common (S.Assert BFalse)) (EVal 1%Z)) halt) initial_state.
Proof.
  apply ParallelLeftAbort. eapply CommandAbort; [reflexivity |].
  apply AbortAssert; [left; reflexivity | reflexivity].
Qed.

Example invalid_address_faults :
  abort two_processors (load_command 1%positive 3%positive 0) initial_state.
Proof.
  eapply CommandAbort; [reflexivity |].
  apply AbortLoad; [left; reflexivity | simpl; tauto | reflexivity].
Qed.

Example null_address_faults :
  abort two_processors
    (C.Prim (C.Common (S.Load 0 (EVal 0%Z))) (EVal 1%Z)) initial_state.
Proof.
  eapply CommandAbort; [reflexivity |].
  apply AbortLoad; [left; reflexivity | simpl; tauto | reflexivity].
Qed.

Example loop_can_choose_zero_iterations active body initial :
  steps active (C.Loop body) initial halt initial.
Proof.
  eapply StepsNext; [apply StepLoop |]. apply steps_one, StepChoiceLeft.
Qed.
