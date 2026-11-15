From Stdlib Require Import List ZArith.
From WMLR Require Import Expressions Languages Machine BufferRelations Separation OperationalSemantics
  ExecutionExamples Assertions AssertionSemantics PersistentAssertions Safety TemporalSafety
  InvariantFragment CellFamilies HeapExtension HeapExtensionFootprint DekkerSyntax
  BufferedPoolCandidate BufferedPoolAdequacy BufferedDekkerResources BufferedDekkerVerification BufferedDekkerProof.
Import ListNotations.

Definition dekker_pool_image := BD.only_image BDP.invariant.
Definition dekker_private_description := BD.Sep BDP.start0 BDP.start1.
Definition dekker_private_image := BD.only_image dekker_private_description.
Definition dekker_augmented := BD.mem (BD.join dekker_pool_image dekker_private_image).

Theorem buffered_dekker_augmented_all_runs s n last t final :
  execution two_processors n dekker_fenced s dekker_augmented last t final ->
  ~ abort two_processors last (State t final) /\
  (terminal last -> ~ (t 0%nat = 0%Z /\ t 1%nat = 0%Z)).
Proof.
  intros Hrun.
  assert (HP : persistent_models BufferedDekker.active s (BD.full dekker_private_image)
    (A.Spatial BufferedDekker.start0 BufferedDekker.start1)).
  { exact (BD.image_models dekker_private_description eq_refl _ (BD.only_image_in _) s). }
  assert (HJ : persistent_full_satisfies BufferedDekker.active s (BD.mem dekker_pool_image) BufferedDekker.invariant).
  { exists (BD.full dekker_pool_image); split; [reflexivity |].
    exact (BD.image_models BDP.invariant eq_refl _ (BD.only_image_in _) s). }
  assert (Hsp : memory_spatial (BD.mem dekker_pool_image)
    (resource_memory BufferedDekker.active (BD.full dekker_private_image)) dekker_augmented).
  { apply BD.join_spatial; reflexivity. }
  destruct (buffered_valid_adequacy _ _ _ _ _ buffered_dekker_invariant_fragment buffered_dekker_valid
    n s _ last t final _ _ HP HJ Hsp ltac:(intros i H; exact H) Hrun) as [Hsafe Hdone].
  split; [exact Hsafe |]. intros HT.
  destruct (Hdone HT) as (local & pool & Hsep & Hfree & Hinv & Hpost).
  eapply buffered_dekker_post_excludes_zero_zero; exact Hpost.
Qed.

Definition dekker_flags_image := BD.Image [(1%positive,0%Z);(2%positive,0%Z)] [] [].
Definition dekker_ghost_image := BD.Image
  [(3%positive,0%Z);(4%positive,0%Z);(5%positive,0%Z);(6%positive,0%Z);
   (7%positive,0%Z);(8%positive,0%Z);(9%positive,0%Z);(10%positive,0%Z);
   (11%positive,0%Z);(12%positive,0%Z);(13%positive,0%Z)] [] [].
Definition dekker_ghost_heap := cell_heap (BD.heap_cells dekker_ghost_image).

Lemma dekker_flags_memory : memory_equiv (BD.mem dekker_flags_image) initial_memory.
Proof.
  split.
  - intros loc; unfold BD.mem,dekker_flags_image,initial_memory,initial_heap; cbn;
      unfold heap_override,heap_update; destruct (Pos.eq_dec loc 1%positive), (Pos.eq_dec loc 2%positive); reflexivity.
  - split; [intros i; unfold BD.mem,dekker_flags_image; cbn;
      destruct (Pos.eq_dec i 1%positive), (Pos.eq_dec i 2%positive); reflexivity |intros; reflexivity].
Qed.

Lemma dekker_augmented_extension : heap_extension dekker_ghost_heap initial_memory dekker_augmented.
Proof.
  assert (HE : memory_equiv dekker_augmented (BD.mem (BD.join dekker_ghost_image dekker_flags_image))).
  { apply BD.image_eqb_spec; reflexivity. }
  destruct HE as [HH [HB HK]]; split.
  - intros loc; rewrite HH; change (cell_heap (BD.heap_cells dekker_ghost_image ++ BD.heap_cells dekker_flags_image) loc =
      heap_override dekker_ghost_heap (shared_heap initial_memory) loc).
    rewrite BD.heap_app; unfold heap_override,dekker_ghost_heap.
    pose proof (proj1 dekker_flags_memory loc) as HF.
    change (cell_heap (BD.heap_cells dekker_flags_image) loc = shared_heap initial_memory loc) in HF.
    rewrite HF; reflexivity.
  - split.
    + intros i; rewrite HB,BD.buffer_join.
      unfold BD.mem,dekker_ghost_image,dekker_flags_image; cbn;
        destruct (Pos.eq_dec i 1%positive), (Pos.eq_dec i 2%positive); reflexivity.
    + intros; reflexivity.
Qed.

Lemma dekker_program_accesses : accesses_within [EVal 1%Z; EVal 2%Z] dekker_fenced.
Proof. repeat split; cbn; auto. Qed.

(** The machine-facing theorem has no candidate definitions or ghost
    resources in its statement. Initial registers are completely arbitrary. *)
Theorem dekker_fenced_all_runs s n last t final :
  execution two_processors n dekker_fenced s initial_memory last t final ->
  ~ abort two_processors last (State t final) /\
  (terminal last -> ~ (t 0%nat = 0%Z /\ t 1%nat = 0%Z)).
Proof.
  intros Hrun.
  destruct (execution_heap_extension _ _ _ _ _ _ _ _ Hrun dekker_ghost_heap dekker_augmented
    dekker_augmented_extension) as (out & Hextended & HE).
  destruct (buffered_dekker_augmented_all_runs _ _ _ _ _ Hextended) as [Hsafe Hpost].
  split; [|exact Hpost]. intros Hbad; apply Hsafe.
  eapply (abort_heap_extension_within two_processors last (State t final) Hbad
    [EVal 1%Z;EVal 2%Z] dekker_ghost_heap out); [|exact HE |].
  - eapply execution_accesses_within; [exact Hrun |exact dekker_program_accesses].
  - intros e [<- |[<- |[]]] loc E; cbn in E; injection E as E; subst loc; reflexivity.
Qed.

Lemma finite_steps_execution active c initial last final : steps active c initial last final ->
  exists n, execution active n c (registers initial) (memory_state initial) last (registers final) (memory_state final).
Proof.
  intros Hrun; induction Hrun.
  - exists 0%nat; destruct initial; constructor.
  - destruct IHHrun as (n & Hn); exists (S n); destruct initial,middle;
      eapply ExecuteNext; eassumption.
Qed.

Theorem dekker_unfenced_zero_zero : exists n t final,
  execution two_processors n store_buffering initial_registers initial_memory halt t final /\
  t 0%nat = 0%Z /\ t 1%nat = 0%Z /\ (forall i, buffers final i = []).
Proof.
  destruct (finite_steps_execution _ _ _ _ _ store_buffering_trace) as (n & Hrun).
  exists n, after_both_loads, after_both_flushes; split; [exact Hrun |].
  split; [reflexivity |]. split; [reflexivity |apply store_buffering_final_buffers_empty].
Qed.

(** A terminating fenced run with results (0,1), complementing the
    universal exclusion theorem. No claim of fairness or total correctness. *)
Theorem dekker_fenced_terminates : exists t final,
  execution two_processors 13 dekker_fenced initial_registers initial_memory halt t final /\
  t 0%nat = 0%Z /\ t 1%nat = 1%Z.
Proof.
  set (m1 := enqueue initial_memory 1%positive 1%positive 1%Z).
  set (m2 := flush_write m1 1%positive 1%positive 1%Z []).
  set (m3 := enqueue m2 2%positive 2%positive 1%Z).
  set (m4 := flush_write m3 2%positive 2%positive 1%Z []).
  set (s1 := update initial_registers 0 0%Z).
  set (s2 := update s1 1 1%Z).
  exists s2,m4; split; [|split; reflexivity].
  eapply ExecuteNext with (t := initial_registers) (middle := m1).
  { apply StepParallelLeft,StepSeq; eapply StepPrimitive with (i:=1%positive); [reflexivity |].
    eapply PrimitiveStore with (previous:=0%Z); [left; reflexivity |reflexivity |reflexivity]. }
  eapply ExecuteNext with (t := initial_registers) (middle := m2).
  { apply StepFlush; eapply FlushWrite with (i:=1%positive); [left; reflexivity |intros H; exact H |reflexivity]. }
  eapply ExecuteNext; [apply StepParallelLeft,StepSeqDone |].
  eapply ExecuteNext.
  { apply StepParallelLeft,StepSeq; eapply StepPrimitive with (i:=1%positive); [reflexivity |].
    apply PrimitiveFence; [left; reflexivity |reflexivity]. }
  eapply ExecuteNext; [apply StepParallelLeft,StepSeqDone |].
  eapply ExecuteNext with (t := s1) (middle := m2).
  { apply StepParallelLeft; eapply StepPrimitive with (i:=1%positive); [reflexivity |].
    apply PrimitiveLoad; [left; reflexivity |intros H; exact H |reflexivity]. }
  eapply ExecuteNext; [apply StepParallelLeftDone |].
  eapply ExecuteNext with (t := s1) (middle := m3).
  { apply StepSeq; eapply StepPrimitive with (i:=2%positive); [reflexivity |].
    eapply PrimitiveStore with (previous:=0%Z); [right; reflexivity |reflexivity |reflexivity]. }
  eapply ExecuteNext; [apply StepSeqDone |].
  eapply ExecuteNext with (t := s1) (middle := m4).
  { apply StepFlush; eapply FlushWrite with (i:=2%positive); [right; reflexivity |intros H; exact H |reflexivity]. }
  eapply ExecuteNext.
  { apply StepSeq; eapply StepPrimitive with (i:=2%positive); [reflexivity |].
    apply PrimitiveFence; [right; reflexivity |reflexivity]. }
  eapply ExecuteNext; [apply StepSeqDone |].
  eapply ExecuteNext with (t := s2) (middle := m4).
  { eapply StepPrimitive with (i:=2%positive); [reflexivity |].
    apply PrimitiveLoad; [right; reflexivity |intros H; exact H |reflexivity]. }
  constructor.
Qed.
