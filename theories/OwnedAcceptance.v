From Stdlib Require Import List ZArith.
From WMLR Require Import Expressions Languages Machine BufferRelations Separation
  RepairedSeparation GeneralizedFlushing FrameDecomposition OperationalSemantics
  ProgramSteps ExecutionExamples Assertions AssertionSemantics ConcreteAssertions
  PersistentAssertions Safety RepairedSafety TemporalSafety RegionalResources
  InvariantFragment InvariantFragmentExamples LockRepresentation HeapRules OwnershipHeap PrivateOwnership
  FlushAttribution OwnedSafety OwnedAdequacy OwnedResources.
Import ListNotations.

(** Fixed checkpoint-5 acceptance tests, before a calculus for owned_valid. *)
Definition acceptance_acquire := C.Prim C.Lock (EVal 1%Z).
Definition acceptance_release := C.Prim C.Unlock (EVal 1%Z).
Definition acceptance_invariant := writer_points_to (EVal 2%Z) (EVal 7%Z).
Definition acceptance_initial := resource_memory two_processors checkpoint_cell_and_pending.

Lemma acceptance_initial_environment mode s :
  owned_environment two_processors mode acceptance_invariant s
    (bare_resource two_processors) (resource_memory two_processors checkpoint_full_cell)
    checkpoint_foreign_pending acceptance_initial PoolFree.
Proof.
  constructor.
  - exact (proj1 (proj2_sig checkpoint_full_cell)).
  - exact (proj1 (proj2_sig checkpoint_cell_and_pending)).
  - exists checkpoint_foreign_pending; split; [apply repaired_empty_right |].
    exact (proj1 checkpoint_cell_pending_spatial).
  - destruct mode; [exact I |]. intros loc _ [[v H] |[i [v H]]]; discriminate || contradiction.
  - split; [intros i H; exact H |].
    exists checkpoint_full_cell; split; [reflexivity |apply checkpoint_full_cell_models].
Qed.

Definition acceptance_private_pre := writer_points_to (EVal 3%Z) (EVal 3%Z).
Definition acceptance_private_post := A.Temporal acceptance_private_pre
  (A.LeadsTo (EVal 3%Z) (EVal 2%Z) (EVal 9%Z)).
Definition acceptance_holder_pre := A.Spatial (A.Lock (EVal 1%Z)) acceptance_invariant.

Theorem owned_private_store_valid mode :
  owned_valid two_processors mode acceptance_invariant acceptance_private_pre
    (store_command 2%positive 3%positive 9%Z) acceptance_private_post.
Proof.
  intros s local HP n; destruct n; [exact I |]. intros later Hfuture.
  assert (HP' : persistent_models two_processors s later acceptance_private_pre).
  { eapply persistent_assertion_flushing_closed; eassumption. }
  destruct (writer_points_to_shape _ _ _ _ _ HP')
    as (loc & writer & Eloc & Hwriter & Hheap & Hbuffers & Hfree & Hmark).
  cbn in Eloc; injection Eloc as Eloc; subst loc.
  assert (Hcell : shared_heap (resource_memory two_processors later) 3%positive = Some 3%Z).
  { rewrite Hheap; apply heap_update_same. }
  split; [intros [annotation H]; discriminate |].
  intros pool frame whole phase Henv; split.
  - intros Hfault; inversion Hfault; subst.
    match goal with E : eval_expr _ (EVal 2%Z) = Z.pos _ |- _ => cbn in E; inversion E; subst end.
    match goal with H : primitive_abort _ _ _ _ |- _ => inversion H; subst end.
    pose proof (framed_cell_read two_processors pool (resource_memory two_processors frame)
      (resource_memory two_processors later) whole 2%positive 3%positive 3%Z
      (or_intror eq_refl) (owned_environment_as_framed _ _ _ _ _ _ _ _ _ Henv)
      Hcell (Hbuffers 2%positive)) as Hread.
    cbn [eval_expr] in *; congruence.
  - intros action next t whole' Hstep; inversion Hstep; subst.
    match goal with E : eval_expr _ (EVal 2%Z) = Z.pos _ |- _ => cbn in E; inversion E; subst end.
    match goal with H : primitive_step _ _ _ _ _ |- _ => inversion H; subst end.
    match goal with E : eval_expr _ (EVal 3%Z) = Z.pos _ |- _ => cbn in E; inversion E; subst end.
    exists (owned_enqueue_resource two_processors later 2%positive 3%positive 9%Z (or_intror eq_refl)),
      pool, phase; split.
    + eapply owned_environment_enqueue; eassumption.
    + split; [eapply owned_enqueue_update; exact Hcell |].
      apply owned_done_safe, writer_cell_enqueue_post, HP'.
Qed.

Theorem owned_holder_skip_valid mode :
  owned_valid two_processors mode acceptance_invariant acceptance_holder_pre halt acceptance_holder_pre.
Proof. intros s local HP n; apply owned_done_safe, HP. Qed.

Lemma acceptance_two_active : two_active_processors two_processors.
Proof. exists 1%positive, 2%positive; split; [left; reflexivity |].
  split; [right; reflexivity |discriminate]. Qed.

Definition acceptance_donation_invariant := A.Or A.Emp acceptance_invariant.

Theorem owned_disjoint_donation_valid :
  owned_valid two_processors DisjointMode acceptance_donation_invariant acceptance_holder_pre
    acceptance_release A.Emp.
Proof.
  intros s local HP n; destruct n; [exact I |]. intros later Hfuture.
  assert (HP' : persistent_models two_processors s later acceptance_holder_pre).
  { eapply persistent_assertion_flushing_closed; eassumption. }
  destruct (owned_lock_cell_shape _ _ _ _ _ _ HP') as [Hheap [Hbuffers Hheld]].
  assert (HJ : persistent_full_satisfies two_processors s
    (release (resource_memory two_processors later)) acceptance_donation_invariant).
  { pose (returned := exist _ _ (full_memory_valid_with_processor two_processors 1%positive
      (release (resource_memory two_processors later)) (or_introl eq_refl)
      (release_well_formed _ _ (proj1 (proj2_sig later))))).
    exists returned; split; [reflexivity |]. right.
    eapply writer_points_to_from_shape with (loc := 2%positive) (owner := 1%positive).
    - reflexivity.
    - left; reflexivity.
    - exact Hheap.
    - exact Hbuffers.
    - intros i H; exact H.
    - left; reflexivity. }
  split; [intros [annotation H]; discriminate |].
  intros pool frame whole phase Henv; split.
  - intros Hfault; inversion Hfault; subst.
    match goal with H : primitive_abort _ _ _ _ |- _ => inversion H end.
  - intros action next t whole' Hstep; inversion Hstep; subst.
    match goal with E : eval_expr _ (EVal 1%Z) = Z.pos _ |- _ => cbn in E; inversion E; subst end.
    match goal with H : primitive_step _ _ _ _ _ |- _ => inversion H; subst end.
    destruct (owned_disjoint_donation_environment _ _ _ _ _ _ _ _ _
      acceptance_two_active Henv Hheld HJ) as [Henv' Hupdate].
    exists (bare_resource two_processors), (release (resource_memory two_processors later)), PoolFree.
    split; [exact Henv' |]. split; [exact Hupdate |].
    apply owned_done_safe, bare_resource_models.
Qed.

Definition acceptance_cell (loc : location) (v : value) writer (Hi : two_processors writer)
    : resource two_processors.
Proof.
  refine (exist _ (Generalized (Memory (heap_update empty_heap loc v) empty_buffers no_blocked)
    (fun i => i = writer)) _).
  split; [split; [intros i H; contradiction |intros; reflexivity] |].
  split; [intros i ->; exact Hi |].
  intros Hnone address; exfalso; apply (Hnone writer); reflexivity.
Defined.

Lemma acceptance_cell_models s loc v writer Hi :
  persistent_models two_processors s (acceptance_cell loc v writer Hi)
    (writer_points_to (EVal (Z.pos loc)) (EVal v)).
Proof.
  eapply writer_points_to_from_shape with (loc := loc) (owner := writer);
    [reflexivity |exact Hi |intros; reflexivity |intros; reflexivity |intros i H; exact H |reflexivity].
Qed.

Definition acceptance_holder := acquired_resource two_processors
  (acceptance_cell 2%positive 7%Z 1%positive (or_introl eq_refl)) 1%positive.
Definition acceptance_stale := acceptance_cell 2%positive 5%Z 1%positive (or_introl eq_refl).
Definition acceptance_private := acceptance_cell 3%positive 3%Z 2%positive (or_intror eq_refl).

Lemma acceptance_holder_models s :
  persistent_models two_processors s acceptance_holder acceptance_holder_pre.
Proof.
  apply acquire_marked_payload; [left; reflexivity |intros i H; exact H |apply acceptance_cell_models].
Qed.

Lemma acceptance_overlap_environment s :
  owned_environment two_processors OverlapMode acceptance_donation_invariant s
    acceptance_holder empty_memory acceptance_stale
    (resource_memory two_processors acceptance_holder) (PoolHeld 1%positive).
Proof.
  constructor.
  - exact (proj1 (empty_generalized_well_formed two_processors)).
  - exact (proj1 (proj2_sig acceptance_holder)).
  - exists acceptance_holder; split.
    + split.
      * split.
        -- split; [intros i H; contradiction |]. split;
             [intros i _ loc [v H] |intros i j _ _ _ loc [v H]]; contradiction.
        -- split.
           ++ intros loc; change (heap_update empty_heap 2%positive 7%Z loc =
                heap_override (heap_update empty_heap 2%positive 5%Z)
                  (heap_update empty_heap 2%positive 7%Z) loc).
              unfold heap_override, heap_update, empty_heap; destruct (Pos.eq_dec loc 2%positive); reflexivity.
           ++ split; [intros i; constructor |].
              intros i; change (blocked_except two_processors 1%positive i <->
                False \/ blocked_except two_processors 1%positive i); tauto.
      * intros i; change (i = 1%positive <-> i = 1%positive \/ i = 1%positive); tauto.
    + exact (proj1 (spatial_empty_left (proj1_sig acceptance_holder))).
  - exact I.
  - split; [split; [left; reflexivity |intros i; reflexivity] |reflexivity].
Qed.

Theorem owned_overlap_donation_invalid :
  ~ owned_valid two_processors OverlapMode acceptance_donation_invariant acceptance_holder_pre
    acceptance_release A.Emp.
Proof.
  intros Hvalid; pose proof (Hvalid initial_registers acceptance_holder
    (acceptance_holder_models _) 2) as Hsafe.
  assert (Hstep : program_step two_processors (ReleaseAction 1%positive) acceptance_release
    (State initial_registers (resource_memory two_processors acceptance_holder)) halt
    (State initial_registers (release (resource_memory two_processors acceptance_holder)))).
  { eapply ProgramPrimitive with (p := C.Unlock) (i := 1%positive); [reflexivity |].
    apply PrimitiveUnlock; [left; reflexivity |reflexivity |].
    split; [left; reflexivity |intros i; reflexivity]. }
  destruct (owned_safe_program_step _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    Hsafe (acceptance_overlap_environment _) Hstep)
    as (local' & pool' & phase' & Henv' & Hupdate & Hsafe').
  destruct (owned_safe_terminal _ _ _ _ _ _ _ _ Hsafe' ltac:(eexists; reflexivity))
    as [Hempty _].
  destruct Henv' as [_ _ [combined [[[_ [Hheap _]] _] [_ [Hwhole _]]]] _ _].
  assert (Hstale : shared_heap (resource_memory two_processors combined) 2%positive = Some 5%Z).
  { rewrite Hheap; unfold heap_override; rewrite Hempty; reflexivity. }
  specialize (Hwhole 2%positive); unfold heap_override in Hwhole.
  fold (resource_memory two_processors combined) in Hwhole; rewrite Hstale in Hwhole.
  discriminate Hwhole.
Qed.

Theorem owned_foreign_barrier_invalid mode :
  ~ owned_valid two_processors mode acceptance_invariant A.Emp
      (C.Seq acceptance_acquire acceptance_release) (A.Barrier (EVal 2%Z)).
Proof.
  intros Hvalid.
  pose proof (Hvalid initial_registers (bare_resource two_processors)
    (bare_resource_models _ _) 4) as Hsafe.
  assert (Hfirst : program_step two_processors (AcquireAction 1%positive)
    (C.Seq acceptance_acquire acceptance_release) (State initial_registers acceptance_initial)
    (C.Seq halt acceptance_release)
    (State initial_registers (acquire two_processors acceptance_initial 1%positive))).
  { apply ProgramSeq; eapply ProgramPrimitive with (p := C.Lock) (i := 1%positive); [reflexivity |].
    apply PrimitiveLock; [left; reflexivity |reflexivity |intros i H; exact H]. }
  destruct (owned_safe_program_step _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    Hsafe (acceptance_initial_environment mode initial_registers) Hfirst)
    as (local1 & pool1 & phase1 & Henv1 & Hupdate1 & Hsafe1).
  assert (Hnext : program_step two_processors OrdinaryAction
    (C.Seq halt acceptance_release)
    (State initial_registers (acquire two_processors acceptance_initial 1%positive))
    acceptance_release
    (State initial_registers (acquire two_processors acceptance_initial 1%positive))).
  { constructor. }
  destruct (owned_safe_program_step _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hsafe1 Henv1 Hnext)
    as (local2 & pool2 & phase2 & Henv2 & Hupdate2 & Hsafe2).
  assert (Hlast : program_step two_processors (ReleaseAction 1%positive)
    acceptance_release
    (State initial_registers (acquire two_processors acceptance_initial 1%positive))
    halt (State initial_registers (release (acquire two_processors acceptance_initial 1%positive)))).
  { eapply ProgramPrimitive with (p := C.Unlock) (i := 1%positive); [reflexivity |].
    apply PrimitiveUnlock; [left; reflexivity |reflexivity |].
    split; [left; reflexivity |intros i; reflexivity]. }
  destruct (owned_safe_program_step _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hsafe2 Henv2 Hlast)
    as (local3 & pool3 & phase3 & Henv3 & Hupdate3 & Hsafe3).
  pose proof (owned_safe_terminal _ _ _ _ _ _ _ _ Hsafe3 ltac:(eexists; reflexivity)) as Hbar.
  destruct Hbar as [_ [Hinactive |Hmark]]; [apply Hinactive; right; reflexivity |].
  destruct (owned_mark_budget _ _ _ _ _ _ _ _ Hupdate3 _ Hmark) as [Hmark2 |Hbad];
    [|discriminate Hbad].
  destruct (owned_mark_budget _ _ _ _ _ _ _ _ Hupdate2 _ Hmark2) as [Hmark1 |Hbad];
    [|contradiction].
  destruct (owned_mark_budget _ _ _ _ _ _ _ _ Hupdate1 _ Hmark1) as [Hbad |Hbad];
    [contradiction |discriminate Hbad].
Qed.

Lemma owned_environment_local_blocks active mode invariant s local pool frame whole phase i :
  owned_environment active mode invariant s local pool frame whole phase ->
  blocked (resource_memory active local) i -> blocked whole i.
Proof.
  intros [_ _ [combined [[[_ [_ [_ Hinner]]] _] [_ [_ [_ Houter]]]]] _ _] H.
  apply Houter; right; apply Hinner; right; exact H.
Qed.

Lemma owned_environment_free_local active mode invariant s local pool frame whole phase :
  owned_environment active mode invariant s local pool frame whole phase ->
  lock_free whole -> lock_free (resource_memory active local).
Proof.
  intros Henv Hfree i H; apply (Hfree i).
  eapply owned_environment_local_blocks; eassumption.
Qed.

Theorem owned_held_reacquire_safe active mode invariant n s local owner post :
  two_active_processors active -> lock_held active (resource_memory active local) owner ->
  owned_safe active mode invariant n (C.Prim C.Lock (EVal (Z.pos owner))) s local post.
Proof.
  intros Hdomain Hheld; destruct n; [exact I |].
  intros later Hfuture; split; [intros [annotation H]; discriminate |].
  assert (Hlater : lock_held active (resource_memory active later) owner).
  { destruct Hheld as [Hi Hblocks]; split; [exact Hi |].
    intros i; rewrite <- (resource_future_blocks _ _ _ Hfuture i); apply Hblocks. }
  intros pool frame whole phase Henv; split.
  - intros Hfault; inversion Hfault; subst.
    match goal with H : primitive_abort _ _ _ _ |- _ => inversion H end.
  - intros action next t whole' Hstep; inversion Hstep; subst.
    match goal with H : primitive_step _ _ _ _ _ |- _ => inversion H; subst end.
    destruct Hdomain as (first & second & Hfirst & Hsecond & Hne).
    exfalso; eapply two_processors_separate_free_held; [exact Hfirst |exact Hsecond |exact Hne | |exact Hlater].
    eapply owned_environment_free_local; eassumption.
Qed.

Lemma held_empty_owner_no_flush active owner m :
  lock_held active m owner -> buffers m owner = [] -> forall m', ~ flush active m m'.
Proof.
  intros [_ Hblocks] Hempty m' Hflush; inversion Hflush; subst.
  destruct (Pos.eq_dec i owner) as [-> |Hne].
  - congruence.
  - match goal with Hlive : ~ blocked m i |- _ => apply Hlive end.
    apply Hblocks; auto.
Qed.

Theorem double_acquire_stuck active owner s m :
  two_active_processors active -> active owner -> lock_free m -> buffers m owner = [] ->
  let lock := C.Prim C.Lock (EVal (Z.pos owner)) in
  let held := acquire active m owner in
  steps active (C.Seq lock lock) (State s m) lock (State s held) /\
  ~ abort active lock (State s held) /\
  (forall next final, ~ step active lock (State s held) next final).
Proof.
  intros Hdomain Hactive Hfree Hempty; cbn zeta.
  assert (Hheld : lock_held active (acquire active m owner) owner).
  { split; [exact Hactive |intros i; reflexivity]. }
  split.
  - eapply StepsNext; [apply StepSeq; eapply StepPrimitive; [reflexivity |apply PrimitiveLock; eassumption] |].
    eapply StepsNext; [apply StepSeqDone |constructor].
  - split.
    + intros Hfault; inversion Hfault; subst.
      match goal with H : primitive_abort _ _ _ _ |- _ => inversion H end.
    + intros next final Hstep; inversion Hstep; subst.
      * match goal with H : primitive_step _ _ _ _ _ |- _ => inversion H; subst end.
        destruct Hdomain as (first & second & Hfirst & Hsecond & Hne).
        eapply (two_processors_separate_free_held active first second
          (acquire active m owner) owner Hfirst Hsecond Hne); [assumption |exact Hheld].
      * eapply held_empty_owner_no_flush; [exact Hheld |exact Hempty |eassumption].
Qed.

Lemma acceptance_cell_domain loc v writer Hi address :
  memory_domain (resource_memory two_processors (acceptance_cell loc v writer Hi)) address -> address = loc.
Proof.
  intros [[w Hheap] |[i [w Hbuffer]]].
  - change (heap_update empty_heap loc v address = Some w) in Hheap.
    unfold heap_update, empty_heap in Hheap; destruct (Pos.eq_dec address loc); [assumption |discriminate].
  - change (In (address,w) []) in Hbuffer; contradiction.
Qed.

Definition acceptance_parallel_memory := Memory
  (heap_override (shared_heap (resource_memory two_processors acceptance_holder))
    (shared_heap (resource_memory two_processors acceptance_private)))
  empty_buffers (blocked_except two_processors 1%positive).

Definition acceptance_private_after := owned_enqueue_resource two_processors acceptance_private
  2%positive 3%positive 9%Z (or_intror eq_refl).
Definition acceptance_parallel_after := enqueue acceptance_parallel_memory 2%positive 3%positive 9%Z.

Lemma acceptance_parallel_spatial :
  memory_spatial (resource_memory two_processors acceptance_holder)
    (resource_memory two_processors acceptance_private) acceptance_parallel_memory.
Proof.
  split.
  - split.
    + intros address Hholder Hprivate.
      assert (Htwo : address = 2%positive).
      { exact (acceptance_cell_domain 2%positive 7%Z 1%positive (or_introl eq_refl) address Hholder). }
      assert (Hthree : address = 3%positive).
      { exact (acceptance_cell_domain 3%positive 3%Z 2%positive (or_intror eq_refl) address Hprivate). }
      congruence.
    + intros i _ H; exact H.
  - split; [intros; reflexivity |]. split; [intros; constructor |].
    intros i; change (blocked_except two_processors 1%positive i <->
      blocked_except two_processors 1%positive i \/ False); tauto.
Qed.

Lemma acceptance_parallel_held : lock_held two_processors acceptance_parallel_memory 1%positive.
Proof. split; [left; reflexivity |intros i; reflexivity]. Qed.

Lemma acceptance_parallel_after_spatial :
  memory_spatial (resource_memory two_processors acceptance_holder)
    (resource_memory two_processors acceptance_private_after) acceptance_parallel_after.
Proof.
  apply spatial_enqueue_right; [exact acceptance_parallel_spatial |].
  left; exists 3%Z; reflexivity.
Qed.

Theorem owned_foreign_holder_store_witness mode s :
  persistent_models two_processors s acceptance_holder acceptance_holder_pre /\
  persistent_models two_processors s acceptance_private acceptance_private_pre /\
  owned_environment two_processors mode acceptance_invariant s acceptance_holder empty_memory
    acceptance_private acceptance_parallel_memory (PoolHeld 1%positive) /\
  owned_environment two_processors mode acceptance_invariant s acceptance_private empty_memory
    acceptance_holder acceptance_parallel_memory (PoolHeld 1%positive) /\
  blocked acceptance_parallel_memory 2%positive /\
  program_step two_processors OrdinaryAction (store_command 2%positive 3%positive 9%Z)
    (State s acceptance_parallel_memory) halt (State s acceptance_parallel_after) /\
  owned_environment two_processors mode acceptance_invariant s acceptance_holder empty_memory
    acceptance_private_after acceptance_parallel_after (PoolHeld 1%positive) /\
  owned_environment two_processors mode acceptance_invariant s acceptance_private_after empty_memory
    acceptance_holder acceptance_parallel_after (PoolHeld 1%positive) /\
  persistent_models two_processors s acceptance_private_after acceptance_private_post.
Proof.
  split; [apply acceptance_holder_models |].
  split; [apply acceptance_cell_models |].
  split.
  - apply owned_held_spatial_environment; [apply memory_spatial_comm, acceptance_parallel_spatial |exact acceptance_parallel_held].
  - split.
    + apply owned_held_spatial_environment; [exact acceptance_parallel_spatial |exact acceptance_parallel_held].
    + split; [split; [right; reflexivity |discriminate] |]. split.
      * eapply ProgramPrimitive with (p := C.Common (S.Store (EVal 3%Z) (EVal 9%Z))) (i := 2%positive);
          [reflexivity |].
        eapply PrimitiveStore with (previous := 3%Z); [right; reflexivity |reflexivity |reflexivity].
      * split.
        -- apply owned_held_spatial_environment;
             [apply memory_spatial_comm, acceptance_parallel_after_spatial |exact acceptance_parallel_held].
        -- split.
           ++ apply owned_held_spatial_environment;
                [exact acceptance_parallel_after_spatial |exact acceptance_parallel_held].
           ++ apply writer_cell_enqueue_post, acceptance_cell_models.
Qed.

Theorem owned_foreign_holder_both_safe mode s n :
  owned_safe two_processors mode acceptance_invariant n halt s acceptance_holder acceptance_holder_pre /\
  owned_safe two_processors mode acceptance_invariant n (store_command 2%positive 3%positive 9%Z)
    s acceptance_private acceptance_private_post /\
  owned_safe two_processors mode acceptance_invariant n halt s acceptance_private_after acceptance_private_post.
Proof.
  split; [apply owned_done_safe, acceptance_holder_models |]. split.
  - apply owned_private_store_valid, acceptance_cell_models.
  - apply owned_done_safe, writer_cell_enqueue_post, acceptance_cell_models.
Qed.

(** The local future exists although this exact flush is blocked in the
    machine by the owner's token in the frame. Safety still covers the future. *)
Theorem owned_blocked_local_future_regression mode s :
  exists later : resource two_processors,
    resource_future two_processors acceptance_private_after later /\
    (forall n, owned_safe two_processors mode acceptance_invariant n halt s later acceptance_private_post) /\
    (forall whole', ~ flush_at two_processors 2%positive acceptance_parallel_after whole').
Proof.
  assert (Hflush : flush_at two_processors 2%positive (resource_memory two_processors acceptance_private_after)
    (flush_write (resource_memory two_processors acceptance_private_after) 2%positive 3%positive 9%Z [])).
  { constructor; [right; reflexivity |intros H; exact H |reflexivity]. }
  destruct (indexed_flush_resource _ _ _ _ Hflush) as (later & Ememory & Hstep & Hmarks).
  assert (Hfuture : resource_future two_processors acceptance_private_after later)
    by (apply generalized_future_one, Hstep).
  exists later; split; [exact Hfuture |]. split.
  - intros n; eapply owned_safe_future; [exact Hfuture |].
    apply owned_done_safe, writer_cell_enqueue_post, acceptance_cell_models.
  - intros whole' Hmachine; inversion Hmachine; subst.
    match goal with Hlive : ~ blocked acceptance_parallel_after 2%positive |- _ => apply Hlive end.
    split; [right; reflexivity |discriminate].
Qed.

Definition acceptance_split_local : resource SplitLockWitness.active :=
  exist _ _ (proj1 SplitLockWitness.fragments_well_formed).
Definition acceptance_split_frame : resource SplitLockWitness.active :=
  exist _ _ (proj2 SplitLockWitness.fragments_well_formed).

Theorem owned_split_token_not_vacuous mode invariant s post :
  owned_environment SplitLockWitness.active mode invariant s acceptance_split_local empty_memory
    acceptance_split_frame SplitLockWitness.whole (PoolHeld 1%positive) /\
  ~ owned_safe SplitLockWitness.active mode invariant 1
      (C.Prim (C.Common (S.Assert BFalse)) (EVal 1%Z)) s acceptance_split_local post.
Proof.
  assert (Henv : owned_environment SplitLockWitness.active mode invariant s acceptance_split_local
    empty_memory acceptance_split_frame SplitLockWitness.whole (PoolHeld 1%positive)).
  { apply owned_held_spatial_environment; [|exact SplitLockWitness.whole_held].
    apply memory_spatial_comm; exact (proj1 SplitLockWitness.fragments_compose). }
  split; [exact Henv |]. intros Hsafe.
  apply (owned_safe_no_abort _ _ _ _ _ _ _ _ _ _ _ _ Hsafe Henv).
  eapply CommandAbort; [reflexivity |apply SplitLockWitness.failing_assert_enabled].
Qed.
