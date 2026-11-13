From Stdlib Require Import List ZArith.
From WMLR Require Import Expressions Languages Machine BufferRelations Separation
  RepairedSeparation GeneralizedFlushing OperationalSemantics ProgramSteps
  Assertions AssertionSemantics ConcreteAssertions PersistentAssertions PersistentRules
  Specifications Safety TemporalSafety RegionalResources OwnershipProtocol
  ExecutionExamples InvariantFragment InvariantFragmentExamples LockRepresentation
  OwnedSafety OwnedAdequacy OwnedResources OwnedRules OwnedAcceptance OwnedCalculus
  StrongTemporalCounterexample OwnedPointsToRules AssertionWriteExamples AssertionUnits.
Import ListNotations.

(** C1: assertion satisfiability is weaker than existence of an environment.
    With two processors, the two different lock atoms compose spatially,
    but their union blocks every processor and is not a complete lock. *)
Definition two_locks := A.Spatial (A.Lock (EVal 1%Z)) (A.Lock (EVal 2%Z)).

Definition both_blocked_resource : resource two_processors.
Proof.
  refine (exist _ (Generalized (Memory empty_heap empty_buffers two_processors) no_blocked) _).
  split; [split; [intros i H; exact H |intros; reflexivity] |].
  split; [intros i H; contradiction |intros; reflexivity].
Defined.

Lemma two_locks_inhabited s : persistent_models two_processors s both_blocked_resource two_locks.
Proof.
  exists (acquired_resource two_processors (bare_resource two_processors) 1%positive),
    (acquired_resource two_processors (bare_resource two_processors) 2%positive).
  split.
  - split.
    + split.
      * split.
        -- intros loc [[v H] |[i [v H]]] _; discriminate || contradiction.
        -- intros i [Hi Hne1] [_ Hne2]; destruct Hi; contradiction.
      * split; [intros; reflexivity |]. split; [intros; constructor |].
        intros i; change (two_processors i <->
          (two_processors i /\ i <> 1%positive) \/ (two_processors i /\ i <> 2%positive)).
        unfold two_processors; intuition congruence.
    + intros i; change (False <-> False \/ False); tauto.
  - split.
    + split; [intros; reflexivity |].
      split; [intros; reflexivity |split; [left; reflexivity |intros; reflexivity]].
    + split; [intros; reflexivity |].
      split; [intros; reflexivity |split; [right; reflexivity |intros; reflexivity]].
Qed.

Lemma two_locks_block_every_processor s local :
  persistent_models two_processors s local two_locks ->
  forall i, two_processors i -> blocked (resource_memory two_processors local) i.
Proof.
  intros (a & b & [[_ [_ [_ Hblocks]]] _] & [_ [_ [_ Hfirst]]] & [_ [_ [_ Hsecond]]]) i Hi.
  apply Hblocks; destruct Hi as [-> | ->].
  - right; apply Hsecond; split; [left; reflexivity |discriminate].
  - left; apply Hfirst; split; [right; reflexivity |discriminate].
Qed.

Lemma all_blocked_has_no_owned_environment mode invariant s local pool frame whole phase :
  (forall i, two_processors i -> blocked (resource_memory two_processors local) i) ->
  ~ owned_environment two_processors mode invariant s local pool frame whole phase.
Proof.
  intros Hlocal Henv.
  assert (Hwhole : forall i, two_processors i -> blocked whole i).
  { intros i Hi; apply (owned_blocked_union _ _ _ _ _ _ _ _ _ i Henv); auto. }
  pose proof (owned_pool_status _ _ _ _ _ _ _ _ _ Henv) as Hstatus.
  destruct phase as [|owner].
  - destruct Hstatus as [Hfree _]; apply (Hfree 1%positive),Hwhole; left; reflexivity.
  - destruct Hstatus as [[Hi Hheld] _].
    exact (proj2 (proj1 (Hheld owner) (Hwhole owner Hi)) eq_refl).
Qed.

Theorem owned_inhabited_but_environmentless_unlock_valid mode invariant post :
  owned_valid two_processors mode invariant two_locks acceptance_release post.
Proof.
  intros s local HP n; destruct n; [exact I |]. intros later Hfuture.
  assert (HP' : persistent_models two_processors s later two_locks).
  { eapply persistent_assertion_flushing_closed; eassumption. }
  split; [intros [annotation E]; discriminate E |].
  intros pool frame whole phase Henv; exfalso.
  eapply all_blocked_has_no_owned_environment;
    [eapply two_locks_block_every_processor; exact HP' |exact Henv].
Qed.

Theorem owned_universal_donation_obstruction_refuted :
  two_active_processors two_processors /\ invariant_fragment acceptance_invariant /\
  (forall s local, persistent_models two_processors s local acceptance_invariant ->
    exists loc value, shared_heap (resource_memory two_processors local) loc = Some value) /\
  (forall s, persistent_models two_processors s both_blocked_resource two_locks) /\
  owned_valid two_processors OverlapMode acceptance_invariant two_locks acceptance_release (A.Pure BFalse).
Proof.
  split; [apply acceptance_two_active |]. split; [constructor |]. split.
  - intros s local HC; destruct (writer_points_to_shape _ _ _ _ _ HC)
      as (loc & owner & E & Hi & Hheap & _).
    exists loc,7%Z; rewrite Hheap; apply heap_update_same.
  - split; [apply two_locks_inhabited |apply owned_inhabited_but_environmentless_unlock_valid].
Qed.

(** C2: the same inhabited release witness already separates the temporal
    frame rule from DJ validity; strong conjunction is not needed. *)
Theorem owned_disjoint_temporal_frame_invalid :
  ~ owned_valid two_processors DisjointMode stm_cell (A.Temporal stm_frame stm_pre)
    acceptance_release (A.Temporal stm_frame stm_post).
Proof.
  intros Hvalid.
  pose proof (Hvalid initial_registers (stm_holder [(1%positive,0%Z);(2%positive,0%Z)])
    (proj2 (stm_framed_precondition _)) 2) as Hsafe.
  destruct (owned_safe_program_step _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    Hsafe (stm_initial_environment _) (stm_release_step _))
    as (local' & pool' & phase' & Henv' & Hupdate & Hsafe').
  destruct (owned_action_transfer _ _ _ _ _ _ _ _ Hupdate) as [_ [-> _]].
  destruct (owned_empty_frame_elim _ _ _ _ _ _ _ _ Henv') as [Hsp [_ HJ]].
  destruct (stm_returned_local_shape _ _ _ Hsp HJ) as [Hheap Hbuffers].
  exact (stm_temporal_post_impossible _ _ _ Hheap Hbuffers
    (owned_safe_terminal _ _ _ _ _ _ _ _ Hsafe' ltac:(eexists; reflexivity))).
Qed.

Theorem owned_disjoint_temporal_frame_counterexample :
  two_active_processors two_processors /\ invariant_fragment stm_cell /\
  frame_variable_condition acceptance_release stm_frame /\
  owned_valid two_processors DisjointMode stm_cell stm_pre acceptance_release stm_post /\
  ~ owned_valid two_processors DisjointMode stm_cell (A.Temporal stm_frame stm_pre)
    acceptance_release (A.Temporal stm_frame stm_post).
Proof.
  split; [apply acceptance_two_active |]. split; [constructor |].
  split; [intros x H; contradiction |].
  split; [apply stm_unframed_release_valid |apply owned_disjoint_temporal_frame_invalid].
Qed.

(** C3: one acquisition already refutes soundness without the invariant
    restriction. Its postcondition requests an unearned foreign mark. *)
Definition all_processor_invariant := A.points_to (EVal 2%Z) (EVal 7%Z).
Definition all_processor_lock_post := A.Temporal
  (A.Spatial (A.Lock (EVal 1%Z)) all_processor_invariant) (A.Barrier (EVal 1%Z)).

Lemma all_processor_initial_environment mode s :
  owned_environment two_processors mode all_processor_invariant s (bare_resource two_processors)
    (resource_memory two_processors checkpoint_full_cell) (empty_resource_value two_processors)
    (resource_memory two_processors checkpoint_full_cell) PoolFree.
Proof.
  apply owned_empty_frame_intro.
  - exact (proj1 (proj2_sig checkpoint_full_cell)).
  - exact (proj1 (spatial_empty_right (proj1_sig checkpoint_full_cell))).
  - split; [intros i H; exact H |].
    exists checkpoint_full_cell; split; [reflexivity |apply assertion_full_cell_points_to].
Qed.

Lemma all_processor_lock_post_foreign_mark s local :
  persistent_models two_processors s local all_processor_lock_post -> complete (proj1_sig local) 2%positive.
Proof.
  intros (body & bar & [_ [_ [_ Houter]]] &
    (token & cell & [_ Hinner] & HL & HC) & HB).
  destruct (alternative_points_to_complete _ _ _ _ _ HC 2%positive) as [Hinactive |Hmark];
    [exfalso; apply Hinactive; right; reflexivity |].
  apply Houter; left; apply Hinner; right; exact Hmark.
Qed.

Theorem owned_all_processor_lock_invalid mode :
  ~ owned_valid two_processors mode all_processor_invariant A.Emp acceptance_acquire all_processor_lock_post.
Proof.
  intros Hvalid.
  assert (Hstep : program_step two_processors (AcquireAction 1%positive) acceptance_acquire
    (State initial_registers (resource_memory two_processors checkpoint_full_cell)) halt
    (State initial_registers (acquire two_processors (resource_memory two_processors checkpoint_full_cell) 1%positive))).
  { eapply ProgramPrimitive with (p := C.Lock) (i := 1%positive); [reflexivity |].
    apply PrimitiveLock; [left; reflexivity |reflexivity |intros i H; exact H]. }
  destruct (owned_safe_program_step _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    (Hvalid initial_registers (bare_resource two_processors) (bare_resource_models _ _) 2)
    (all_processor_initial_environment mode initial_registers) Hstep)
    as (local & pool & phase & Henv & Hupdate & Hsafe).
  pose proof (all_processor_lock_post_foreign_mark _ _
    (owned_safe_terminal _ _ _ _ _ _ _ _ Hsafe ltac:(eexists; reflexivity))) as Hmark.
  destruct (owned_mark_budget _ _ _ _ _ _ _ _ Hupdate _ Hmark) as [Hfalse |Hfalse];
    [exact Hfalse |discriminate Hfalse].
Qed.

Theorem owned_soundness_without_fragment_refuted mode :
  two_active_processors two_processors /\
  owned_derivation two_processors all_processor_invariant mode A.Emp acceptance_acquire all_processor_lock_post /\
  ~ owned_valid two_processors mode all_processor_invariant A.Emp acceptance_acquire all_processor_lock_post.
Proof.
  split; [apply acceptance_two_active |].
  split; [apply OwnedLock |apply owned_all_processor_lock_invalid].
Qed.

(** C4: a one-cell fragment invariant and a singleton processor domain.
    The concrete machine performs both acquisitions. The safety predicate
    rejects the second acquisition's held-to-held action, regardless of
    what successor resources the first step chooses. *)
Definition single_active (i : processor) : Prop := i = 1%positive.
Definition single_initial := Memory (heap_update empty_heap 2%positive 7%Z) empty_buffers no_blocked.
Definition single_pool : resource single_active.
Proof.
  refine (exist _ (Generalized single_initial single_active) _).
  split; [split; [intros i H; contradiction |intros; reflexivity] |].
  split; [intros i H; exact H |].
  intros Hnone loc; exfalso; apply (Hnone 1%positive); reflexivity.
Defined.

Definition single_lock_post := A.Temporal
  (A.Spatial (A.Lock (EVal 1%Z)) acceptance_invariant) (A.Barrier (EVal 1%Z)).
Definition double_acquire := C.Seq acceptance_acquire acceptance_acquire.
Definition double_acquire_post := A.Spatial single_lock_post single_lock_post.

Lemma single_pool_models s : persistent_models single_active s single_pool acceptance_invariant.
Proof.
  eapply writer_points_to_from_shape with (loc := 2%positive) (owner := 1%positive);
    [reflexivity |reflexivity |intros; reflexivity |intros; reflexivity
     |intros i H; exact H |reflexivity].
Qed.

Lemma single_initial_environment mode s :
  owned_environment single_active mode acceptance_invariant s (bare_resource single_active)
    single_initial (empty_resource_value single_active) single_initial PoolFree.
Proof.
  apply owned_empty_frame_intro.
  - exact (proj1 (proj2_sig single_pool)).
  - exact (proj1 (spatial_empty_right (proj1_sig single_pool))).
  - split; [intros i H; exact H |].
    exists single_pool; split; [reflexivity |apply single_pool_models].
Qed.

Theorem owned_singleton_double_acquire_derived mode :
  owned_derivation single_active acceptance_invariant mode A.Emp double_acquire double_acquire_post.
Proof.
  eapply OwnedSequence with (middle := single_lock_post); [apply OwnedLock |].
  eapply OwnedConsequence with
    (pre' := A.Spatial single_lock_post A.Emp) (post' := double_acquire_post).
  - intros s r H; apply (proj2 (assertion_unit_spatial_right _ _ _ _)),H.
  - apply OwnedFrameSP; [apply OwnedLock |intros x H; contradiction].
  - intros s r H; exact H.
Qed.

Lemma single_first_acquire_step s :
  program_step single_active (AcquireAction 1%positive) double_acquire (State s single_initial)
    (C.Seq halt acceptance_acquire) (State s (acquire single_active single_initial 1%positive)).
Proof.
  apply ProgramSeq; eapply ProgramPrimitive with (p := C.Lock) (i := 1%positive); [reflexivity |].
  apply PrimitiveLock; [reflexivity |reflexivity |intros i H; exact H].
Qed.

Lemma single_second_acquire_step s :
  program_step single_active (AcquireAction 1%positive) acceptance_acquire
    (State s (acquire single_active single_initial 1%positive)) halt
    (State s (acquire single_active (acquire single_active single_initial 1%positive) 1%positive)).
Proof.
  eapply ProgramPrimitive with (p := C.Lock) (i := 1%positive); [reflexivity |].
  apply PrimitiveLock; [reflexivity |reflexivity |apply singleton_acquire_still_free].
Qed.

Theorem single_double_acquire_execution s :
  execution single_active 3 double_acquire s single_initial halt s
    (acquire single_active (acquire single_active single_initial 1%positive) 1%positive).
Proof.
  eapply ExecuteNext; [eapply program_step_erases; apply single_first_acquire_step |].
  eapply ExecuteNext; [apply StepSeqDone |].
  eapply ExecuteNext; [eapply program_step_erases; apply single_second_acquire_step |constructor].
Qed.

Theorem owned_singleton_double_acquire_invalid mode post :
  ~ owned_valid single_active mode acceptance_invariant A.Emp double_acquire post.
Proof.
  intros Hvalid.
  destruct (owned_safe_program_step _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    (Hvalid initial_registers (bare_resource single_active) (bare_resource_models _ _) 3)
    (single_initial_environment mode initial_registers) (single_first_acquire_step _))
    as (local1 & pool1 & phase1 & Henv1 & Hupdate1 & Hsafe1).
  destruct (owned_action_transfer _ _ _ _ _ _ _ _ Hupdate1) as [_ [Ephase1 _]]; subst phase1.
  assert (Hnext : program_step single_active OrdinaryAction (C.Seq halt acceptance_acquire)
    (State initial_registers (acquire single_active single_initial 1%positive)) acceptance_acquire
    (State initial_registers (acquire single_active single_initial 1%positive))).
  { apply ProgramSeqDone. }
  destruct (owned_safe_program_step _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hsafe1 Henv1 Hnext)
    as (local2 & pool2 & phase2 & Henv2 & Hupdate2 & Hsafe2).
  destruct (owned_action_transfer _ _ _ _ _ _ _ _ Hupdate2) as [Ephase2 _]; subst phase2.
  destruct (owned_safe_program_step _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    Hsafe2 Henv2 (single_second_acquire_step _))
    as (local3 & pool3 & phase3 & Henv3 & Hupdate3 & Hsafe3).
  destruct (owned_action_transfer _ _ _ _ _ _ _ _ Hupdate3) as [Ephase3 _]; discriminate Ephase3.
Qed.

Theorem owned_soundness_without_two_processors_refuted mode :
  invariant_fragment acceptance_invariant /\
  owned_derivation single_active acceptance_invariant mode A.Emp double_acquire double_acquire_post /\
  ~ owned_valid single_active mode acceptance_invariant A.Emp double_acquire double_acquire_post.
Proof.
  split; [constructor |].
  split; [apply owned_singleton_double_acquire_derived |apply owned_singleton_double_acquire_invalid].
Qed.
