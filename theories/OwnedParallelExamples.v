From Stdlib Require Import List ZArith.
From WMLR Require Import Expressions Languages Machine Separation RepairedSeparation
  GeneralizedFlushing OperationalSemantics ProgramSteps ExecutionExamples Assertions
  AssertionSemantics ConcreteAssertions PersistentAssertions Safety Specifications
  TemporalSafety RegionalResources InvariantFragment InvariantFragmentExamples
  OwnedSafety OwnedAdequacy OwnedResources OwnedRules OwnedAcceptance OwnedFraming
  OwnedInterference OwnedParallel.
Import ListNotations.

Theorem owned_parallel_acquire_store_valid mode :
  owned_valid two_processors mode acceptance_invariant
    (A.Spatial A.Emp acceptance_private_pre)
    (C.Parallel acceptance_acquire (store_command 2%positive 3%positive 9%Z))
    (A.Spatial
      (A.Temporal (A.Spatial (A.Lock (EVal 1%Z)) acceptance_invariant) (A.Barrier (EVal 1%Z)))
      acceptance_private_post).
Proof.
  apply owned_parallel_valid.
  - apply owned_lock_valid; [apply acceptance_two_active |constructor].
  - apply owned_private_store_valid.
  - split; intros x H Hmod; contradiction.
  - intros x H; contradiction.
  - intros x H; contradiction.
Qed.

(** Both finished-thread reductions retain the token and its cell as a
    spatial frame for the still-running private store. *)
Theorem owned_parallel_finished_left_valid mode :
  owned_valid two_processors mode acceptance_invariant
    (A.Spatial acceptance_holder_pre acceptance_private_pre)
    (C.Parallel halt (store_command 2%positive 3%positive 9%Z))
    (A.Spatial acceptance_holder_pre acceptance_private_post).
Proof.
  apply owned_parallel_valid; [apply owned_holder_skip_valid |apply owned_private_store_valid | | |];
    try (intros x H; contradiction).
  split; intros x H Hmod; contradiction.
Qed.

Theorem owned_parallel_finished_right_valid mode :
  owned_valid two_processors mode acceptance_invariant
    (A.Spatial acceptance_private_pre acceptance_holder_pre)
    (C.Parallel (store_command 2%positive 3%positive 9%Z) halt)
    (A.Spatial acceptance_private_post acceptance_holder_pre).
Proof.
  apply owned_parallel_valid; [apply owned_private_store_valid |apply owned_holder_skip_valid | | |];
    try (intros x H; contradiction).
  split; intros x H Hmod; contradiction.
Qed.

Definition parallel_acquire_initial := release acceptance_parallel_memory.

Lemma parallel_acquire_initial_spatial :
  memory_spatial (resource_memory two_processors checkpoint_full_cell)
    (resource_memory two_processors acceptance_private) parallel_acquire_initial.
Proof.
  split.
  - split.
    + intros address Hcell Hprivate.
      assert (Htwo : address = 2%positive).
      { exact (acceptance_cell_domain 2%positive 7%Z 1%positive (or_introl eq_refl) address Hcell). }
      assert (Hthree : address = 3%positive).
      { exact (acceptance_cell_domain 3%positive 3%Z 2%positive (or_intror eq_refl) address Hprivate). }
      congruence.
    + intros i H _; exact H.
  - split; [intros; reflexivity |]. split; [intros; constructor |].
    intros i; change (False <-> False \/ False); tauto.
Qed.

Theorem owned_parallel_acquire_store_enabled mode s :
  persistent_models two_processors s acceptance_private (A.Spatial A.Emp acceptance_private_pre) /\
  owned_environment two_processors mode acceptance_invariant s acceptance_private
    (resource_memory two_processors checkpoint_full_cell) (empty_resource_value two_processors)
    parallel_acquire_initial PoolFree /\
  program_step two_processors (AcquireAction 1%positive)
    (C.Parallel acceptance_acquire (store_command 2%positive 3%positive 9%Z))
    (State s parallel_acquire_initial)
    (C.Parallel halt (store_command 2%positive 3%positive 9%Z))
    (State s acceptance_parallel_memory) /\
  blocked acceptance_parallel_memory 2%positive /\
  program_step two_processors OrdinaryAction
    (C.Parallel halt (store_command 2%positive 3%positive 9%Z))
    (State s acceptance_parallel_memory) (C.Parallel halt halt)
    (State s acceptance_parallel_after).
Proof.
  split.
  - exists (bare_resource two_processors), acceptance_private; split; [apply spatial_empty_left |].
    split; [|apply acceptance_cell_models].
    split; [intros; reflexivity |]. split; [intros; reflexivity |intros i H; exact H].
  - split.
    + apply owned_empty_frame_intro.
      * exact (proj1 (proj2_sig checkpoint_full_cell)).
      * exact parallel_acquire_initial_spatial.
      * split; [intros i H; exact H |].
        exists checkpoint_full_cell; split; [reflexivity |apply checkpoint_full_cell_models].
    + split.
      * apply ProgramParallelLeft; eapply ProgramPrimitive with (p := C.Lock) (i := 1%positive); [reflexivity |].
        apply PrimitiveLock; [left; reflexivity |reflexivity |intros i H; exact H].
      * split; [split; [right; reflexivity |discriminate] |].
        apply ProgramParallelRight; eapply ProgramPrimitive with
          (p := C.Common (S.Store (EVal 3%Z) (EVal 9%Z))) (i := 2%positive); [reflexivity |].
        eapply PrimitiveStore with (previous := 3%Z); [right; reflexivity |reflexivity |reflexivity].
Qed.

(** A small assignment specification specifically for the register-update
    regression below. This does not supply the remaining general primitive
    rule suite or the dissertation's LOAD/STORE rules. *)
Definition parallel_assignment (actor : processor) x v :=
  C.Prim (C.Common (S.Assign x (EVal v))) (EVal (Z.pos actor)).
Definition parallel_assigned x v := A.And A.Emp (A.Pure (BEq (EVar x) (EVal v))).

Lemma owned_parallel_assignment_valid mode actor x v :
  two_processors actor ->
  owned_valid two_processors mode acceptance_invariant A.Emp
    (parallel_assignment actor x v) (parallel_assigned x v).
Proof.
  intros Hi s local HP n; destruct n; [exact I |]. intros later Hfuture.
  assert (HP' : persistent_models two_processors s later A.Emp).
  { eapply persistent_assertion_flushing_closed; eassumption. }
  split; [intros [annotation E]; discriminate E |].
  intros pool frame whole phase Henv; split.
  - intros Hfault; inversion Hfault; subst.
    match goal with H : primitive_abort _ _ _ _ |- _ => inversion H end.
  - intros action next t whole' Hstep; inversion Hstep; subst.
    match goal with E : eval_expr _ (EVal (Z.pos actor)) = Z.pos _ |- _ =>
      cbn in E; inversion E; subst end.
    match goal with H : primitive_step _ _ _ _ _ |- _ => inversion H; subst end.
    exists later, pool, phase; split.
    + eapply owned_environment_stack_agrees; [|exact Henv]. intros y Hy; contradiction.
    + split; [apply owned_update_identity |]. apply owned_done_safe.
      split; [exact HP' |]. change (Z.eqb (update s x v x) v = true).
      rewrite update_same; apply Z.eqb_refl.
Qed.

Theorem owned_parallel_registers_valid mode :
  owned_valid two_processors mode acceptance_invariant (A.Spatial A.Emp A.Emp)
    (C.Parallel (parallel_assignment 1%positive 0 7%Z) (parallel_assignment 2%positive 1 9%Z))
    (A.Spatial (parallel_assigned 0 7%Z) (parallel_assigned 1 9%Z)).
Proof.
  apply owned_parallel_valid.
  - apply owned_parallel_assignment_valid; left; reflexivity.
  - apply owned_parallel_assignment_valid; right; reflexivity.
  - split; intros x Hfv Hmod; cbn in Hfv, Hmod; intuition congruence.
  - intros x Hmod Hfv; contradiction.
  - intros x Hmod Hfv; contradiction.
Qed.

Theorem owned_parallel_registers_enabled mode s :
  let last := update (update s 0 7%Z) 1 9%Z in
  persistent_models two_processors s (bare_resource two_processors) (A.Spatial A.Emp A.Emp) /\
  owned_environment two_processors mode acceptance_invariant s (bare_resource two_processors)
    (resource_memory two_processors checkpoint_full_cell) (empty_resource_value two_processors)
    (resource_memory two_processors checkpoint_full_cell) PoolFree /\
  program_step two_processors OrdinaryAction
    (C.Parallel (parallel_assignment 1%positive 0 7%Z) (parallel_assignment 2%positive 1 9%Z))
    (State s (resource_memory two_processors checkpoint_full_cell))
    (C.Parallel halt (parallel_assignment 2%positive 1 9%Z))
    (State (update s 0 7%Z) (resource_memory two_processors checkpoint_full_cell)) /\
  program_step two_processors OrdinaryAction
    (C.Parallel halt (parallel_assignment 2%positive 1 9%Z))
    (State (update s 0 7%Z) (resource_memory two_processors checkpoint_full_cell))
    (C.Parallel halt halt) (State last (resource_memory two_processors checkpoint_full_cell)) /\
  last 0 = 7%Z /\ last 1 = 9%Z.
Proof.
  cbn zeta; split.
  - exists (bare_resource two_processors), (bare_resource two_processors).
    split; [apply spatial_empty_left |]. split;
      (split; [intros; reflexivity |]; split; [intros; reflexivity |intros i H; exact H]).
  - split.
    + apply owned_empty_frame_intro.
      * exact (proj1 (proj2_sig checkpoint_full_cell)).
      * exact (proj1 (spatial_empty_right (proj1_sig checkpoint_full_cell))).
      * split; [intros i H; exact H |].
        exists checkpoint_full_cell; split; [reflexivity |apply checkpoint_full_cell_models].
    + split.
      * apply ProgramParallelLeft; eapply ProgramPrimitive with
          (p := C.Common (S.Assign 0 (EVal 7%Z))) (i := 1%positive); [reflexivity |].
        apply PrimitiveAssign; left; reflexivity.
      * split.
        -- apply ProgramParallelRight; eapply ProgramPrimitive with
             (p := C.Common (S.Assign 1 (EVal 9%Z))) (i := 2%positive); [reflexivity |].
           apply PrimitiveAssign; right; reflexivity.
        -- split; reflexivity.
Qed.
