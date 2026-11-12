From Stdlib Require Import List ZArith.
From WMLR Require Import Expressions Languages Machine BufferRelations Separation OperationalSemantics
  ProgramSteps ExecutionExamples Assertions AssertionSemantics ConcreteAssertions PersistentAssertions Safety
  TemporalSafety RegionalResources InvariantFragment InvariantFragmentExamples PrivateOwnership
  OwnedSafety OwnedAdequacy OwnedResources OwnedAcceptance OwnedContainerEntailments OwnedContainer
  OwnedCalculus OwnedContainerDerivation.
Import ListNotations.

Definition container_pool_memory value := Memory
  (heap_update (heap_update empty_heap 2%positive value) 1%positive 1%Z) empty_buffers no_blocked.
Definition container_full_pool (value : Z) : resource two_processors.
Proof.
  refine (exist _ (Generalized (container_pool_memory value) two_processors) _).
  split; [split; [intros i H; contradiction |intros; reflexivity] |].
  split; [intros i H; exact H |intros Hnone address; exfalso; apply (Hnone 1%positive); left; reflexivity].
Defined.

Lemma container_full_pool_models s value :
  persistent_models two_processors s (container_full_pool value) container_invariant.
Proof.
  pose (flag := container_heap_resource two_processors (container_full_pool value) 1%positive (or_introl eq_refl) 1%positive 1%Z).
  pose (item := container_heap_resource two_processors (container_full_pool value) 1%positive (or_introl eq_refl) 2%positive value).
  right; exists flag,item; split.
  - split.
    + split.
      * split; [|intros i H _; exact H]. intros loc HF HX.
        pose proof (container_heap_domain _ _ _ _ _ _ _ HF) as EF.
        pose proof (container_heap_domain _ _ _ _ _ _ _ HX) as EX; congruence.
      * split.
        -- intros loc; change (heap_update (heap_update empty_heap 2%positive value) 1%positive 1%Z loc =
            heap_override (heap_update empty_heap 1%positive 1%Z) (heap_update empty_heap 2%positive value) loc).
           unfold heap_override, heap_update; destruct (Pos.eq_dec loc 1%positive), (Pos.eq_dec loc 2%positive); subst; try congruence; reflexivity.
        -- split; [intros i; constructor |intros i; cbn; unfold no_blocked; tauto].
    + intros i; change (two_processors i <-> two_processors i \/ two_processors i); tauto.
  - split; [apply container_heap_models |apply container_cell_some with (value := value), container_heap_models].
Qed.

Definition container_initial := Memory (shared_heap (container_pool_memory 7%Z))
  (buffer_update empty_buffers 2%positive [(3%positive,17%Z)]) no_blocked.
Definition container_first_held := acquire two_processors container_initial 1%positive.
Definition container_remove_pending := enqueue container_first_held 1%positive 1%positive 0%Z.
Definition container_remove_flushed := flush_write container_remove_pending 1%positive 1%positive 0%Z [].
Definition container_removed := release container_remove_flushed.
Definition container_private_pending := enqueue container_removed 1%positive 2%positive 9%Z.
Definition container_private_flushed := flush_write container_private_pending 1%positive 2%positive 9%Z [].
Definition container_second_held := acquire two_processors container_private_flushed 1%positive.
Definition container_return_pending := enqueue container_second_held 1%positive 1%positive 1%Z.
Definition container_return_flushed := flush_write container_return_pending 1%positive 1%positive 1%Z [].
Definition container_final := release container_return_flushed.

Lemma container_initial_split :
  memory_spatial (container_pool_memory 7%Z) (resource_memory two_processors checkpoint_foreign_pending) container_initial.
Proof.
  split.
  - split; [|intros i H _; exact H]. intros loc Hpool Hforeign.
    destruct Hforeign as [[v H] |[i [v H]]]; [discriminate |].
    change (In (loc,v) (buffer_update empty_buffers 2%positive [(3%positive,17%Z)] i)) in H.
    unfold buffer_update in H; destruct (Pos.eq_dec i 2%positive); [|contradiction].
    destruct H as [E |H]; [inversion E; subst |contradiction].
    destruct Hpool as [[w H] |[j [w H]]]; discriminate || contradiction.
  - split; [intros loc; reflexivity |]. split; [intros i; apply interleaves_app |intros i; cbn; unfold no_blocked; tauto].
Qed.

Theorem owned_container_initial s :
  persistent_models two_processors s checkpoint_foreign_pending container_foreign /\
  persistent_full_satisfies two_processors s (container_pool_memory 7%Z) container_invariant /\
  owned_environment two_processors DisjointMode container_invariant s checkpoint_foreign_pending
    (container_pool_memory 7%Z) (empty_resource_value two_processors) container_initial PoolFree /\
  shared_heap (container_pool_memory 7%Z) 1%positive = Some 1%Z /\
  shared_heap (container_pool_memory 7%Z) 2%positive = Some 7%Z /\
  lock_free container_initial.
Proof.
  assert (HP : persistent_models two_processors s checkpoint_foreign_pending container_foreign).
  { split; [right; reflexivity |left]. split; [intros; reflexivity |].
    split; [intros; reflexivity |intros i H; contradiction]. }
  assert (HJ : persistent_full_satisfies two_processors s (container_pool_memory 7%Z) container_invariant).
  { exists (container_full_pool 7%Z); split; [reflexivity |apply container_full_pool_models]. }
  split; [exact HP |]. split; [exact HJ |]. split.
  - apply owned_empty_frame_intro.
    + exact (proj1 (proj2_sig (container_full_pool 7%Z))).
    + apply container_initial_split.
    + split; [intros i H; exact H |exact HJ].
  - split; [reflexivity |]. split; [reflexivity |intros i H; exact H].
Qed.

Lemma container_execution_sequence active n m first second s initial t middle u final :
  execution active n first s initial halt t middle ->
  execution active m second t middle halt u final ->
  execution active (n + S m) (C.Seq first second) s initial halt u final.
Proof.
  intros Hfirst Hsecond; remember halt as last eqn:E in Hfirst.
  induction Hfirst; subst.
  - cbn; eapply ExecuteNext; [apply StepSeqDone |exact Hsecond].
  - cbn; eapply ExecuteNext; [apply StepSeq; exact H |apply IHHfirst; assumption || reflexivity].
Qed.

Lemma container_select_trace s memory value :
  ~ blocked memory 1%positive -> local_read memory 1%positive 1%Z = Some value ->
  execution two_processors 3 (container_select value) s memory halt (update s 0 value) memory.
Proof.
  intros Hunblocked Hread; unfold container_select.
  eapply ExecuteNext; [apply StepSeq; eapply StepPrimitive; [reflexivity |apply PrimitiveLoad; [left; reflexivity |exact Hunblocked |exact Hread]] |].
  eapply ExecuteNext; [apply StepSeqDone |].
  eapply ExecuteNext; [|constructor]. eapply StepPrimitive; [reflexivity |].
  apply PrimitiveAssume; [left; reflexivity |].
  change (Z.eqb (update s 0 value 0) value = true); rewrite update_same; apply Z.eqb_refl.
Qed.

Lemma container_remove_trace s :
  execution two_processors 10 container_remove s container_initial halt (update s 0 1%Z) container_removed.
Proof.
  unfold container_remove; change 10 with (1 + S 8).
  eapply container_execution_sequence with (t := s) (middle := container_first_held).
  - eapply ExecuteNext; [|constructor]. eapply StepPrimitive; [reflexivity |].
    apply PrimitiveLock; [left; reflexivity |reflexivity |intros i H; exact H].
  - change 8 with (3 + S 4).
    eapply container_execution_sequence with (t := update s 0 1%Z) (middle := container_first_held).
    + apply container_select_trace; [intros [_ H]; apply H; reflexivity |reflexivity].
    + change 4 with (2 + S 1).
      eapply container_execution_sequence with (t := update s 0 1%Z) (middle := container_remove_flushed).
      * eapply ExecuteNext; [eapply StepPrimitive; [reflexivity |] |].
        -- eapply PrimitiveStore with (previous := 1%Z); [left; reflexivity |reflexivity |reflexivity].
        -- eapply ExecuteNext; [apply StepFlush; apply FlushWrite with (i := 1%positive); [left; reflexivity |intros [_ H]; apply H; reflexivity |reflexivity] |constructor].
      * eapply ExecuteNext; [|constructor]. eapply StepPrimitive; [reflexivity |].
        apply PrimitiveUnlock; [left; reflexivity |reflexivity |split; [left; reflexivity |intros i; reflexivity]].
Qed.

Lemma container_return_trace s :
  execution two_processors 11 container_return s container_private_pending halt (update s 0 0%Z) container_final.
Proof.
  unfold container_return; change 11 with (2 + S 8).
  eapply container_execution_sequence with (t := s) (middle := container_second_held).
  - eapply ExecuteNext; [apply StepFlush; apply FlushWrite with (i := 1%positive); [left; reflexivity |intros H; exact H |reflexivity] |].
    eapply ExecuteNext; [|constructor]. eapply StepPrimitive; [reflexivity |].
    apply PrimitiveLock; [left; reflexivity |reflexivity |intros i H; exact H].
  - change 8 with (3 + S 4).
    eapply container_execution_sequence with (t := update s 0 0%Z) (middle := container_second_held).
    + apply container_select_trace; [intros [_ H]; apply H; reflexivity |reflexivity].
    + change 4 with (2 + S 1).
      eapply container_execution_sequence with (t := update s 0 0%Z) (middle := container_return_flushed).
      * eapply ExecuteNext; [eapply StepPrimitive; [reflexivity |] |].
        -- eapply PrimitiveStore with (previous := 0%Z); [left; reflexivity |reflexivity |reflexivity].
        -- eapply ExecuteNext; [apply StepFlush; apply FlushWrite with (i := 1%positive); [left; reflexivity |intros [_ H]; apply H; reflexivity |reflexivity] |constructor].
      * eapply ExecuteNext; [|constructor]. eapply StepPrimitive; [reflexivity |].
        apply PrimitiveUnlock; [left; reflexivity |reflexivity |split; [left; reflexivity |intros i; reflexivity]].
Qed.

Theorem owned_container_trace s :
  execution two_processors 24 container_program s container_initial halt
    (update (update s 0 1%Z) 0 0%Z) container_final.
Proof.
  unfold container_program; change 24 with (10 + S 13).
  eapply container_execution_sequence; [apply container_remove_trace |].
  change 13 with (1 + S 11).
  eapply container_execution_sequence with (middle := container_private_pending).
  - eapply ExecuteNext; [|constructor]. eapply StepPrimitive; [reflexivity |].
    eapply PrimitiveStore with (previous := 7%Z); [left; reflexivity |reflexivity |reflexivity].
  - apply container_return_trace.
Qed.

Theorem owned_container_reacquire_waits s :
  forall action next final,
    ~ program_step two_processors action container_acquire (State s container_private_pending) next final.
Proof.
  intros action next final Hstep; inversion Hstep; subst.
  match goal with E : eval_expr _ (EVal 1%Z) = Z.pos _ |- _ => cbn in E; inversion E; subst end.
  match goal with H : primitive_step _ _ _ _ _ |- _ => inversion H; subst end; discriminate.
Qed.

Theorem owned_container_foreign_pending_throughout :
  Forall (fun m => buffers m 2%positive = [(3%positive,17%Z)])
    [container_initial; container_first_held; container_remove_pending; container_remove_flushed;
     container_removed; container_private_pending; container_private_flushed; container_second_held;
     container_return_pending; container_return_flushed; container_final].
Proof. repeat constructor. Qed.

Theorem owned_container_final_contents :
  shared_heap container_final 1%positive = Some 1%Z /\
  shared_heap container_final 2%positive = Some 9%Z /\
  buffers container_final 1%positive = [] /\
  buffers container_final 2%positive = [(3%positive,17%Z)] /\ lock_free container_final.
Proof. repeat split; try reflexivity; intros i H; exact H. Qed.

Theorem owned_container_all_runs_safe s n last t final :
  execution two_processors n container_program s container_initial last t final ->
  ~ abort two_processors last (State t final) /\
  (terminal last -> exists local pool,
    memory_spatial pool (resource_memory two_processors local) final /\
    persistent_models two_processors t local container_foreign /\
    ((lock_free final /\ persistent_full_satisfies two_processors t pool container_invariant) \/
      exists owner, lock_held two_processors (resource_memory two_processors local) owner /\ pool = empty_memory)).
Proof.
  intros Hrun; destruct (owned_container_initial s) as [HP [HJ [Henv [Hf [Hx Hfree]]]]].
  eapply owned_derivation_adequacy; [apply container_invariant_fragment |apply acceptance_two_active
    |apply owned_container_derived |exact HP |exact HJ |exact Hfree |apply container_initial_split |exact Hrun].
Qed.
