From Stdlib Require Import List ZArith.
From WMLR Require Import Expressions Languages Machine BufferRelations Separation GeneralizedFlushing
  OperationalSemantics ProgramSteps ExecutionExamples Assertions AssertionSemantics ConcreteAssertions
  PersistentAssertions PersistentRules Specifications Safety OwnershipProtocol TemporalSafety InvariantFragment
  OwnedSafety OwnedAdequacy OwnedAcceptance OwnedCalculus OwnedDerivedRules OwnedHeap
  OwnedContainerEntailments AssertionAlgebra AssertionUnits.
Import ListNotations.

(** Independent queue item 5.2, using the existing program calculus only.
    A framed fence appends its barrier to any assertion, in either mode. *)
Lemma owned_derive_fence_after active invariant mode pre annotation :
  owned_derivation active invariant mode pre
    (C.Prim (C.Common S.Fence) annotation) (A.Temporal pre (A.Barrier annotation)).
Proof.
  destruct mode; [|apply OwnedWeaken]; eapply OwnedConsequence with (pre' := A.Temporal pre A.Emp).
  - intros s r H; apply (proj2 (assertion_unit_temporal_right _ _ _ _)),H.
  - apply OwnedFrameTM; [apply OwnedFence |intros x H; contradiction].
  - intros s r H; exact H.
  - intros s r H; apply (proj2 (assertion_unit_temporal_right _ _ _ _)),H.
  - apply OwnedFrameTM; [apply OwnedFence |intros x H; contradiction].
  - intros s r H; exact H.
Qed.

(** Arbitrary positive cell address, integer values, active issuing
    processor, invariant and ownership mode. No new program rule. *)
Theorem owned_derive_store_fence_cell active invariant mode loc old next actor : active actor ->
  owned_derivation active invariant mode (container_cell loc old)
    (C.Seq (store_command actor loc next) (C.Prim (C.Common S.Fence) (EVal (Z.pos actor))))
    (container_cell loc next).
Proof.
  intros Hi; eapply OwnedSequence with (middle := container_history loc actor next).
  - eapply OwnedConsequence; [intros s r H; exact H |apply owned_derive_store_cell |].
    apply container_temporal_mono; [apply container_cell_some |intros s r H; exact H].
  - eapply OwnedConsequence; [intros s r H; exact H |apply owned_derive_fence_after |].
    apply container_history_complete,Hi.
Qed.

Corollary owned_store_fence_cell_valid active invariant mode loc old next actor :
  invariant_fragment invariant -> two_active_processors active -> active actor ->
  owned_valid active mode invariant (container_cell loc old)
    (C.Seq (store_command actor loc next) (C.Prim (C.Common S.Fence) (EVal (Z.pos actor))))
    (container_cell loc next).
Proof. intros HJ Htwo Hi; apply owned_calculus_sound; [exact HJ |exact Htwo |apply owned_derive_store_fence_cell,Hi]. Qed.

Definition fence_cell_initial loc old := acceptance_cell loc old 1%positive (or_introl eq_refl).
Definition fence_cell_pending loc old next := enqueue
  (resource_memory two_processors (fence_cell_initial loc old)) 1%positive loc next.
Definition fence_cell_final loc old next := flush_write (fence_cell_pending loc old next) 1%positive loc next [].

Lemma fence_cell_environment mode s loc old :
  owned_environment two_processors mode A.Emp s (fence_cell_initial loc old) empty_memory
    (empty_resource_value two_processors) (resource_memory two_processors (fence_cell_initial loc old)) PoolFree.
Proof.
  apply owned_empty_frame_intro.
  - exact (proj1 (empty_generalized_well_formed two_processors)).
  - exact (proj1 (spatial_empty_left (proj1_sig (fence_cell_initial loc old)))).
  - split; [intros i H; exact H |apply protocol_empty_satisfies].
Qed.

Lemma fence_cell_store_step s loc old next :
  program_step two_processors OrdinaryAction (store_command 1%positive loc next)
    (State s (resource_memory two_processors (fence_cell_initial loc old))) halt
    (State s (fence_cell_pending loc old next)).
Proof.
  eapply ProgramPrimitive with (p := C.Common (S.Store (EVal (Z.pos loc)) (EVal next))) (i := 1%positive);
    [reflexivity |].
  eapply PrimitiveStore with (previous := old); [left; reflexivity |reflexivity |].
  change (heap_update empty_heap loc old loc = Some old); apply heap_update_same.
Qed.

Theorem owned_plain_store_cell_invalid mode loc old next :
  ~ owned_valid two_processors mode A.Emp (container_cell loc old)
    (store_command 1%positive loc next) (container_cell loc next).
Proof.
  intros Hvalid; pose proof (Hvalid initial_registers (fence_cell_initial loc old)
    (acceptance_cell_models _ _ _ _ _) 2) as Hsafe.
  destruct (owned_safe_program_step _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hsafe
    (fence_cell_environment mode initial_registers loc old)
    (fence_cell_store_step initial_registers loc old next))
    as (local & pool & phase & Henv & Hupdate & Hlast).
  pose proof (owned_safe_terminal _ _ _ _ _ _ _ _ Hlast ltac:(eexists; reflexivity)) as Hcell.
  destruct (container_cell_shape _ _ _ _ _ Hcell) as (writer & Hw & Hheap & Hbuffers & Hfree & Hmark).
  destruct Hupdate as [[Hphase [Hpool Hblocked]] Hfootprint Hbudget]; cbn in Hphase,Hpool; subst phase pool.
  destruct (proj1 (owned_empty_frame_elim _ _ _ _ _ _ _ _ Henv)) as [_ [_ [Hwhole _]]].
  specialize (Hwhole 1%positive).
  change (interleaves [] (buffers (resource_memory two_processors local) 1%positive) [(loc,next)]) in Hwhole.
  rewrite Hbuffers in Hwhole; inversion Hwhole.
Qed.

Corollary owned_plain_store_cell_not_derivable mode loc old next :
  ~ owned_derivation two_processors A.Emp mode (container_cell loc old)
    (store_command 1%positive loc next) (container_cell loc next).
Proof.
  intros H; apply (owned_plain_store_cell_invalid mode loc old next),owned_calculus_sound;
    [constructor |apply acceptance_two_active |exact H].
Qed.

(** An inhabited free-pool start and complete execution: issue, drop the
    completed sequence prefix, flush the write, then execute the fence. *)
Theorem owned_store_fence_cell_witness mode s loc old next :
  persistent_models two_processors s (fence_cell_initial loc old) (container_cell loc old) /\
  owned_environment two_processors mode A.Emp s (fence_cell_initial loc old) empty_memory
    (empty_resource_value two_processors) (resource_memory two_processors (fence_cell_initial loc old)) PoolFree /\
  execution two_processors 4
    (C.Seq (store_command 1%positive loc next) (C.Prim (C.Common S.Fence) (EVal 1%Z)))
    s (resource_memory two_processors (fence_cell_initial loc old)) halt s (fence_cell_final loc old next) /\
  buffers (fence_cell_pending loc old next) 1%positive = [(loc,next)] /\
  buffers (fence_cell_final loc old next) 1%positive = [] /\
  shared_heap (fence_cell_final loc old next) loc = Some next.
Proof.
  split; [apply acceptance_cell_models |]. split; [apply fence_cell_environment |]. split.
  - eapply ExecuteNext; [apply StepSeq; eapply program_step_erases; apply fence_cell_store_step |].
    eapply ExecuteNext; [apply StepSeqDone |].
    eapply ExecuteNext; [apply StepFlush |].
    + apply FlushWrite with (i := 1%positive) (address := loc) (v := next) (rest := []);
        [left; reflexivity |intros H; exact H |reflexivity].
    + eapply ExecuteNext; [eapply StepPrimitive with (i := 1%positive); [reflexivity |] |constructor].
      apply PrimitiveFence; [left; reflexivity |reflexivity].
  - split; [reflexivity |]. split; [reflexivity |apply heap_update_same].
Qed.
