From Stdlib Require Import List ZArith.
From WMLR Require Import Expressions Languages Machine BufferRelations Separation StableCompatibility
  RepairedSeparation GeneralizedFlushing OperationalSemantics ExecutionExamples Assertions AssertionSemantics
  ConcreteAssertions RepairedAssertions PersistentAssertions Safety OwnershipProtocol PrivateOwnership
  FlushingCounterexample TemporalFrameCounterexample TemporalSafety TemporalFence.
Import ListNotations.

Lemma unmarked_emp s : persistent_models two_processors s unmarked_empty_resource A.Emp.
Proof.
  split; [intros; reflexivity |]. split; [intros; reflexivity |intros i H; contradiction].
Qed.

(** The stronger validity premise rejects the false source specification,
    instead of banning the pending temporal frame. *)
Theorem prefix_skip_cannot_invent_barrier :
  ~ prefix_valid two_processors A.Emp A.Emp (Concurrent.skip (EVal 1%Z)) (A.Barrier (EVal 1%Z)).
Proof.
  intros H. specialize (H (fun _ => 0%Z) unmarked_empty_resource (unmarked_emp _) 1).
  destruct H as [Hdone _]. destruct (Hdone (ex_intro _ (EVal 1%Z) eq_refl)) as [_ [Hnot |Hmark]].
  - apply Hnot; left; reflexivity.
  - exact Hmark.
Qed.

Lemma pending_before_emp_resource s : persistent_models two_processors s wand_pending_resource
  (A.Temporal pending_prefix A.Emp).
Proof.
  destruct (pending_prefix_before_emp s) as [r [Er Hp]].
  (* Both witnesses have the same generalized tuple; satisfaction depends
     only on that tuple. Avoid equality of subtype proof fields. *)
  destruct Hp as (a & b & Hsep & Ha & Hb).
  exists a, b. split; [|auto].
  change (repaired_temporal two_processors (proj1_sig a) (proj1_sig b) (proj1_sig r)) in Hsep.
  rewrite Er in Hsep; exact Hsep.
Qed.

Definition pending_fence := Concurrent.Prim (Concurrent.Common Sequential.Fence) (EVal 1%Z).
Definition pending_fence_post := A.Temporal pending_prefix (A.Barrier (EVal 1%Z)).

Theorem pending_fence_valid : prefix_valid two_processors A.Emp
  (A.Temporal pending_prefix A.Emp) pending_fence pending_fence_post.
Proof. apply prefix_framed_fence_valid. Qed.

Lemma pending_fence_environment s : prefix_environment two_processors
  (fun t m => persistent_full_satisfies two_processors t m A.Emp) s
  wand_pending_resource empty_memory unmarked_empty_resource wand_pending_memory.
Proof.
  constructor.
  - exact (proj1 (empty_generalized_well_formed two_processors)).
  - exact (proj1 wand_pending_valid).
  - exists wand_pending_resource; split.
    + split; [|apply temporal_empty_left].
      split; [intros i H; contradiction |]. split;
        [intros i _ loc [v H]; contradiction |intros i j _ _ _ loc [v H]; contradiction].
    + exact (proj1 (spatial_empty_left (proj1_sig wand_pending_resource))).
  - left; intros i H; contradiction.
  - left; apply protocol_empty_satisfies.
Qed.

Theorem pending_fence_no_abort s n last t final :
  execution two_processors n pending_fence s wand_pending_memory last t final ->
  ~ abort two_processors last (State t final).
Proof.
  intros Hrun. eapply prefix_execution_no_abort; [exact Hrun | |apply pending_fence_environment].
  apply pending_fence_valid, pending_before_emp_resource.
Qed.

Theorem pending_fence_all_terminating_runs s n last t final :
  execution two_processors n pending_fence s wand_pending_memory last t final -> terminal last ->
  exists local shared frame,
    prefix_environment two_processors (fun u m => persistent_full_satisfies two_processors u m A.Emp)
      t local shared frame final /\
    memory_flushes two_processors empty_memory (resource_memory two_processors frame) /\
    persistent_models two_processors t local pending_fence_post.
Proof.
  intros Hrun Hlast. eapply prefix_execution_post with (frame := unmarked_empty_resource);
    [exact Hrun |apply pending_fence_valid, pending_before_emp_resource |apply pending_fence_environment |exact Hlast].
Qed.

Example pending_fence_trace s : execution two_processors 2 pending_fence s wand_pending_memory
  halt s wand_flushed_memory.
Proof.
  eapply ExecuteNext; [apply StepFlush, wand_actual_flush |].
  eapply ExecuteNext; [|constructor]. eapply StepPrimitive; [reflexivity |].
  apply PrimitiveFence; [left; reflexivity |apply wand_flushed_buffers].
Qed.

Example pending_fence_finishes_after_flush :
  buffers wand_pending_memory 1%positive = [(1%positive, 7%Z)] /\
  buffers wand_flushed_memory 1%positive = [] /\ shared_heap wand_flushed_memory 1%positive = Some 7%Z.
Proof. split; [reflexivity |]. split; [apply wand_flushed_buffers |reflexivity]. Qed.
