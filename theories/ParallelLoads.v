From Stdlib Require Import List ZArith.
From WMLR Require Import Expressions Languages Machine Separation FrameDecomposition OperationalSemantics
  ExecutionExamples Assertions AssertionSemantics PersistentAssertions Safety HeapRules Specifications
  OwnershipProtocol OwnershipHeap OwnershipExamples PrivateOwnership PrivateRules PrivateHeap PrivateCalculus
  PrivateExamples VariableSupport ThreadProgress SharedViews ParallelOwnership ParallelExamples.
Import ListNotations.

Definition load_for owner loc target := Concurrent.Prim
  (Concurrent.Common (Sequential.Load target (EVal (Z.pos loc)))) (EVal (Z.pos owner)).
Definition restore_and_load owner temporary loc target :=
  Concurrent.Seq (restore_for owner temporary) (load_for owner loc target).
Definition loaded_cell loc v target := A.And (cell_assertion loc v) (A.Pure (BEq (EVar target) (EVal v))).

Theorem restore_and_load_derivable active owner temporary loc v target :
  private_derivation active owner protected_seven Closed (cell_assertion loc v)
    (restore_and_load owner temporary loc target) Closed (loaded_cell loc v target).
Proof.
  eapply PrivateSequence; [apply restore_for_derivable |apply PrivateLoad, cell_assertion_fresh].
Qed.

Definition left_reader := restore_and_load 1%positive 9%Z 2%positive 0.
Definition right_reader target := restore_and_load 2%positive 5%Z 3%positive target.
Definition competing_readers target := Concurrent.Parallel left_reader (right_reader target).
Definition left_reader_spec := Build_concurrent_specification protected_seven retained_assertion left_reader
  (loaded_cell 2%positive 11%Z 0).
Definition right_reader_spec target := Build_concurrent_specification protected_seven right_assertion (right_reader target)
  (loaded_cell 3%positive 13%Z target).

Lemma competing_readers_variable_condition : parallel_variable_condition left_reader_spec (right_reader_spec 1).
Proof. split; unfold Specifications.disjoint; simpl; intros x Hread Hwrite; intuition congruence. Qed.

Example competing_readers_modify_registers : ~ memory_only left_reader /\ ~ memory_only (right_reader 1).
Proof. split; intros H; [apply (H 0) |apply (H 1)]; simpl; auto. Qed.

Theorem competing_readers_no_abort s n last t final :
  execution two_processors n (competing_readers 1) s parallel_initial last t final ->
  ~ abort two_processors last (State t final).
Proof.
  intros Hrun. exact (proj1 (private_parallel_rule two_processors 1%positive 2%positive
    protected_seven retained_assertion (loaded_cell 2%positive 11%Z 0)
    right_assertion (loaded_cell 3%positive 13%Z 1) _ _ _ _ _ _ _ ltac:(discriminate)
    competing_readers_variable_condition (restore_and_load_derivable _ _ _ _ _ _) (restore_and_load_derivable _ _ _ _ _ _)
    (parallel_initial_environment s) (retained_cell_models s) (right_cell_models s) _ _ _ _ Hrun)).
Qed.

Lemma loaded_cell_elim active s local loc v target :
  persistent_full_satisfies active s local (loaded_cell loc v target) ->
  persistent_full_satisfies active s local (cell_assertion loc v) /\ s target = v.
Proof.
  intros [resource [Er [Hcell Hvalue]]]. split; [exists resource; auto |].
  change (Z.eqb (s target) v = true) in Hvalue; apply Z.eqb_eq, Hvalue.
Qed.

Theorem competing_readers_all_terminating_runs s n last t final :
  execution two_processors n (competing_readers 1) s parallel_initial last t final -> terminal last ->
  lock_free final /\ shared_heap final 1%positive = Some 7%Z /\
    shared_heap final 2%positive = Some 11%Z /\ shared_heap final 3%positive = Some 13%Z /\
    t 0 = 11%Z /\ t 1 = 13%Z.
Proof.
  intros Hrun Hlast.
  destruct (proj2 (private_parallel_rule two_processors 1%positive 2%positive
    protected_seven retained_assertion (loaded_cell 2%positive 11%Z 0)
    right_assertion (loaded_cell 3%positive 13%Z 1) _ _ _ _ _ _ _ ltac:(discriminate)
    competing_readers_variable_condition (restore_and_load_derivable _ _ _ _ _ _) (restore_and_load_derivable _ _ _ _ _ _)
    (parallel_initial_environment s) (retained_cell_models s) (right_cell_models s) _ _ _ _ Hrun) Hlast)
    as (pool & combined & Hpool & HJ & HQ & Hfree).
  destruct (full_spatial_elim _ _ _ _ _ HQ) as (a & b & Hab & Ha & Hb).
  destruct (loaded_cell_elim _ _ _ _ _ _ Ha) as [HcellA Hx].
  destruct (loaded_cell_elim _ _ _ _ _ _ Hb) as [HcellB Hy].
  destruct (persistent_cell_shape _ _ _ _ _ HJ) as [Hshared _].
  destruct (persistent_cell_shape _ _ _ _ _ HcellA) as [Hleft _].
  destruct (persistent_cell_shape _ _ _ _ _ HcellB) as [Hright _].
  split; [exact Hfree |]. split.
  - eapply spatial_heap_value; [apply memory_spatial_comm, Hpool |exact Hshared].
  - split.
    + eapply spatial_heap_value; [exact Hpool |].
      eapply spatial_heap_value; [apply memory_spatial_comm, Hab |exact Hleft].
    + split; [|auto]. eapply spatial_heap_value; [exact Hpool |]. eapply spatial_heap_value; eassumption.
Qed.

Lemma restore_result_other active owner temporary initial loc : loc <> 1%positive ->
  shared_heap (restore_result active owner temporary initial) loc = shared_heap initial loc.
Proof.
  intros Hneq. unfold restore_result; cbn [release flush_write enqueue acquire shared_heap].
  rewrite !heap_update_other by exact Hneq; reflexivity.
Qed.

Theorem restore_and_load_trace active owner temporary loc v target s initial :
  active owner -> lock_free initial -> (forall i, buffers initial i = []) ->
  shared_heap initial 1%positive = Some 7%Z -> shared_heap initial loc = Some v -> loc <> 1%positive ->
  execution active 13 (restore_and_load owner temporary loc target) s initial halt (update s target v)
    (restore_result active owner temporary initial).
Proof.
  intros Hi Hfree Hempty Hshared Hprivate Hneq.
  change (execution active (11 + 2) (restore_and_load owner temporary loc target) s initial halt (update s target v)
    (restore_result active owner temporary initial)). eapply execution_append.
  - apply execution_sequence_prefix, restore_for_trace; assumption.
  - eapply ExecuteNext; [apply StepSeqDone |]. eapply ExecuteNext; [|constructor].
    eapply StepPrimitive; [reflexivity |]. apply PrimitiveLoad; [exact Hi |intros H; exact H |].
    unfold local_read; rewrite (restore_result_empty _ _ _ _ Hempty); cbn [buffer_lookup eval_expr].
    rewrite restore_result_other by exact Hneq; exact Hprivate.
Qed.

(** Both schedules exercise the retired thread's register postcondition:
    one side has finished before the other side writes its result. *)
Example competing_readers_left_first target : execution two_processors 27 (competing_readers target)
  protocol_stack parallel_initial halt (update (update protocol_stack 0 11%Z) target 13%Z) left_then_right_result.
Proof.
  change (execution two_processors (13 + 14) (competing_readers target) protocol_stack parallel_initial
    halt (update (update protocol_stack 0 11%Z) target 13%Z) left_then_right_result).
  eapply execution_append.
  - apply execution_parallel_left, restore_and_load_trace;
      [left; reflexivity |intros i H; exact H |intros; reflexivity |reflexivity |reflexivity |discriminate].
  - eapply ExecuteNext; [apply StepParallelLeftDone |]. apply restore_and_load_trace;
      [right; reflexivity |intros i H; exact H |apply restore_result_empty; intros; reflexivity |
       apply restore_result_cell |rewrite restore_result_other by discriminate; reflexivity |discriminate].
Qed.

Example competing_readers_right_first : execution two_processors 27 (competing_readers 1)
  protocol_stack parallel_initial halt (update (update protocol_stack 1 13%Z) 0 11%Z) right_then_left_result.
Proof.
  change (execution two_processors (13 + 14) (competing_readers 1) protocol_stack parallel_initial
    halt (update (update protocol_stack 1 13%Z) 0 11%Z) right_then_left_result).
  eapply execution_append.
  - apply execution_parallel_right, restore_and_load_trace;
      [right; reflexivity |intros i H; exact H |intros; reflexivity |reflexivity |reflexivity |discriminate].
  - eapply ExecuteNext; [apply StepParallelRightDone |]. apply restore_and_load_trace;
      [left; reflexivity |intros i H; exact H |apply restore_result_empty; intros; reflexivity |
       apply restore_result_cell |rewrite restore_result_other by discriminate; reflexivity |discriminate].
Qed.

Theorem same_destination_rejected : ~ parallel_variable_condition left_reader_spec (right_reader_spec 0).
Proof. intros [H _]. apply (H 0); simpl; auto. Qed.

(** Dropping the side condition has a concrete cost: a successful run
    overwrites the finished left thread's previously established x = 11. *)
Theorem same_destination_loses_left_result :
  execution two_processors 27 (competing_readers 0) protocol_stack parallel_initial halt
    (update (update protocol_stack 0 11%Z) 0 13%Z) left_then_right_result /\
  update (update protocol_stack 0 11%Z) 0 13%Z 0 = 13%Z /\
  update (update protocol_stack 0 11%Z) 0 13%Z 0 <> 11%Z.
Proof. split; [apply competing_readers_left_first |split; [reflexivity |discriminate]]. Qed.
