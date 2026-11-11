From Stdlib Require Import List ZArith.
From WMLR Require Import Expressions Languages Machine Separation GeneralizedFlushing
  OperationalSemantics ExecutionExamples Assertions AssertionSemantics ConcreteAssertions SeparationExamples RepairedExamples
  RepairedAssertions PersistentAssertions FlushingCounterexample Safety SafetyExamples RepairedSafety
  PersistentRules HeapRules LockRules PersistentCalculus.
Import ListNotations.

Example persistent_wand_rejects_unstable_model s :
  ~ persistent_models two_processors s wand_pending_resource impossible_future.
Proof.
  intros Hwand.
  assert (Hfuture : resource_future two_processors wand_pending_resource wand_flushed_resource).
  { apply generalized_future_one. eapply GeneralizedFlush with (i := 1%positive).
    - constructor; [left; reflexivity |intros H; contradiction |apply buffer_update_same].
    - intros j Hj; exact Hj.
    - intros j Hj; exact Hj.
    - left; reflexivity. }
  assert (Hbar : persistent_models two_processors s wand_barrier_resource (A.Barrier (EVal 1%Z))).
  { split.
    - split; [intros; reflexivity |]. split; [intros; reflexivity |intros i H; contradiction].
    - right; left; reflexivity. }
  specialize (Hwand _ Hfuture _ _ Hbar wand_after_barrier_composition). discriminate.
Qed.

Lemma persistent_cell_seven s :
  persistent_full_satisfies all_processors s (cell_memory 1%positive 7%Z) (cell_assertion 1%positive 7%Z).
Proof.
  exists (cell_resource 1%positive 7%Z). split; [reflexivity |].
  apply (proj2 (persistent_wand_free_unchanged _ _ _ _ (cell_assertion_wand_free _ _))).
  apply repaired_points_to_cell.
Qed.

Example load_seven_derivable : persistent_derivation all_processors (A.Pure BTrue)
  (cell_assertion 1%positive 7%Z)
  (Concurrent.Prim (Concurrent.Common (Sequential.Load 0 (EVal 1%Z))) (EVal 1%Z))
  (A.And (cell_assertion 1%positive 7%Z) (A.Pure (BEq (EVar 0) (EVal 7%Z)))).
Proof. apply DeriveLoadCell; simpl; tauto. Qed.

Definition cell_store_result := A.Temporal (cell_assertion 1%positive 7%Z)
  (A.LeadsTo (EVal 1%Z) (EVal 1%Z) (EVal 9%Z)).
Definition stored_cell := enqueue (cell_memory 1%positive 7%Z) 1%positive 1%positive 9%Z.
Definition flushed_stored_cell := flush_write stored_cell 1%positive 1%positive 9%Z [].

Example store_nine_derivable : persistent_derivation all_processors (A.Pure BTrue)
  (cell_assertion 1%positive 7%Z)
  (Concurrent.Prim (Concurrent.Common (Sequential.Store (EVal 1%Z) (EVal 9%Z))) (EVal 1%Z)) cell_store_result.
Proof. apply DeriveStoreCell. Qed.

Example stored_cell_flush : flush all_processors stored_cell flushed_stored_cell.
Proof. constructor; [exact I |intros H; contradiction |reflexivity]. Qed.

(** A temporal postcondition survives overwriting the old heap cell. The
    past value is retained in its logical component, not asserted as current. *)
Example store_post_survives_flush s :
  persistent_full_satisfies all_processors s flushed_stored_cell cell_store_result /\
  shared_heap flushed_stored_cell 1%positive = Some 9%Z.
Proof.
  split; [|reflexivity]. eapply persistent_full_flushing_closed.
  - econstructor; [apply stored_cell_flush |constructor].
  - apply cell_store_post; [exact I |apply persistent_cell_seven].
Qed.

Definition lock_roundtrip := Concurrent.Seq
  (Concurrent.Prim Concurrent.Lock (EVal 1%Z)) (Concurrent.Prim Concurrent.Unlock (EVal 1%Z)).

Example lock_roundtrip_derivable :
  persistent_derivation all_processors (A.Pure BTrue) A.Emp lock_roundtrip A.Emp.
Proof.
  apply DeriveSequence with (middle := A.Lock (EVal 1%Z)); [apply DeriveLock |].
  eapply DeriveConsequence with (p' := A.And (A.Lock (EVal 1%Z)) (A.Pure BTrue)) (q' := A.Emp).
  - intros s r H; split; [exact H |reflexivity].
  - apply DeriveUnlockPure.
  - intros s r H; exact H.
Qed.

Example lock_roundtrip_trace : execution all_processors 3 lock_roundtrip zero_stack empty_memory
  halt zero_stack empty_memory.
Proof.
  unfold lock_roundtrip. eapply ExecuteNext with
    (next := Concurrent.Seq halt (Concurrent.Prim Concurrent.Unlock (EVal 1%Z)))
    (middle := acquire all_processors empty_memory 1%positive).
  - apply StepSeq. eapply StepPrimitive; [reflexivity |]. apply PrimitiveLock;
      [exact I |reflexivity |intros i H; contradiction].
  - eapply ExecuteNext; [apply StepSeqDone |]. eapply ExecuteNext.
    + eapply StepPrimitive; [reflexivity |]. apply PrimitiveUnlock;
        [exact I |reflexivity |split; [exact I |intros i; reflexivity]].
    + constructor.
Qed.

Lemma persistent_empty_true_environment s : repaired_environment all_processors
  (fun s m => persistent_full_satisfies all_processors s m (A.Pure BTrue))
  s empty_memory empty_memory empty_memory empty_memory.
Proof.
  constructor; try apply empty_memory_well_formed.
  - exists empty_memory. split.
    + exact (proj1 (RepairedSeparation.repaired_empty_left all_processors empty_generalized)).
    + exact (proj1 (spatial_empty_left empty_generalized)).
  - left; intros i H; contradiction.
  - left; exists full_barrier_resource; split; reflexivity.
Qed.

Theorem lock_roundtrip_no_abort n last t final :
  execution all_processors n lock_roundtrip zero_stack empty_memory last t final ->
  ~ abort all_processors last (State t final).
Proof.
  intros Hrun. eapply persistent_derivation_no_abort;
    [apply lock_roundtrip_derivable | |apply persistent_empty_true_environment |exact Hrun].
  exists full_barrier_resource. split; [reflexivity |].
  split; [intros; reflexivity |]. split; [intros; reflexivity |intros i H; contradiction].
Qed.
