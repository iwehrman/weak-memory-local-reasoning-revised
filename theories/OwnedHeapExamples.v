From Stdlib Require Import List ZArith.
From WMLR Require Import Expressions Languages Machine BufferRelations OrderedBuffers Separation
  StableCompatibility RepairedSeparation OperationalSemantics ProgramSteps ExecutionExamples
  Assertions AssertionSemantics ConcreteAssertions PersistentAssertions Safety Specifications
  OwnershipProtocol HeapRules TemporalSafety RegionalResources InvariantFragment InvariantFragmentExamples
  OwnedSafety OwnedAdequacy OwnedResources OwnedAcceptance StrongTemporalCounterexample
  OwnedStructural OwnedPrimitives OwnedHeapResources OwnedHeap.
Import ListNotations.

Definition heap_foreign_cell := acceptance_cell 2%positive 7%Z 1%positive (or_introl eq_refl).
Definition heap_foreign_pre := A.strong_temporal acceptance_invariant A.Emp.
Definition heap_foreign_load := C.Prim (C.Common (S.Load 0 (EVal 2%Z))) (EVal 2%Z).

Theorem owned_foreign_writer_load_valid mode :
  owned_valid two_processors mode A.Emp heap_foreign_pre heap_foreign_load
    (A.And heap_foreign_pre (A.Pure (BEq (EVar 0) (EVal 7%Z)))).
Proof. apply owned_load_any_writer_valid; intros H; contradiction. Qed.

Lemma heap_foreign_cell_environment mode s :
  owned_environment two_processors mode A.Emp s heap_foreign_cell empty_memory
    (empty_resource_value two_processors) (resource_memory two_processors heap_foreign_cell) PoolFree.
Proof.
  apply owned_empty_frame_intro.
  - exact (proj1 (empty_generalized_well_formed two_processors)).
  - exact (proj1 (spatial_empty_left (proj1_sig heap_foreign_cell))).
  - split; [intros i H; exact H |apply protocol_empty_satisfies].
Qed.

Theorem owned_foreign_writer_load_enabled mode s :
  persistent_models two_processors s heap_foreign_cell heap_foreign_pre /\
  owned_environment two_processors mode A.Emp s heap_foreign_cell empty_memory
    (empty_resource_value two_processors) (resource_memory two_processors heap_foreign_cell) PoolFree /\
  program_step two_processors OrdinaryAction heap_foreign_load
    (State s (resource_memory two_processors heap_foreign_cell)) halt
    (State (update s 0 7%Z) (resource_memory two_processors heap_foreign_cell)) /\
  persistent_models two_processors (update s 0 7%Z) heap_foreign_cell
    (A.And heap_foreign_pre (A.Pure (BEq (EVar 0) (EVal 7%Z)))) /\
  ~ complete (proj1_sig heap_foreign_cell) 2%positive.
Proof.
  split; [apply persistent_strong_emp_right, acceptance_cell_models |].
  split; [apply heap_foreign_cell_environment |]. split.
  - eapply ProgramPrimitive with (p := C.Common (S.Load 0 (EVal 2%Z))) (i := 2%positive); [reflexivity |].
    apply PrimitiveLoad; [right; reflexivity |intros H; exact H |reflexivity].
  - split.
    + split; [apply persistent_strong_emp_right, acceptance_cell_models |reflexivity].
    + intros H; discriminate.
Qed.

(** The writer-specific axiom cannot use this cell as a write by processor
    2, although processor 2 can read it. The new rule does not add mark 2. *)
Theorem heap_foreign_cell_not_second_write s :
  ~ persistent_models two_processors s heap_foreign_cell (A.LeadsTo (EVal 2%Z) (EVal 2%Z) (EVal 7%Z)).
Proof.
  intros [_ [[_ [Hbuffers _]] |[_ [_ [_ Hmark]]]]].
  - specialize (Hbuffers 2%positive); discriminate.
  - discriminate.
Qed.

Theorem owned_foreign_writer_store_valid mode :
  owned_valid two_processors mode A.Emp heap_foreign_pre (store_command 2%positive 2%positive 9%Z)
    (A.Temporal heap_foreign_pre (A.LeadsTo (EVal 2%Z) (EVal 2%Z) (EVal 9%Z))).
Proof. apply owned_store_any_writer_valid. Qed.

Theorem owned_foreign_writer_store_enabled mode s :
  owned_environment two_processors mode A.Emp s heap_foreign_cell empty_memory
    (empty_resource_value two_processors) (resource_memory two_processors heap_foreign_cell) PoolFree /\
  program_step two_processors OrdinaryAction (store_command 2%positive 2%positive 9%Z)
    (State s (resource_memory two_processors heap_foreign_cell)) halt
    (State s (enqueue (resource_memory two_processors heap_foreign_cell) 2%positive 2%positive 9%Z)) /\
  persistent_models two_processors s
    (owned_enqueue_resource two_processors heap_foreign_cell 2%positive 2%positive 9%Z (or_intror eq_refl))
    (A.Temporal heap_foreign_pre (A.LeadsTo (EVal 2%Z) (EVal 2%Z) (EVal 9%Z))) /\
  ~ complete (proj1_sig (owned_enqueue_resource two_processors heap_foreign_cell
      2%positive 2%positive 9%Z (or_intror eq_refl))) 2%positive.
Proof.
  split; [apply heap_foreign_cell_environment |]. split.
  - eapply ProgramPrimitive with (p := C.Common (S.Store (EVal 2%Z) (EVal 9%Z))) (i := 2%positive); [reflexivity |].
    eapply PrimitiveStore with (previous := 7%Z); [right; reflexivity |reflexivity |reflexivity].
  - split.
    + apply owned_enqueue_temporal_post; [apply persistent_strong_emp_right, acceptance_cell_models |].
      intros other Hne [v H]; contradiction.
    + intros H; discriminate.
Qed.

Definition heap_pending_pre := A.strong_temporal checkpoint_foreign_write A.Emp.
Definition heap_pending_load := C.Prim (C.Common (S.Load 0 (EVal 3%Z))) (EVal 2%Z).
Definition heap_pending_store := store_command 2%positive 3%positive 9%Z.
Definition heap_older_duplicates := stm_pending [(3%positive,17%Z);(3%positive,17%Z)].
Definition heap_pending_whole := stm_pending [(3%positive,17%Z);(3%positive,17%Z);(3%positive,17%Z)].

Theorem owned_buffered_load_store_valid mode :
  owned_valid two_processors mode A.Emp heap_pending_pre
    (C.Seq heap_pending_load heap_pending_store)
    (A.Temporal heap_pending_pre (A.LeadsTo (EVal 3%Z) (EVal 2%Z) (EVal 9%Z))).
Proof.
  eapply owned_sequence_valid with (middle := heap_pending_pre).
  - eapply owned_consequence_valid with (pre' := heap_pending_pre)
      (post' := A.And heap_pending_pre (A.Pure (BEq (EVar 0) (EVal 17%Z))));
      [intros s r H; exact H | |intros s r [H _]; exact H].
    apply owned_load_valid; intros H; contradiction.
  - apply owned_store_valid.
Qed.

Lemma heap_pending_models s :
  persistent_models two_processors s checkpoint_foreign_pending heap_pending_pre.
Proof.
  apply persistent_strong_emp_right; split; [right; reflexivity |left].
  split; [intros; reflexivity |]. split; [intros; reflexivity |intros i H; contradiction].
Qed.

Lemma heap_duplicate_pending_environment s :
  owned_environment two_processors OverlapMode A.Emp s checkpoint_foreign_pending empty_memory
    heap_older_duplicates (resource_memory two_processors heap_pending_whole) PoolFree.
Proof.
  constructor.
  - exact (proj1 (empty_generalized_well_formed two_processors)).
  - exact (proj1 (proj2_sig heap_pending_whole)).
  - exists heap_pending_whole; split.
    + split.
      * split.
        -- split; [intros i H _; exact H |]. split.
           ++ intros i _ loc _ [v H]; discriminate.
           ++ intros i j _ _ Hne loc [v Hv] [w Hw].
              change (In (loc,v) (buffer_update empty_buffers 2%positive [(3%positive,17%Z);(3%positive,17%Z)] i)) in Hv.
              change (In (loc,w) (buffer_update empty_buffers 2%positive [(3%positive,17%Z)] j)) in Hw.
              unfold buffer_update in Hv, Hw; destruct (Pos.eq_dec i 2%positive), (Pos.eq_dec j 2%positive); subst; contradiction.
        -- split; [intros; reflexivity |]. split.
           ++ intros i; change (ordered_overrides
                (buffer_update empty_buffers 2%positive [(3%positive,17%Z);(3%positive,17%Z)] i)
                (buffer_update empty_buffers 2%positive [(3%positive,17%Z)] i)
                (buffer_update empty_buffers 2%positive [(3%positive,17%Z);(3%positive,17%Z);(3%positive,17%Z)] i)).
              unfold buffer_update; destruct (Pos.eq_dec i 2%positive); [apply ordered_append |constructor].
           ++ intros i; change (False <-> False \/ False); tauto.
      * intros i; change (False <-> False \/ False); tauto.
    + exact (proj1 (spatial_empty_left (proj1_sig heap_pending_whole))).
  - exact I.
  - split; [intros i H; exact H |apply protocol_empty_satisfies].
Qed.

Theorem owned_buffered_load_store_trace s :
  persistent_models two_processors s checkpoint_foreign_pending heap_pending_pre /\
  owned_environment two_processors OverlapMode A.Emp s checkpoint_foreign_pending empty_memory
    heap_older_duplicates (resource_memory two_processors heap_pending_whole) PoolFree /\
  execution two_processors 3 (C.Seq heap_pending_load heap_pending_store) s
    (resource_memory two_processors heap_pending_whole) halt (update s 0 17%Z)
    (enqueue (resource_memory two_processors heap_pending_whole) 2%positive 3%positive 9%Z).
Proof.
  split; [apply heap_pending_models |]. split; [apply heap_duplicate_pending_environment |].
  eapply ExecuteNext; [apply StepSeq; eapply StepPrimitive; [reflexivity |] |].
  - apply PrimitiveLoad; [right; reflexivity |intros H; exact H |reflexivity].
  - eapply ExecuteNext; [apply StepSeqDone |]. eapply ExecuteNext; [|constructor].
    eapply StepPrimitive; [reflexivity |].
    eapply PrimitiveStore with (previous := 17%Z); [right; reflexivity |reflexivity |reflexivity].
Qed.

Definition heap_same_write := A.LeadsTo (EVal 2%Z) (EVal 1%Z) (EVal 7%Z).
Definition heap_split_tail := A.Or A.Emp heap_same_write.
Definition heap_split_pre := A.strong_temporal heap_same_write heap_split_tail.

Lemma heap_same_write_models s : persistent_models two_processors s heap_foreign_cell heap_same_write.
Proof.
  split; [left; reflexivity |right]. split; [intros; reflexivity |].
  split; [intros; reflexivity |]. split; [intros i H; exact H |reflexivity].
Qed.

Lemma heap_cell_temporal_self :
  repaired_temporal two_processors (proj1_sig heap_foreign_cell) (proj1_sig heap_foreign_cell)
    (proj1_sig heap_foreign_cell).
Proof.
  assert (Hstable : stable_compatible two_processors (resource_memory two_processors heap_foreign_cell)
    (resource_memory two_processors heap_foreign_cell)).
  { split; [intros i H _; exact H |]. split;
      [intros i _ loc [v H] |intros i j _ _ _ loc [v H]]; contradiction. }
  split; [exact Hstable |]. split.
  - split; [apply stable_implies_original_compatible, Hstable |]. split.
    + intros loc; change (heap_update empty_heap 2%positive 7%Z loc =
        heap_override (heap_update empty_heap 2%positive 7%Z) (heap_update empty_heap 2%positive 7%Z) loc).
      unfold heap_override, heap_update, empty_heap; destruct (Pos.eq_dec loc 2%positive); reflexivity.
    + split; [intros; reflexivity |intros i; change (False <-> False \/ False); tauto].
  - split; [intros; reflexivity |intros i; change (i = 1%positive <-> i = 1%positive \/ i = 1%positive); tauto].
Qed.

(** The spatial witness gives the tail emp; this temporal witness gives
    the same tail an overlapping cell. They are independently existential.
    This does not assert that no alternative common witness exists. *)
Theorem heap_store_independent_witnesses s :
  persistent_models two_processors s heap_foreign_cell heap_split_pre.
Proof.
  split.
  - exists heap_foreign_cell, (bare_resource two_processors); split; [apply spatial_empty_right |].
    split; [apply heap_same_write_models |left; apply bare_resource_models].
  - exists heap_foreign_cell, heap_foreign_cell; split; [apply heap_cell_temporal_self |].
    split; [apply heap_same_write_models |right; apply heap_same_write_models].
Qed.

Theorem owned_independent_witness_store_valid mode :
  owned_valid two_processors mode A.Emp heap_split_pre (store_command 1%positive 2%positive 9%Z)
    (A.Temporal heap_split_pre (A.LeadsTo (EVal 2%Z) (EVal 1%Z) (EVal 9%Z))).
Proof. apply owned_store_valid. Qed.

Theorem owned_independent_witness_store_enabled mode s :
  owned_environment two_processors mode A.Emp s heap_foreign_cell empty_memory
    (empty_resource_value two_processors) (resource_memory two_processors heap_foreign_cell) PoolFree /\
  program_step two_processors OrdinaryAction (store_command 1%positive 2%positive 9%Z)
    (State s (resource_memory two_processors heap_foreign_cell)) halt
    (State s (enqueue (resource_memory two_processors heap_foreign_cell) 1%positive 2%positive 9%Z)) /\
  persistent_models two_processors s
    (owned_enqueue_resource two_processors heap_foreign_cell 1%positive 2%positive 9%Z (or_introl eq_refl))
    (A.Temporal heap_split_pre (A.LeadsTo (EVal 2%Z) (EVal 1%Z) (EVal 9%Z))).
Proof.
  split; [apply heap_foreign_cell_environment |]. split.
  - eapply ProgramPrimitive with (p := C.Common (S.Store (EVal 2%Z) (EVal 9%Z))) (i := 1%positive); [reflexivity |].
    eapply PrimitiveStore with (previous := 7%Z); [left; reflexivity |reflexivity |reflexivity].
  - apply owned_enqueue_temporal_post; [apply heap_store_independent_witnesses |].
    intros other Hne [v H]; contradiction.
Qed.
