From Stdlib Require Import List ZArith.
From WMLR Require Import Expressions Languages Machine BufferRelations Separation RepairedSeparation RepairedFlushing
  GeneralizedFlushing FrameDecomposition OperationalSemantics ExecutionExamples Assertions AssertionSemantics
  PersistentAssertions Safety Specifications HeapRules OwnershipProtocol OwnershipHeap OwnershipCalculus
  OwnershipExamples PrivateOwnership PrivateExamples ParallelExamples SpatialFramingExamples TemporalSafety RegionalResources
  InvariantCompleteness RegionalExamples SeparatedSafety SeparatedRules SeparatedCalculus.
Import ListNotations.

Definition separated_pending : resource two_processors :=
  pending_write_resource two_processors 2%positive 3%positive 17%Z (or_intror eq_refl).

Lemma separated_pending_models s : persistent_models two_processors s separated_pending spatial_pending_assertion.
Proof.
  split; [right; reflexivity |]. left; split; [intros; reflexivity |].
  split; [intros; reflexivity |intros i H; contradiction].
Qed.

Lemma separated_pending_spatial : memory_spatial (resource_memory two_processors separated_pending)
  (protocol_cell 7%Z) regional_pending_initial.
Proof.
  apply memory_spatial_comm, spatial_pending_extension; [intros; reflexivity |].
  intros [[v H] |[i [v H]]]; [discriminate |contradiction].
Qed.

Lemma separated_pending_initial s :
  separated_environment two_processors 1%positive protected_seven Closed s separated_pending
    (protocol_cell 7%Z) (bare_resource two_processors) regional_pending_initial /\
  persistent_models two_processors s separated_pending regional_pending_pre.
Proof.
  split.
  - constructor.
    + exact (protocol_region_ok _ _ _ _ _ _ _ _ (protocol_cell_initial_environment s)).
    + intros i H; contradiction.
    + intros i H; contradiction.
    + exists separated_pending; split; [apply repaired_temporal_bare_left |apply separated_pending_spatial].
  - apply temporal_emp_right_intro, separated_pending_models.
Qed.

Theorem separated_roundtrip_derivable active owner invariant :
  separated_derivation active owner invariant Closed A.Emp A.Emp (regional_roundtrip owner) Closed A.Emp A.Emp.
Proof.
  apply SeparateProtected; [eapply OwnSequence; [apply OwnAcquire |apply OwnRelease] |intros x H; contradiction].
Qed.

(** The private frame is genuinely pending; the invariant stays outside it. *)
Theorem separated_pending_roundtrip_derivable :
  separated_derivation two_processors 1%positive protected_seven Closed A.Emp regional_pending_pre
    (regional_roundtrip 1%positive) Closed A.Emp regional_pending_pre.
Proof.
  apply SeparateFrameTM; [apply separated_roundtrip_derivable |intros x H; contradiction].
Qed.

Theorem separated_restore_derivable :
  separated_derivation two_processors 1%positive protected_seven Closed A.Emp regional_pending_pre
    restore_using_unlock_fence Closed A.Emp regional_pending_pre.
Proof.
  apply SeparateFrameTM; [|intros x H; contradiction].
  apply SeparateProtected; [apply restore_using_unlock_fence_derivable |intros x H; contradiction].
Qed.

Theorem separated_restore_all_runs s n last t final :
  execution two_processors n restore_using_unlock_fence s regional_pending_initial last t final ->
  ~ abort two_processors last (State t final) /\
  (terminal last -> exists local protected history,
    separated_environment two_processors 1%positive protected_seven Closed t local protected history final /\
    persistent_models two_processors t local regional_pending_pre /\
    persistent_full_satisfies two_processors t protected protected_seven).
Proof.
  intros Hrun; destruct (separated_pending_initial s) as [Henv HP].
  assert (Hsafe : separated_safe two_processors 1%positive protected_seven (S n) restore_using_unlock_fence
    s Closed separated_pending (protocol_cell 7%Z) Closed A.Emp regional_pending_pre).
  { apply (separated_calculus_sound _ _ _ _ _ _ _ _ _ _ separated_restore_derivable);
      [exact (separated_protected_ok _ _ _ _ _ _ _ _ _ Henv) |
       exact (separated_local_free _ _ _ _ _ _ _ _ _ Henv) |apply protocol_empty_satisfies |exact HP]. }
  split; [eapply separated_execution_no_abort; eassumption |]. intros Hlast.
  destruct (separated_execution_post _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hrun Hsafe Henv Hlast)
    as (local & protected & history & Henv' & _ & _ & HQ).
  exists local, protected, history; split; [exact Henv' |]. split; [exact HQ |].
  exact (proj2 (proj2 (separated_protected_ok _ _ _ _ _ _ _ _ _ Henv'))).
Qed.

(** The formerly derivable source triple is now semantically invalid.
    Its initial environment places a pending processor-2 write in the external
    history; acquisition/release on processor 1 cannot discharge that history. *)
Theorem separated_roundtrip_cannot_import_barrier :
  ~ separated_closed_valid two_processors 1%positive protected_seven A.Emp
    (regional_roundtrip 1%positive) (A.Barrier (EVal 2%Z)).
Proof.
  intros Hvalid.
  assert (Henv : separated_environment two_processors 1%positive protected_seven Closed protocol_stack
    (bare_resource two_processors) (protocol_cell 7%Z) separated_pending regional_pending_initial).
  { constructor.
    - exact (protocol_region_ok _ _ _ _ _ _ _ _ (protocol_cell_initial_environment protocol_stack)).
    - intros i H; contradiction.
    - intros i H; contradiction.
    - exists separated_pending; split; [apply repaired_temporal_bare_right |apply separated_pending_spatial]. }
  pose proof (Hvalid _ _ _ (separated_protected_ok _ _ _ _ _ _ _ _ _ Henv)
    (separated_local_free _ _ _ _ _ _ _ _ _ Henv) (protocol_empty_satisfies _ _) (bare_resource_models _ _) 4) as Hsafe.
  destruct (separated_execution_post _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    (regional_pending_roundtrip_trace protocol_stack) Hsafe Henv ltac:(eexists; reflexivity))
    as (local & protected & history & Henv' & _ & _ & Hbar).
  destruct Henv' as [[Hwf [Hfree HJ]] Hl Hh [combined [Htm Hsp]]].
  (* Only the barrier and the actual temporal witnesses are needed; no
     assertion about the future of the pending history is assumed. *)
  destruct Hbar as [Hlocalempty [Hnot |Hmark]]; [exfalso; apply Hnot; right; reflexivity |].
  destruct Htm as [_ [[_ [_ [Hb _]]] [Hbefore _]]].
  assert (Hcombinedempty : buffers (resource_memory two_processors combined) 2%positive = []).
  { unfold resource_memory; rewrite Hb, (Hbefore _ Hmark), (proj1 (proj2 Hlocalempty) 2%positive); reflexivity. }
  destruct (persistent_cell_shape _ _ _ _ _ HJ) as [_ [Hprotectedempty _]].
  pose proof (proj1 (proj2 (proj2 Hsp)) 2%positive) as Hbuffers.
  rewrite Hcombinedempty, Hprotectedempty in Hbuffers; apply interleaves_nil_left in Hbuffers; discriminate.
Qed.

Corollary separated_import_barrier_not_derivable :
  ~ separated_derivation two_processors 1%positive protected_seven Closed A.Emp A.Emp
    (regional_roundtrip 1%positive) Closed A.Emp (A.Barrier (EVal 2%Z)).
Proof. intros H; apply separated_roundtrip_cannot_import_barrier, separated_calculus_sound, H. Qed.

Definition separated_fence_two := Concurrent.Prim (Concurrent.Common Sequential.Fence) (EVal 2%Z).
Definition separated_fence_final := flush_write regional_pending_initial 2%positive 3%positive 17%Z [].

Theorem separated_pending_fence_derivable :
  separated_derivation two_processors 1%positive protected_seven Closed A.Emp regional_pending_pre
    separated_fence_two Closed A.Emp regional_impossible_post.
Proof. apply SeparateFrameTM; [apply SeparateFence |intros x H; contradiction]. Qed.

Example separated_pending_fence_trace s : execution two_processors 2 separated_fence_two s regional_pending_initial
  halt s separated_fence_final.
Proof.
  eapply ExecuteNext; [apply StepFlush; apply FlushWrite with (i := 2%positive);
    [right; reflexivity |intros H; contradiction |reflexivity] |].
  eapply ExecuteNext; [|constructor]. eapply StepPrimitive; [reflexivity |].
  apply PrimitiveFence; [right; reflexivity |reflexivity].
Qed.

Example separated_pending_fence_changes_buffer :
  buffers regional_pending_initial 2%positive = [(3%positive, 17%Z)] /\
  buffers separated_fence_final 2%positive = [] /\ shared_heap separated_fence_final 3%positive = Some 17%Z.
Proof. repeat split; reflexivity. Qed.

Theorem separated_pending_fence_all_runs s n last t final :
  execution two_processors n separated_fence_two s regional_pending_initial last t final ->
  ~ abort two_processors last (State t final) /\
  (terminal last -> exists local protected history,
    separated_environment two_processors 1%positive protected_seven Closed t local protected history final /\
    persistent_models two_processors t local regional_impossible_post).
Proof.
  intros Hrun; destruct (separated_pending_initial s) as [Henv HP].
  assert (Hsafe : separated_safe two_processors 1%positive protected_seven (S n) separated_fence_two
    s Closed separated_pending (protocol_cell 7%Z) Closed A.Emp regional_impossible_post).
  { apply (separated_calculus_sound _ _ _ _ _ _ _ _ _ _ separated_pending_fence_derivable);
      [exact (separated_protected_ok _ _ _ _ _ _ _ _ _ Henv) |
       exact (separated_local_free _ _ _ _ _ _ _ _ _ Henv) |apply protocol_empty_satisfies |exact HP]. }
  split; [eapply separated_execution_no_abort; eassumption |]. intros Hlast.
  destruct (separated_execution_post _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hrun Hsafe Henv Hlast)
    as (local & protected & history & Henv' & _ & _ & HQ).
  exists local, protected, history; auto.
Qed.

(** The protected update really runs with the foreign write left pending.
    Only the issuing processor needs an empty buffer at acquire/fence/release. *)
Theorem separated_restore_pending_trace s : execution two_processors 11 restore_using_unlock_fence
  s regional_pending_initial halt s (restore_result two_processors 1%positive 9%Z regional_pending_initial).
Proof.
  set (locked := acquire two_processors regional_pending_initial 1%positive).
  set (pending := enqueue locked 1%positive 1%positive 9%Z).
  set (flushed := flush_write pending 1%positive 1%positive 9%Z []).
  set (pending' := enqueue flushed 1%positive 1%positive 7%Z).
  set (flushed' := flush_write pending' 1%positive 1%positive 7%Z []).
  unfold restore_using_unlock_fence. eapply ExecuteNext with
    (next := Concurrent.Seq halt (Concurrent.Seq (owner_store 9%Z)
      (Concurrent.Seq owner_fence (Concurrent.Seq (owner_store 7%Z) owner_release)))) (middle := locked).
  - apply StepSeq; eapply StepPrimitive; [reflexivity |]. apply PrimitiveLock;
      [left; reflexivity |reflexivity |intros i H; contradiction].
  - eapply ExecuteNext; [apply StepSeqDone |]. eapply ExecuteNext with
      (next := Concurrent.Seq halt (Concurrent.Seq owner_fence (Concurrent.Seq (owner_store 7%Z) owner_release))) (middle := pending).
    + apply StepSeq; eapply StepPrimitive; [reflexivity |]. apply PrimitiveStore with (previous := 7%Z);
        [left; reflexivity |reflexivity |reflexivity].
    + eapply ExecuteNext; [apply StepSeqDone |]. eapply ExecuteNext with (middle := flushed).
      * apply StepFlush; apply FlushWrite with (i := 1%positive);
          [left; reflexivity |intros [_ H]; apply H; reflexivity |reflexivity].
      * eapply ExecuteNext with (next := Concurrent.Seq halt (Concurrent.Seq (owner_store 7%Z) owner_release)).
        -- apply StepSeq; eapply StepPrimitive; [reflexivity |]. apply PrimitiveFence; [left; reflexivity |reflexivity].
        -- eapply ExecuteNext; [apply StepSeqDone |]. eapply ExecuteNext with
             (next := Concurrent.Seq halt owner_release) (middle := pending').
           ++ apply StepSeq; eapply StepPrimitive; [reflexivity |]. apply PrimitiveStore with (previous := 9%Z);
                [left; reflexivity |reflexivity |reflexivity].
           ++ eapply ExecuteNext; [apply StepSeqDone |]. eapply ExecuteNext with (middle := flushed').
              ** apply StepFlush; apply FlushWrite with (i := 1%positive);
                   [left; reflexivity |intros [_ H]; apply H; reflexivity |reflexivity].
              ** eapply ExecuteNext; [|constructor]. eapply StepPrimitive; [reflexivity |]. apply PrimitiveUnlock;
                   [left; reflexivity |reflexivity |split; [left; reflexivity |intros i; reflexivity]].
Qed.

Example separated_restore_keeps_foreign_write :
  buffers (restore_result two_processors 1%positive 9%Z regional_pending_initial) 2%positive = [(3%positive, 17%Z)] /\
  shared_heap (restore_result two_processors 1%positive 9%Z regional_pending_initial) 1%positive = Some 7%Z.
Proof. split; reflexivity. Qed.

Definition separated_old_private := cell_assertion 2%positive 5%Z.
Definition separated_historical_pre := A.Temporal separated_old_private retained_assertion.
Definition separated_historical_post := A.Temporal separated_old_private private_final_assertion.

Theorem separated_historical_load_derivable :
  separated_derivation two_processors 1%positive protected_seven Closed A.Emp separated_historical_pre
    read_private Closed A.Emp separated_historical_post.
Proof.
  apply SeparateFrameTM.
  - apply SeparateLoad; [apply cell_assertion_fresh |intros H; contradiction].
  - intros x Hx Hfree; simpl in Hx; destruct Hx as [E |H]; [subst x |contradiction].
    exact (cell_assertion_fresh 2%positive 5%Z 0 Hfree).
Qed.

(** Older and current heap values may overlap within the private history. *)
Lemma separated_historical_initial s : exists local : resource two_processors,
  resource_memory two_processors local = retained_cell /\
  persistent_models two_processors s local separated_historical_pre /\
  separated_environment two_processors 1%positive protected_seven Closed s local (protocol_cell 7%Z)
    (bare_resource two_processors) private_initial.
Proof.
  set (old := Memory (heap_update empty_heap 2%positive 5%Z) empty_buffers no_blocked).
  assert (Hold : persistent_full_satisfies two_processors s old separated_old_private).
  { apply (persistent_cell_from_shape two_processors 1%positive);
      [exact two_processor_cases |left; reflexivity |intros; reflexivity |intros; reflexivity |intros i H; exact H]. }
  destruct Hold as (past & Epast & HR).
  destruct (retained_cell_models s) as (local & Elocal & HP).
  assert (Htm : repaired_temporal two_processors (proj1_sig past) (proj1_sig local) (proj1_sig local)).
  { rewrite Epast, Elocal; split.
    - split; [intros i H; contradiction |]. split;
        [intros i _ loc [v H]; contradiction |intros i j _ _ _ loc [v H]; contradiction].
    - split.
      + split.
        * split; [intros i H; contradiction |]. split;
            [intros i _ loc [v H]; contradiction |intros i j _ _ _ loc [v H]; contradiction].
        * split.
          -- intros loc; unfold old, retained_cell; cbn [underlying shared_heap].
             unfold heap_override, heap_update; destruct (Pos.eq_dec loc 2%positive); reflexivity.
          -- split; [intros; reflexivity |intros i; simpl; unfold no_blocked; tauto].
      + split; [intros; reflexivity |intros i; simpl; tauto]. }
  assert (Eraw : resource_memory two_processors local = retained_cell) by (unfold resource_memory; rewrite Elocal; reflexivity).
  exists local; split; [exact Eraw |]. split.
  - exists past, local; auto.
  - constructor.
    + exact (protocol_region_ok _ _ _ _ _ _ _ _ (protocol_cell_initial_environment s)).
    + rewrite Eraw; intros i H; contradiction.
    + intros i H; contradiction.
    + exists local; split; [apply repaired_temporal_bare_left |]. rewrite Eraw.
      apply memory_spatial_comm, private_initial_split.
Qed.

Theorem separated_historical_load_all_runs s n last t final :
  execution two_processors n read_private s private_initial last t final ->
  ~ abort two_processors last (State t final) /\
  (terminal last -> exists local protected history,
    separated_environment two_processors 1%positive protected_seven Closed t local protected history final /\
    persistent_models two_processors t local separated_historical_post).
Proof.
  intros Hrun; destruct (separated_historical_initial s) as (local & E & HP & Henv).
  assert (Hsafe : separated_safe two_processors 1%positive protected_seven (S n) read_private
    s Closed local (protocol_cell 7%Z) Closed A.Emp separated_historical_post).
  { apply (separated_calculus_sound _ _ _ _ _ _ _ _ _ _ separated_historical_load_derivable);
      [exact (separated_protected_ok _ _ _ _ _ _ _ _ _ Henv) |
       exact (separated_local_free _ _ _ _ _ _ _ _ _ Henv) |apply protocol_empty_satisfies |exact HP]. }
  split; [eapply separated_execution_no_abort; eassumption |]. intros Hlast.
  destruct (separated_execution_post _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hrun Hsafe Henv Hlast)
    as (local' & protected & history & Henv' & _ & _ & HQ).
  exists local', protected, history; auto.
Qed.
