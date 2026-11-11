From Stdlib Require Import List ZArith.
From WMLR Require Import Expressions Languages Machine BufferRelations Separation StableCompatibility RepairedSeparation
  GeneralizedFlushing AssertionFlushing FrameDecomposition OperationalSemantics ExecutionExamples Assertions AssertionSemantics
  ConcreteAssertions PersistentAssertions Safety Specifications HeapRules OwnershipProtocol OwnershipRules OwnershipHeap
  OwnershipCalculus OwnershipExamples PrivateOwnership SpatialExchange SpatialFramingExamples TemporalSafety
  RegionalResources RegionalSafety InvariantCompleteness RegionalExamples SeparatedSafety SeparatedRules SeparatedHeap
  SeparatedCalculus SeparatedExamples TransferredCells OwnershipTransfer.
Import ListNotations.

Definition optional_seven := A.Or A.Emp protected_seven.
Definition transfer_entry_assertion := owned_assertion 1%positive (A.Spatial A.Emp protected_seven).
Definition transferred_seven := processor_cell 1%positive 1%positive 7%Z.
Definition transfer_read := Concurrent.Prim (Concurrent.Common (Sequential.Load 0 (EVal 1%Z))) (EVal 1%Z).
Definition take_and_read := Concurrent.Seq owner_fence (Concurrent.Seq owner_release transfer_read).
Definition transfer_result := A.And transferred_seven (A.Pure (BEq (EVar 0) (EVal 7%Z))).
Definition framed_transfer_result := A.Temporal spatial_pending_assertion transfer_result.
Definition transfer_initial := acquire two_processors regional_pending_initial 1%positive.
Definition transfer_pool := acquire two_processors (protocol_cell 7%Z) 1%positive.

Lemma owned_emp_entails_optional active owner p :
  regional_entails active (owned_assertion owner A.Emp) (owned_assertion owner (A.Or A.Emp p)).
Proof.
  intros s r (token & payload & Hsp & Hlock & Hemp); exists token, payload; split; [exact Hsp |].
  split; [exact Hlock |left; exact Hemp].
Qed.

Theorem take_and_read_derivable :
  separated_derivation two_processors 1%positive optional_seven Open transfer_entry_assertion A.Emp
    take_and_read Closed A.Emp transfer_result.
Proof.
  unfold take_and_read; eapply SeparateSequence; [apply SeparateTakeCell |].
  eapply SeparateSequence.
  - eapply SeparateConsequence with (protected_pre' := owned_assertion 1%positive optional_seven).
    + apply owned_emp_entails_optional.
    + intros s r H; exact H.
    + apply SeparateProtected; [apply OwnRelease |intros x H; contradiction].
    + intros s r H; exact H.
    + intros s r H; exact H.
  - apply SeparateProcessorLoad.
    + change (~ In 0 (A.fv protected_seven)); apply cell_assertion_fresh.
    + intros H; exact H.
Qed.

Theorem framed_take_and_read_derivable :
  separated_derivation two_processors 1%positive optional_seven Open transfer_entry_assertion regional_pending_pre
    take_and_read Closed A.Emp framed_transfer_result.
Proof. apply SeparateFrameTM; [apply take_and_read_derivable |intros x Hmod Hfv; exact Hfv]. Qed.

Lemma transfer_pool_certificate s :
  protocol_region two_processors 1%positive optional_seven Open s transfer_pool /\
  protocol_assertion two_processors Open s transfer_pool transfer_entry_assertion.
Proof.
  split.
  - split.
    + apply acquire_well_formed; exact (proj1 (persistent_full_well_formed _ _ _ _ (protocol_cell_models s 7%Z))).
    + split; [left; reflexivity |intros i; reflexivity].
  - apply acquire_exposes_invariant; [left; reflexivity |intros i H; contradiction |].
    eapply full_spatial_intro.
    + exact (proj1 (spatial_empty_left (Generalized (protocol_cell 7%Z) two_processors))).
    + apply protocol_empty_satisfies.
    + apply protocol_cell_models.
Qed.

Lemma transfer_pending_split :
  memory_spatial (resource_memory two_processors separated_pending) transfer_pool transfer_initial.
Proof.
  apply protocol_spatial_reblock; [intros i H; contradiction |apply separated_pending_spatial].
Qed.

Lemma transfer_initial_certificate s :
  separated_environment two_processors 1%positive optional_seven Open s separated_pending transfer_pool
    (bare_resource two_processors) transfer_initial /\
  protocol_assertion two_processors Open s transfer_pool transfer_entry_assertion /\
  persistent_models two_processors s separated_pending regional_pending_pre.
Proof.
  split.
  - constructor.
    + exact (proj1 (transfer_pool_certificate s)).
    + intros i H; contradiction.
    + intros i H; contradiction.
    + exists separated_pending; split; [apply repaired_temporal_bare_left |apply transfer_pending_split].
  - split; [exact (proj2 (transfer_pool_certificate s)) |apply temporal_emp_right_intro, separated_pending_models].
Qed.

Theorem transfer_program_all_runs command s n last t final :
  separated_derivation two_processors 1%positive optional_seven Open transfer_entry_assertion regional_pending_pre
    command Closed A.Emp framed_transfer_result ->
  execution two_processors n command s transfer_initial last t final ->
  ~ abort two_processors last (State t final) /\
  (terminal last -> t 0 = 7%Z /\ lock_free final /\ exists local protected history,
    separated_environment two_processors 1%positive optional_seven Closed t local protected history final /\
    persistent_models two_processors t local framed_transfer_result /\
    persistent_full_satisfies two_processors t protected A.Emp).
Proof.
  intros Hderiv Hrun; destruct (transfer_initial_certificate s) as [Henv [HS HP]].
  assert (Hsafe : separated_safe two_processors 1%positive optional_seven (S n) command s
    Open separated_pending transfer_pool Closed A.Emp framed_transfer_result).
  { apply (separated_calculus_sound _ _ _ _ _ _ _ _ _ _ Hderiv);
      [exact (separated_protected_ok _ _ _ _ _ _ _ _ _ Henv) |
       exact (separated_local_free _ _ _ _ _ _ _ _ _ Henv) |exact HS |exact HP]. }
  split; [eapply separated_execution_no_abort; eassumption |]. intros Hlast.
  destruct (separated_execution_post _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hrun Hsafe Henv Hlast)
    as (local & protected & history & Henv' & Hfuture & _ & HQ).
  pose proof HQ as (past & cell & [_ [[_ [Hlocalheap _]] _]] & HR & Hcell & Hregister).
  change (Z.eqb (t 0) 7 = true) in Hregister; apply Z.eqb_eq in Hregister.
  destruct (processor_cell_shape _ _ _ _ _ _ (or_introl eq_refl) Hcell) as [Hcellheap _].
  assert (Hlocal : shared_heap (resource_memory two_processors local) 1%positive = Some 7%Z).
  { unfold resource_memory; rewrite Hlocalheap; unfold heap_override; rewrite Hcellheap; reflexivity. }
  destruct Henv' as [[Hwf [Hpf HJ]] Hlf Hhf [combined [Htm Hsp]]].
  assert (Hcombined : shared_heap (resource_memory two_processors combined) 1%positive = Some 7%Z).
  { destruct Htm as [_ [[_ [Hh _]] _]]. unfold resource_memory; rewrite Hh; unfold heap_override.
    change (match shared_heap (resource_memory two_processors local) 1%positive with
      Some v => Some v | None => shared_heap (resource_memory two_processors history) 1%positive end = Some 7%Z).
    rewrite Hlocal; reflexivity. }
  assert (Hempty : persistent_full_satisfies two_processors t protected A.Emp).
  { destruct HJ as (r & E & [Hempty |HcellJ]); [exists r; auto |].
    assert (HJcell : persistent_full_satisfies two_processors t protected protected_seven) by (exists r; auto).
    destruct (persistent_cell_shape _ _ _ _ _ HJcell) as [Hph _].
    exfalso; apply (proj1 (proj1 Hsp) 1%positive); left; exists 7%Z; assumption. }
  split; [exact Hregister |]. split.
  - eapply spatial_free_union; [exact Hsp |eapply temporal_free_union; eassumption |exact Hpf].
  - exists local, protected, history; split; [|auto]. constructor; try assumption.
    + split; [exact Hwf |]. split; [exact Hpf |].
      destruct Hempty as (r & E & H); exists r; split; [exact E |left; exact H].
    + exists combined; auto.
Qed.

Example take_and_read_trace s : execution two_processors 5 take_and_read s transfer_initial
  halt (update s 0 7%Z) regional_pending_initial.
Proof.
  unfold take_and_read; eapply ExecuteNext with (next := Concurrent.Seq halt (Concurrent.Seq owner_release transfer_read)).
  - apply StepSeq; eapply StepPrimitive; [reflexivity |]; apply PrimitiveFence; [left; reflexivity |reflexivity].
  - eapply ExecuteNext; [apply StepSeqDone |]. eapply ExecuteNext with
      (next := Concurrent.Seq halt transfer_read) (middle := regional_pending_initial).
    + apply StepSeq; eapply StepPrimitive; [reflexivity |]; apply PrimitiveUnlock;
        [left; reflexivity |reflexivity |split; [left; reflexivity |intros i; reflexivity]].
    + eapply ExecuteNext; [apply StepSeqDone |]. eapply ExecuteNext; [|constructor].
      eapply StepPrimitive; [reflexivity |]; apply PrimitiveLoad; [left; reflexivity |intros H; contradiction |reflexivity].
Qed.

Theorem take_and_read_all_runs s n last t final :
  execution two_processors n take_and_read s transfer_initial last t final ->
  ~ abort two_processors last (State t final) /\
  (terminal last -> t 0 = 7%Z /\ lock_free final /\ exists local protected history,
    separated_environment two_processors 1%positive optional_seven Closed t local protected history final /\
    persistent_models two_processors t local framed_transfer_result /\
    persistent_full_satisfies two_processors t protected A.Emp).
Proof. apply transfer_program_all_runs, framed_take_and_read_derivable. Qed.

Definition release_take_and_read := Concurrent.Seq owner_release transfer_read.

Theorem release_take_and_read_derivable :
  separated_derivation two_processors 1%positive optional_seven Open transfer_entry_assertion A.Emp
    release_take_and_read Closed A.Emp transfer_result.
Proof.
  unfold release_take_and_read; eapply SeparateSequence.
  - eapply SeparateConsequence with
      (protected_pre' := owned_assertion 1%positive (A.Spatial optional_seven protected_seven)).
    + intros s r (token & payload & Hsp & Htoken & empty & cell & Hinner & Hemp & Hcell).
      exists token, payload; split; [exact Hsp |]. split; [exact Htoken |].
      exists empty, cell; split; [exact Hinner |]. split; [left; exact Hemp |exact Hcell].
    + intros s r H; exact H.
    + apply SeparateTakeRelease.
    + intros s r H; exact H.
    + intros s r H; exact H.
  - apply SeparateProcessorLoad.
    + change (~ In 0 (A.fv protected_seven)); apply cell_assertion_fresh.
    + intros H; exact H.
Qed.

Theorem framed_release_take_and_read_derivable :
  separated_derivation two_processors 1%positive optional_seven Open transfer_entry_assertion regional_pending_pre
    release_take_and_read Closed A.Emp framed_transfer_result.
Proof. apply SeparateFrameTM; [apply release_take_and_read_derivable |intros x Hmod Hfv; exact Hfv]. Qed.

Theorem release_take_and_read_all_runs s n last t final :
  execution two_processors n release_take_and_read s transfer_initial last t final ->
  ~ abort two_processors last (State t final) /\
  (terminal last -> t 0 = 7%Z /\ lock_free final /\ exists local protected history,
    separated_environment two_processors 1%positive optional_seven Closed t local protected history final /\
    persistent_models two_processors t local framed_transfer_result /\
    persistent_full_satisfies two_processors t protected A.Emp).
Proof. apply transfer_program_all_runs, framed_release_take_and_read_derivable. Qed.

Example release_take_and_read_trace s : execution two_processors 3 release_take_and_read s transfer_initial
  halt (update s 0 7%Z) regional_pending_initial.
Proof.
  unfold release_take_and_read; eapply ExecuteNext with (next := Concurrent.Seq halt transfer_read)
    (middle := regional_pending_initial).
  - apply StepSeq; eapply StepPrimitive; [reflexivity |]; apply PrimitiveUnlock;
      [left; reflexivity |reflexivity |split; [left; reflexivity |intros i; reflexivity]].
  - eapply ExecuteNext; [apply StepSeqDone |]. eapply ExecuteNext; [|constructor].
    eapply StepPrimitive; [reflexivity |]; apply PrimitiveLoad; [left; reflexivity |intros H; contradiction |reflexivity].
Qed.

Example withdrawal_preserves_foreign_pending : buffers regional_pending_initial 2%positive = [(3%positive, 17%Z)].
Proof. reflexivity. Qed.

Lemma owned_empty_buffers active owner s protected :
  persistent_full_satisfies active s protected (owned_assertion owner A.Emp) -> forall i, buffers protected i = [].
Proof.
  intros H; destruct (full_spatial_elim _ _ _ _ _ H) as (token & payload & Hsp & Htoken & Hempty).
  destruct Htoken as (rt & Et & [_ [Htb _]]); rewrite Et in Htb.
  destruct Hempty as (re & Ee & [_ [Heb _]]); rewrite Ee in Heb.
  intros i; pose proof (proj1 (proj2 (proj2 Hsp)) i) as Hbuffers.
  rewrite Htb, Heb in Hbuffers; apply interleaves_nil_left, Hbuffers.
Qed.

(** Keeping the old all-processor points-to as the withdrawal postcondition
    is unsound even when the transfer executes a real owner fence. *)
Theorem withdrawal_as_all_processor_cell_invalid :
  ~ separated_valid two_processors 1%positive optional_seven Open transfer_entry_assertion A.Emp owner_fence
    Open (owned_assertion 1%positive A.Emp) protected_seven.
Proof.
  intros Hvalid.
  assert (Henv : separated_environment two_processors 1%positive optional_seven Open protocol_stack
    (bare_resource two_processors) transfer_pool separated_pending transfer_initial).
  { constructor; [exact (proj1 (transfer_pool_certificate protocol_stack)) |
      intros i H; contradiction |intros i H; contradiction |].
    exists separated_pending; split; [apply repaired_temporal_bare_right |apply transfer_pending_split]. }
  pose proof (Hvalid protocol_stack (bare_resource two_processors) transfer_pool
    (proj1 (transfer_pool_certificate protocol_stack)) ltac:(intros i H; contradiction)
    (proj2 (transfer_pool_certificate protocol_stack)) (bare_resource_models _ _) 2) as Hsafe.
  assert (Hrun : execution two_processors 1 owner_fence protocol_stack transfer_initial halt protocol_stack transfer_initial).
  { eapply ExecuteNext; [|constructor]; eapply StepPrimitive; [reflexivity |]; apply PrimitiveFence;
      [left; reflexivity |reflexivity]. }
  destruct (separated_execution_post _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hrun Hsafe Henv ltac:(eexists; reflexivity))
    as (local & protected & history & Henv' & _ & HS & HP).
  pose proof (cell_resource_complete _ _ _ _ _ HP 2%positive (or_intror eq_refl)) as Hmark.
  destruct (persistent_cell_resource_shape _ _ _ _ _ HP) as [_ [Hlocalempty _]].
  destruct Henv' as [_ _ _ [combined [[_ [[_ [_ [Hb _]]] [Hbefore _]]] Hsp]]].
  assert (Hcombinedempty : buffers (resource_memory two_processors combined) 2%positive = []).
  { unfold resource_memory; rewrite Hb, Hlocalempty, (Hbefore _ Hmark); reflexivity. }
  pose proof (proj1 (proj2 (proj2 Hsp)) 2%positive) as Hbuffers.
  rewrite Hcombinedempty, (owned_empty_buffers _ _ _ _ HS) in Hbuffers.
  apply interleaves_nil_left in Hbuffers; discriminate.
Qed.
