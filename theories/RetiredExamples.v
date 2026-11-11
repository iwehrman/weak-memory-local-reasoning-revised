From Stdlib Require Import List ZArith.
From WMLR Require Import Expressions Languages Machine BufferRelations Separation OperationalSemantics
  ExecutionExamples Assertions AssertionSemantics PersistentAssertions Safety Specifications HeapRules
  OwnershipProtocol OwnershipRules OwnershipHeap PrivateOwnership TemporalSafety TransferredCells OwnershipTransfer
  RetiredHeaps RetiredSafety RetiredTransfer RetiredRules.
Import ListNotations.

(** An exact entailment available in the previous interpretation and lost
    deliberately in RH. Remembered ownership cannot remain live after return. *)
Theorem prior_processor_cell_emp_entails_current active owner loc v s r :
  persistent_models active s r (A.Temporal (processor_cell owner loc v) A.Emp) ->
  persistent_models active s r (processor_cell owner loc v).
Proof.
  intros (a & b & Htm & HP & Hemp).
  pose proof (processor_cell_active _ _ _ _ _ _ HP) as Hi.
  destruct (processor_cell_shape _ _ _ _ _ _ Hi HP) as [Hheap [Hbuffers [Hfree Hmark]]].
  destruct (temporal_emp_memory_right _ _ _ _ Hemp Htm) as [Eh [Eb Ek]].
  apply processor_cell_from_shape.
  - exact Hi.
  - intros address; rewrite Eh; apply Hheap.
  - intros i; rewrite Eb; apply Hbuffers.
  - intros i H; apply (Hfree i), Ek, H.
  - apply (proj2 (proj2 (proj2 Htm)) owner); auto.
Qed.

Definition retired_old := RH.singleton 1%positive 1%positive 5%Z.
Definition retired_current := RH.singleton 1%positive 1%positive 7%Z.
Definition retired_initial_local := RH.compose retired_old retired_current.
Definition retired_initial_pool := acquire two_processors empty_memory 1%positive.
Definition retired_initial_whole := acquire two_processors (RH.project retired_current) 1%positive.
Definition retired_old_assertion := processor_cell 1%positive 1%positive 5%Z.
Definition retired_current_assertion := processor_cell 1%positive 1%positive 7%Z.
Definition retired_donation_invariant := A.Spatial A.Emp retired_current_assertion.
Definition retired_release := Concurrent.Prim Concurrent.Unlock (EVal 1%Z).
Definition retired_fence := Concurrent.Prim (Concurrent.Common Sequential.Fence) (EVal 1%Z).
Definition retired_read := Concurrent.Prim (Concurrent.Common (Sequential.Load 0 (EVal 1%Z))) (EVal 1%Z).
Definition retired_roundtrip := Concurrent.Seq retired_fence (Concurrent.Seq retired_release retired_read).
Definition retired_read_post := A.And retired_current_assertion (A.Pure (BEq (EVar 0) (EVal 7%Z))).

Lemma retired_initial_certificate invariant s :
  retired_environment two_processors 1%positive invariant Open s retired_initial_local retired_initial_pool RH.empty retired_initial_whole /\
  protocol_assertion two_processors Open s retired_initial_pool (owned_assertion 1%positive A.Emp) /\
  RH.models two_processors s retired_initial_local (A.Temporal retired_old_assertion retired_current_assertion).
Proof.
  assert (Hi : two_processors 1%positive) by (left; reflexivity).
  split.
  - constructor.
    + split.
      * apply acquire_well_formed; exact (proj1 (empty_generalized_well_formed two_processors)).
      * split; [exact Hi |intros i; reflexivity].
    + intros i; reflexivity.
    + exists (RH.compose RH.empty retired_initial_local); split; [apply RH.temporal_compose |].
      split.
      * split.
        -- intros loc _ [[v H] |[i [v H]]]; discriminate || contradiction.
        -- intros i H; contradiction.
      * split.
        -- intros address; unfold retired_initial_whole, retired_initial_pool, RH.project, acquire; cbn [shared_heap].
           unfold heap_override; cbn [empty_memory shared_heap empty_heap].
           unfold RH.live_heap, RH.compose, retired_initial_local, retired_old, retired_current,
             RH.singleton, RH.take, RH.set_entry, RH.empty; cbn [RH.compose RH.entries RH.override].
           destruct (Pos.eq_dec address 1%positive); reflexivity.
        -- split; [intros i; constructor |]. intros i.
           change (blocked_except two_processors 1%positive i <-> False \/ blocked_except two_processors 1%positive i); tauto.
  - split.
    + apply acquire_exposes_invariant; [exact Hi |intros i H; contradiction |apply protocol_empty_satisfies].
    + exists retired_old, retired_current; split; [apply RH.temporal_compose |]. split;
        apply RH.processor_cell_intro; try exact Hi; apply RH.take_vacant_cell; intros address; reflexivity.
Qed.

Theorem retired_framed_donation_derivable :
  retired_derivation two_processors 1%positive retired_donation_invariant Open (owned_assertion 1%positive A.Emp)
    (A.Temporal retired_old_assertion retired_current_assertion) retired_release Closed A.Emp
    (A.Temporal retired_old_assertion A.Emp).
Proof.
  apply RetiredFrameTM; [apply RetiredDonateRelease; reflexivity |intros x H; contradiction].
Qed.

Theorem retired_donation_all_runs n s last t final :
  execution two_processors n retired_release s retired_initial_whole last t final ->
  ~ abort two_processors last (State t final) /\
  (terminal last -> exists local pool,
    retired_environment two_processors 1%positive retired_donation_invariant Closed t local pool RH.empty final /\
    RH.models two_processors t local (A.Temporal retired_old_assertion A.Emp)).
Proof.
  intros Hrun; destruct (retired_initial_certificate retired_donation_invariant s) as [Henv [HS HP]].
  pose proof (retired_calculus_sound _ _ _ _ _ _ _ _ _ _ retired_framed_donation_derivable
    s retired_initial_local retired_initial_pool (retired_region_ok _ _ _ _ _ _ _ _ _ Henv)
    (retired_pool_flushed _ _ _ _ _ _ _ _ _ Henv) HS HP (S n)) as Hsafe.
  split; [eapply retired_execution_no_abort; eassumption |].
  intros Hlast; destruct (retired_execution_post _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hrun Hsafe Henv Hlast)
    as (local & pool & Henv' & _ & HQ); exists local, pool; auto.
Qed.

Theorem retired_donation_trace s : execution two_processors 1 retired_release s retired_initial_whole
  halt s (release retired_initial_whole).
Proof.
  eapply ExecuteNext; [|constructor]. apply StepPrimitive with (i := 1%positive); [reflexivity |].
  constructor; [left; reflexivity |reflexivity |]. split; [left; reflexivity |intros i; reflexivity].
Qed.

Theorem retired_donation_returns_current_ownership n s last t final :
  execution two_processors n retired_release s retired_initial_whole last t final -> terminal last ->
  exists local pool,
    retired_environment two_processors 1%positive retired_donation_invariant Closed t local pool RH.empty final /\
    RH.models two_processors t local (A.Temporal retired_old_assertion A.Emp) /\
    shared_heap pool 1%positive = Some 7%Z /\ RH.live_heap local 1%positive = None.
Proof.
  intros Hrun Hlast; destruct (proj2 (retired_donation_all_runs _ _ _ _ _ Hrun) Hlast)
    as (local & pool & Henv & HQ).
  destruct (retired_region_ok _ _ _ _ _ _ _ _ _ Henv) as [_ [_ HJ]].
  destruct (full_spatial_elim _ _ _ _ _ HJ) as (empty & cell & Hsp & Hemp & Hcell).
  destruct (protected_processor_cell_shape _ _ _ _ _ _ (or_introl eq_refl) Hcell) as [Hh _].
  assert (Hvalue : shared_heap pool 1%positive = Some 7%Z).
  { rewrite (proj1 (proj2 Hsp)); unfold heap_override; rewrite Hh, heap_update_same; reflexivity. }
  exists local, pool; split; [exact Henv |]. split; [exact HQ |]. split; [exact Hvalue |].
  eapply retired_pool_excludes_private_cell; eassumption.
Qed.

Theorem retired_roundtrip_derivable : retired_derivation two_processors 1%positive A.Emp
  Open (owned_assertion 1%positive A.Emp) (A.Temporal retired_old_assertion retired_current_assertion)
  retired_roundtrip Closed A.Emp (A.Temporal retired_old_assertion retired_read_post).
Proof.
  apply RetiredFrameTM.
  - unfold retired_roundtrip; eapply RetiredSequence; [apply RetiredDonateFence |].
    eapply RetiredSequence; [apply RetiredTakeRelease |].
    apply RetiredLoad; intros H; exact H.
  - intros x Hmod Hfv; exact Hfv.
Qed.

Theorem retired_roundtrip_all_runs n s last t final :
  execution two_processors n retired_roundtrip s retired_initial_whole last t final ->
  ~ abort two_processors last (State t final) /\
  (terminal last -> t 0 = 7%Z /\ exists local pool,
    retired_environment two_processors 1%positive A.Emp Closed t local pool RH.empty final /\
    RH.models two_processors t local (A.Temporal retired_old_assertion retired_read_post)).
Proof.
  intros Hrun; destruct (retired_initial_certificate A.Emp s) as [Henv [HS HP]].
  pose proof (retired_calculus_sound _ _ _ _ _ _ _ _ _ _ retired_roundtrip_derivable
    s retired_initial_local retired_initial_pool (retired_region_ok _ _ _ _ _ _ _ _ _ Henv)
    (retired_pool_flushed _ _ _ _ _ _ _ _ _ Henv) HS HP (S n)) as Hsafe.
  split; [eapply retired_execution_no_abort; eassumption |].
  intros Hlast; destruct (retired_execution_post _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hrun Hsafe Henv Hlast)
    as (local & pool & Henv' & _ & HQ).
  split.
  - destruct HQ as (a & b & Htm & HR & HC & Hregister).
    change (Z.eqb (t 0) 7 = true) in Hregister; apply Z.eqb_eq, Hregister.
  - exists local, pool; auto.
Qed.

Theorem retired_roundtrip_trace s : execution two_processors 5 retired_roundtrip s retired_initial_whole
  halt (update s 0 7%Z) (release retired_initial_whole).
Proof.
  unfold retired_roundtrip.
  eapply ExecuteNext with (next := Concurrent.Seq halt (Concurrent.Seq retired_release retired_read))
    (t := s) (middle := retired_initial_whole).
  - apply StepSeq; apply StepPrimitive with (i := 1%positive); [reflexivity |].
    constructor; [left; reflexivity |reflexivity].
  - eapply ExecuteNext; [apply StepSeqDone |].
    eapply ExecuteNext with (next := Concurrent.Seq halt retired_read) (t := s) (middle := release retired_initial_whole).
    + apply StepSeq; apply StepPrimitive with (i := 1%positive); [reflexivity |].
      constructor; [left; reflexivity |reflexivity |]. split; [left; reflexivity |intros i; reflexivity].
    + eapply ExecuteNext; [apply StepSeqDone |].
      eapply ExecuteNext; [|constructor]. apply StepPrimitive with (i := 1%positive); [reflexivity |].
      apply PrimitiveLoad; [left; reflexivity |intros H; exact H |].
      unfold local_read; cbn [release buffers buffer_lookup shared_heap eval_expr].
      change (RH.live_heap retired_current 1%positive = Some 7%Z).
      unfold retired_current, RH.singleton, RH.take, RH.live_heap; cbn [RH.entries].
      rewrite RH.set_same; reflexivity.
Qed.
