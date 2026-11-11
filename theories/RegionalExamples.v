From Stdlib Require Import List ZArith.
From WMLR Require Import Expressions Languages Machine BufferRelations Separation StableCompatibility RepairedSeparation
  GeneralizedFlushing AssertionFlushing FrameDecomposition OperationalSemantics ExecutionExamples
  Assertions AssertionSemantics PersistentAssertions Safety Specifications HeapRules OwnershipProtocol OwnershipHeap
  OwnershipExamples PrivateOwnership SpatialFramingExamples TemporalSafety RegionalResources RegionalSafety
  RegionalCalculus RegionalFraming InvariantCompleteness.
Import ListNotations.

Definition regional_pending_initial := add_spatial_pending (protocol_cell 7%Z).
Definition regional_pending_pre := A.Temporal spatial_pending_assertion A.Emp.
Definition regional_impossible_post := A.Temporal spatial_pending_assertion (A.Barrier (EVal 2%Z)).

Lemma regional_empty_private_initial s : exists region : resource two_processors,
  resource_memory two_processors region = protocol_cell 7%Z /\
  marked_region two_processors 1%positive protected_seven Closed s (bare_resource two_processors) region /\
  persistent_models two_processors s (bare_resource two_processors) A.Emp.
Proof.
  destruct (protocol_cell_models s 7%Z) as (region & E & HJ).
  exists region; split; [unfold resource_memory; rewrite E; reflexivity |]. split; [|apply bare_resource_models].
  split.
  - unfold resource_memory; rewrite E; intros i H; contradiction.
  - exists region; split; [exact HJ |apply spatial_empty_right].
Qed.

Lemma regional_full_initial active owner invariant pre s local region pool :
  lock_free region -> persistent_full_satisfies active s pool invariant ->
  persistent_full_satisfies active s local pre -> memory_spatial pool local region ->
  exists localr regionr : resource active,
    resource_memory active regionr = region /\
    marked_region active owner invariant Closed s localr regionr /\ persistent_models active s localr pre.
Proof.
  intros Hfree (rp & Ep & HJ) (rl & El & HP) Hsp.
  assert (Hg : spatial (proj1_sig rp) (proj1_sig rl) (Generalized region active)).
  { rewrite Ep, El; split; [exact Hsp |intros i; simpl; tauto]. }
  exists rl, (exist _ _ (spatial_well_formed _ _ _ _ (proj2_sig rp) (proj2_sig rl) Hg)).
  split; [reflexivity |]. split; [split; [exact Hfree |exists rp; auto] |exact HP].
Qed.

Lemma regional_pending_initial_certificate s : exists local region : resource two_processors,
  resource_memory two_processors region = regional_pending_initial /\
  marked_region two_processors 1%positive protected_seven Closed s local region /\
  persistent_models two_processors s local regional_pending_pre.
Proof.
  assert (Hsp : memory_spatial (protocol_cell 7%Z) spatial_pending regional_pending_initial).
  { apply spatial_pending_extension; [intros; reflexivity |].
    intros [[v H] |[i [v H]]]; [discriminate |contradiction]. }
  destruct (regional_full_initial two_processors 1%positive protected_seven spatial_pending_assertion s
    spatial_pending regional_pending_initial (protocol_cell 7%Z)
    ltac:(intros i H; contradiction) (protocol_cell_models _ _) (spatial_pending_models _) Hsp)
    as (local & region & E & Hr & HP).
  exists local, region; split; [exact E |]. split; [exact Hr |apply temporal_emp_right_intro, HP].
Qed.

(** Processor 1's lock and unlock do not flush processor 2's pending write. *)
Theorem regional_pending_roundtrip_trace s : execution two_processors 3 (regional_roundtrip 1%positive)
  s regional_pending_initial halt s regional_pending_initial.
Proof.
  eapply ExecuteNext with (middle := acquire two_processors regional_pending_initial 1%positive)
    (next := Concurrent.Seq halt (Concurrent.Prim Concurrent.Unlock (EVal 1%Z))).
  - apply StepSeq. eapply StepPrimitive; [reflexivity |]. apply PrimitiveLock;
      [left; reflexivity |reflexivity |intros i H; contradiction].
  - eapply ExecuteNext; [apply StepSeqDone |]. eapply ExecuteNext; [|constructor].
    eapply StepPrimitive; [reflexivity |]. apply PrimitiveUnlock;
      [left; reflexivity |reflexivity |split; [left; reflexivity |intros i; reflexivity]].
Qed.

Theorem regional_pending_roundtrip_derivable : regional_derivation two_processors 1%positive protected_seven
  Closed regional_pending_pre (regional_roundtrip 1%positive) Closed regional_pending_pre.
Proof. apply regional_roundtrip_derivable. Qed.

Theorem regional_pending_roundtrip_no_abort s n last t final :
  execution two_processors n (regional_roundtrip 1%positive) s regional_pending_initial last t final ->
  ~ abort two_processors last (State t final).
Proof.
  intros Hrun. destruct (regional_pending_initial_certificate s) as (local & region & E & Hr & HP).
  pose proof (regional_empty_history _ _ _ _ _ _ _ Hr) as Henv; rewrite E in Henv.
  eapply regional_execution_no_abort; [exact Hrun | |exact Henv].
  apply (regional_calculus_sound _ _ _ _ _ _ _ _ regional_pending_roundtrip_derivable); assumption.
Qed.

Theorem regional_pending_roundtrip_all_terminating_runs s n last t final :
  execution two_processors n (regional_roundtrip 1%positive) s regional_pending_initial last t final -> terminal last ->
  exists local region history,
    regional_environment two_processors 1%positive protected_seven Closed t local region history final /\
    persistent_models two_processors t local regional_pending_pre.
Proof.
  intros Hrun Hlast. destruct (regional_pending_initial_certificate s) as (local & region & E & Hr & HP).
  pose proof (regional_empty_history _ _ _ _ _ _ _ Hr) as Henv; rewrite E in Henv.
  assert (Hsafe : regional_safe two_processors 1%positive protected_seven (S n)
    (regional_roundtrip 1%positive) s Closed local region Closed regional_pending_pre).
  { apply (regional_calculus_sound _ _ _ _ _ _ _ _ regional_pending_roundtrip_derivable); assumption. }
  destruct (regional_execution_post _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hrun Hsafe Henv Hlast)
    as (local' & region' & history' & Henv' & _ & HP').
  exists local', region', history'; auto.
Qed.

(** In this candidate, even closed-to-closed temporal framing conflicts with
    the proved acquire/release/consequence fragment. The source specification
    has an actual derivation; its precondition is satisfiable. *)
Theorem regional_temporal_frame_counterexample :
  regional_derivation two_processors 1%positive protected_seven Closed A.Emp
    (regional_roundtrip 1%positive) Closed (A.Barrier (EVal 2%Z)) /\
  frame_variable_condition (regional_roundtrip 1%positive) spatial_pending_assertion /\
  ~ regional_valid two_processors 1%positive protected_seven Closed regional_pending_pre
    (regional_roundtrip 1%positive) Closed regional_impossible_post.
Proof.
  split; [apply regional_roundtrip_barrier_derivable; right; reflexivity |].
  split; [intros x H; contradiction |].
  intros Hvalid. destruct (regional_pending_initial_certificate (fun _ => 0%Z)) as (local & region & E & Hr & HP).
  pose proof (regional_empty_history _ _ _ _ _ _ _ Hr) as Henv; rewrite E in Henv.
  pose proof (Hvalid _ _ _ Hr HP 4) as Hsafe.
  destruct (regional_execution_residual _ _ _ _ _ _ _ _ _ _ (regional_pending_roundtrip_trace _)
    _ _ _ _ _ _ Hsafe Henv) as (phase' & local' & region' & history' & Henv' & Hhf & _ & Hdone & _).
  destruct (Hdone (ex_intro _ (EVal 1%Z) eq_refl)) as [-> HQ].
  pose proof (temporal_barrier_resource_empty _ _ _ _ 2%positive (or_intror eq_refl) HQ) as Hlocalempty.
  assert (Ehistory : resource_memory two_processors history' = empty_memory).
  { exact (future_without_buffers _ _ _ Hhf ltac:(intros i; reflexivity)). }
  destruct Henv' as [[Hfree [pool [HJ [Hsp Hmarks]]]] Hhf' [combined [Eworld [_ [[_ [_ [Hb _]]] _]]]]].
  pose proof (proj1 (proj2 (persistent_cell_resource_shape _ _ _ _ _ HJ))) as Hpoolbuffers.
  assert (Hregionempty : buffers (resource_memory two_processors region') 2%positive = []).
  { pose proof (proj1 (proj2 (proj2 Hsp)) 2%positive) as Hbuf.
    rewrite Hpoolbuffers in Hbuf. unfold resource_memory in Hlocalempty; rewrite Hlocalempty in Hbuf.
    apply interleaves_nil_left, Hbuf. }
  assert (Hwholeempty : buffers regional_pending_initial 2%positive = []).
  { rewrite <- Eworld; unfold resource_memory; rewrite Hb.
    change (buffers (resource_memory two_processors history') 2%positive ++
      buffers (resource_memory two_processors region') 2%positive = []).
    rewrite Ehistory, Hregionempty; reflexivity. }
  discriminate Hwholeempty.
Qed.

Example regional_pending_write_survives_roundtrip : buffers regional_pending_initial 2%positive = [(3%positive, 17%Z)].
Proof. reflexivity. Qed.

Definition regional_old_history := cell_assertion 1%positive 5%Z.
Definition regional_boundary_assertion := A.Temporal regional_old_history (A.Spatial protected_seven regional_pending_pre).

(** Historical cell 1=5 overlaps the current shared cell 1=7. Processor 2's
    unrelated pending write is retained in the private component. *)
Lemma regional_overlap_pending_initial s :
  persistent_full_satisfies two_processors s regional_pending_initial regional_boundary_assertion.
Proof.
  destruct (regional_pending_initial_certificate s) as (local & region & Eregion & [Hfree [pool [HJ Hsp]]] & HP).
  destruct (protocol_cell_models s 5%Z) as (past & Epast & HR).
  assert (Hmarks : forall i, two_processors i -> complete (proj1_sig region) i).
  { intros i Hi; apply (proj2 Hsp i); left; exact (cell_resource_complete _ _ _ _ _ HJ i Hi). }
  assert (Htm : repaired_temporal two_processors (proj1_sig past) (proj1_sig region) (proj1_sig region)).
  { rewrite Epast. split.
    - split; [intros i H; contradiction |]. split;
        [intros i _ loc [v H]; contradiction |intros i j _ _ _ loc [v H]; contradiction].
    - split.
      + split.
        * split; [intros i H; contradiction |]. split;
            [intros i _ loc [v H]; contradiction |intros i j _ _ _ loc [v H]; contradiction].
        * split.
          -- intros loc. change (shared_heap (resource_memory two_processors region) loc =
               heap_override (shared_heap (protocol_cell 5%Z)) (shared_heap (resource_memory two_processors region)) loc).
             rewrite Eregion. cbn [regional_pending_initial add_spatial_pending protocol_cell shared_heap].
             unfold heap_override, heap_update; destruct (Pos.eq_dec loc 1%positive); reflexivity.
          -- split; [intros i; reflexivity |]. intros i; simpl; unfold no_blocked; tauto.
      + split; [intros; reflexivity |]. intros i; simpl.
        split; [auto |intros [Hi |Hi]; [apply Hmarks, Hi |exact Hi]]. }
  rewrite <- Eregion. apply persistent_promote_full.
  exists past, region; split; [exact Htm |]. split; [exact HR |]. exists pool, local; split; [exact Hsp |auto].
Qed.

Theorem regional_overlap_pending_all_runs s n last t final :
  execution two_processors n (regional_roundtrip 1%positive) s regional_pending_initial last t final ->
  ~ abort two_processors last (State t final) /\
  (terminal last -> lock_free final /\ persistent_full_satisfies two_processors t final regional_boundary_assertion).
Proof.
  apply (regional_history_frame_rule two_processors 1%positive protected_seven regional_pending_pre
    (regional_roundtrip 1%positive) regional_pending_pre regional_old_history s regional_pending_initial).
  - apply regional_calculus_sound, regional_pending_roundtrip_derivable.
  - intros x H; contradiction.
  - intros i H; contradiction.
  - apply regional_overlap_pending_initial.
Qed.
