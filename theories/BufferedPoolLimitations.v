From Stdlib Require Import List ZArith.
From WMLR Require Import Expressions Languages Machine BufferRelations Separation StableCompatibility
  RepairedSeparation GeneralizedFlushing OperationalSemantics ProgramSteps Assertions AssertionSemantics
  ConcreteAssertions PersistentAssertions TemporalSafety RegionalResources InvariantFragment
  OwnedSafety OwnedContainerEntailments BufferedPoolCandidate BufferedPoolResources BufferedDekkerResources.
Import ListNotations.

(** At full marks, an already drained one-write history carries exactly
    the current cell value. The named writer must be active. *)
Theorem buffered_full_mark_drained_history active s (r : resource active) loc old actor value :
  active actor -> (forall i, active i -> complete (proj1_sig r) i) ->
  buffers (resource_memory active r) actor = [] ->
  (persistent_models active s r
    (A.Temporal (writer_points_to (EVal (Z.pos loc)) (EVal old))
      (A.LeadsTo (EVal (Z.pos loc)) (EVal (Z.pos actor)) (EVal value))) <->
   persistent_models active s r (writer_points_to (EVal (Z.pos loc)) (EVal value))).
Proof.
  intros Hi Hfull Hdrained; split.
  - intros (a & b & Htm & Ha & Hb).
    apply (container_history_drained active s r loc actor value); [|exact Hdrained].
    exists a,b; split; [exact Htm |]. split; [exact (container_cell_some active loc old s a Ha) |exact Hb].
  - intros Hcell.
    destruct (container_cell_shape _ _ _ _ _ Hcell) as (owner & Howner & Hheap & Hbuffers & Hfree & Hmark).
    pose (past := container_heap_resource active r actor (Hfull actor Hi) loc old).
    exists past,r; split.
    + assert (Hstable : stable_compatible active (resource_memory active past) (resource_memory active r)).
      { split; [intros i H; contradiction |]. split;
          [intros i Hactive l [v H] |intros i j Hactive Hactive' Hneq l [v H]]; contradiction. }
      split; [exact Hstable |]. split.
      * split; [apply stable_implies_original_compatible,Hstable |]. split.
        -- intros l; unfold heap_override; rewrite Hheap.
           change (heap_update empty_heap loc value l =
             match heap_update empty_heap loc value l with Some v => Some v |None => heap_update empty_heap loc old l end).
           unfold heap_update; destruct (Pos.eq_dec l loc); reflexivity.
        -- split; [intros; reflexivity |]. intros i; change (blocked (resource_memory active r) i <-> False \/ blocked (resource_memory active r) i); tauto.
      * split; [intros; reflexivity |intros i; change (complete (proj1_sig r) i <-> complete (proj1_sig r) i \/ complete (proj1_sig r) i); tauto].
    + split; [apply container_heap_models |]. split; [exact Hi |right].
      split; [exact Hheap |]. split; [exact Hbuffers |]. split; [exact Hfree |apply Hfull,Hi].
Qed.

Corollary buffered_full_pool_drained_history active s pool loc old actor value :
  active actor -> buffers pool actor = [] ->
  (persistent_full_satisfies active s pool
    (A.Temporal (writer_points_to (EVal (Z.pos loc)) (EVal old))
      (A.LeadsTo (EVal (Z.pos loc)) (EVal (Z.pos actor)) (EVal value))) <->
   persistent_full_satisfies active s pool (writer_points_to (EVal (Z.pos loc)) (EVal value))).
Proof.
  intros Hi HB; split; intros (r & E & HM); exists r; split; [exact E | |exact E |];
    apply (buffered_full_mark_drained_history active s r loc old actor value Hi
      ltac:(intros i H; rewrite E; exact H)
      ltac:(unfold resource_memory; rewrite E; exact HB)); exact HM.
Qed.

Theorem buffered_empty_ordinary_cannot_own_cell active s pool local' pool' address value :
  buffered_update active OrdinaryAction (empty_resource_value active) pool local' pool' ->
  ~ persistent_models active s local' (writer_points_to address value).
Proof.
  intros Hupdate Hcell.
  pose proof (buffered_unmarked_ordinary_no_heap active (empty_resource_value active) pool local' pool'
    ltac:(intros i H; exact H) Hupdate) as Hempty.
  destruct (writer_points_to_shape _ _ _ _ _ Hcell) as (loc & owner & E & Hi & Hheap & _).
  specialize (Hheap loc); rewrite Hempty,heap_update_same in Hheap; discriminate.
Qed.

(** A concrete enabled load with one pooled cell and an unmarked emp.
    The proof uses that input, not the alternative empty-pool branch. *)
Theorem buffered_emp_load_withdrawal_premise_invalid :
  ~ buffered_atomic_premise BD.active
    (A.Or A.Emp (writer_points_to (EVal 1%Z) (EVal 0%Z))) A.Emp
    (S.Load 0 (EVal 1%Z)) (EVal 1%Z) (writer_points_to (EVal 1%Z) (EVal 0%Z)).
Proof.
  intros [_ HP]. set (pool := BD.mem (BD.cell 1%positive 0%Z)).
  set (s := fun _ : ident => (-1)%Z).
  assert (HJ : persistent_full_satisfies BD.active s pool
    (A.Or A.Emp (writer_points_to (EVal 1%Z) (EVal 0%Z)))).
  { exists (BD.full (BD.cell 1%positive 0%Z)); split; [reflexivity |right; apply BD.full_cell]. }
  assert (Hsp : memory_spatial pool (resource_memory BD.active (empty_resource_value BD.active)) pool).
  { exact (proj1 (spatial_empty_right (proj1_sig (BD.full (BD.cell 1%positive 0%Z))))). }
  destruct (HP s (empty_resource_value BD.active) pool pool (bare_resource_models _ _) HJ Hsp
    ltac:(intros i H; exact H)) as [_ Hnext].
  assert (HS : program_step BD.active OrdinaryAction (C.Prim (C.Common (S.Load 0 (EVal 1%Z))) (EVal 1%Z))
    (State s pool) halt (State (update s 0 0%Z) pool)).
  { eapply ProgramPrimitive with (i := 1%positive) (p := C.Common (S.Load 0 (EVal 1%Z))); [reflexivity |apply PrimitiveLoad; [left; reflexivity |intros H; exact H |reflexivity]]. }
  destruct (Hnext _ _ _ _ HS) as (local' & pool' & Hsp' & Hfree & Hinv & Hpost & Hupdate).
  eapply buffered_empty_ordinary_cannot_own_cell; eassumption.
Qed.
