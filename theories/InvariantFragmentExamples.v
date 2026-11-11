From Stdlib Require Import List ZArith.
From WMLR Require Import Expressions Machine BufferRelations Separation
  RepairedSeparation ExecutionExamples Assertions AssertionSemantics ConcreteAssertions
  PersistentAssertions HeapRules TemporalSafety TemporalFence RegionalResources
  TransferredCells InvariantFragment.
Import ListNotations.

Definition checkpoint_foreign_write := A.LeadsTo (EVal 3%Z) (EVal 2%Z) (EVal 17%Z).
Definition checkpoint_foreign_pending : resource two_processors :=
  pending_write_resource two_processors 2%positive 3%positive 17%Z (or_intror eq_refl).
Definition checkpoint_owner_marked : resource two_processors :=
  mark_processor two_processors checkpoint_foreign_pending 1%positive (or_introl eq_refl).

Lemma checkpoint_foreign_buffer_pending :
  buffers (resource_memory two_processors checkpoint_owner_marked) 2%positive = [(3%positive, 17%Z)].
Proof. apply buffer_update_same. Qed.

Lemma checkpoint_foreign_before_owner_barrier s :
  persistent_models two_processors s checkpoint_owner_marked
    (A.Temporal checkpoint_foreign_write (A.Barrier (EVal 1%Z))).
Proof.
  exists checkpoint_foreign_pending,
    (mark_processor two_processors (bare_resource two_processors) 1%positive (or_introl eq_refl)).
  split.
  - split; [exact (proj1 (repaired_temporal_bare_right two_processors checkpoint_foreign_pending)) |].
    split; [exact (proj1 (temporal_empty_right two_processors (proj1_sig checkpoint_foreign_pending))) |].
    split.
    + intros i [Hfalse | ->]; [contradiction |].
      change (buffer_update empty_buffers 2%positive [(3%positive, 17%Z)] 1%positive = []).
      rewrite buffer_update_other by discriminate; reflexivity.
    + intros i; change ((False \/ i = 1%positive) <-> False \/ False \/ i = 1%positive); tauto.
  - split.
    + split; [right; reflexivity |left]. split; [intros; reflexivity |].
      split; [intros; reflexivity |intros i H; contradiction].
    + apply marked_emp_barrier, bare_resource_models.
Qed.

(** The unguarded premise can donate processor 2's write although only
    processor 1 has passed its barrier. The guarded fragment forbids this. *)
Theorem checkpoint_unlock_foreign_write_test s :
  persistent_models two_processors s checkpoint_owner_marked
    (A.Temporal checkpoint_foreign_write (A.Barrier (EVal 1%Z))) /\
  persistent_models two_processors s checkpoint_owner_marked
    (A.Spatial (A.Pure BTrue) A.Emp) /\
  (forall p, invariant_fragment p ->
    ~ persistent_models two_processors s checkpoint_owner_marked (A.Spatial p A.Emp)).
Proof.
  split; [apply checkpoint_foreign_before_owner_barrier |]. split.
  - eapply bare_pure_unlock_premise; apply checkpoint_foreign_before_owner_barrier.
  - intros p Hfragment; eapply invariant_cannot_absorb_pending with (i := 2%positive).
    + exact Hfragment.
    + rewrite checkpoint_foreign_buffer_pending; discriminate.
Qed.

Theorem bare_pure_is_not_buffer_free s :
  persistent_full_satisfies two_processors s
    (resource_memory two_processors checkpoint_owner_marked) (A.Pure BTrue) /\
  buffers (resource_memory two_processors checkpoint_owner_marked) 2%positive <> [].
Proof.
  split.
  - exists (exist _ _ (full_memory_valid_with_processor two_processors 1%positive
      (resource_memory two_processors checkpoint_owner_marked) (or_introl eq_refl)
      (proj1 (proj2_sig checkpoint_owner_marked)))); split; reflexivity.
  - rewrite checkpoint_foreign_buffer_pending; discriminate.
Qed.

Definition checkpoint_container := A.Or
  (writer_points_to (EVal 1%Z) (EVal 0%Z))
  (A.Spatial (writer_points_to (EVal 1%Z) (EVal 1%Z))
    (A.Exists 0 (writer_points_to (EVal 2%Z) (EVar 0)))).

Theorem checkpoint_container_fragment : invariant_fragment checkpoint_container.
Proof.
  apply InvariantOr; [apply InvariantCell |]. apply InvariantSpatial;
    [apply InvariantCell |apply InvariantExists, InvariantCell].
Qed.

Theorem checkpoint_guarded_container_fragment b :
  invariant_fragment (A.And (A.Pure b) checkpoint_container).
Proof. apply InvariantGuard, checkpoint_container_fragment. Qed.

Theorem checkpoint_container_acquire_remark active owner s m :
  active owner -> persistent_full_satisfies active s m checkpoint_container ->
  exists r : resource active, resource_memory active r = m /\
    (forall i, complete (proj1_sig r) i <-> i = owner) /\
    persistent_models active s r checkpoint_container /\
    (forall i, buffers (resource_memory active r) i = []) /\
    lock_free (resource_memory active r).
Proof. intros Howner; apply invariant_singleton_remark; [exact Howner |apply checkpoint_container_fragment]. Qed.

(** An actual nonempty source cell at full completeness. *)
Definition checkpoint_full_cell : resource two_processors.
Proof.
  refine (exist _ (Generalized (Memory (heap_update empty_heap 2%positive 7%Z)
    empty_buffers no_blocked) two_processors) _).
  apply (full_memory_valid_with_processor two_processors 1%positive); [left; reflexivity |].
  split; [intros i H; contradiction |intros; reflexivity].
Defined.

Lemma checkpoint_full_cell_models s :
  persistent_models two_processors s checkpoint_full_cell (writer_points_to (EVal 2%Z) (EVal 7%Z)).
Proof.
  eapply writer_points_to_from_shape with (loc := 2%positive) (owner := 2%positive);
    try reflexivity; [right; reflexivity |intros i H; contradiction |right; reflexivity].
Qed.

Definition checkpoint_remarked_cell : resource two_processors :=
  remark_resource two_processors checkpoint_full_cell (fun i => i = 1%positive)
    (fun i H => or_introl H) (ex_intro _ 1%positive eq_refl).

Theorem checkpoint_cell_remark_and_no_foreign_barrier s :
  persistent_models two_processors s checkpoint_remarked_cell (writer_points_to (EVal 2%Z) (EVal 7%Z)) /\
  ~ persistent_models two_processors s checkpoint_remarked_cell
    (A.Spatial (writer_points_to (EVal 2%Z) (EVal 7%Z)) (A.Barrier (EVal 2%Z))).
Proof.
  split.
  - exact (invariant_fragment_remark _ (InvariantCell _ _) two_processors s
      checkpoint_full_cell checkpoint_remarked_cell eq_refl
      (ex_intro _ 1%positive eq_refl) (checkpoint_full_cell_models s)).
  - intros (cell & bar & [_ Hmarks] & Hcell & Hemp & [Hinactive |Hmark]).
    + apply Hinactive; right; reflexivity.
    + assert (Hbad : complete (proj1_sig checkpoint_remarked_cell) 2%positive).
      { apply Hmarks; right; exact Hmark. }
      discriminate Hbad.
Qed.

(** A nonempty donated cell can coexist with a retained foreign pending write.
    This is a concrete check of the release assertions, not a command proof. *)
Definition checkpoint_cell_and_pending : resource two_processors.
Proof.
  refine (exist _ (Generalized (Memory (heap_update empty_heap 2%positive 7%Z)
    (buffer_update empty_buffers 2%positive [(3%positive, 17%Z)]) no_blocked)
    (fun i => i = 1%positive)) _).
  split.
  - exact (proj1 (proj2_sig checkpoint_foreign_pending)).
  - split; [intros i H; left; exact H |].
    intros Hnone loc; exfalso; apply (Hnone 1%positive); reflexivity.
Defined.

Lemma checkpoint_cell_pending_spatial :
  spatial (proj1_sig checkpoint_remarked_cell) (proj1_sig checkpoint_foreign_pending)
    (proj1_sig checkpoint_cell_and_pending).
Proof.
  split.
  - split.
    + split.
      * intros loc [[v Hv] |[i [v Hv]]] [[w Hw] |[j [w Hw]]];
          try solve [discriminate |contradiction].
        change (heap_update empty_heap 2%positive 7%Z loc = Some v) in Hv.
        unfold heap_update, empty_heap in Hv.
        destruct (Pos.eq_dec loc 2%positive) as [-> |Hneq]; [|discriminate].
        change (In (2%positive, w)
          (buffer_update empty_buffers 2%positive [(3%positive, 17%Z)] j)) in Hw.
        unfold buffer_update in Hw; destruct (Pos.eq_dec j 2%positive);
          cbn [In empty_buffers] in Hw; intuition discriminate.
      * intros i H; contradiction.
    + split; [intros; reflexivity |]. split.
      * intros i; exact (interleaves_app []
          (buffer_update empty_buffers 2%positive [(3%positive, 17%Z)] i)).
      * intros i; change (False <-> False \/ False); tauto.
  - intros i; change (i = 1%positive <-> i = 1%positive \/ False); tauto.
Qed.

Definition checkpoint_release_payload :=
  A.Spatial (writer_points_to (EVal 2%Z) (EVal 7%Z)) checkpoint_foreign_write.

Theorem checkpoint_nonempty_release_assertions s :
  persistent_models two_processors s checkpoint_cell_and_pending
    (A.Temporal checkpoint_release_payload (A.Barrier (EVal 1%Z))) /\
  persistent_models two_processors s checkpoint_cell_and_pending checkpoint_release_payload /\
  buffers (resource_memory two_processors checkpoint_cell_and_pending) 2%positive = [(3%positive, 17%Z)].
Proof.
  assert (Hpayload : persistent_models two_processors s checkpoint_cell_and_pending checkpoint_release_payload).
  { exists checkpoint_remarked_cell, checkpoint_foreign_pending; split; [apply checkpoint_cell_pending_spatial |].
    split; [exact (proj1 (checkpoint_cell_remark_and_no_foreign_barrier s)) |].
    split; [right; reflexivity |left]. split; [intros; reflexivity |].
    split; [intros; reflexivity |intros i H; contradiction]. }
  split; [|split; [exact Hpayload |apply buffer_update_same]].
  exists checkpoint_cell_and_pending,
    (mark_processor two_processors (bare_resource two_processors) 1%positive (or_introl eq_refl)).
  split; [|split; [exact Hpayload |apply marked_emp_barrier, bare_resource_models]].
  split; [exact (proj1 (repaired_temporal_bare_right two_processors checkpoint_cell_and_pending)) |].
  split; [exact (proj1 (temporal_empty_right two_processors (proj1_sig checkpoint_cell_and_pending))) |].
  split.
  - intros i [Hfalse | ->]; [contradiction |].
    change (buffer_update empty_buffers 2%positive [(3%positive, 17%Z)] 1%positive = []).
    rewrite buffer_update_other by discriminate; reflexivity.
  - intros i; change (i = 1%positive <-> i = 1%positive \/ False \/ i = 1%positive); tauto.
Qed.
