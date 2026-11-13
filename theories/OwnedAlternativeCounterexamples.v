From Stdlib Require Import List ZArith.
From WMLR Require Import Expressions Languages Machine BufferRelations Separation
  OperationalSemantics ProgramSteps Assertions AssertionSemantics ConcreteAssertions
  PersistentAssertions PersistentRules TemporalSafety OwnershipProtocol ExecutionExamples Specifications InvariantFragment
  InvariantFragmentExamples OwnedSafety OwnedAdequacy OwnedAcceptance OwnedCalculus
  OwnedFenceExamples OwnedPointsToRules OwnedContainerEntailments AssertionUnits
  AssertionAlgebra AssertionWriteAlgebra AssertionWriteExamples OwnedFraming RepairedSeparation.
Import ListNotations.

(** Original STORE-P has both a load command and a strong-temporal write
    suffix. The suffix is impossible even if the command typo is fixed. *)
Definition literal_store_p_pre := A.strong_temporal (A.points_to (EVal 2%Z) (EVal 7%Z)) A.Emp.
Definition literal_store_p_post := A.strong_temporal literal_store_p_pre
  (A.LeadsTo (EVal 2%Z) (EVal 1%Z) (EVal 7%Z)).

Lemma literal_store_p_post_false s r :
  ~ persistent_models two_processors s r literal_store_p_post.
Proof.
  intros [Hsp Htm].
  assert (HW : persistent_models two_processors s r
    (A.Spatial (A.LeadsTo (EVal 2%Z) (EVal 1%Z) (EVal 7%Z))
      (A.LeadsTo (EVal 2%Z) (EVal 1%Z) (EVal 7%Z)))).
  { eapply container_spatial_mono; [|intros t a H; exact H |exact Hsp].
    intros t a H; apply assertion_points_to_write_active;
      [intros; exists 1%positive; split; [reflexivity |left; reflexivity] |].
    apply (proj1 (assertion_unit_strong_right _ _ _ _)),H. }
  apply assertion_spatial_writes_exclusive in HW; discriminate HW.
Qed.

Lemma literal_store_p_environment mode s :
  owned_environment two_processors mode A.Emp s checkpoint_full_cell empty_memory
    (empty_resource_value two_processors) (resource_memory two_processors checkpoint_full_cell) PoolFree.
Proof.
  apply owned_empty_frame_intro.
  - exact (proj1 (empty_generalized_well_formed two_processors)).
  - exact (proj1 (spatial_empty_left (proj1_sig checkpoint_full_cell))).
  - split; [intros i H; exact H |apply protocol_empty_satisfies].
Qed.

Theorem owned_literal_store_p_invalid mode :
  (forall s, persistent_models two_processors s checkpoint_full_cell literal_store_p_pre) /\
  ~ owned_valid two_processors mode A.Emp literal_store_p_pre
    (C.Prim (C.Common (S.Load 0 (EVal 2%Z))) (EVal 1%Z)) literal_store_p_post.
Proof.
  assert (HP : forall s, persistent_models two_processors s checkpoint_full_cell literal_store_p_pre).
  { intros s; apply (proj2 (assertion_unit_strong_right _ _ _ _)),assertion_full_cell_points_to. }
  split; [exact HP |intros Hvalid].
  assert (Hstep : program_step two_processors OrdinaryAction
    (C.Prim (C.Common (S.Load 0 (EVal 2%Z))) (EVal 1%Z))
    (State initial_registers (resource_memory two_processors checkpoint_full_cell)) halt
    (State (update initial_registers 0 7%Z) (resource_memory two_processors checkpoint_full_cell))).
  { eapply ProgramPrimitive with (p := C.Common (S.Load 0 (EVal 2%Z))) (i := 1%positive);
      [reflexivity |].
    apply PrimitiveLoad; [left; reflexivity |intros H; exact H |reflexivity]. }
  destruct (owned_safe_program_step _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    (Hvalid _ _ (HP _) 2) (literal_store_p_environment mode initial_registers) Hstep)
    as (local & pool & phase & Henv & Hupdate & Hlast).
  apply (literal_store_p_post_false (update initial_registers 0 7%Z) local).
  eapply owned_safe_terminal; [exact Hlast |eexists; reflexivity].
Qed.

(** The requested SHARE counterexample: acquisition already returns J.
    Wrapping its postcondition in another spatial J duplicates the cell. *)
Definition share_cell := writer_points_to (EVal 2%Z) (EVal 7%Z).
Definition share_lock_post := A.Temporal (A.Spatial (A.Lock (EVal 1%Z)) share_cell) (A.Barrier (EVal 1%Z)).

Lemma share_lock_post_duplicate_false s r :
  ~ persistent_models two_processors s r (A.Spatial share_cell share_lock_post).
Proof.
  intros (a & b & [[[Hd HK] Hmerge] Hmarks] & HA & HB).
  apply assertion_barrier_suffix_elim in HB.
  destruct HB as (l & c & [[Hdis [Hh Hrest]] Hcm] & HL & HC).
  destruct (writer_points_to_shape _ _ _ _ _ HA) as (loc & actor & E & Hi & Ha & Harest).
  destruct (writer_points_to_shape _ _ _ _ _ HC) as (loc' & actor' & E' & Hi' & Hc & Hcrest).
  cbn in E,E'; inversion E; inversion E'; subst loc loc'.
  apply (Hd 2%positive).
  - left; exists 7%Z; rewrite Ha; apply heap_update_same.
  - left; exists 7%Z; rewrite Hh; unfold heap_override.
    change (shared_heap (resource_memory two_processors c) 2%positive) with
      (shared_heap (underlying (proj1_sig c)) 2%positive) in Hc.
    rewrite Hc,heap_update_same; reflexivity.
Qed.

Theorem owned_original_share_lock_counterexample mode :
  owned_derivation two_processors share_cell mode A.Emp acceptance_acquire share_lock_post /\
  (forall s, persistent_models two_processors s checkpoint_full_cell (A.Spatial share_cell A.Emp)) /\
  ~ owned_valid two_processors mode A.Emp (A.Spatial share_cell A.Emp) acceptance_acquire
    (A.Spatial share_cell share_lock_post).
Proof.
  split; [apply OwnedLock |].
  assert (HP : forall s, persistent_models two_processors s checkpoint_full_cell (A.Spatial share_cell A.Emp)).
  { intros; apply (proj2 (assertion_unit_spatial_right _ _ _ _)),checkpoint_full_cell_models. }
  split; [exact HP |intros Hvalid].
  assert (Hstep : program_step two_processors (AcquireAction 1%positive) acceptance_acquire
    (State initial_registers (resource_memory two_processors checkpoint_full_cell)) halt
    (State initial_registers (acquire two_processors (resource_memory two_processors checkpoint_full_cell) 1%positive))).
  { eapply ProgramPrimitive with (p := C.Lock) (i := 1%positive); [reflexivity |].
    apply PrimitiveLock; [left; reflexivity |reflexivity |intros i H; exact H]. }
  destruct (owned_safe_program_step _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    (Hvalid _ _ (HP _) 2) (literal_store_p_environment mode initial_registers) Hstep)
    as (local & pool & phase & Henv & Hupdate & Hlast).
  apply (share_lock_post_duplicate_false initial_registers local).
  eapply owned_safe_terminal; [exact Hlast |eexists; reflexivity].
Qed.

(** This definition contains NO Lock atom, but Pure true can absorb its
    token. Thus syntactic absence of Lock does not suffice for SHARE. *)
Definition share_hidden_lock_post := A.Spatial share_cell (A.Pure BTrue).

Lemma share_hidden_lock_derivation mode :
  owned_derivation two_processors share_cell mode A.Emp acceptance_acquire share_hidden_lock_post.
Proof.
  eapply OwnedConsequence; [intros s r H; exact H |apply OwnedLock |].
  intros s r H; apply assertion_barrier_suffix_elim in H.
  apply container_spatial_comm in H.
  eapply container_spatial_mono; [intros t a HC; exact HC | |exact H].
  intros t a HL; reflexivity.
Qed.

Lemma share_hidden_lock_post_duplicate_false s r :
  ~ persistent_models two_processors s r (A.Spatial share_cell share_hidden_lock_post).
Proof.
  intros (a & b & [[[Hd HK] Hmerge] Hmarks] & HA & c & d & Hsp & HC & HD).
  destruct (writer_points_to_shape _ _ _ _ _ HA) as (loc & actor & E & Hi & Ha & Harest).
  destruct (writer_points_to_shape _ _ _ _ _ HC) as (loc' & actor' & E' & Hi' & Hc & Hcrest).
  cbn in E,E'; inversion E; inversion E'; subst loc loc'.
  apply (Hd 2%positive).
  - left; exists 7%Z; rewrite Ha; apply heap_update_same.
  - apply (resource_repaired_domain two_processors c d b (spatial_in_repaired _ _ _ _ Hsp) 2%positive).
    left; left; exists 7%Z; rewrite Hc; apply heap_update_same.
Qed.

Theorem owned_syntactic_lock_free_share_counterexample mode :
  owned_derivation two_processors share_cell mode A.Emp acceptance_acquire share_hidden_lock_post /\
  ~ owned_valid two_processors mode A.Emp (A.Spatial share_cell A.Emp) acceptance_acquire
    (A.Spatial share_cell share_hidden_lock_post).
Proof.
  split; [apply share_hidden_lock_derivation |intros Hvalid].
  assert (HP : persistent_models two_processors initial_registers checkpoint_full_cell (A.Spatial share_cell A.Emp)).
  { apply (proj2 (assertion_unit_spatial_right _ _ _ _)),checkpoint_full_cell_models. }
  assert (Hstep : program_step two_processors (AcquireAction 1%positive) acceptance_acquire
    (State initial_registers (resource_memory two_processors checkpoint_full_cell)) halt
    (State initial_registers (acquire two_processors (resource_memory two_processors checkpoint_full_cell) 1%positive))).
  { eapply ProgramPrimitive with (p := C.Lock) (i := 1%positive); [reflexivity |].
    apply PrimitiveLock; [left; reflexivity |reflexivity |intros i H; exact H]. }
  destruct (owned_safe_program_step _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    (Hvalid _ _ HP 2) (literal_store_p_environment mode initial_registers) Hstep)
    as (local & pool & phase & Henv & Hupdate & Hlast).
  apply (share_hidden_lock_post_duplicate_false initial_registers local).
  eapply owned_safe_terminal; [exact Hlast |eexists; reflexivity].
Qed.
