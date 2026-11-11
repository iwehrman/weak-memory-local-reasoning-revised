From Stdlib Require Import List ZArith.
From WMLR Require Import Expressions Languages Machine BufferRelations Separation RepairedFlushing
  OperationalSemantics ExecutionExamples Assertions AssertionSemantics PersistentAssertions Safety
  HeapRules OwnershipProtocol OwnershipHeap OwnershipExamples PrivateOwnership PrivateRules PrivateCalculus
  SpatialExchange PrivateFraming PrivateExamples ParallelExamples ParallelLoads Specifications.
Import ListNotations.

Definition spatial_pending := Memory empty_heap
  (buffer_update empty_buffers 2%positive [(3%positive, 17%Z)]) no_blocked.
Definition spatial_pending_assertion := A.LeadsTo (EVal 3%Z) (EVal 2%Z) (EVal 17%Z).
Definition add_spatial_pending m := Memory (shared_heap m) (buffers spatial_pending) (blocked m).
Definition framed_initial := add_spatial_pending private_initial.
Definition framed_flushed := flush_write framed_initial 2%positive 3%positive 17%Z [].

Lemma spatial_pending_models s : persistent_full_satisfies two_processors s spatial_pending spatial_pending_assertion.
Proof.
  assert (Hwf : generalized_well_formed two_processors (Generalized spatial_pending two_processors)).
  { split; [split |split].
    - intros i H; contradiction.
    - intros i H; cbn [underlying spatial_pending buffers]; unfold buffer_update.
      destruct (Pos.eq_dec i 2%positive) as [-> |Hneq]; [exfalso; apply H; right; reflexivity |reflexivity].
    - auto.
    - intros H loc; exfalso; apply (H 1%positive); left; reflexivity. }
  exists (exist _ _ Hwf); split; [reflexivity |]. split; [right; reflexivity |].
  left; split; [intros; reflexivity |]. split; [intros; reflexivity |intros i H; contradiction].
Qed.

Lemma spatial_pending_domain loc : memory_domain spatial_pending loc -> loc = 3%positive.
Proof.
  intros [[v H] |[i [v H]]]; [discriminate |].
  cbn [spatial_pending buffers] in H; unfold buffer_update in H.
  destruct (Pos.eq_dec i 2%positive); [|contradiction]. simpl in H. intuition congruence.
Qed.

Lemma spatial_pending_extension m : (forall i, buffers m i = []) -> ~ memory_domain m 3%positive ->
  memory_spatial m spatial_pending (add_spatial_pending m).
Proof.
  intros Hempty Hfresh; split.
  - split.
    + intros loc Hm Hp; apply spatial_pending_domain in Hp; subst; contradiction.
    + intros i _ H; contradiction.
  - split; [intros; reflexivity |]. split.
    + intros i; cbn [add_spatial_pending buffers]; rewrite Hempty.
      exact (interleaves_app [] (buffers spatial_pending i)).
    + intros i; simpl; unfold no_blocked; tauto.
Qed.

Lemma framed_initial_extension : memory_spatial private_initial spatial_pending framed_initial.
Proof.
  apply spatial_pending_extension; [intros; reflexivity |].
  intros [[v H] |[i [v H]]]; [discriminate |contradiction].
Qed.

Theorem framed_restore_valid : private_valid two_processors 1%positive protected_seven
  Closed (A.Spatial retained_assertion spatial_pending_assertion) private_restore_program Closed
  (A.Spatial private_final_assertion spatial_pending_assertion).
Proof.
  apply private_spatial_frame_valid.
  - apply private_calculus_sound, private_restore_derivable.
  - intros x _ H; contradiction.
Qed.

Lemma framed_initial_certificate s : exists local,
  private_environment two_processors 1%positive protected_seven Closed s local framed_initial empty_memory framed_initial /\
  persistent_full_satisfies two_processors s local (A.Spatial retained_assertion spatial_pending_assertion).
Proof.
  pose proof (proj1 (persistent_full_well_formed _ _ _ _ (spatial_pending_models s))) as Hpending.
  destruct (private_region_extend _ _ _ _ _ _ _ _ _
    (private_region_ok _ _ _ _ _ _ _ _ _ (private_initial_environment s)) Hpending
    ltac:(intros i H; contradiction) framed_initial_extension) as (local & Hr & Hlocal).
  exists local; split.
  - constructor.
    + exact Hr.
    + exact (proj1 (empty_generalized_well_formed two_processors)).
    + exact (proj1 (proj2 Hr)).
    + intros i H; contradiction.
    + exact (proj1 (spatial_empty_left (Generalized framed_initial two_processors))).
  - eapply full_spatial_intro; [exact Hlocal |apply retained_cell_models |apply spatial_pending_models].
Qed.

Theorem framed_restore_no_abort s n last t final :
  execution two_processors n private_restore_program s framed_initial last t final ->
  ~ abort two_processors last (State t final).
Proof.
  intros Hrun. destruct (framed_initial_certificate s) as (local & Henv & HP).
  eapply private_execution_no_abort; [exact Hrun | |exact Henv].
  apply framed_restore_valid; [exact (private_region_ok _ _ _ _ _ _ _ _ _ Henv) |exact HP].
Qed.

Theorem framed_restore_all_terminating_runs s n last t final :
  execution two_processors n private_restore_program s framed_initial last t final -> terminal last ->
  lock_free final /\ t 0 = 11%Z /\ exists local pool region external,
    memory_spatial pool local region /\ memory_spatial external region final /\
    persistent_full_satisfies two_processors t pool protected_seven /\
    persistent_full_satisfies two_processors t local (A.Spatial private_final_assertion spatial_pending_assertion).
Proof.
  intros Hrun Hlast. destruct (framed_initial_certificate s) as (local & Henv & HP).
  assert (Hsafe : private_safe two_processors 1%positive protected_seven (S n) private_restore_program s
    Closed local framed_initial Closed (A.Spatial private_final_assertion spatial_pending_assertion)).
  { apply framed_restore_valid; [exact (private_region_ok _ _ _ _ _ _ _ _ _ Henv) |exact HP]. }
  destruct (private_execution_closed_post _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hrun Hsafe Henv Hlast)
    as (local' & pool & region & external & Hinner & Houter & Hflush & Hfree & HJ & HQ).
  split; [exact Hfree |]. split.
  - destruct (full_spatial_elim _ _ _ _ _ HQ) as (left & right & Hsep & Hleft & Hright).
    exact (proj2 (loaded_cell_elim _ _ _ _ _ _ Hleft)).
  - exists local', pool, region, external; auto.
Qed.

Example framed_restore_trace s : execution two_processors 14 private_restore_program s framed_initial halt
  (update s 0 11%Z) (restore_result two_processors 1%positive 9%Z framed_flushed).
Proof.
  eapply ExecuteNext with (middle := framed_flushed).
  - apply StepFlush. constructor; [right; reflexivity |intros H; contradiction |reflexivity].
  - change (execution two_processors 13 (restore_and_load 1%positive 9%Z 2%positive 0) s framed_flushed
      halt (update s 0 11%Z) (restore_result two_processors 1%positive 9%Z framed_flushed)).
    apply restore_and_load_trace;
      [left; reflexivity |intros i H; contradiction | |reflexivity |reflexivity |discriminate].
    intros i. cbn [framed_flushed flush_write buffers framed_initial add_spatial_pending spatial_pending].
    unfold buffer_update; destruct (Pos.eq_dec i 2%positive); reflexivity.
Qed.
