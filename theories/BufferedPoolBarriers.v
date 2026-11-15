From Stdlib Require Import List ZArith Bool.
From WMLR Require Import Expressions Languages Machine BufferRelations Separation RepairedSeparation
  GeneralizedFlushing OperationalSemantics ProgramSteps Assertions AssertionSemantics ConcreteAssertions
  PersistentAssertions PersistentRules PrivateOwnership OwnedHeapResources TemporalSafety TemporalFence InvariantFragment OwnedSafety AssertionResourceEquivalence
  RepairedExamples RegionalResources Specifications Safety BufferedPoolCandidate BufferedPoolResources BufferedPoolRules BufferedPoolPrimitives
  BufferedPoolCalculus BufferedDekkerResources.
Import ListNotations.

(** Initial barriers describe empty private histories. They change no machine
    state and make no claim that some other component's buffer is empty. *)
Definition buffered_initial_barrier active actor (Hi : active actor) : resource active :=
  mark_processor active (empty_resource_value active) actor Hi.

Lemma buffered_initial_barrier_models active actor (Hi : active actor) s :
  persistent_models active s (buffered_initial_barrier active actor Hi) (A.Barrier (EVal (Z.pos actor))).
Proof. apply marked_emp_barrier,bare_resource_models. Qed.

Lemma buffered_initial_barriers_split active i j (Hi : active i) (Hj : active j) s :
  exists local : resource active, resource_memory active local = empty_memory /\
    persistent_models active s local (A.Spatial (A.Barrier (EVal (Z.pos i))) (A.Barrier (EVal (Z.pos j)))).
Proof.
  set (a := buffered_initial_barrier active i Hi).
  set (b := buffered_initial_barrier active j Hj).
  exists (mark_processor active a j Hj); split; [reflexivity |].
  exists a,b; split.
  - split; [exact (proj1 (spatial_empty_left empty_generalized)) |].
    intros k; cbn; unfold no_blocked; tauto.
  - split; apply buffered_initial_barrier_models.
Qed.

(** No empty-buffer hypothesis is needed: the private resources are empty.
    In particular this initializes both barriers on every empty-buffer start. *)
Theorem buffered_barrier_parallel_initial_adequacy active J i j left right LQ RQ :
  active i -> active j -> buffered_invariant_fragment J ->
  buffered_derivation active J (A.Barrier (EVal (Z.pos i))) left LQ ->
  buffered_derivation active J (A.Barrier (EVal (Z.pos j))) right RQ ->
  parallel_variable_condition
    (Build_concurrent_specification J (A.Barrier (EVal (Z.pos i))) left LQ)
    (Build_concurrent_specification J (A.Barrier (EVal (Z.pos j))) right RQ) ->
  frame_variable_condition left J -> frame_variable_condition right J ->
  forall n s whole last t final,
    persistent_full_satisfies active s whole J -> lock_free whole ->
    execution active n (C.Parallel left right) s whole last t final ->
    ~ abort active last (State t final) /\
    (terminal last -> exists local' pool', memory_spatial pool' (resource_memory active local') final /\
      lock_free final /\ persistent_full_satisfies active t pool' J /\
      persistent_models active t local' (A.Spatial LQ RQ)).
Proof.
  intros Hi Hj Hfragment HL HR Hvars HLJ HRJ n s whole last t final HJ Hfree Hrun.
  destruct (buffered_initial_barriers_split active i j Hi Hj s) as (local & E & HP).
  eapply buffered_derivation_adequacy with (local := local) (pool := whole); try eassumption.
  - eapply BufferedParallel; eassumption.
  - rewrite E; exact (proj1 (spatial_empty_right (Generalized whole active))).
Qed.

(** The addendum's literal triple also admits the empty-pool branch. A
    barrier cannot make its unallocated load safe, independently of marks. *)
Theorem buffered_barrier_load_withdrawal_premise_invalid :
  ~ buffered_atomic_premise BD.active
    (A.Or A.Emp (writer_points_to (EVal 1%Z) (EVal 0%Z))) (A.Barrier (EVal 1%Z))
    (S.Load 0 (EVal 1%Z)) (EVal 1%Z)
    (A.Spatial (A.Barrier (EVal 1%Z)) (writer_points_to (EVal 1%Z) (EVal 0%Z))).
Proof.
  intros [_ HP]. set (s := fun _ : ident => (-1)%Z).
  pose (local := buffered_initial_barrier BD.active 1%positive (or_introl eq_refl)).
  assert (HJ : persistent_full_satisfies BD.active s empty_memory
    (A.Or A.Emp (writer_points_to (EVal 1%Z) (EVal 0%Z)))).
  { exists (exist _ (Generalized empty_memory BD.active) (empty_full_valid BD.active)); split; [reflexivity |].
    left; change (empty_atom (Generalized empty_memory BD.active)); split; [intros; reflexivity |].
    split; [intros; reflexivity |intros i H; exact H]. }
  destruct (HP s local empty_memory empty_memory (buffered_initial_barrier_models _ _ _ _) HJ
    (proj1 (spatial_empty_left empty_generalized)) ltac:(intros i H; exact H)) as [Hbad _].
  apply Hbad; eapply CommandAbort with (i := 1%positive); [reflexivity |].
  apply AbortLoad; [left; reflexivity |intros H; exact H |reflexivity].
Qed.

Lemma buffered_empty_spatial active (a b : resource active) :
  empty_atom (proj1_sig a) ->
  (forall i, complete (proj1_sig a) i -> complete (proj1_sig b) i) ->
  spatial (proj1_sig a) (proj1_sig b) (proj1_sig b).
Proof.
  intros [Hheap [Hbuf Hfree]] Hmarks; split; [|intros i; split; [auto |intros [H |H]; auto]].
  split.
  - split.
    + intros loc [[v H] |[i [v H]]] HB; [rewrite Hheap in H; discriminate |rewrite Hbuf in H; contradiction].
    + intros i H; exfalso; exact (Hfree i H).
  - split.
    + intros loc; unfold heap_override; rewrite Hheap; destruct (shared_heap (underlying (proj1_sig b)) loc); reflexivity.
    + split; [intros i; rewrite Hbuf; apply interleaves_app |intros i; split; [auto |intros [H |H]; [exfalso; exact (Hfree i H) |exact H]]].
Qed.

(** The nonempty branch does allow withdrawal with exactly the old marks.
    This lemma is a successor construction, not a universally safe triple. *)
Lemma buffered_marked_cell_withdrawal s local pool whole :
  persistent_models BD.active s local (A.Barrier (EVal 1%Z)) ->
  persistent_full_satisfies BD.active s pool (writer_points_to (EVal 1%Z) (EVal 0%Z)) ->
  memory_spatial pool (resource_memory BD.active local) whole ->
  exists local' : resource BD.active,
    memory_spatial empty_memory (resource_memory BD.active local') whole /\
    persistent_models BD.active s local'
      (A.Spatial (A.Barrier (EVal 1%Z)) (writer_points_to (EVal 1%Z) (EVal 0%Z))) /\
    buffered_update BD.active OrdinaryAction local pool local' empty_memory.
Proof.
  intros HP (r & Er & Hr) Hsp.
  assert (Hmark : complete (proj1_sig local) 1%positive).
  { destruct (proj2 HP) as [Hbad |H]; [exfalso; apply Hbad; left; reflexivity |exact H]. }
  destruct (BD.cell_shape s r 1%positive 0%Z Hr) as [Hpool _].
  unfold resource_memory in Hpool; rewrite Er in Hpool; cbn in Hpool.
  destruct (proj1 HP) as [Hheap [Hbuf Hfree]].
  assert (Hwhole : memory_equiv whole (BD.mem (BD.cell 1%positive 0%Z))).
  { destruct Hsp as [_ [Hh [Hb Hk]]]; split.
    - intros loc; rewrite Hh; unfold heap_override; rewrite Hheap; apply Hpool.
    - split.
      + intros i; specialize (Hb i); rewrite Hbuf in Hb; apply interleaves_nil_right in Hb; rewrite Hb; apply Hpool.
      + intros i; rewrite Hk,(proj2 (proj2 Hpool) i); split; [intros [H |H]; [exact H |exfalso; exact (Hfree i H)] |auto]. }
  set (received := BD.with_marks (BD.cell 1%positive 0%Z) local 1%positive Hmark).
  assert (Hcell : persistent_models BD.active s received (writer_points_to (EVal 1%Z) (EVal 0%Z))).
  { apply writer_points_to_from_shape with (loc := 1%positive) (owner := 1%positive);
      try reflexivity; [left; reflexivity | |intros i H; exact H |exact Hmark].
    intros i; unfold received,resource_memory,BD.with_marks,BD.mem,BD.cell; cbn;
      destruct (Pos.eq_dec i 1%positive), (Pos.eq_dec i 2%positive); reflexivity. }
  exists received; split.
  - eapply BD.spatial_equiv; [apply assertion_memory_equiv_refl |apply assertion_memory_equiv_refl |
      apply assertion_memory_equiv_sym,Hwhole |exact (proj1 (spatial_empty_left (proj1_sig received)))].
  - split.
    + exists local,received; split; [apply buffered_empty_spatial; [exact (proj1 HP) |auto] |auto].
    + constructor; [|intros i H; left; exact H].
      intros loc [H |H]; [destruct H as [[v H] |[i [v H]]]; discriminate || contradiction |].
      left; apply (proj2 (assertion_domain_equiv _ _ Hpool loc)); exact H.
Qed.

(** A nearby true atomic contract: the stack guard selects the allocated
    branch before the load and the empty branch after it. This is deliberately
    a single-thread protocol; CONC cannot transport a sibling across changes
    to this invariant's guard register. *)
Definition buffered_withdrawal_guard := BEq (EVar 0) (EVal 0%Z).
Definition buffered_guarded_withdrawal_invariant :=
  A.Or (A.And (A.Pure (BNot buffered_withdrawal_guard)) (writer_points_to (EVal 1%Z) (EVal 0%Z)))
    (A.And (A.Pure buffered_withdrawal_guard) A.Emp).

Theorem buffered_guarded_barrier_withdrawal_premise :
  buffered_atomic_premise BD.active buffered_guarded_withdrawal_invariant
    (A.And (A.Pure (BNot buffered_withdrawal_guard)) (A.Barrier (EVal 1%Z)))
    (S.Load 0 (EVal 1%Z)) (EVal 1%Z)
    (A.Spatial (A.Barrier (EVal 1%Z)) (writer_points_to (EVal 1%Z) (EVal 0%Z))).
Proof.
  assert (Hallocated : forall s local pool, persistent_models BD.active s local
    (A.And (A.Pure (BNot buffered_withdrawal_guard)) (A.Barrier (EVal 1%Z))) ->
    persistent_full_satisfies BD.active s pool buffered_guarded_withdrawal_invariant ->
    persistent_full_satisfies BD.active s pool (writer_points_to (EVal 1%Z) (EVal 0%Z))).
  { intros s local pool [Hguard Hbar] (r & E & [[Hsame Hcell] |[Hwrong Hemp]]).
    - exists r; auto.
    - change (negb (eval_bexpr s buffered_withdrawal_guard) = true) in Hguard.
      change (eval_bexpr s buffered_withdrawal_guard = true) in Hwrong; rewrite Hwrong in Hguard; discriminate. }
  apply buffered_primitive_premise; [exact I | |].
  - intros s local HP pool whole HJ Hsp Hfree actor E Hbad.
    destruct (Hallocated _ _ _ HP HJ) as (r & Er & Hr).
    destruct (buffered_cell_read _ _ _ _ _ actor Hr) as (loc & Ea & Hread & _).
    cbn in Ea; injection Ea as Ea; subst loc.
    unfold resource_memory in Hread; rewrite Er in Hread; cbn in Hread.
    pose proof (spatial_read_right _ _ _ _ _ _ (memory_spatial_comm _ _ _ Hsp) Hread) as Hwhole.
    change (local_read whole actor (eval_expr s (EVal 1%Z)) = Some 0%Z) in Hwhole.
    inversion Hbad; subst; congruence.
  - intros s local HP pool whole HJ Hsp Hfree actor t whole' E Hstep.
    destruct (Hallocated _ _ _ HP HJ) as (r & Er & Hr).
    destruct (buffered_cell_read _ _ _ _ _ actor Hr) as (loc & Ea & Hread & _).
    cbn in Ea; injection Ea as Ea; subst loc.
    unfold resource_memory in Hread; rewrite Er in Hread; cbn in Hread.
    pose proof (spatial_read_right _ _ _ _ _ _ (memory_spatial_comm _ _ _ Hsp) Hread) as Hwhole.
    change (local_read whole actor (eval_expr s (EVal 1%Z)) = Some 0%Z) in Hwhole.
    inversion Hstep; subst.
    match goal with H : local_read _ _ _ = Some ?v |- _ => assert (v = 0%Z) by congruence; subst v end.
    destruct (buffered_marked_cell_withdrawal s local pool whole' (proj2 HP)
      (ex_intro _ r (conj Er Hr)) Hsp) as (received & Hout & Hpost & Hbudget).
    exists received,empty_memory; split; [exact Hout |]. split; [exact Hfree |]. split.
    + exists (exist _ (Generalized empty_memory BD.active) (empty_full_valid BD.active)); split; [reflexivity |].
      right; split; [change (Z.eqb (update s 0 0%Z 0) 0%Z = true); rewrite update_same; reflexivity |].
      change (empty_atom (Generalized empty_memory BD.active)); split; [intros; reflexivity |].
      split; [intros; reflexivity |intros i H; exact H].
    + split; [|exact Hbudget].
      assert (Hagree : agrees (A.fv (A.Spatial (A.Barrier (EVal 1%Z))
        (writer_points_to (EVal 1%Z) (EVal 0%Z)))) s (update s 0 0%Z)).
      { intros x Hx; cbn in Hx; contradiction. }
      apply (proj1 (future_satisfies_agrees _ _ _ _ _ Hagree received)),Hpost.
Qed.

Theorem buffered_guarded_barrier_withdrawal_derived :
  buffered_derivation BD.active buffered_guarded_withdrawal_invariant
    (A.And (A.Pure (BNot buffered_withdrawal_guard)) (A.Barrier (EVal 1%Z)))
    (C.Prim (C.Common (S.Load 0 (EVal 1%Z))) (EVal 1%Z))
    (A.Spatial (A.Barrier (EVal 1%Z)) (writer_points_to (EVal 1%Z) (EVal 0%Z))).
Proof. apply BufferedAtomic,buffered_guarded_barrier_withdrawal_premise. Qed.

Theorem buffered_guarded_barrier_withdrawal_valid :
  buffered_valid BD.active buffered_guarded_withdrawal_invariant
    (A.And (A.Pure (BNot buffered_withdrawal_guard)) (A.Barrier (EVal 1%Z)))
    (C.Prim (C.Common (S.Load 0 (EVal 1%Z))) (EVal 1%Z))
    (A.Spatial (A.Barrier (EVal 1%Z)) (writer_points_to (EVal 1%Z) (EVal 0%Z))).
Proof.
  apply buffered_calculus_sound; [|apply buffered_guarded_barrier_withdrawal_derived].
  apply BufferedOr; apply BufferedGuard; [apply BufferedCell |apply BufferedEmp].
Qed.

Theorem buffered_guarded_barrier_withdrawal_enabled :
  let s := fun _ : ident => (-1)%Z in
  let local := buffered_initial_barrier BD.active 1%positive (or_introl eq_refl) in
  let whole := BD.mem (BD.cell 1%positive 0%Z) in
  persistent_models BD.active s local
    (A.And (A.Pure (BNot buffered_withdrawal_guard)) (A.Barrier (EVal 1%Z))) /\
  persistent_full_satisfies BD.active s whole buffered_guarded_withdrawal_invariant /\
  memory_spatial whole (resource_memory BD.active local) whole /\
  program_step BD.active OrdinaryAction (C.Prim (C.Common (S.Load 0 (EVal 1%Z))) (EVal 1%Z))
    (State s whole) halt (State (update s 0 0%Z) whole).
Proof.
  cbn zeta; split; [split; [reflexivity |apply buffered_initial_barrier_models] |].
  split.
  - exists (BD.full (BD.cell 1%positive 0%Z)); split; [reflexivity |].
    left; split; [reflexivity |apply BD.full_cell].
  - split; [exact (proj1 (spatial_empty_right (proj1_sig (BD.full (BD.cell 1%positive 0%Z))))) |].
    eapply ProgramPrimitive with (i := 1%positive) (p := C.Common (S.Load 0 (EVal 1%Z))); [reflexivity |].
    apply PrimitiveLoad; [left; reflexivity |intros H; exact H |reflexivity].
Qed.
