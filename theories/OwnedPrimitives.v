From Stdlib Require Import List ZArith Bool.
From WMLR Require Import Expressions Languages Machine BufferRelations OrderedBuffers Separation
  RepairedSeparation GeneralizedFlushing OperationalSemantics ProgramSteps Assertions
  AssertionSemantics ConcreteAssertions PersistentAssertions AssertionSubstitution Safety
  PrivateOwnership TemporalSafety TemporalFence OwnedSafety OwnedResources OwnedRules
  OwnedInterference OwnedParallel.
Import ListNotations.

(** A proof helper with concrete action obligations, not a rule constructor
    that assumes safety. All rules below discharge these obligations. *)
Lemma owned_primitive_rule active mode invariant pre primitive annotation post :
  primitive <> C.Common S.Skip ->
  (forall s local, persistent_models active s local pre -> forall pool frame whole phase,
    owned_environment active mode invariant s local pool frame whole phase -> forall actor,
    eval_expr s annotation = Z.pos actor -> ~ primitive_abort active primitive actor (State s whole)) ->
  (forall s local, persistent_models active s local pre -> forall pool frame whole phase,
    owned_environment active mode invariant s local pool frame whole phase -> forall actor t whole',
    eval_expr s annotation = Z.pos actor -> primitive_step active primitive actor (State s whole) (State t whole') ->
    exists local' pool' phase',
      owned_environment active mode invariant t local' pool' frame whole' phase' /\
      owned_update active (primitive_action primitive actor) phase phase' local pool local' pool' /\
      persistent_models active t local' post) ->
  owned_valid active mode invariant pre (C.Prim primitive annotation) post.
Proof.
  intros HnotSkip Hnoabort Haction s local HP n; destruct n; [exact I |].
  intros later Hfuture.
  assert (HP' : persistent_models active s later pre).
  { eapply persistent_assertion_flushing_closed; eassumption. }
  split; [intros [ann E]; inversion E; contradiction |].
  intros pool frame whole phase Henv; split.
  - intros Hfault; inversion Hfault; subst; eapply Hnoabort; eassumption.
  - intros action next t whole' Hstep; inversion Hstep; subst.
    match goal with H : primitive_step _ _ _ _ _ |- _ =>
      destruct (Haction _ _ HP' _ _ _ _ Henv _ _ _ ltac:(eassumption) H)
        as (local' & pool' & phase' & Henv' & Hupdate & HQ) end.
    exists local', pool', phase'; split; [exact Henv' |]. split; [exact Hupdate |apply owned_done_safe, HQ].
Qed.

Lemma owned_environment_update_stack active mode invariant s local pool frame whole phase x v :
  ~ In x (A.fv invariant) ->
  owned_environment active mode invariant s local pool frame whole phase ->
  owned_environment active mode invariant (update s x v) local pool frame whole phase.
Proof.
  intros Hfresh Henv; eapply owned_environment_stack_agrees;
    [apply agrees_update_irrelevant, Hfresh |exact Henv].
Qed.

Theorem owned_assignment_valid active mode invariant post x rhs annotation :
  ~ In x (A.fv invariant) ->
  owned_valid active mode invariant (assertion_subst x rhs post)
    (C.Prim (C.Common (S.Assign x rhs)) annotation) post.
Proof.
  intros Hfresh; apply owned_primitive_rule; [discriminate | |].
  - intros s local HP pool frame whole phase Henv actor E Hfault; inversion Hfault.
  - intros s local HP pool frame whole phase Henv actor t whole' E Hstep; inversion Hstep; subst.
    exists local, pool, phase; split; [apply owned_environment_update_stack; assumption |].
    split; [apply owned_update_identity |apply (proj1 (persistent_assertion_subst _ _ _ _ _ _)), HP].
Qed.

Theorem owned_assume_valid active mode invariant pre condition annotation :
  owned_valid active mode invariant (A.Or (A.Pure (BNot condition)) pre)
    (C.Prim (C.Common (S.Assume condition)) annotation) pre.
Proof.
  apply owned_primitive_rule; [discriminate | |].
  - intros s local HP pool frame whole phase Henv actor E Hfault; inversion Hfault.
  - intros s local HP pool frame whole phase Henv actor t whole' E Hstep; inversion Hstep; subst.
    exists local, pool, phase; split; [exact Henv |]. split; [apply owned_update_identity |].
    destruct HP as [Hb |HP]; [|exact HP]. change (negb (eval_bexpr t condition) = true) in Hb.
    match goal with H : eval_bexpr t condition = true |- _ => rewrite H in Hb end; discriminate.
Qed.

Theorem owned_assert_valid active mode invariant pre condition annotation :
  owned_valid active mode invariant (A.And (A.Pure condition) pre)
    (C.Prim (C.Common (S.Assert condition)) annotation) pre.
Proof.
  apply owned_primitive_rule; [discriminate | |].
  - intros s local [Hb HP] pool frame whole phase Henv actor E Hfault; inversion Hfault; subst.
    change (eval_bexpr s condition = true) in Hb; congruence.
  - intros s local [Hb HP] pool frame whole phase Henv actor t whole' E Hstep; inversion Hstep; subst.
    exists local, pool, phase; split; [exact Henv |]. split; [apply owned_update_identity |exact HP].
Qed.

Lemma owned_environment_mark active mode invariant s local pool frame whole phase actor (Hi : active actor) :
  owned_environment active mode invariant s local pool frame whole phase ->
  owned_environment active mode invariant s (mark_processor active local actor Hi) pool frame whole phase.
Proof.
  intros [Hp Hw [combined [[Hmerge Hmarks] Hpool]] Hmode Hstatus]; constructor; try assumption.
  exists (mark_processor active combined actor Hi); split; [|exact Hpool].
  split; [exact Hmerge |]. intros i.
  change ((complete (proj1_sig combined) i \/ i = actor) <->
    complete (proj1_sig frame) i \/ complete (proj1_sig local) i \/ i = actor).
  rewrite (Hmarks i); tauto.
Qed.

Lemma owned_fence_update active phase local pool actor (Hi : active actor) :
  owned_update active (FenceAction actor) phase phase local pool (mark_processor active local actor Hi) pool.
Proof.
  constructor; [split; [reflexivity |]; split; [reflexivity |intros; reflexivity]
    |intros; assumption |intros i [H |H]; [left; exact H |right; exact H]].
Qed.

Lemma owned_environment_empty_buffer active mode invariant s local pool frame whole phase actor :
  owned_environment active mode invariant s local pool frame whole phase -> buffers whole actor = [] ->
  buffers (resource_memory active local) actor = [].
Proof.
  intros Henv Hempty.
  destruct (owned_composition _ _ _ _ _ _ _ _ _ Henv) as (combined & [[_ [_ [Hb _]]] _] & Hpool).
  pose proof (proj2 (spatial_empty_buffer_parts _ _ _ _ Hpool Hempty)) as Hcombined.
  specialize (Hb actor); unfold resource_memory in Hcombined; rewrite Hcombined in Hb.
  pose proof (ordered_interleaves _ _ _ Hb) as Hmerge.
  unfold resource_memory; inversion Hmerge; congruence.
Qed.

Theorem owned_fence_valid active mode invariant annotation :
  owned_valid active mode invariant A.Emp
    (C.Prim (C.Common S.Fence) annotation) (A.Barrier annotation).
Proof.
  apply owned_primitive_rule; [discriminate | |].
  - intros s local HP pool frame whole phase Henv actor E Hfault; inversion Hfault.
  - intros s local HP pool frame whole phase Henv actor t whole' E Hstep; inversion Hstep; subst.
    match goal with Hi : active actor |- _ => exists (mark_processor active local actor Hi), pool, phase end.
    split; [apply owned_environment_mark, Henv |]. split; [apply owned_fence_update |].
    match goal with Hi : active actor |- _ =>
      change (barrier_atom active (eval_expr t annotation) (proj1_sig (mark_processor active local actor Hi))) end.
    rewrite E.
    eapply marked_emp_barrier; exact HP.
Qed.

Theorem owned_fence_general_valid active mode invariant pre annotation :
  owned_valid active mode invariant pre
    (C.Prim (C.Common S.Fence) annotation) (A.Temporal pre (A.Barrier annotation)).
Proof.
  apply owned_primitive_rule; [discriminate | |].
  - intros s local HP pool frame whole phase Henv actor E Hfault; inversion Hfault.
  - intros s local HP pool frame whole phase Henv actor t whole' E Hstep; inversion Hstep; subst.
    assert (Hempty : buffers (resource_memory active local) actor = []).
    { eapply owned_environment_empty_buffer; eassumption. }
    match goal with Hi : active actor |- _ =>
      exists (mark_processor active local actor Hi), pool, phase;
      pose proof (owned_marked_barrier_intro _ _ _ _ _ Hi HP Hempty) as Hpost end.
    split; [apply owned_environment_mark, Henv |]. split; [apply owned_fence_update |].
    destruct Hpost as (a & b & Htm & Ha & Hb); exists a, b; split; [exact Htm |]. split; [exact Ha |].
    change (barrier_atom active (eval_expr t annotation) (proj1_sig b)); rewrite E; exact Hb.
Qed.
