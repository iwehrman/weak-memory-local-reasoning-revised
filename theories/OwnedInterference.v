From Stdlib Require Import List Arith ZArith.
From WMLR Require Import Expressions Languages Machine Separation OperationalSemantics ProgramSteps
  Assertions AssertionSemantics PersistentAssertions Safety Specifications OwnedSafety.
Import ListNotations.

(** Stack transport for the existing semantics. These are support lemmas,
    not a second safety predicate or a derivation-dependent certificate. *)

Lemma stack_agrees_incl xs ys s t : incl xs ys -> agrees ys s t -> agrees xs s t.
Proof. intros Hsub Hagree x Hx; apply Hagree, Hsub, Hx. Qed.

Lemma stack_agrees_sym xs s t : agrees xs s t -> agrees xs t s.
Proof. intros H x Hx; symmetry; apply H, Hx. Qed.

Lemma stack_agrees_update xs s t x v :
  agrees xs s t -> agrees xs (update s x v) (update t x v).
Proof.
  intros H y Hy; unfold update; destruct (Nat.eq_dec y x); [reflexivity |apply H, Hy].
Qed.

Lemma primitive_step_stack_agrees active primitive actor initial final :
  primitive_step active primitive actor initial final ->
  forall variables s, incl (C.primitive_fv primitive) variables ->
  agrees variables s (registers initial) ->
  exists t, primitive_step active primitive actor (State s (memory_state initial))
    (State t (memory_state final)) /\ agrees variables t (registers final).
Proof.
  destruct 1; intros variables other Hsupport Hagree; cbn [registers memory_state C.primitive_fv S.primitive_fv] in *.
  - exists other; split; [apply PrimitiveAssume; [exact H |] |exact Hagree].
    rewrite (eval_bexpr_agrees _ _ _ (stack_agrees_incl _ _ _ _ Hsupport Hagree)); exact H0.
  - exists other; split; [apply PrimitiveAssert; [exact H |] |exact Hagree].
    rewrite (eval_bexpr_agrees _ _ _ (stack_agrees_incl _ _ _ _ Hsupport Hagree)); exact H0.
  - assert (E : eval_expr other rhs = eval_expr s rhs).
    { apply eval_expr_agrees; intros y Hy; apply Hagree, Hsupport; right; exact Hy. }
    exists (update other x (eval_expr s rhs)); split.
    + rewrite <- E; apply PrimitiveAssign, H.
    + apply stack_agrees_update, Hagree.
  - assert (E : eval_expr other address = eval_expr s address).
    { apply eval_expr_agrees; intros y Hy; apply Hagree, Hsupport; right; exact Hy. }
    exists (update other x v); split.
    + apply PrimitiveLoad; [exact H |exact H0 |rewrite E; exact H1].
    + apply stack_agrees_update, Hagree.
  - assert (Ea : eval_expr other address = eval_expr s address).
    { apply eval_expr_agrees; intros y Hy; apply Hagree, Hsupport, in_or_app; auto. }
    assert (Ev : eval_expr other rhs = eval_expr s rhs).
    { apply eval_expr_agrees; intros y Hy; apply Hagree, Hsupport, in_or_app; auto. }
    exists other; split; [|exact Hagree]. rewrite <- Ev.
    eapply PrimitiveStore; [exact H |rewrite Ea; exact H0 |exact H1].
  - exists other; split; [apply PrimitiveFence; assumption |exact Hagree].
  - exists other; split; [apply PrimitiveLock; assumption |exact Hagree].
  - exists other; split; [apply PrimitiveUnlock; assumption |exact Hagree].
Qed.

Lemma primitive_abort_stack_agrees active primitive actor initial :
  primitive_abort active primitive actor initial ->
  forall variables s, incl (C.primitive_fv primitive) variables ->
  agrees variables s (registers initial) ->
  primitive_abort active primitive actor (State s (memory_state initial)).
Proof.
  destruct 1; intros variables other Hsupport Hagree; cbn [registers memory_state C.primitive_fv S.primitive_fv] in *.
  - apply AbortAssert; [exact H |].
    rewrite (eval_bexpr_agrees _ _ _ (stack_agrees_incl _ _ _ _ Hsupport Hagree)); exact H0.
  - apply AbortLoad; [exact H |exact H0 |].
    assert (E : eval_expr other address = eval_expr s address).
    { apply eval_expr_agrees; intros y Hy; apply Hagree, Hsupport; right; exact Hy. }
    rewrite E; exact H1.
  - apply AbortStore; [exact H |].
    assert (E : eval_expr other address = eval_expr s address).
    { apply eval_expr_agrees; intros y Hy; apply Hagree, Hsupport, in_or_app; auto. }
    rewrite E; exact H0.
Qed.

Theorem program_step_stack_agrees active action command initial next final :
  program_step active action command initial next final ->
  forall variables s, incl (C.fv command) variables ->
  agrees variables s (registers initial) ->
  exists t, program_step active action command (State s (memory_state initial))
    next (State t (memory_state final)) /\ agrees variables t (registers final).
Proof.
  induction 1; intros variables other Hsupport Hagree.
  - destruct (primitive_step_stack_agrees _ _ _ _ _ H0 variables other
      ltac:(intros x Hx; apply Hsupport, in_or_app; auto) Hagree) as (last & Hprimitive & Hlast).
    exists last; split; [|exact Hlast]. eapply ProgramPrimitive; [|exact Hprimitive].
    assert (E : eval_expr other annotation = eval_expr s annotation).
    { apply eval_expr_agrees; intros x Hx; apply Hagree, Hsupport, in_or_app; auto. }
    rewrite E; exact H.
  - destruct (IHprogram_step variables other
      ltac:(intros x Hx; apply Hsupport, in_or_app; auto) Hagree) as (last & Hstep & Hlast).
    exists last; split; [apply ProgramSeq, Hstep |exact Hlast].
  - exists other; split; [apply ProgramSeqDone |exact Hagree].
  - exists other; split; [apply ProgramChoiceLeft |exact Hagree].
  - exists other; split; [apply ProgramChoiceRight |exact Hagree].
  - exists other; split; [apply ProgramLoop |exact Hagree].
  - destruct (IHprogram_step variables other
      ltac:(intros x Hx; apply Hsupport, in_or_app; auto) Hagree) as (last & Hstep & Hlast).
    exists last; split; [apply ProgramParallelLeft, Hstep |exact Hlast].
  - destruct (IHprogram_step variables other
      ltac:(intros x Hx; apply Hsupport, in_or_app; auto) Hagree) as (last & Hstep & Hlast).
    exists last; split; [apply ProgramParallelRight, Hstep |exact Hlast].
  - exists other; split; [apply ProgramParallelLeftDone |exact Hagree].
  - exists other; split; [apply ProgramParallelRightDone |exact Hagree].
Qed.

Theorem abort_stack_agrees active command initial :
  abort active command initial ->
  forall variables s, incl (C.fv command) variables ->
  agrees variables s (registers initial) -> abort active command (State s (memory_state initial)).
Proof.
  induction 1; intros variables other Hsupport Hagree.
  - eapply CommandAbort.
    + assert (E : eval_expr other annotation = eval_expr s annotation).
      { apply eval_expr_agrees; intros x Hx; apply Hagree, Hsupport, in_or_app; auto. }
      rewrite E; exact H.
    + exact (primitive_abort_stack_agrees _ _ _ _ H0 variables other
        ltac:(intros x Hx; apply Hsupport, in_or_app; auto) Hagree).
  - apply SeqAbort; eapply IHabort; [|exact Hagree]. intros x Hx; apply Hsupport, in_or_app; auto.
  - apply ParallelLeftAbort; eapply IHabort; [|exact Hagree]. intros x Hx; apply Hsupport, in_or_app; auto.
  - apply ParallelRightAbort; eapply IHabort; [|exact Hagree]. intros x Hx; apply Hsupport, in_or_app; auto.
Qed.

Lemma owned_environment_stack_agrees active mode invariant s t local pool frame whole phase :
  agrees (A.fv invariant) s t ->
  owned_environment active mode invariant s local pool frame whole phase ->
  owned_environment active mode invariant t local pool frame whole phase.
Proof.
  intros Hagree [Hp Hw Hcomp Hmode Hstatus]; constructor; try assumption.
  destruct phase; [destruct Hstatus as [Hfree HJ]; split; [exact Hfree |] |exact Hstatus].
  eapply persistent_full_agrees; eassumption.
Qed.

Theorem owned_safe_stack_agrees active mode invariant n command s t local post variables :
  incl (A.fv invariant) variables -> incl (C.fv command) variables -> incl (A.fv post) variables ->
  agrees variables s t -> owned_safe active mode invariant n command s local post ->
  owned_safe active mode invariant n command t local post.
Proof.
  intros HJ; revert command s t local; induction n;
    intros command s t local HC HQ Hagree Hsafe; [exact I |].
  intros later Hfuture; destruct (Hsafe later Hfuture) as [Hdone Hprogress].
  split.
  - intros Hterminal.
    apply (proj1 (future_satisfies_agrees _ _ post s t
      (stack_agrees_incl _ _ _ _ HQ Hagree) later)), Hdone, Hterminal.
  - intros pool frame whole phase Henv.
    assert (Henv0 : owned_environment active mode invariant s later pool frame whole phase).
    { eapply owned_environment_stack_agrees; [apply stack_agrees_sym; exact (stack_agrees_incl _ _ _ _ HJ Hagree) |exact Henv]. }
    destruct (Hprogress _ _ _ _ Henv0) as [Habort Hstep]. split.
    + intros Hfault; apply Habort.
      exact (abort_stack_agrees _ _ _ Hfault variables s HC Hagree).
    + intros action next last whole' Hprogram.
      destruct (program_step_stack_agrees _ _ _ _ _ _ Hprogram variables s HC Hagree)
        as (last0 & Hprogram0 & Hagree').
      destruct (Hstep _ _ _ _ Hprogram0)
        as (local' & pool' & phase' & Henv' & Hupdate & Hsafe').
      exists local', pool', phase'; split.
      * eapply owned_environment_stack_agrees; [exact (stack_agrees_incl _ _ _ _ HJ Hagree') |exact Henv'].
      * split; [exact Hupdate |].
        eapply IHn; [|exact HQ |exact Hagree' |exact Hsafe'].
        intros x Hx; apply HC.
        eapply step_fv_subset; [exact (program_step_erases _ _ _ _ _ _ Hprogram) |exact Hx].
Qed.
