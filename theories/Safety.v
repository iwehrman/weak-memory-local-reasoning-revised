From Stdlib Require Import List Arith Lia ZArith.
From WMLR Require Import Expressions Languages Machine Separation
  OperationalSemantics Assertions AssertionSemantics ConcreteAssertions.
Import ListNotations.

Definition state_predicate := stack -> memory -> Prop.

(** Buffer-complete assertion satisfaction, used in Section 4.5.2. The
    existential resource witness avoids proof-irrelevance assumptions. *)
Definition full_satisfies active s m p : Prop :=
  exists r : resource active,
    proj1_sig r = Generalized m active /\ models active s r p.

Definition locked active m : Prop := exists i, lock_held active m i.
Definition terminal c : Prop := exists annotation, c = Concurrent.skip annotation.

Definition framed active shared frame local whole : Prop :=
  exists combined, memory_spatiotemporal active frame local combined /\
    memory_spatial shared combined whole.

(** Explicit well-formedness checks represent the dissertation's implicit
    restriction of all quantified tuples to multiprocessor memory systems. *)
Record environment active (invariant : state_predicate) s local shared frame whole : Prop := {
  environment_local_wf : memory_well_formed active local;
  environment_shared_wf : memory_well_formed active shared;
  environment_frame_wf : memory_well_formed active frame;
  environment_whole_wf : memory_well_formed active whole;
  environment_framed : framed active shared frame local whole;
  environment_lock_complete : lock_complete active whole;
  environment_invariant : invariant s shared \/ locked active whole
}.

(** The three clauses on pp. 131-132, including the existential post-step
    decomposition and the requirement that the external frame only flush.
    This is the original safety semantics, not an ownership-aware replacement. *)
Fixpoint safe active (n : nat) c s local
    (invariant post : state_predicate) : Prop :=
  match n with
  | 0 => True
  | S remaining =>
      (terminal c -> post s local) /\
      (forall shared frame whole,
        environment active invariant s local shared frame whole ->
        ~ abort active c (State s whole)) /\
      (forall shared frame whole next s' whole',
        environment active invariant s local shared frame whole ->
        step active c (State s whole) next (State s' whole') ->
        exists local' shared' frame',
          environment active invariant s' local' shared' frame' whole' /\
          memory_flushes active frame frame' /\
          safe active remaining next s' local' invariant post)
  end.

Definition valid_specification active invariant pre c post : Prop :=
  forall s local, full_satisfies active s local pre ->
    forall n, safe active n c s local
      (fun s m => full_satisfies active s m invariant)
      (fun s m => full_satisfies active s m post).

Lemma full_satisfies_agrees active s t m p :
  agrees (ConcurrentAssertion.fv p) s t ->
  full_satisfies active s m p -> full_satisfies active t m p.
Proof.
  intros Hagree [r [Hr Hp]]. exists r; split; [exact Hr |].
  apply (proj1 (concrete_satisfies_agrees _ _ _ _ _ Hagree)), Hp.
Qed.

Lemma full_satisfies_pure active s m b :
  full_satisfies active s m (ConcurrentAssertion.Pure b) -> eval_bexpr s b = true.
Proof. intros [r [_ H]]; exact H. Qed.

Lemma memory_flushes_trans active a b c :
  memory_flushes active a b -> memory_flushes active b c -> memory_flushes active a c.
Proof. intros H; induction H; intros Htail; [exact Htail | econstructor; eauto]. Qed.

Lemma safe_weaken_one active n c s local invariant post :
  safe active (S n) c s local invariant post -> safe active n c s local invariant post.
Proof.
  revert c s local. induction n; intros c s local Hsafe; [exact I |].
  destruct Hsafe as [Hterminal [Habort Hstep]]. split; [exact Hterminal |].
  split; [exact Habort |]. intros shared frame whole next s' whole' Henv Htransition.
  destruct (Hstep _ _ _ _ _ _ Henv Htransition) as [local' [shared' [frame' [Henv' [Hflush Hsafe']]]]].
  exists local', shared', frame'. split; [exact Henv' |]. split; [exact Hflush | apply IHn, Hsafe'].
Qed.

Theorem safe_index_mono active n m c s local invariant post :
  n <= m -> safe active m c s local invariant post -> safe active n c s local invariant post.
Proof.
  intros Hle. induction Hle; intros Hsafe; [exact Hsafe |].
  apply IHHle, safe_weaken_one, Hsafe.
Qed.

Theorem safe_post_mono active n c s local invariant (post post' : state_predicate) :
  (forall t m, post t m -> post' t m) ->
  safe active n c s local invariant post -> safe active n c s local invariant post'.
Proof.
  intros Hpost. revert c s local. induction n; intros c s local Hsafe; [exact I |].
  destruct Hsafe as [Hterminal [Habort Hstep]]. split; [intros H; apply Hpost, Hterminal, H |].
  split; [exact Habort |]. intros shared frame whole next s' whole' Henv Htransition.
  destruct (Hstep _ _ _ _ _ _ Henv Htransition) as [local' [shared' [frame' [Henv' [Hflush Hsafe']]]]].
  exists local', shared', frame'. split; [exact Henv' |]. split; [exact Hflush | apply IHn, Hsafe'].
Qed.

Definition assertion_entails active p q : Prop :=
  forall s (r : resource active), models active s r p -> models active s r q.

Lemma full_entails active p q : assertion_entails active p q ->
  forall s m, full_satisfies active s m p -> full_satisfies active s m q.
Proof. intros H s m [r [Hr Hp]]. exists r; split; [exact Hr | apply H, Hp]. Qed.

Theorem consequence_valid active invariant pre pre' c post' post :
  assertion_entails active pre pre' -> valid_specification active invariant pre' c post' ->
  assertion_entails active post' post -> valid_specification active invariant pre c post.
Proof.
  intros Hpre Hvalid Hpost s m Hmodels n.
  eapply safe_post_mono; [apply full_entails, Hpost |].
  apply Hvalid, (full_entails _ _ _ Hpre), Hmodels.
Qed.

Theorem disjunction_valid active invariant pre pre' c post :
  valid_specification active invariant pre c post ->
  valid_specification active invariant pre' c post ->
  valid_specification active invariant (ConcurrentAssertion.Or pre pre') c post.
Proof.
  intros Hleft Hright s m [r [Hr [Hp | Hp]]] n.
  - apply Hleft. exists r; auto.
  - apply Hright. exists r; auto.
Qed.

(** Exact finite execution length, for relating safety indices to the
    already formalized operational transitions. *)
Inductive execution active : nat -> Concurrent.command -> stack -> memory ->
    Concurrent.command -> stack -> memory -> Prop :=
| ExecuteRefl c s m : execution active 0 c s m c s m
| ExecuteNext n c s m next t middle last u final :
    step active c (State s m) next (State t middle) ->
    execution active n next t middle last u final ->
    execution active (S n) c s m last u final.

Theorem safe_execution_residual active n c s whole last t final :
  execution active n c s whole last t final ->
  forall local shared frame invariant post,
    safe active (S n) c s local invariant post ->
    environment active invariant s local shared frame whole ->
    exists local' shared' frame',
      environment active invariant t local' shared' frame' final /\
      memory_flushes active frame frame' /\ safe active 1 last t local' invariant post.
Proof.
  intros Hrun. induction Hrun; intros local shared frame invariant post Hsafe Henv.
  - exists local, shared, frame. split; [exact Henv |]. split; [constructor | exact Hsafe].
  - destruct Hsafe as [_ [_ Hprogress]].
    destruct (Hprogress _ _ _ _ _ _ Henv H) as [local' [shared' [frame' [Henv' [Hflush Hsafe']]]]].
    destruct (IHHrun _ _ _ _ _ Hsafe' Henv') as [local'' [shared'' [frame'' [Henv'' [Hflush' Hsafe'']]]]].
    exists local'', shared'', frame''. split; [exact Henv'' |]. split; [|exact Hsafe''].
    eapply memory_flushes_trans; eassumption.
Qed.

Theorem safe_execution_no_abort active n c s whole last t final local shared frame invariant post :
  execution active n c s whole last t final ->
  safe active (S n) c s local invariant post ->
  environment active invariant s local shared frame whole ->
  ~ abort active last (State t final).
Proof.
  intros Hrun Hsafe Henv.
  destruct (safe_execution_residual _ _ _ _ _ _ _ _ Hrun _ _ _ _ _ Hsafe Henv)
    as [local' [shared' [frame' [Henv' [_ [_ [Hnoabort _]]]]]]].
  exact (Hnoabort _ _ _ Henv').
Qed.

Theorem safe_execution_post active n c s whole last t final local shared frame invariant post :
  execution active n c s whole last t final ->
  safe active (S n) c s local invariant post ->
  environment active invariant s local shared frame whole -> terminal last ->
  exists local' shared' frame',
    environment active invariant t local' shared' frame' final /\
    memory_flushes active frame frame' /\ post t local'.
Proof.
  intros Hrun Hsafe Henv Hterminal.
  destruct (safe_execution_residual _ _ _ _ _ _ _ _ Hrun _ _ _ _ _ Hsafe Henv)
    as [local' [shared' [frame' [Henv' [Hflush [Hpost _]]]]]].
  exists local', shared', frame'. split; [exact Henv' |].
  split; [exact Hflush | apply Hpost, Hterminal].
Qed.

Theorem assignment_preserves_environment active invariant s local shared frame whole x rhs :
  ~ In x (ConcurrentAssertion.fv invariant) ->
  environment active (fun s m => full_satisfies active s m invariant) s local shared frame whole ->
  environment active (fun s m => full_satisfies active s m invariant)
    (update s x (eval_expr s rhs)) local shared frame whole.
Proof.
  intros Hfresh Henv. destruct Henv as [Hl Hj Hf Hw Hsep Hlock Hinv].
  constructor; try assumption. destruct Hinv as [Hinv | Hlocked]; [left | right; exact Hlocked].
  eapply full_satisfies_agrees; [apply agrees_update_irrelevant, Hfresh | exact Hinv].
Qed.

(** A checked repair of the non-silent assignment action. Full axiom validity
    also requires closure under intervening silent steps; it is not claimed here. *)
Theorem repaired_assignment_action active invariant b x rhs i s local shared frame whole :
  active i -> ~ In x (ConcurrentAssertion.fv invariant) ->
  environment active (fun s m => full_satisfies active s m invariant) s local shared frame whole ->
  full_satisfies active s local (ConcurrentAssertion.Pure (subst_bexpr x rhs b)) ->
  step active (Concurrent.Prim (Concurrent.Common (Sequential.Assign x rhs)) (EVal (Z.pos i)))
    (State s whole) halt (State (update s x (eval_expr s rhs)) whole) /\
  environment active (fun s m => full_satisfies active s m invariant)
    (update s x (eval_expr s rhs)) local shared frame whole /\
  full_satisfies active (update s x (eval_expr s rhs)) local (ConcurrentAssertion.Pure b).
Proof.
  intros Hi Hfresh Henv [r [Hr Hpre]]. split.
  - eapply StepPrimitive; [reflexivity | apply PrimitiveAssign, Hi].
  - split; [apply assignment_preserves_environment; assumption |].
    exists r; split; [exact Hr |].
    change (eval_bexpr s (subst_bexpr x rhs b) = true) in Hpre.
    rewrite eval_subst_bexpr in Hpre. exact Hpre.
Qed.
