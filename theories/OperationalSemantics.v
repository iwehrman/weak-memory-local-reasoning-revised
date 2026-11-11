From Stdlib Require Import List ZArith.
From WMLR Require Import Expressions Languages Machine.
Import ListNotations.
Module S := Sequential.
Module C := Concurrent.

(** Figure 4.1. Loads require an unblocked processor, including loads served
    from that processor's buffer. Stores may issue while blocked. Fences and
    lock operations wait for an empty local buffer. *)
Inductive primitive_step (active : processor_domain)
    : C.primitive -> processor -> state -> state -> Prop :=
| PrimitiveAssume i s m condition :
    active i -> eval_bexpr s condition = true ->
    primitive_step active (C.Common (S.Assume condition)) i (State s m) (State s m)
| PrimitiveAssert i s m condition :
    active i -> eval_bexpr s condition = true ->
    primitive_step active (C.Common (S.Assert condition)) i (State s m) (State s m)
| PrimitiveAssign i s m x rhs :
    active i ->
    primitive_step active (C.Common (S.Assign x rhs)) i
      (State s m) (State (update s x (eval_expr s rhs)) m)
| PrimitiveLoad i s m x address v :
    active i -> ~ blocked m i -> local_read m i (eval_expr s address) = Some v ->
    primitive_step active (C.Common (S.Load x address)) i
      (State s m) (State (update s x v) m)
| PrimitiveStore i s m address rhs loc previous :
    active i -> eval_expr s address = Z.pos loc ->
    local_read m i (Z.pos loc) = Some previous ->
    primitive_step active (C.Common (S.Store address rhs)) i
      (State s m) (State s (enqueue m i loc (eval_expr s rhs)))
| PrimitiveFence i s m :
    active i -> buffers m i = [] ->
    primitive_step active (C.Common S.Fence) i (State s m) (State s m)
| PrimitiveLock i s m :
    active i -> buffers m i = [] -> lock_free m ->
    primitive_step active C.Lock i (State s m) (State s (acquire active m i))
| PrimitiveUnlock i s m :
    active i -> buffers m i = [] -> lock_held active m i ->
    primitive_step active C.Unlock i (State s m) (State s (release m)).

(** A false assumption is stuck. A false assertion faults. A blocked load
    waits even if its address is invalid. Skip has no primitive step. *)
Inductive primitive_abort (active : processor_domain)
    : C.primitive -> processor -> state -> Prop :=
| AbortAssert i s m condition :
    active i -> eval_bexpr s condition = false ->
    primitive_abort active (C.Common (S.Assert condition)) i (State s m)
| AbortLoad i s m x address :
    active i -> ~ blocked m i -> local_read m i (eval_expr s address) = None ->
    primitive_abort active (C.Common (S.Load x address)) i (State s m)
| AbortStore i s m address rhs :
    active i -> local_read m i (eval_expr s address) = None ->
    primitive_abort active (C.Common (S.Store address rhs)) i (State s m).

(** Figure 4.2 writes terminal skip without a processor. The syntax retains
    annotations, so generated terminal skips use a constant label. Every
    annotated skip is terminal, and its label is never evaluated. *)
Definition halt : C.command := C.skip (EVal 1%Z).

Inductive step (active : processor_domain)
    : C.command -> state -> C.command -> state -> Prop :=
| StepPrimitive p annotation s m i final :
    eval_expr s annotation = Z.pos i ->
    primitive_step active p i (State s m) final ->
    step active (C.Prim p annotation) (State s m) halt final
| StepFlush c s m m' :
    flush active m m' -> step active c (State s m) c (State s m')
| StepSeq first first' second initial final :
    step active first initial first' final ->
    step active (C.Seq first second) initial (C.Seq first' second) final
| StepSeqDone annotation next initial :
    step active (C.Seq (C.skip annotation) next) initial next initial
| StepChoiceLeft lhs rhs initial :
    step active (C.Choice lhs rhs) initial lhs initial
| StepChoiceRight lhs rhs initial :
    step active (C.Choice lhs rhs) initial rhs initial
| StepLoop body initial :
    step active (C.Loop body) initial
      (C.Choice halt (C.Seq body (C.Loop body))) initial
| StepParallelLeft lhs lhs' rhs initial final :
    step active lhs initial lhs' final ->
    step active (C.Parallel lhs rhs) initial (C.Parallel lhs' rhs) final
| StepParallelRight lhs rhs rhs' initial final :
    step active rhs initial rhs' final ->
    step active (C.Parallel lhs rhs) initial (C.Parallel lhs rhs') final
| StepParallelLeftDone annotation rhs initial :
    step active (C.Parallel (C.skip annotation) rhs) initial rhs initial
| StepParallelRightDone lhs annotation initial :
    step active (C.Parallel lhs (C.skip annotation)) initial lhs initial.

Inductive abort (active : processor_domain) : C.command -> state -> Prop :=
| CommandAbort p annotation s m i :
    eval_expr s annotation = Z.pos i ->
    primitive_abort active p i (State s m) ->
    abort active (C.Prim p annotation) (State s m)
| SeqAbort first second initial :
    abort active first initial -> abort active (C.Seq first second) initial
| ParallelLeftAbort lhs rhs initial :
    abort active lhs initial -> abort active (C.Parallel lhs rhs) initial
| ParallelRightAbort lhs rhs initial :
    abort active rhs initial -> abort active (C.Parallel lhs rhs) initial.

(** Reflexive-transitive closure of successful steps. Faulting executions
    consist of such a prefix followed by an abort. No fairness is assumed. *)
Inductive steps (active : processor_domain)
    : C.command -> state -> C.command -> state -> Prop :=
| StepsRefl c initial : steps active c initial c initial
| StepsNext c initial next middle final terminal :
    step active c initial next middle ->
    steps active next middle final terminal ->
    steps active c initial final terminal.

Lemma steps_one active c initial next final :
  step active c initial next final -> steps active c initial next final.
Proof. intros H; eapply StepsNext; [exact H | constructor]. Qed.

Lemma steps_trans active c initial middle intermediate final terminal :
  steps active c initial middle intermediate ->
  steps active middle intermediate final terminal ->
  steps active c initial final terminal.
Proof.
  intros Hprefix Hsuffix. induction Hprefix; [exact Hsuffix |].
  eapply StepsNext; eauto.
Qed.

Lemma primitive_preserves_unmodified active p i initial final :
  primitive_step active p i initial final ->
  forall x, ~ In x (C.primitive_mod p) -> registers initial x = registers final x.
Proof.
  intros Hstep. destruct Hstep; intros y Hfresh; simpl in *; try reflexivity.
  - symmetry. apply update_other. intros Heq. apply Hfresh. simpl; auto.
  - symmetry. apply update_other. intros Heq. apply Hfresh. simpl; auto.
Qed.

(** Lemma 2, p. 48, for the concurrent semantics of pp. 93-98. *)
Theorem step_fv_subset active c initial next final :
  step active c initial next final ->
  forall x, In x (C.fv next) -> In x (C.fv c).
Proof.
  intros Hstep. induction Hstep; intros x Hin; simpl in *;
    repeat rewrite in_app_iff in *; intuition eauto.
Qed.

Theorem step_modifies_subset active c initial next final :
  step active c initial next final ->
  forall x, In x (C.modifies next) -> In x (C.modifies c).
Proof.
  intros Hstep. induction Hstep; intros x Hin; simpl in *;
    repeat rewrite in_app_iff in *; intuition eauto.
Qed.

Theorem step_preserves_unmodified active c initial next final :
  step active c initial next final ->
  forall x, ~ In x (C.modifies c) -> registers initial x = registers final x.
Proof.
  intros Hstep. induction Hstep; intros x Hfresh; simpl in *; try reflexivity.
  - exact (primitive_preserves_unmodified _ _ _ _ _ H0 x Hfresh).
  - apply IHHstep. intros Hin. apply Hfresh, in_or_app. auto.
  - apply IHHstep. intros Hin. apply Hfresh, in_or_app. auto.
  - apply IHHstep. intros Hin. apply Hfresh, in_or_app. auto.
Qed.

Theorem lemma2 active c initial next final :
  step active c initial next final ->
  (forall x, In x (C.fv next) -> In x (C.fv c)) /\
  (forall x, In x (C.modifies next) -> In x (C.modifies c)) /\
  (forall x, ~ In x (C.modifies c) -> registers initial x = registers final x).
Proof.
  intros H. repeat split.
  - eapply step_fv_subset; eauto.
  - eapply step_modifies_subset; eauto.
  - eapply step_preserves_unmodified; eauto.
Qed.

Theorem steps_preserve_unmodified active c initial final terminal :
  steps active c initial final terminal ->
  forall x, ~ In x (C.modifies c) -> registers initial x = registers terminal x.
Proof.
  intros Hsteps. induction Hsteps; intros x Hfresh; [reflexivity |].
  transitivity (registers middle x).
  - eapply step_preserves_unmodified; eauto.
  - apply IHHsteps. intros Hin. apply Hfresh.
    eapply step_modifies_subset; eauto.
Qed.

Theorem steps_fv_subset active c initial final terminal :
  steps active c initial final terminal ->
  forall x, In x (C.fv final) -> In x (C.fv c).
Proof.
  intros Hsteps. induction Hsteps; intros x Hin; [exact Hin |].
  eapply step_fv_subset; [exact H | apply IHHsteps, Hin].
Qed.

Theorem steps_modifies_subset active c initial final terminal :
  steps active c initial final terminal ->
  forall x, In x (C.modifies final) -> In x (C.modifies c).
Proof.
  intros Hsteps. induction Hsteps; intros x Hin; [exact Hin |].
  eapply step_modifies_subset; [exact H | apply IHHsteps, Hin].
Qed.

Lemma primitive_preserves_well_formed active p i initial final :
  primitive_step active p i initial final ->
  memory_well_formed active (memory_state initial) ->
  memory_well_formed active (memory_state final).
Proof.
  intros Hstep Hwf. destruct Hstep; simpl in *; try exact Hwf.
  - apply update_buffers_well_formed; assumption.
  - apply acquire_well_formed, Hwf.
  - apply release_well_formed, Hwf.
Qed.

Theorem step_preserves_well_formed active c initial next final :
  step active c initial next final ->
  memory_well_formed active (memory_state initial) ->
  memory_well_formed active (memory_state final).
Proof.
  intros Hstep. induction Hstep; intros Hwf; try exact Hwf; try auto.
  - eapply primitive_preserves_well_formed; eauto.
  - eapply flush_preserves_well_formed; eauto.
Qed.

Lemma primitive_preserves_lock_complete active p i initial final :
  primitive_step active p i initial final ->
  lock_complete active (memory_state initial) ->
  lock_complete active (memory_state final).
Proof.
  intros Hstep Hcomplete. destruct Hstep; simpl in *; try exact Hcomplete.
  - right. exists i. split; [assumption | intros j; reflexivity].
  - left. intros j Hblocked. exact Hblocked.
Qed.

Theorem step_preserves_lock_complete active c initial next final :
  step active c initial next final ->
  lock_complete active (memory_state initial) ->
  lock_complete active (memory_state final).
Proof.
  intros Hstep. induction Hstep; intros Hcomplete; try exact Hcomplete; try auto.
  - eapply primitive_preserves_lock_complete; eauto.
  - eapply flush_preserves_lock_complete; eauto.
Qed.

Theorem steps_preserve_well_formed active c initial final terminal :
  steps active c initial final terminal ->
  memory_well_formed active (memory_state initial) ->
  memory_well_formed active (memory_state terminal).
Proof.
  intros Hsteps. induction Hsteps; intros Hwf; [exact Hwf |].
  apply IHHsteps. eapply step_preserves_well_formed; eauto.
Qed.

Theorem steps_preserve_lock_complete active c initial final terminal :
  steps active c initial final terminal ->
  lock_complete active (memory_state initial) ->
  lock_complete active (memory_state terminal).
Proof.
  intros Hsteps. induction Hsteps; intros Hcomplete; [exact Hcomplete |].
  apply IHHsteps. eapply step_preserves_lock_complete; eauto.
Qed.
