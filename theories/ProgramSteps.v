From Stdlib Require Import ZArith.
From WMLR Require Import Expressions Languages Machine OperationalSemantics.

(** Labels classify existing non-flush steps; they do not change execution.
    In particular, a fence and an assumption may both leave memory unchanged. *)
Inductive program_action :=
| OrdinaryAction
| FenceAction (actor : processor)
| AcquireAction (actor : processor)
| ReleaseAction (actor : processor).

Definition primitive_action (p : Concurrent.primitive) (i : processor) :=
  match p with
  | Concurrent.Common Sequential.Fence => FenceAction i
  | Concurrent.Lock => AcquireAction i
  | Concurrent.Unlock => ReleaseAction i
  | _ => OrdinaryAction
  end.

Inductive program_step active : program_action ->
    Concurrent.command -> state -> Concurrent.command -> state -> Prop :=
| ProgramPrimitive p annotation s m i final :
    eval_expr s annotation = Z.pos i ->
    primitive_step active p i (State s m) final ->
    program_step active (primitive_action p i)
      (Concurrent.Prim p annotation) (State s m) halt final
| ProgramSeq action first first' second initial final :
    program_step active action first initial first' final ->
    program_step active action (Concurrent.Seq first second) initial
      (Concurrent.Seq first' second) final
| ProgramSeqDone annotation next initial :
    program_step active OrdinaryAction (Concurrent.Seq (Concurrent.skip annotation) next)
      initial next initial
| ProgramChoiceLeft lhs rhs initial :
    program_step active OrdinaryAction (Concurrent.Choice lhs rhs) initial lhs initial
| ProgramChoiceRight lhs rhs initial :
    program_step active OrdinaryAction (Concurrent.Choice lhs rhs) initial rhs initial
| ProgramLoop body initial :
    program_step active OrdinaryAction (Concurrent.Loop body) initial
      (Concurrent.Choice halt (Concurrent.Seq body (Concurrent.Loop body))) initial
| ProgramParallelLeft action lhs lhs' rhs initial final :
    program_step active action lhs initial lhs' final ->
    program_step active action (Concurrent.Parallel lhs rhs) initial
      (Concurrent.Parallel lhs' rhs) final
| ProgramParallelRight action lhs rhs rhs' initial final :
    program_step active action rhs initial rhs' final ->
    program_step active action (Concurrent.Parallel lhs rhs) initial
      (Concurrent.Parallel lhs rhs') final
| ProgramParallelLeftDone annotation rhs initial :
    program_step active OrdinaryAction (Concurrent.Parallel (Concurrent.skip annotation) rhs)
      initial rhs initial
| ProgramParallelRightDone lhs annotation initial :
    program_step active OrdinaryAction (Concurrent.Parallel lhs (Concurrent.skip annotation))
      initial lhs initial.

Theorem program_step_erases active action c initial next final :
  program_step active action c initial next final -> step active c initial next final.
Proof. induction 1; econstructor; eassumption. Qed.

Theorem step_program_or_flush active c initial next final :
  step active c initial next final ->
  (exists action, program_step active action c initial next final) \/
  (next = c /\ registers final = registers initial /\
    flush active (memory_state initial) (memory_state final)).
Proof.
  induction 1.
  - left; eexists; econstructor; eassumption.
  - right; repeat split; assumption || reflexivity.
  - destruct IHstep as [[action Hprogram] | [-> [Hs Hflush]]].
    + left; exists action; apply ProgramSeq, Hprogram.
    + right; auto.
  - left; exists OrdinaryAction; constructor.
  - left; exists OrdinaryAction; constructor.
  - left; exists OrdinaryAction; constructor.
  - left; exists OrdinaryAction; constructor.
  - destruct IHstep as [[action Hprogram] | [-> [Hs Hflush]]].
    + left; exists action; apply ProgramParallelLeft, Hprogram.
    + right; auto.
  - destruct IHstep as [[action Hprogram] | [-> [Hs Hflush]]].
    + left; exists action; apply ProgramParallelRight, Hprogram.
    + right; auto.
  - left; exists OrdinaryAction; constructor.
  - left; exists OrdinaryAction; constructor.
Qed.

Corollary state_step_program_or_flush active c s m next t m' :
  step active c (State s m) next (State t m') ->
  (exists action, program_step active action c (State s m) next (State t m')) \/
  (next = c /\ t = s /\ flush active m m').
Proof. apply step_program_or_flush. Qed.

Lemma program_skip_impossible active action annotation initial next final :
  ~ program_step active action (Concurrent.skip annotation) initial next final.
Proof.
  intros H; inversion H; subst.
  match goal with Hprim : primitive_step _ _ _ _ _ |- _ => inversion Hprim end.
Qed.
