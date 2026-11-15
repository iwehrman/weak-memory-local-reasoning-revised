From Stdlib Require Import List.
From WMLR Require Import Expressions Languages Machine Separation GeneralizedFlushing
  OperationalSemantics ProgramSteps Assertions AssertionSemantics PersistentAssertions
  Safety Specifications OwnedSafety OwnedInterference BufferedPoolCandidate BufferedPoolRules.
Import ListNotations.

Lemma buffered_environment_stack_agrees active mode J s t local pool frame whole :
  agrees (A.fv J) s t -> buffered_environment active mode J s local pool frame whole ->
  buffered_environment active mode J t local pool frame whole.
Proof.
  intros Hagree [Hp Hw Hfree HJ Hcomp Hmode]; constructor; try assumption.
  eapply persistent_full_agrees; eassumption.
Qed.

Theorem buffered_safe_stack_agrees active mode J n c s t local Q variables :
  incl (A.fv J) variables -> incl (C.fv c) variables -> incl (A.fv Q) variables ->
  agrees variables s t -> buffered_safe active mode J n c s local Q ->
  buffered_safe active mode J n c t local Q.
Proof.
  intros HJ; revert c s t local; induction n;
    intros c s t local HC HQ Hagree Hsafe; [exact I |].
  intros later Hfuture; destruct (Hsafe later Hfuture) as [Hdone Hprogress].
  split.
  - intros Hterminal; apply (proj1 (future_satisfies_agrees _ _ Q s t
      (stack_agrees_incl _ _ _ _ HQ Hagree) later)), Hdone, Hterminal.
  - intros pool frame whole Henv.
    assert (Henv0 : buffered_environment active mode J s later pool frame whole).
    { eapply buffered_environment_stack_agrees;
        [apply stack_agrees_sym; exact (stack_agrees_incl _ _ _ _ HJ Hagree) |exact Henv]. }
    destruct (Hprogress _ _ _ Henv0) as [Habort [Hstep Hflush]]. split.
    + intros Hfault; apply Habort; exact (abort_stack_agrees _ _ _ Hfault variables s HC Hagree).
    + split.
      * intros action next last whole' Hprogram.
        destruct (program_step_stack_agrees _ _ _ _ _ _ Hprogram variables s HC Hagree)
          as (last0 & Hprogram0 & Hagree').
        destruct (Hstep _ _ _ _ Hprogram0) as (local' & pool' & Henv' & Hupdate & Hsafe').
        exists local', pool'; split.
        -- eapply buffered_environment_stack_agrees; [exact (stack_agrees_incl _ _ _ _ HJ Hagree') |exact Henv'].
        -- split; [exact Hupdate |]. eapply IHn; [|exact HQ |exact Hagree' |exact Hsafe'].
           intros x Hx; apply HC; eapply step_fv_subset;
             [exact (program_step_erases _ _ _ _ _ _ Hprogram) |exact Hx].
      * intros actor whole' Hphysical.
        destruct (Hflush _ _ Hphysical) as (local' & frame' & pool' & Hupdate & Henv' & Hsafe').
        exists local', frame', pool'; split; [exact Hupdate |]. split.
        -- eapply buffered_environment_stack_agrees; [exact (stack_agrees_incl _ _ _ _ HJ Hagree) |exact Henv'].
        -- exact (IHn _ _ _ _ HC HQ Hagree Hsafe').
Qed.

Lemma buffered_safe_step_interference active mode J n actor sibling s t whole whole' action next local Q :
  program_step active action actor (State s whole) next (State t whole') ->
  Specifications.disjoint (C.modifies actor) (C.fv sibling ++ A.fv Q) ->
  frame_variable_condition actor J -> buffered_safe active mode J n sibling s local Q ->
  buffered_safe active mode J n sibling t local Q.
Proof.
  intros Hstep Hsibling HJ Hsafe.
  eapply buffered_safe_stack_agrees with (variables := A.fv J ++ (C.fv sibling ++ A.fv Q));
    [| | | |exact Hsafe].
  - intros x Hx; apply in_or_app; auto.
  - intros x Hx; apply in_or_app; right; apply in_or_app; auto.
  - intros x Hx; apply in_or_app; right; apply in_or_app; auto.
  - intros x Hx; apply (step_preserves_unmodified _ _ _ _ _ (program_step_erases _ _ _ _ _ _ Hstep) x).
    intros Hmod; apply in_app_or in Hx; destruct Hx as [Hx |Hx];
      [exact (HJ x Hmod Hx) |exact (Hsibling x Hmod Hx)].
Qed.
