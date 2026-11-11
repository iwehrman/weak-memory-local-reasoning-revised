From Stdlib Require Import List ZArith.
From WMLR Require Import Expressions Languages Machine Separation
  OperationalSemantics Assertions AssertionSemantics RepairedAssertions Safety RepairedSafety.
Import ListNotations.

Theorem repaired_safe_post_mono active n c s local invariant (post post' : state_predicate) :
  (forall t m, post t m -> post' t m) ->
  repaired_safe active n c s local invariant post -> repaired_safe active n c s local invariant post'.
Proof.
  intros Hpost. revert c s local. induction n; intros c s local Hsafe; [exact I |].
  destruct Hsafe as [Hterminal [Habort Hstep]]. split; [intros H; apply Hpost, Hterminal, H |].
  split; [exact Habort |]. intros shared frame whole next s' whole' Henv Htransition.
  destruct (Hstep _ _ _ _ _ _ Henv Htransition) as
    [local' [shared' [frame' [Henv' [Hflush [Howned Hsafe']]]]]].
  exists local', shared', frame'. split; [exact Henv' |]. split; [exact Hflush |].
  split; [exact Howned | apply IHn, Hsafe'].
Qed.

Definition repaired_entails active p q : Prop :=
  forall s (r : resource active), repaired_models active s r p -> repaired_models active s r q.

Lemma repaired_full_entails active p q : repaired_entails active p q ->
  forall s m, repaired_full_satisfies active s m p -> repaired_full_satisfies active s m q.
Proof. intros H s m [r [Hr Hp]]. exists r; split; [exact Hr | apply H, Hp]. Qed.

Theorem repaired_consequence_valid active invariant pre pre' c post' post :
  repaired_entails active pre pre' -> repaired_valid_specification active invariant pre' c post' ->
  repaired_entails active post' post -> repaired_valid_specification active invariant pre c post.
Proof.
  intros Hpre Hvalid Hpost s m Hmodels n.
  eapply repaired_safe_post_mono; [apply repaired_full_entails, Hpost |].
  apply Hvalid, (repaired_full_entails _ _ _ Hpre), Hmodels.
Qed.

Theorem repaired_disjunction_valid active invariant pre pre' c post :
  repaired_valid_specification active invariant pre c post ->
  repaired_valid_specification active invariant pre' c post ->
  repaired_valid_specification active invariant (ConcurrentAssertion.Or pre pre') c post.
Proof.
  intros Hleft Hright s m [r [Hr [Hp | Hp]]] n.
  - apply Hleft. exists r; auto.
  - apply Hright. exists r; auto.
Qed.

Theorem repaired_safe_sequence active n first second s local invariant middle post :
  repaired_safe active n first s local invariant middle ->
  (forall k t m, middle t m -> repaired_safe active k second t m invariant post) ->
  repaired_safe active n (Concurrent.Seq first second) s local invariant post.
Proof.
  intros Hfirst Hsecond. revert first s local Hfirst.
  induction n; intros first s local Hfirst; [exact I |].
  destruct Hfirst as [Hterminal [Habort Hstep]]. split; [intros [ann H]; discriminate |].
  split.
  - intros shared frame whole Henv Hfault. inversion Hfault; subst.
    eapply Habort; eassumption.
  - intros shared frame whole next t whole' Henv Htransition. inversion Htransition; subst.
    + assert (Hfirststep : step active first (State t whole) first (State t whole')).
      { apply StepFlush; assumption. }
      destruct (Hstep _ _ _ _ _ _ Henv Hfirststep) as
        [local' [shared' [frame' [Henv' [Hflush [Howned Hsafe']]]]]].
      exists local', shared', frame'. split; [exact Henv' |]. split; [exact Hflush |].
      split; [exact Howned | apply IHn, Hsafe'].
    + match goal with H : step _ first _ _ _ |- _ =>
        destruct (Hstep _ _ _ _ _ _ Henv H) as
          [local' [shared' [frame' [Henv' [Hflush [Howned Hsafe']]]]]] end.
      exists local', shared', frame'. split; [exact Henv' |]. split; [exact Hflush |].
      split; [exact Howned | apply IHn, Hsafe'].
    + exists local, shared, frame. split; [exact Henv |]. split; [constructor |].
      split; [apply ownership_preserved_refl |]. apply Hsecond, Hterminal.
      eexists; reflexivity.
Qed.

Theorem repaired_sequence_valid active invariant pre middle post first second :
  repaired_valid_specification active invariant pre first middle ->
  repaired_valid_specification active invariant middle second post ->
  repaired_valid_specification active invariant pre (Concurrent.Seq first second) post.
Proof.
  intros Hfirst Hsecond s m Hp n. eapply repaired_safe_sequence.
  - apply Hfirst, Hp.
  - intros k t local Hmiddle. apply Hsecond, Hmiddle.
Qed.

(** A proved fragment of the corrected derivation system. Its rules contain
    no safety or specification-validity premises. Pure entailment is ordinary
    logical implication on register expressions. Memory and parallel rules
    remain to be added, with their own soundness obligations. *)
Inductive pure_derivation (invariant : bexpr) : bexpr -> Concurrent.command -> bexpr -> Prop :=
| PureSkip p annotation : pure_derivation invariant p (Concurrent.skip annotation) p
| PureAssign q x rhs annotation :
    ~ In x (bexpr_fv invariant) ->
    pure_derivation invariant (subst_bexpr x rhs q)
      (Concurrent.Prim (Concurrent.Common (Sequential.Assign x rhs)) annotation) q
| PureSequence p r q first second :
    pure_derivation invariant p first r -> pure_derivation invariant r second q ->
    pure_derivation invariant p (Concurrent.Seq first second) q
| PureConsequence p p' q' q command :
    (forall s, eval_bexpr s p = true -> eval_bexpr s p' = true) ->
    pure_derivation invariant p' command q' ->
    (forall s, eval_bexpr s q' = true -> eval_bexpr s q = true) ->
    pure_derivation invariant p command q.

Theorem pure_fragment_sound active invariant p c q :
  pure_derivation invariant p c q ->
  repaired_valid_specification active (ConcurrentAssertion.Pure invariant)
    (ConcurrentAssertion.Pure p) c (ConcurrentAssertion.Pure q).
Proof.
  induction 1.
  - intros s m Hp n. apply repaired_skip_safe; [| |exact Hp];
      intros t local local' Hflush Hpure; eapply repaired_full_pure_flushes; eassumption.
  - apply repaired_pure_assignment_valid, H.
  - eapply repaired_sequence_valid; eassumption.
  - eapply repaired_consequence_valid; [|exact IHpure_derivation |];
      intros s r Hp; [apply H | apply H1]; exact Hp.
Qed.
