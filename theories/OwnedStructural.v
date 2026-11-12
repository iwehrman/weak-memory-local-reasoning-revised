From Stdlib Require Import List Arith.
From WMLR Require Import Expressions Languages Machine Separation GeneralizedFlushing
  OperationalSemantics ProgramSteps Assertions AssertionSemantics PersistentAssertions
  PersistentRules Safety OwnedSafety OwnedResources OwnedParallel.
Import ListNotations.

Theorem owned_skip_valid active mode invariant pre annotation :
  owned_valid active mode invariant pre (C.skip annotation) pre.
Proof. intros s local HP n; apply owned_done_safe, HP. Qed.

Theorem owned_consequence_valid active mode invariant pre pre' command post' post :
  persistent_entails active pre pre' ->
  owned_valid active mode invariant pre' command post' ->
  persistent_entails active post' post ->
  owned_valid active mode invariant pre command post.
Proof.
  intros HP Hvalid HQ s local Hpre n; eapply owned_safe_post_mono;
    [exact HQ |apply Hvalid, HP, Hpre].
Qed.

Theorem owned_disjunction_valid active mode invariant pre pre' command post :
  owned_valid active mode invariant pre command post ->
  owned_valid active mode invariant pre' command post ->
  owned_valid active mode invariant (A.Or pre pre') command post.
Proof. intros HL HR s local [HP |HP] n; [apply HL, HP |apply HR, HP]. Qed.

Theorem owned_safe_sequence active mode invariant n first second s local middle post :
  owned_safe active mode invariant n first s local middle ->
  (forall t r, persistent_models active t r middle -> owned_safe active mode invariant n second t r post) ->
  owned_safe active mode invariant n (C.Seq first second) s local post.
Proof.
  revert first s local; induction n; intros first s local Hfirst Hsecond; [exact I |].
  intros later Hfuture; pose proof (owned_safe_future _ _ _ _ _ _ _ _ _ Hfuture Hfirst) as Hfirst0.
  split; [intros [annotation E]; discriminate E |].
  intros pool frame whole phase Henv; split.
  - intros Hfault; inversion Hfault; subst.
    eapply (owned_safe_no_abort _ _ _ _ _ _ _ _ _ _ _ _ Hfirst0 Henv); eassumption.
  - intros action next t whole' Hstep; inversion Hstep; subst.
    + match goal with H : program_step active _ first _ _ _ |- _ =>
        destruct (owned_safe_program_step _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hfirst0 Henv H)
          as (local' & pool' & phase' & Henv' & Hupdate & Hsafe') end.
      exists local', pool', phase'; split; [exact Henv' |]. split; [exact Hupdate |].
      apply IHn; [exact Hsafe' |]. intros u r HP; apply owned_safe_weaken_one, Hsecond, HP.
    + exists later, pool, phase; split; [exact Henv |]. split; [apply owned_update_identity |].
      apply owned_safe_weaken_one, Hsecond.
      eapply owned_safe_terminal; [exact Hfirst0 |eexists; reflexivity].
Qed.

Theorem owned_sequence_valid active mode invariant pre middle post first second :
  owned_valid active mode invariant pre first middle ->
  owned_valid active mode invariant middle second post ->
  owned_valid active mode invariant pre (C.Seq first second) post.
Proof.
  intros HL HR s local HP n; eapply owned_safe_sequence;
    [apply HL, HP |intros t r HQ; apply HR, HQ].
Qed.

Theorem owned_safe_choice active mode invariant n left right s local post :
  owned_safe active mode invariant n left s local post ->
  owned_safe active mode invariant n right s local post ->
  owned_safe active mode invariant n (C.Choice left right) s local post.
Proof.
  destruct n; intros HL HR; [exact I |]. intros later Hfuture.
  split; [intros [annotation E]; discriminate E |].
  intros pool frame whole phase Henv; split; [intros H; inversion H |].
  intros action next t whole' Hstep; inversion Hstep; subst;
    exists later, pool, phase; split; [exact Henv | |exact Henv |];
    split; try apply owned_update_identity; apply owned_safe_weaken_one;
    eapply owned_safe_future; [exact Hfuture |exact HL |exact Hfuture |exact HR].
Qed.

Theorem owned_choice_valid active mode invariant pre left right post :
  owned_valid active mode invariant pre left post ->
  owned_valid active mode invariant pre right post ->
  owned_valid active mode invariant pre (C.Choice left right) post.
Proof. intros HL HR s local HP n; apply owned_safe_choice; [apply HL, HP |apply HR, HP]. Qed.

Theorem owned_loop_valid active mode invariant pre body :
  owned_valid active mode invariant pre body pre ->
  owned_valid active mode invariant pre (C.Loop body) pre.
Proof.
  intros Hbody s local HP n; revert s local HP; induction n; intros s local HP; [exact I |].
  intros later Hfuture.
  assert (HP' : persistent_models active s later pre).
  { eapply persistent_assertion_flushing_closed; eassumption. }
  split; [intros [annotation E]; discriminate E |].
  intros pool frame whole phase Henv; split; [intros H; inversion H |].
  intros action next t whole' Hstep; inversion Hstep; subst.
  exists later, pool, phase; split; [exact Henv |]. split; [apply owned_update_identity |].
  apply owned_safe_choice; [apply owned_done_safe, HP' |].
  eapply owned_safe_sequence; [apply Hbody, HP' |exact IHn].
Qed.
