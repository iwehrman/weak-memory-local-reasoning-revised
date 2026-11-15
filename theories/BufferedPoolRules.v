From Stdlib Require Import List Arith Lia ZArith.
From WMLR Require Import Expressions Languages Machine BufferRelations Separation
  RepairedSeparation GeneralizedFlushing OperationalSemantics ProgramSteps Assertions
  AssertionSemantics PersistentAssertions PersistentRules Specifications Safety TemporalSafety
  InvariantFragment OwnedSafety BufferedPoolCandidate BufferedPoolResources BufferedPoolExtension.
Import ListNotations.

Lemma buffered_safe_future active mode J n c s local later Q :
  resource_future active local later -> buffered_safe active mode J n c s local Q ->
  buffered_safe active mode J n c s later Q.
Proof.
  destruct n; [intros; exact I |]. intros Hfuture Hsafe last Hlast; apply Hsafe.
  eapply generalized_future_trans; eassumption.
Qed.

Lemma buffered_safe_weaken_one active mode J n c s local Q :
  buffered_safe active mode J (S n) c s local Q -> buffered_safe active mode J n c s local Q.
Proof.
  revert c s local; induction n; intros c s local Hsafe; [exact I |].
  intros later Hfuture; destruct (Hsafe later Hfuture) as [Hdone Henvs].
  split; [exact Hdone |]. intros pool frame whole Henv.
  destruct (Henvs _ _ _ Henv) as [Hbad [Hstep Hflush]]. split; [exact Hbad |]. split.
  - intros action next t whole' Hprogram.
    destruct (Hstep _ _ _ _ Hprogram) as (local' & pool' & Henv' & Hupdate & Hsafe').
    exists local', pool'; split; [exact Henv' |]. split; [exact Hupdate |exact (IHn _ _ _ Hsafe')].
  - intros actor whole' Hphysical.
    destruct (Hflush _ _ Hphysical) as (local' & frame' & pool' & Hupdate & Henv' & Hsafe').
    exists local', frame', pool'; split; [exact Hupdate |]. split; [exact Henv' |exact (IHn _ _ _ Hsafe')].
Qed.

Lemma buffered_safe_post_mono active mode J n c s local Q Q' :
  persistent_entails active Q Q' -> buffered_safe active mode J n c s local Q ->
  buffered_safe active mode J n c s local Q'.
Proof.
  intros Hent; revert c s local; induction n; intros c s local Hsafe; [exact I |].
  intros later Hfuture; destruct (Hsafe later Hfuture) as [Hdone Henvs].
  split; [intros Hlast; apply Hent, Hdone, Hlast |]. intros pool frame whole Henv.
  destruct (Henvs _ _ _ Henv) as [Hbad [Hstep Hflush]]. split; [exact Hbad |]. split.
  - intros action next t whole' Hprogram.
    destruct (Hstep _ _ _ _ Hprogram) as (local' & pool' & Henv' & Hupdate & Hsafe').
    exists local', pool'; split; [exact Henv' |]. split; [exact Hupdate |exact (IHn _ _ _ Hsafe')].
  - intros actor whole' Hphysical.
    destruct (Hflush _ _ Hphysical) as (local' & frame' & pool' & Hupdate & Henv' & Hsafe').
    exists local', frame', pool'; split; [exact Hupdate |]. split; [exact Henv' |exact (IHn _ _ _ Hsafe')].
Qed.

Lemma buffered_safe_done active J n annotation s local Q :
  persistent_models active s local Q ->
  buffered_safe active DisjointMode J n (C.skip annotation) s local Q.
Proof.
  revert local; induction n; intros local HQ; [exact I |].
  intros later Hfuture.
  pose proof (persistent_assertion_flushing_closed _ _ _ _ _ Hfuture HQ) as HQlater.
  split; [intros; exact HQlater |]. intros pool frame whole Henv; split.
  - intros Hbad; inversion Hbad; subst; match goal with H : primitive_abort _ _ _ _ |- _ => inversion H end.
  - split.
    + intros action next t whole' Hstep; exfalso; eapply program_skip_impossible; eassumption.
    + intros actor whole' Hflush.
      destruct (buffered_environment_flush _ _ _ _ _ _ _ _ _ Henv Hflush)
        as (local' & frame' & pool' & Hupdate & Henv' & Hfuture').
      exists local', frame', pool'; split; [exact Hupdate |]. split; [exact Henv' |].
      apply IHn; eapply persistent_assertion_flushing_closed; eassumption.
Qed.

Theorem buffered_atomic_valid active J P p annotation Q :
  buffered_atomic_rule active J P p annotation Q.
Proof.
  intros Hfragment Hpremise; split; [exact I |]. intros s local HP n.
  revert local HP; induction n; intros local HP; [exact I |].
  intros later Hfuture.
  pose proof (persistent_assertion_flushing_closed _ _ _ _ _ Hfuture HP) as HPlater.
  split.
  - intros [label E]; inversion E; subst; exact (False_rect _ (proj1 Hpremise)).
  - intros pool frame whole Henv.
    destruct (buffered_atomic_extension _ _ _ _ _ _ _ _ _ _ _ Hpremise HPlater Henv) as [Hbad Hstep].
    split; [exact Hbad |]. split.
    + intros action next t whole' Hprogram.
      destruct (Hstep _ _ _ _ Hprogram) as (local' & pool' & Henv' & Hupdate & HQ).
      exists local', pool'; split; [exact Henv' |]. split; [exact Hupdate |].
      inversion Hprogram; subst; apply buffered_safe_done, HQ.
    + intros actor whole' Hflush.
      destruct (buffered_environment_flush _ _ _ _ _ _ _ _ _ Henv Hflush)
        as (local' & frame' & pool' & Hupdate & Henv' & Hfuture').
      exists local', frame', pool'; split; [exact Hupdate |]. split; [exact Henv' |].
      apply IHn; eapply persistent_assertion_flushing_closed; eassumption.
Qed.

Theorem buffered_skip_valid active J P annotation : buffered_skip_rule active J P annotation.
Proof. intros _; split; [exact I |]. intros; apply buffered_safe_done; assumption. Qed.

Theorem buffered_consequence_valid active J P P' c Q' Q :
  buffered_consequence_rule active J P P' c Q' Q.
Proof.
  intros HP [Hfree Hvalid] HQ; split; [exact Hfree |]. intros s local Hpre n.
  eapply buffered_safe_post_mono; [exact HQ |apply Hvalid, HP, Hpre].
Qed.

Lemma buffered_update_identity active local pool :
  buffered_update active OrdinaryAction local pool local pool.
Proof. constructor; [auto |intros; auto]. Qed.

Theorem buffered_safe_sequence active mode J n first second s local middle post :
  buffered_safe active mode J n first s local middle ->
  (forall t r, persistent_models active t r middle -> buffered_safe active mode J n second t r post) ->
  buffered_safe active mode J n (C.Seq first second) s local post.
Proof.
  revert first s local; induction n; intros first s local Hfirst Hsecond; [exact I |].
  intros later Hfuture; split; [intros [label E]; discriminate E |]. intros pool frame whole Henv.
  destruct (Hfirst later Hfuture) as [Hdone Henvs].
  destruct (Henvs _ _ _ Henv) as [Hbad [Hstep Hflush]]. split.
  - intros H; inversion H; subst; apply Hbad; assumption.
  - split.
    + intros action next t whole' Hprogram; inversion Hprogram; subst.
      * destruct (Hstep _ _ _ _ ltac:(eassumption)) as (local' & pool' & Henv' & Hupdate & Hsafe').
        exists local', pool'; split; [exact Henv' |]. split; [exact Hupdate |].
        eapply IHn; [exact Hsafe' |]. intros; apply buffered_safe_weaken_one, Hsecond; assumption.
      * exists later, pool; split; [exact Henv |]. split; [apply buffered_update_identity |].
        apply buffered_safe_weaken_one, Hsecond, Hdone; eexists; reflexivity.
    + intros actor whole' Hphysical.
      destruct (Hflush _ _ Hphysical) as (local' & frame' & pool' & Hupdate & Henv' & Hsafe').
      exists local', frame', pool'; split; [exact Hupdate |]. split; [exact Henv' |].
      eapply IHn; [exact Hsafe' |]. intros; apply buffered_safe_weaken_one, Hsecond; assumption.
Qed.

Theorem buffered_sequence_valid active J P middle Q first second :
  buffered_sequence_rule active J P middle Q first second.
Proof.
  intros [Hfirst Vfirst] [Hsecond Vsecond]; split; [split; assumption |].
  intros s local HP n; eapply buffered_safe_sequence; [apply Vfirst, HP |].
  intros; apply Vsecond; assumption.
Qed.

Lemma buffered_safe_terminal active mode J n c s local Q :
  buffered_safe active mode J (S n) c s local Q -> terminal c -> persistent_models active s local Q.
Proof. intros H; exact (proj1 (H local (GeneralizedRefl _ _))). Qed.

Lemma buffered_safe_no_abort active mode J n c s local Q pool frame whole :
  buffered_safe active mode J (S n) c s local Q ->
  buffered_environment active mode J s local pool frame whole -> ~ abort active c (State s whole).
Proof. intros H Henv; exact (proj1 (proj2 (H local (GeneralizedRefl _ _)) _ _ _ Henv)). Qed.

Lemma buffered_safe_program_step active mode J n c s local Q pool frame whole action next t whole' :
  buffered_safe active mode J (S n) c s local Q ->
  buffered_environment active mode J s local pool frame whole ->
  program_step active action c (State s whole) next (State t whole') ->
  exists local' pool', buffered_environment active mode J t local' pool' frame whole' /\
    buffered_update active action local pool local' pool' /\
    buffered_safe active mode J n next t local' Q.
Proof. intros H Henv; exact (proj1 (proj2 (proj2 (H local (GeneralizedRefl _ _)) _ _ _ Henv)) _ _ _ _). Qed.
