From Stdlib Require Import List Arith.
From WMLR Require Import Expressions Languages Machine Separation GeneralizedFlushing
  OperationalSemantics ProgramSteps Assertions AssertionSemantics PersistentAssertions
  Safety OwnedSafety BufferedPoolCandidate BufferedPoolResources BufferedPoolRules BufferedPoolInterference.
Import ListNotations.

Theorem buffered_disjunction_valid active J P P' c Q :
  buffered_disjunction_rule active J P P' c Q.
Proof.
  intros [Hfree HL] [_ HR]; split; [exact Hfree |].
  intros s local [HP |HP] n; [apply HL,HP |apply HR,HP].
Qed.

Lemma buffered_safe_choice active J n left right s local post :
  buffered_safe active DisjointMode J n left s local post ->
  buffered_safe active DisjointMode J n right s local post ->
  buffered_safe active DisjointMode J n (C.Choice left right) s local post.
Proof.
  revert local; induction n; intros local HL HR; [exact I |].
  intros later Hfuture; split; [intros [annotation E]; discriminate E |].
  intros pool frame whole Henv; split; [intros H; inversion H |]. split.
  - intros action next t whole' Hstep; inversion Hstep; subst;
      exists later,pool; split; [exact Henv | |exact Henv |]; split;
      try apply buffered_update_identity; apply buffered_safe_weaken_one;
      eapply buffered_safe_future; [exact Hfuture |exact HL |exact Hfuture |exact HR].
  - intros actor whole' Hflush.
    destruct (buffered_environment_flush _ _ _ _ _ _ _ _ _ Henv Hflush)
      as (local' & frame' & pool' & Hupdate & Henv' & Hfuture').
    exists local',frame',pool'; split; [exact Hupdate |]. split; [exact Henv' |].
    apply IHn; apply buffered_safe_weaken_one;
      eapply buffered_safe_future; try exact HL; try exact HR;
      eapply generalized_future_trans; eassumption.
Qed.

Theorem buffered_choice_valid active J P left right Q : buffered_choice_rule active J P left right Q.
Proof.
  intros [Hleft HL] [Hright HR]; split; [split; assumption |].
  intros s local HP n; apply buffered_safe_choice; [apply HL,HP |apply HR,HP].
Qed.

Theorem buffered_loop_valid active J P body : buffered_loop_rule active J P body.
Proof.
  intros [Hfree Hbody]; split; [exact Hfree |].
  intros s local HP n; revert s local HP; induction n; intros s local HP; [exact I |].
  intros later Hfuture.
  pose proof (persistent_assertion_flushing_closed _ _ _ _ _ Hfuture HP) as HP'.
  split; [intros [annotation E]; discriminate E |].
  intros pool frame whole Henv; split; [intros H; inversion H |]. split.
  - intros action next t whole' Hstep; inversion Hstep; subst.
    exists later,pool; split; [exact Henv |]. split; [apply buffered_update_identity |].
    apply buffered_safe_choice; [apply buffered_safe_done,HP' |].
    eapply buffered_safe_sequence; [apply Hbody,HP' |exact IHn].
  - intros actor whole' Hflush.
    destruct (buffered_environment_flush _ _ _ _ _ _ _ _ _ Henv Hflush)
      as (local' & frame' & pool' & Hupdate & Henv' & Hfuture').
    exists local',frame',pool'; split; [exact Hupdate |]. split; [exact Henv' |].
    apply IHn; eapply persistent_assertion_flushing_closed; eassumption.
Qed.

Theorem buffered_exists_valid active J P c Q x : buffered_exists_rule active J P c Q x.
Proof.
  intros HJ HC HQ [Hfree Hvalid]; split; [exact Hfree |]. intros s local [v HP] n.
  eapply buffered_safe_stack_agrees with (s := update s x v)
    (variables := A.fv J ++ C.fv c ++ A.fv Q).
  - intros y Hy; apply in_or_app; auto.
  - intros y Hy; apply in_or_app; right; apply in_or_app; auto.
  - intros y Hy; apply in_or_app; right; apply in_or_app; auto.
  - intros y Hy; apply update_other. intros E; subst y; repeat rewrite in_app_iff in Hy; tauto.
  - apply Hvalid,HP.
Qed.
