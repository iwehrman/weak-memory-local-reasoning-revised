From Stdlib Require Import List ZArith.
From WMLR Require Import Expressions Languages Machine BufferRelations Separation RepairedSeparation
  GeneralizedFlushing FrameDecomposition OperationalSemantics Assertions AssertionSemantics
  PersistentAssertions Safety RepairedSafety OwnershipProtocol OwnershipHeap TemporalSafety TemporalTransfer RegionalResources.
Import ListNotations.

Fixpoint regional_safe active owner invariant n command s phase (local region : resource active) finish post : Prop :=
  match n with
  | O => True
  | S remaining =>
    marked_region active owner invariant phase s local region /\
    (terminal command -> phase = finish /\ persistent_models active s local post) /\
    (forall history whole, regional_environment active owner invariant phase s local region history whole ->
      ~ abort active command (State s whole)) /\
    (forall history whole next t whole',
      regional_environment active owner invariant phase s local region history whole ->
      step active command (State s whole) next (State t whole') ->
      exists phase' local' region' history',
        regional_environment active owner invariant phase' t local' region' history' whole' /\
        resource_future active history history' /\
        domain_included (resource_memory active region') (resource_memory active region) /\
        regional_safe active owner invariant remaining next t phase' local' region' finish post)
  end.

Definition regional_valid active owner invariant start pre command finish post : Prop :=
  forall s local region, marked_region active owner invariant start s local region ->
    persistent_models active s local pre -> forall n,
      regional_safe active owner invariant n command s start local region finish post.

Definition regional_entails active pre post : Prop := forall s (r : resource active),
  persistent_models active s r pre -> persistent_models active s r post.

Lemma regional_safe_post_mono active owner invariant n command s phase local region finish post post' :
  regional_entails active post post' ->
  regional_safe active owner invariant n command s phase local region finish post ->
  regional_safe active owner invariant n command s phase local region finish post'.
Proof.
  intros Hentails; revert command s phase local region.
  induction n; intros command s phase local region Hsafe; [exact I |].
  destruct Hsafe as [Hr [Hdone [Hnoabort Hprogress]]]; split; [exact Hr |]. split.
  - intros Hlast; destruct (Hdone Hlast) as [E HQ]; split; [exact E |apply Hentails, HQ].
  - split; [exact Hnoabort |]. intros history whole next t whole' Henv Hstep.
    destruct (Hprogress _ _ _ _ _ Henv Hstep) as (phase' & local' & region' & history' & Henv' & Hhf & Hdom & Hsafe').
    exists phase', local', region', history'; split; [exact Henv' |]. split; [exact Hhf |].
    split; [exact Hdom |apply IHn, Hsafe'].
Qed.

Theorem regional_consequence_valid active owner invariant start pre pre' command finish post' post :
  regional_entails active pre pre' -> regional_valid active owner invariant start pre' command finish post' ->
  regional_entails active post' post -> regional_valid active owner invariant start pre command finish post.
Proof.
  intros Hpre Hvalid Hpost s local region Hr HP n. eapply regional_safe_post_mono;
    [exact Hpost |apply Hvalid; [exact Hr |apply Hpre, HP]].
Qed.

Lemma regional_skip_safe active owner invariant n annotation s phase local region post :
  marked_region active owner invariant phase s local region -> persistent_models active s local post ->
  regional_safe active owner invariant n (Concurrent.skip annotation) s phase local region phase post.
Proof.
  revert s local region. induction n; intros s local region Hr Hp; [exact I |].
  split; [exact Hr |]. split; [intros _; auto |]. split; [intros; apply skip_no_abort |].
  intros history whole next t whole' Henv Hstep.
  destruct (skip_step_flush _ _ _ _ _ _ _ Hstep) as [-> [-> Hflush]].
  destruct (regional_environment_flush _ _ _ _ _ _ _ _ _ _ Henv Hflush)
    as (local' & region' & history' & Henv' & Hlf & Hhf & Hdomain).
  exists phase, local', region', history'. split; [exact Henv' |]. split; [exact Hhf |].
  split; [exact Hdomain |]. apply IHn;
    [exact (regional_region_ok _ _ _ _ _ _ _ _ _ Henv') |eapply persistent_assertion_flushing_closed; eassumption].
Qed.

Lemma regional_primitive_rule active owner invariant start pre primitive annotation finish post :
  primitive <> Concurrent.Common Sequential.Skip ->
  (forall s local region history whole,
    regional_environment active owner invariant start s local region history whole ->
    persistent_models active s local pre -> forall i,
    eval_expr s annotation = Z.pos i -> ~ primitive_abort active primitive i (State s whole)) ->
  (forall s local region history whole,
    regional_environment active owner invariant start s local region history whole ->
    persistent_models active s local pre -> forall i t whole',
    eval_expr s annotation = Z.pos i -> primitive_step active primitive i (State s whole) (State t whole') ->
    exists local' region' history', regional_environment active owner invariant finish t local' region' history' whole' /\
      resource_future active history history' /\
      domain_included (resource_memory active region') (resource_memory active region) /\
      persistent_models active t local' post) ->
  regional_valid active owner invariant start pre (Concurrent.Prim primitive annotation) finish post.
Proof.
  intros Hnot Hfault Haction s local region Hr Hp n. revert s local region Hr Hp.
  induction n; intros s local region Hr Hp; [exact I |]. split; [exact Hr |]. split.
  - intros [ann E]; inversion E; contradiction.
  - split.
    + intros history whole Henv Habort. inversion Habort; subst; eapply Hfault; eassumption.
    + intros history whole next t whole' Henv Hstep. inversion Hstep; subst.
      * match goal with H : primitive_step _ _ _ _ _ |- _ =>
          destruct (Haction _ _ _ _ _ Henv Hp _ _ _ ltac:(eassumption) H)
            as (local' & region' & history' & Henv' & Hhf & Hdomain & HQ) end.
        exists finish, local', region', history'. split; [exact Henv' |]. split; [exact Hhf |].
        split; [exact Hdomain |]. apply regional_skip_safe;
          [exact (regional_region_ok _ _ _ _ _ _ _ _ _ Henv') |exact HQ].
      * match goal with H : flush _ _ _ |- _ =>
          destruct (regional_environment_flush _ _ _ _ _ _ _ _ _ _ Henv H)
            as (local' & region' & history' & Henv' & Hlf & Hhf & Hdomain) end.
        exists start, local', region', history'. split; [exact Henv' |]. split; [exact Hhf |].
        split; [exact Hdomain |]. apply IHn;
          [exact (regional_region_ok _ _ _ _ _ _ _ _ _ Henv') |eapply persistent_assertion_flushing_closed; eassumption].
Qed.

Theorem regional_acquire_valid active owner invariant pre :
  regional_valid active owner invariant Closed pre
    (Concurrent.Prim Concurrent.Lock (EVal (Z.pos owner))) Open
    (owned_assertion owner (A.Spatial invariant pre)).
Proof.
  apply regional_primitive_rule; [discriminate | |].
  - intros s local region history whole Henv HP i E Hfault; inversion Hfault.
  - intros s local region history whole [[Hfree [pool [HJ Hsp]]] Hhistory [combined [Eworld Htm]]]
      HP i t whole' E Hstep.
    simpl in E; inversion E; subst i. inversion Hstep; subst.
    exists (acquired_resource active region owner), (acquired_resource active region owner), history.
    split.
    + constructor.
      * split; [reflexivity |]. split; [assumption |intros j; reflexivity].
      * exact Hhistory.
      * exists (acquired_resource active combined owner); split.
        -- reflexivity.
        -- apply temporal_acquire_recompose; assumption.
    + split; [constructor |]. split; [intros loc H; exact H |].
      apply acquire_marked_payload; [assumption |exact Hfree |]. exists pool, local; auto.
Qed.

Theorem regional_release_valid active owner invariant post :
  regional_valid active owner invariant Open (owned_assertion owner (A.Spatial invariant post))
    (Concurrent.Prim Concurrent.Unlock (EVal (Z.pos owner))) Closed post.
Proof.
  apply regional_primitive_rule; [discriminate | |].
  - intros s local region history whole Henv HP i E Hfault; inversion Hfault.
  - intros s local region history whole [[-> Hheld] Hhistory [combined [Eworld Htm]]]
      HP i t whole' E Hstep.
    simpl in E; inversion E; subst i. inversion Hstep; subst.
    destruct (release_marked_invariant _ _ _ _ _ Hheld HP) as (payload & Hboth & Hfree & Heq & Hmarks).
    destruct Hboth as (pool & private & Hsp & HJ & HQ).
    exists private, payload, history. split.
    + constructor.
      * split; [exact Hfree |exists pool; auto].
      * exact Hhistory.
      * exists (released_resource active combined); split.
        -- reflexivity.
        -- eapply temporal_release_recompose; eassumption.
    + split; [constructor |]. split; [|exact HQ].
      intros loc H; apply (memory_equiv_domain _ _ Heq), H.
Qed.

Theorem regional_safe_sequence active owner invariant n first second s phase local region middle mid post finish :
  regional_safe active owner invariant n first s phase local region middle mid ->
  regional_valid active owner invariant middle mid second finish post ->
  regional_safe active owner invariant n (Concurrent.Seq first second) s phase local region finish post.
Proof.
  intros Hfirst Hsecond. revert first s phase local region Hfirst.
  induction n; intros first s phase local region Hfirst; [exact I |].
  destruct Hfirst as [Hr [Hterminal [Habort Hprogress]]]. split; [exact Hr |].
  split; [intros [ann E]; discriminate |]. split.
  - intros history whole Henv Hfault; inversion Hfault; subst; eapply Habort; eassumption.
  - intros history whole next t whole' Henv Hstep; inversion Hstep; subst.
    + assert (Hfirststep : step active first (State t whole) first (State t whole')) by (apply StepFlush; assumption).
      destruct (Hprogress _ _ _ _ _ Henv Hfirststep) as (phase' & local' & region' & history' & Henv' & Hhf & Hdom & Hsafe).
      exists phase', local', region', history'. split; [exact Henv' |]. split; [exact Hhf |].
      split; [exact Hdom |apply IHn, Hsafe].
    + match goal with H : step _ first _ _ _ |- _ =>
        destruct (Hprogress _ _ _ _ _ Henv H) as (phase' & local' & region' & history' & Henv' & Hhf & Hdom & Hsafe) end.
      exists phase', local', region', history'. split; [exact Henv' |]. split; [exact Hhf |].
      split; [exact Hdom |apply IHn, Hsafe].
    + destruct (Hterminal ltac:(eexists; reflexivity)) as [E Hmid]; subst phase.
      exists middle, local, region, history. split; [exact Henv |]. split; [constructor |].
      split; [intros loc H; exact H |apply Hsecond; assumption].
Qed.

Theorem regional_sequence_valid active owner invariant start pre first middle mid second finish post :
  regional_valid active owner invariant start pre first middle mid ->
  regional_valid active owner invariant middle mid second finish post ->
  regional_valid active owner invariant start pre (Concurrent.Seq first second) finish post.
Proof.
  intros Hfirst Hsecond s local region Hr HP n. eapply regional_safe_sequence;
    [apply Hfirst; assumption |exact Hsecond].
Qed.

Theorem regional_roundtrip_valid active owner invariant pre : regional_valid active owner invariant Closed pre
  (Concurrent.Seq (Concurrent.Prim Concurrent.Lock (EVal (Z.pos owner)))
    (Concurrent.Prim Concurrent.Unlock (EVal (Z.pos owner)))) Closed pre.
Proof. eapply regional_sequence_valid; [apply regional_acquire_valid |apply regional_release_valid]. Qed.

Theorem regional_execution_residual active owner invariant n command s whole last t final :
  execution active n command s whole last t final -> forall phase local region history finish post,
  regional_safe active owner invariant (S n) command s phase local region finish post ->
  regional_environment active owner invariant phase s local region history whole ->
  exists phase' local' region' history', regional_environment active owner invariant phase' t local' region' history' final /\
    resource_future active history history' /\ regional_safe active owner invariant 1 last t phase' local' region' finish post.
Proof.
  induction 1; intros phase local region history finish post Hsafe Henv.
  - exists phase, local, region, history. split; [exact Henv |]. split; [constructor |exact Hsafe].
  - destruct Hsafe as [_ [_ [_ Hprogress]]].
    destruct (Hprogress _ _ _ _ _ Henv H) as (phase' & local' & region' & history' & Henv' & Hhf & Hdom & Hsafe').
    destruct (IHexecution _ _ _ _ _ _ Hsafe' Henv') as (phase'' & local'' & region'' & history'' & Henv'' & Hhf' & Hsafe'').
    exists phase'', local'', region'', history''. split; [exact Henv'' |]. split; [|exact Hsafe''].
    eapply generalized_future_trans; eassumption.
Qed.

Theorem regional_execution_no_abort active owner invariant n command s whole last t final phase local region history finish post :
  execution active n command s whole last t final ->
  regional_safe active owner invariant (S n) command s phase local region finish post ->
  regional_environment active owner invariant phase s local region history whole -> ~ abort active last (State t final).
Proof.
  intros Hrun Hsafe Henv. destruct (regional_execution_residual _ _ _ _ _ _ _ _ _ _ Hrun _ _ _ _ _ _ Hsafe Henv)
    as (phase' & local' & region' & history' & Henv' & _ & _ & _ & Hnoabort & _).
  exact (Hnoabort _ _ Henv').
Qed.

Theorem regional_execution_post active owner invariant n command s whole last t final phase local region history finish post :
  execution active n command s whole last t final ->
  regional_safe active owner invariant (S n) command s phase local region finish post ->
  regional_environment active owner invariant phase s local region history whole -> terminal last ->
  exists local' region' history', regional_environment active owner invariant finish t local' region' history' final /\
    memory_flushes active (resource_memory active history) (resource_memory active history') /\
    persistent_models active t local' post.
Proof.
  intros Hrun Hsafe Henv Hlast. destruct (regional_execution_residual _ _ _ _ _ _ _ _ _ _ Hrun _ _ _ _ _ _ Hsafe Henv)
    as (phase' & local' & region' & history' & Henv' & Hhf & _ & Hdone & _).
  destruct (Hdone Hlast) as [-> HQ]. exists local', region', history'. split; [exact Henv' |].
  split; [apply generalized_future_memory_flushes, Hhf |exact HQ].
Qed.
