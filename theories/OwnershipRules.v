From Stdlib Require Import List ZArith.
From WMLR Require Import Expressions Languages Machine BufferRelations Separation
  FrameDecomposition OperationalSemantics Assertions AssertionSemantics ConcreteAssertions
  PersistentAssertions Safety HeapRules LockRules OwnershipProtocol.
Import ListNotations.

Lemma acquire_exposes_invariant active owner invariant s pool :
  active owner -> lock_free pool -> persistent_full_satisfies active s pool invariant ->
  persistent_full_satisfies active s (acquire active pool owner)
    (A.Spatial (A.Lock (EVal (Z.pos owner))) invariant).
Proof.
  intros Hi Hfree [r [Hr Hinv]].
  assert (Hpool : memory_well_formed active pool).
  { pose proof (proj1 (proj2_sig r)) as H; rewrite Hr in H; exact H. }
  pose (token := exist _ (Generalized (acquire active empty_memory owner) active)
    (full_memory_valid_with_processor active owner _ Hi
      (acquire_well_formed active empty_memory owner (proj1 (empty_generalized_well_formed active))))).
  pose (out := exist _ (Generalized (acquire active pool owner) active)
    (full_memory_valid_with_processor active owner _ Hi (acquire_well_formed active pool owner Hpool))).
  exists out; split; [reflexivity |]. exists token, r. split.
  - split.
    + split.
      * split.
        -- intros loc [[v Hv] |[i [v Hv]]] _; discriminate || contradiction.
        -- intros i _ H; apply (Hfree i); rewrite Hr in H; exact H.
      * split.
        -- intros loc; cbn [out token proj1_sig underlying acquire shared_heap].
           rewrite Hr; simpl. unfold heap_override; destruct (shared_heap pool loc); reflexivity.
        -- split.
           ++ intros i; cbn [out token proj1_sig underlying acquire buffers]; rewrite Hr; simpl.
              apply (interleaves_app [] (buffers pool i)).
           ++ intros i; cbn [out token proj1_sig underlying acquire blocked]; rewrite Hr; simpl.
              split; [auto |intros [H |H]; [exact H |exfalso; apply (Hfree i H)]].
    + intros i; cbn [out token proj1_sig complete]; rewrite Hr; simpl; tauto.
  - split; [|exact Hinv].
    split; [intros; reflexivity |]. split; [intros; reflexivity |]. split; [exact Hi |intros i; reflexivity].
Qed.

(** The existing lock atom is empty in heap/buffers. Removing it leaves a
    witness for J with exactly the released region's heap and buffers. *)
Lemma release_returns_invariant active owner invariant s region :
  lock_held active region owner ->
  persistent_full_satisfies active s region (A.Spatial (A.Lock (EVal (Z.pos owner))) invariant) ->
  exists pool, persistent_full_satisfies active s pool invariant /\ lock_free pool /\
    memory_equiv (release region) pool.
Proof.
  intros Hheld [r [Hr [token [payload [Hsep [Htoken Hinv]]]]]].
  change (lock_atom active (Z.pos owner) (proj1_sig token)) in Htoken.
  destruct Htoken as [Hheap [Hbuffers Htoken]].
  change (spatial (proj1_sig token) (proj1_sig payload) (proj1_sig r)) in Hsep.
  rewrite Hr in Hsep. destruct Hsep as [[[Hd Hblocks] [Hh [Hb Hk]]] Hcomplete].
  set (pool := underlying (proj1_sig payload)).
  assert (Hfree : lock_free pool).
  { intros i Hi. assert (Hglobal : blocked region i) by (apply Hk; right; exact Hi).
    apply (proj2 Hheld i) in Hglobal.
    apply (Hblocks i); [apply (proj2 Htoken i), Hglobal |exact Hi]. }
  exists pool. split; [apply persistent_promote_full, Hinv |]. split; [exact Hfree |].
  split.
  - intros loc; cbn [release shared_heap]; rewrite Hh; unfold heap_override.
    rewrite Hheap. destruct (shared_heap pool loc) eqn:E; unfold pool in E; rewrite E; reflexivity.
  - split.
    + intros i; cbn [release buffers]. specialize (Hb i); rewrite Hbuffers in Hb.
      apply interleaves_nil_left, Hb.
    + intros i; cbn [release blocked]. split; [contradiction |intros H; exact (Hfree i H)].
Qed.

Theorem protocol_acquire_valid active owner invariant :
  protocol_valid active owner invariant Closed A.Emp
    (Concurrent.Prim Concurrent.Lock (EVal (Z.pos owner))) Open
    (A.Spatial (A.Lock (EVal (Z.pos owner))) invariant).
Proof.
  apply protocol_primitive_rule; [discriminate | |].
  - intros s region frame whole Henv Hp i Heval Hfault; inversion Hfault.
  - intros s region frame whole [Hr Hf Hw Hfree Hsep] Hp i t whole' Heval Hstep.
    simpl in Heval; inversion Heval; subst i. inversion Hstep; subst.
    destruct Hr as [Hwf [Hregionfree Hinv]]. assert (Hi : active owner) by assumption.
    exists (acquire active region owner), frame. split.
    + constructor; try assumption.
      * split; [apply acquire_well_formed, Hwf |]. split; [exact Hi |intros i; reflexivity].
      * apply acquire_well_formed, Hw.
      * apply protocol_spatial_reblock; assumption.
    + split; [constructor |]. split; [intros loc H; exact H |].
      apply acquire_exposes_invariant; assumption.
Qed.

Theorem protocol_release_valid active owner invariant :
  protocol_valid active owner invariant Open (A.Spatial (A.Lock (EVal (Z.pos owner))) invariant)
    (Concurrent.Prim Concurrent.Unlock (EVal (Z.pos owner))) Closed A.Emp.
Proof.
  apply protocol_primitive_rule; [discriminate | |].
  - intros s region frame whole Henv Hp i Heval Hfault; inversion Hfault.
  - intros s region frame whole [Hr Hf Hw Hfree Hsep] Hp i t whole' Heval Hstep.
    simpl in Heval; inversion Heval; subst i. inversion Hstep; subst.
    destruct Hr as [Hwf Hheld].
    destruct (release_returns_invariant _ _ _ _ _ Hheld Hp) as [pool [Hinv [Hpoolfree Hequiv]]].
    exists pool, frame. split.
    + constructor; try assumption.
      * split; [exact (proj1 (persistent_full_well_formed _ _ _ _ Hinv)) |auto].
      * apply release_well_formed, Hw.
      * eapply protocol_spatial_equiv_right; [exact Hequiv |]. apply protocol_spatial_reblock; assumption.
    + split; [constructor |]. split.
      * intros loc [[v Hv] |[i [v Hv]]].
        -- left; exists v; rewrite <- (proj1 Hequiv loc) in Hv; exact Hv.
        -- right; exists i, v; rewrite <- (proj1 (proj2 Hequiv) i) in Hv; exact Hv.
      * apply protocol_empty_satisfies.
Qed.

Theorem protocol_safe_sequence active owner invariant n first second s phase region middle mid post finish :
  protocol_safe active owner invariant n first s phase region middle mid ->
  protocol_valid active owner invariant middle mid second finish post ->
  protocol_safe active owner invariant n (Concurrent.Seq first second) s phase region finish post.
Proof.
  intros Hfirst Hsecond. revert first s phase region Hfirst.
  induction n; intros first s phase region Hfirst; [exact I |].
  destruct Hfirst as [Hr [Hterminal [Habort Hstep]]]. split; [exact Hr |].
  split; [intros [ann H]; discriminate |]. split.
  - intros frame whole Henv Hfault; inversion Hfault; subst; eapply Habort; eassumption.
  - intros frame whole next t whole' Henv Htransition; inversion Htransition; subst.
    + assert (Hfirststep : step active first (State t whole) first (State t whole')).
      { apply StepFlush; assumption. }
      destruct (Hstep _ _ _ _ _ Henv Hfirststep) as [phase' [region' [frame' [Henv' [Hflush [Hdom Hsafe]]]]]].
      exists phase', region', frame'. split; [exact Henv' |]. split; [exact Hflush |].
      split; [exact Hdom |apply IHn, Hsafe].
    + match goal with H : step _ first _ _ _ |- _ =>
        destruct (Hstep _ _ _ _ _ Henv H) as [phase' [region' [frame' [Henv' [Hflush [Hdom Hsafe]]]]]] end.
      exists phase', region', frame'. split; [exact Henv' |]. split; [exact Hflush |].
      split; [exact Hdom |apply IHn, Hsafe].
    + destruct (Hterminal ltac:(eexists; reflexivity)) as [E Hmid]; subst phase.
      exists middle, region, frame. split; [exact Henv |]. split; [constructor |].
      split; [intros loc H; exact H |apply Hsecond; assumption].
Qed.

Theorem protocol_sequence_valid active owner invariant start pre first middle mid second finish post :
  protocol_valid active owner invariant start pre first middle mid ->
  protocol_valid active owner invariant middle mid second finish post ->
  protocol_valid active owner invariant start pre (Concurrent.Seq first second) finish post.
Proof.
  intros Hfirst Hsecond s region Hr Hp n. eapply protocol_safe_sequence;
    [apply Hfirst; assumption |exact Hsecond].
Qed.

Theorem protocol_execution_residual active owner invariant n command s whole last t final :
  execution active n command s whole last t final -> forall phase region frame finish post,
  protocol_safe active owner invariant (S n) command s phase region finish post ->
  protocol_environment active owner invariant phase s region frame whole ->
  exists phase' region' frame', protocol_environment active owner invariant phase' t region' frame' final /\
    memory_flushes active frame frame' /\
    protocol_safe active owner invariant 1 last t phase' region' finish post.
Proof.
  intros Hrun. induction Hrun; intros phase region frame finish post Hsafe Henv.
  - exists phase, region, frame. split; [exact Henv |]. split; [constructor |exact Hsafe].
  - destruct Hsafe as [_ [_ [_ Hprogress]]].
    destruct (Hprogress _ _ _ _ _ Henv H) as [phase' [region' [frame' [Henv' [Hflush [Hdom Hsafe']]]]]].
    destruct (IHHrun _ _ _ _ _ Hsafe' Henv') as [phase'' [region'' [frame'' [Henv'' [Hflush' Hsafe'']]]]].
    exists phase'', region'', frame''. split; [exact Henv'' |]. split; [|exact Hsafe''].
    eapply memory_flushes_trans; eassumption.
Qed.

Theorem protocol_execution_no_abort active owner invariant n command s whole last t final phase region frame finish post :
  execution active n command s whole last t final ->
  protocol_safe active owner invariant (S n) command s phase region finish post ->
  protocol_environment active owner invariant phase s region frame whole ->
  ~ abort active last (State t final).
Proof.
  intros Hrun Hsafe Henv.
  destruct (protocol_execution_residual _ _ _ _ _ _ _ _ _ _ Hrun _ _ _ _ _ Hsafe Henv)
    as [phase' [region' [frame' [Henv' [_ [_ [_ [Hnoabort _]]]]]]]].
  eapply Hnoabort; exact Henv'.
Qed.

Theorem protocol_execution_closed_post active owner invariant n command s whole last t final phase region frame post :
  execution active n command s whole last t final ->
  protocol_safe active owner invariant (S n) command s phase region Closed post ->
  protocol_environment active owner invariant phase s region frame whole -> terminal last ->
  exists pool frame', memory_spatial frame' pool final /\ memory_flushes active frame frame' /\
    lock_free final /\ persistent_full_satisfies active t pool invariant /\
    persistent_full_satisfies active t empty_memory post.
Proof.
  intros Hrun Hsafe Henv Hlast.
  destruct (protocol_execution_residual _ _ _ _ _ _ _ _ _ _ Hrun _ _ _ _ _ Hsafe Henv)
    as [phase' [pool [frame' [Henv' [Hflush [Hr [Hpost _]]]]]]].
  destruct (Hpost Hlast) as [E Hp]; subst phase'.
  destruct Hr as [Hwf [Hfree Hinv]]. destruct Henv' as [_ _ _ Hframe Hsep].
  exists pool, frame'. split; [exact Hsep |]. split; [exact Hflush |]. split.
  - intros i H. apply (proj2 (proj2 (proj2 Hsep)) i) in H.
    destruct H; [apply (Hframe i) |apply (Hfree i)]; assumption.
  - split; assumption.
Qed.
