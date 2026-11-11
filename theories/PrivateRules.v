From Stdlib Require Import List ZArith.
From WMLR Require Import Expressions Languages Machine BufferRelations Separation FrameDecomposition
  OperationalSemantics Assertions AssertionSemantics PersistentAssertions Safety HeapRules
  OwnershipProtocol OwnershipRules OwnershipHeap PrivateOwnership.
Import ListNotations.

Theorem private_acquire_valid active owner invariant p :
  private_valid active owner invariant Closed p
    (Concurrent.Prim Concurrent.Lock (EVal (Z.pos owner))) Open (owned_assertion owner (A.Spatial invariant p)).
Proof.
  apply private_primitive_rule; [discriminate | |].
  - intros s local region frame whole Henv Hp i Heval Hfault; inversion Hfault.
  - intros s local region frame whole [Hr Hf Hw Hframefree Hsep] Hp i t whole' Heval Hstep.
    simpl in Heval; inversion Heval; subst i. inversion Hstep; subst.
    destruct Hr as [Hl [Hr [Hfree [pool [Hinv Hinner]]]]]. assert (Hi : active owner) by assumption.
    exists (acquire active region owner), (acquire active region owner), frame. split.
    + constructor; try assumption.
      * split; [apply acquire_well_formed, Hr |]. split; [apply acquire_well_formed, Hr |].
        split; [reflexivity |split; [exact Hi |intros j; reflexivity]].
      * apply acquire_well_formed, Hw.
      * apply protocol_spatial_reblock; assumption.
    + split; [constructor |]. split; [intros loc H; exact H |].
      apply acquire_exposes_invariant; [exact Hi |exact Hfree |]. eapply full_spatial_intro; eassumption.
Qed.

Theorem private_release_valid active owner invariant q :
  private_valid active owner invariant Open (owned_assertion owner (A.Spatial invariant q))
    (Concurrent.Prim Concurrent.Unlock (EVal (Z.pos owner))) Closed q.
Proof.
  apply private_primitive_rule; [discriminate | |].
  - intros s local region frame whole Henv Hp i Heval Hfault; inversion Hfault.
  - intros s local region frame whole [Hr Hf Hw Hframefree Hsep] Hp i t whole' Heval Hstep.
    simpl in Heval; inversion Heval; subst i. inversion Hstep; subst.
    destruct Hr as [Hl [Hr [-> Hheld]]].
    destruct (release_returns_invariant _ _ _ _ _ Hheld Hp) as [payload [Hboth [Hfree Heq]]].
    destruct (full_spatial_elim _ _ _ _ _ Hboth) as [pool [private [Hinner [HJ HQ]]]].
    exists private, payload, frame. split.
    + constructor; try assumption.
      * split; [exact (proj1 (persistent_full_well_formed _ _ _ _ HQ)) |].
        split; [exact (proj1 (persistent_full_well_formed _ _ _ _ Hboth)) |].
        split; [exact Hfree |exists pool; auto].
      * apply release_well_formed, Hw.
      * eapply protocol_spatial_equiv_right; [exact Heq |]. apply protocol_spatial_reblock; assumption.
    + split; [constructor |]. split; [|exact HQ].
      intros address Hdom; apply (memory_equiv_domain _ _ Heq), Hdom.
Qed.

Lemma private_open_as_protocol active owner invariant s region frame whole :
  private_environment active owner invariant Open s region region frame whole ->
  protocol_environment active owner invariant Open s region frame whole.
Proof. intros [[Hl [Hr [_ Hheld]]] Hf Hw Hfree Hsep]; constructor; auto; split; assumption. Qed.

Lemma protocol_open_as_private active owner invariant s region frame whole :
  protocol_environment active owner invariant Open s region frame whole ->
  private_environment active owner invariant Open s region region frame whole.
Proof.
  intros [[Hr Hheld] Hf Hw Hfree Hsep]; constructor; try assumption.
  split; [exact Hr |]. split; [exact Hr |]. split; [reflexivity |exact Hheld].
Qed.

(** Reuse checked open primitive rules. The two semantics agree on the open
    view; a successful primitive terminates, fixing the output phase. *)
Theorem private_lift_open_primitive active owner invariant pre primitive annotation post :
  primitive <> Concurrent.Common Sequential.Skip ->
  protocol_valid active owner invariant Open pre (Concurrent.Prim primitive annotation) Open post ->
  private_valid active owner invariant Open pre (Concurrent.Prim primitive annotation) Open post.
Proof.
  intros Hnot Hvalid. apply private_primitive_rule; [exact Hnot | |].
  - intros s local region frame whole Henv Hp i Heval Hfault.
    destruct (private_region_ok _ _ _ _ _ _ _ _ _ Henv) as [_ [_ [E Hheld]]]; subst local.
    pose proof (private_open_as_protocol _ _ _ _ _ _ _ Henv) as Henv0.
    destruct (Hvalid _ _ (protocol_region_ok _ _ _ _ _ _ _ _ Henv0) Hp 1) as [_ [_ [Hnoabort _]]].
    apply (Hnoabort _ _ Henv0). eapply CommandAbort; eassumption.
  - intros s local region frame whole Henv Hp i t whole' Heval Hstep.
    destruct (private_region_ok _ _ _ _ _ _ _ _ _ Henv) as [_ [_ [E Hheld]]]; subst local.
    pose proof (private_open_as_protocol _ _ _ _ _ _ _ Henv) as Henv0.
    destruct (Hvalid _ _ (protocol_region_ok _ _ _ _ _ _ _ _ Henv0) Hp 2) as [_ [_ [_ Hprogress]]].
    assert (Hactual : step active (Concurrent.Prim primitive annotation) (State s whole) halt (State t whole')).
    { eapply StepPrimitive; eassumption. }
    destruct (Hprogress _ _ _ _ _ Henv0 Hactual) as [phase' [region' [frame' [Henv' [Hflush [Hdom [_ [Hpost _]]]]]]]].
    destruct (Hpost ltac:(eexists; reflexivity)) as [E Hpost']; subst phase'.
    exists region', region', frame'. split; [apply protocol_open_as_private, Henv' |].
    split; [exact Hflush |]. split; assumption.
Qed.

Theorem private_safe_sequence active owner invariant n first second s phase local region middle mid post finish :
  private_safe active owner invariant n first s phase local region middle mid ->
  private_valid active owner invariant middle mid second finish post ->
  private_safe active owner invariant n (Concurrent.Seq first second) s phase local region finish post.
Proof.
  intros Hfirst Hsecond. revert first s phase local region Hfirst.
  induction n; intros first s phase local region Hfirst; [exact I |].
  destruct Hfirst as [Hr [Hterminal [Habort Hstep]]]. split; [exact Hr |].
  split; [intros [ann H]; discriminate |]. split.
  - intros frame whole Henv Hfault; inversion Hfault; subst; eapply Habort; eassumption.
  - intros frame whole next t whole' Henv Htransition; inversion Htransition; subst.
    + assert (Hfirststep : step active first (State t whole) first (State t whole')).
      { apply StepFlush; assumption. }
      destruct (Hstep _ _ _ _ _ Henv Hfirststep) as [phase' [local' [region' [frame' [Henv' [Hflush [Hdom Hsafe]]]]]]].
      exists phase', local', region', frame'. split; [exact Henv' |]. split; [exact Hflush |].
      split; [exact Hdom |apply IHn, Hsafe].
    + match goal with H : step _ first _ _ _ |- _ =>
        destruct (Hstep _ _ _ _ _ Henv H) as [phase' [local' [region' [frame' [Henv' [Hflush [Hdom Hsafe]]]]]]] end.
      exists phase', local', region', frame'. split; [exact Henv' |]. split; [exact Hflush |].
      split; [exact Hdom |apply IHn, Hsafe].
    + destruct (Hterminal ltac:(eexists; reflexivity)) as [E Hmid]; subst phase.
      exists middle, local, region, frame. split; [exact Henv |]. split; [constructor |].
      split; [intros loc H; exact H |apply Hsecond; assumption].
Qed.

Theorem private_sequence_valid active owner invariant start pre first middle mid second finish post :
  private_valid active owner invariant start pre first middle mid ->
  private_valid active owner invariant middle mid second finish post ->
  private_valid active owner invariant start pre (Concurrent.Seq first second) finish post.
Proof.
  intros Hfirst Hsecond s local region Hr Hp n. eapply private_safe_sequence;
    [apply Hfirst; assumption |exact Hsecond].
Qed.

Theorem private_execution_residual active owner invariant n command s whole last t final :
  execution active n command s whole last t final -> forall phase local region frame finish post,
  private_safe active owner invariant (S n) command s phase local region finish post ->
  private_environment active owner invariant phase s local region frame whole ->
  exists phase' local' region' frame', private_environment active owner invariant phase' t local' region' frame' final /\
    memory_flushes active frame frame' /\ private_safe active owner invariant 1 last t phase' local' region' finish post.
Proof.
  intros Hrun. induction Hrun; intros phase local region frame finish post Hsafe Henv.
  - exists phase, local, region, frame. split; [exact Henv |]. split; [constructor |exact Hsafe].
  - destruct Hsafe as [_ [_ [_ Hprogress]]].
    destruct (Hprogress _ _ _ _ _ Henv H) as [phase' [local' [region' [frame' [Henv' [Hflush [Hdom Hsafe']]]]]]].
    destruct (IHHrun _ _ _ _ _ _ Hsafe' Henv') as [phase'' [local'' [region'' [frame'' [Henv'' [Hflush' Hsafe'']]]]]].
    exists phase'', local'', region'', frame''. split; [exact Henv'' |]. split; [|exact Hsafe''].
    eapply memory_flushes_trans; eassumption.
Qed.

Theorem private_execution_no_abort active owner invariant n command s whole last t final phase local region frame finish post :
  execution active n command s whole last t final ->
  private_safe active owner invariant (S n) command s phase local region finish post ->
  private_environment active owner invariant phase s local region frame whole ->
  ~ abort active last (State t final).
Proof.
  intros Hrun Hsafe Henv.
  destruct (private_execution_residual _ _ _ _ _ _ _ _ _ _ Hrun _ _ _ _ _ _ Hsafe Henv)
    as [phase' [local' [region' [frame' [Henv' [_ [_ [_ [Hnoabort _]]]]]]]]].
  eapply Hnoabort; exact Henv'.
Qed.

Theorem private_execution_closed_post active owner invariant n command s whole last t final phase local region frame post :
  execution active n command s whole last t final ->
  private_safe active owner invariant (S n) command s phase local region Closed post ->
  private_environment active owner invariant phase s local region frame whole -> terminal last ->
  exists local' pool region' frame', memory_spatial pool local' region' /\ memory_spatial frame' region' final /\
    memory_flushes active frame frame' /\ lock_free final /\
    persistent_full_satisfies active t pool invariant /\ persistent_full_satisfies active t local' post.
Proof.
  intros Hrun Hsafe Henv Hlast.
  destruct (private_execution_residual _ _ _ _ _ _ _ _ _ _ Hrun _ _ _ _ _ _ Hsafe Henv)
    as [phase' [local' [region' [frame' [Henv' [Hflush [Hr [Hpost _]]]]]]]].
  destruct (Hpost Hlast) as [E HQ]; subst phase'.
  destruct Hr as [Hl [Hr [Hfree [pool [HJ Hinner]]]]].
  destruct Henv' as [_ _ _ Hframe Houter].
  exists local', pool, region', frame'. split; [exact Hinner |]. split; [exact Houter |].
  split; [exact Hflush |]. split.
  - intros i H; apply (proj2 (proj2 (proj2 Houter)) i) in H.
    destruct H; [apply (Hframe i) |apply (Hfree i)]; assumption.
  - split; assumption.
Qed.
