From Stdlib Require Import List ZArith.
From WMLR Require Import Expressions Languages Machine Separation FrameDecomposition OperationalSemantics
  Assertions AssertionSemantics PersistentAssertions Safety OwnershipProtocol PrivateOwnership PrivateRules PrivateCalculus.
Import ListNotations.

Definition memory_only command := forall x, ~ In x (Concurrent.modifies command).

Lemma memory_only_step active command s whole next t whole' : memory_only command ->
  step active command (State s whole) next (State t whole') ->
  memory_only next /\ forall x, s x = t x.
Proof.
  intros Hmemory Hstep. split.
  - intros x H; apply (Hmemory x); eapply step_modifies_subset; eassumption.
  - intros x; exact (step_preserves_unmodified _ _ _ _ _ Hstep x (Hmemory x)).
Qed.

Lemma private_derivation_skip active owner invariant start pre annotation finish post :
  private_derivation active owner invariant start pre (Concurrent.skip annotation) finish post ->
  start = finish /\ pre = post.
Proof. intros H; inversion H; auto. Qed.

Lemma private_primitive_derivation_step active owner invariant start pre primitive annotation finish post s local region frame whole next t whole' :
  private_derivation active owner invariant start pre (Concurrent.Prim primitive annotation) finish post ->
  private_environment active owner invariant start s local region frame whole ->
  persistent_full_satisfies active s local pre ->
  step active (Concurrent.Prim primitive annotation) (State s whole) next (State t whole') ->
  exists phase' pre' local' region' frame',
    private_environment active owner invariant phase' t local' region' frame' whole' /\
    memory_flushes active frame frame' /\ domain_included region' region /\
    persistent_full_satisfies active t local' pre' /\
    private_derivation active owner invariant phase' pre' next finish post.
Proof.
  intros Hderive Henv Hp Hstep. inversion Hstep; subst.
  - pose proof (private_calculus_sound _ _ _ _ _ _ _ _ Hderive _ _ _
      (private_region_ok _ _ _ _ _ _ _ _ _ Henv) Hp 2) as [_ [_ [_ Hprogress]]].
    destruct (Hprogress _ _ _ _ _ Henv Hstep) as [phase' [local' [region' [frame' [Henv' [Hflush [Hdom [_ [Hpost _]]]]]]]]].
    destruct (Hpost ltac:(eexists; reflexivity)) as [E HQ]; subst phase'.
    exists finish, post, local', region', frame'. split; [exact Henv' |].
    split; [exact Hflush |]. split; [exact Hdom |]. split; [exact HQ |apply PrivateSkip].
  - match goal with H : flush _ _ _ |- _ =>
      destruct (private_environment_flush _ _ _ _ _ _ _ _ _ _ Henv H)
        as [local' [region' [frame' [Henv' [Hlocal [Hframe Hdom]]]]]] end.
    exists start, pre, local', region', frame'. split; [exact Henv' |].
    split; [exact Hframe |]. split; [exact Hdom |]. split; [|exact Hderive].
    eapply persistent_full_flushing_closed; eassumption.
Qed.

Theorem private_derivation_step active owner invariant start pre command finish post :
  private_derivation active owner invariant start pre command finish post ->
  forall s local region frame whole next t whole',
  private_environment active owner invariant start s local region frame whole ->
  persistent_full_satisfies active s local pre -> step active command (State s whole) next (State t whole') ->
  exists phase' pre' local' region' frame',
    private_environment active owner invariant phase' t local' region' frame' whole' /\
    memory_flushes active frame frame' /\ domain_included region' region /\
    persistent_full_satisfies active t local' pre' /\ private_derivation active owner invariant phase' pre' next finish post.
Proof.
  intros Hderive. induction Hderive; intros s local region frame whole next t whole' Henv Hp Hstep;
    try solve [eapply private_primitive_derivation_step; [econstructor; eauto |exact Henv |exact Hp |exact Hstep]].
  inversion Hstep; subst.
  - match goal with H : flush _ _ _ |- _ =>
      destruct (private_environment_flush _ _ _ _ _ _ _ _ _ _ Henv H)
        as [local' [region' [frame' [Henv' [Hlocal [Hframe Hdom]]]]]] end.
    exists start, pre, local', region', frame'. split; [exact Henv' |]. split; [exact Hframe |].
    split; [exact Hdom |]. split; [eapply persistent_full_flushing_closed; eassumption |].
    eapply PrivateSequence; eassumption.
  - match goal with H : step _ first _ _ _ |- _ =>
      destruct (IHHderive1 _ _ _ _ _ _ _ _ Henv Hp H)
        as [phase' [pre' [local' [region' [frame' [Henv' [Hframe [Hdom [Hp' Hderive']]]]]]]]] end.
    exists phase', pre', local', region', frame'. split; [exact Henv' |]. split; [exact Hframe |].
    split; [exact Hdom |]. split; [exact Hp' |]. eapply PrivateSequence; eassumption.
  - destruct (private_derivation_skip _ _ _ _ _ _ _ _ Hderive1) as [Ephase Epre]; subst.
    exists middle, mid, local, region, frame. split; [exact Henv |]. split; [constructor |].
    split; [intros loc H; exact H |]. split; assumption.
Qed.

Definition thread_spec active owner invariant phase command post s local :=
  memory_only command /\ exists pre, persistent_full_satisfies active s local pre /\
    private_derivation active owner invariant phase pre command Closed post.

Lemma thread_spec_transport active owner invariant phase command post s local t local' :
  (forall x, s x = t x) -> memory_flushes active local local' ->
  thread_spec active owner invariant phase command post s local ->
  thread_spec active owner invariant phase command post t local'.
Proof.
  intros Hagrees Hflush [Hmemory [pre [Hp Hderive]]]. split; [exact Hmemory |]. exists pre; split; [|exact Hderive].
  eapply persistent_full_agrees; [intros x _; apply Hagrees |].
  eapply persistent_full_flushing_closed; eassumption.
Qed.

Lemma thread_spec_terminal active owner invariant phase annotation post s local :
  thread_spec active owner invariant phase (Concurrent.skip annotation) post s local ->
  phase = Closed /\ persistent_full_satisfies active s local post.
Proof.
  intros [_ [pre [Hp Hd]]]. destruct (private_derivation_skip _ _ _ _ _ _ _ _ Hd) as [E F]; subst; auto.
Qed.

Theorem thread_spec_progress active owner invariant phase command post s local region frame whole next t whole' :
  thread_spec active owner invariant phase command post s local ->
  private_environment active owner invariant phase s local region frame whole ->
  step active command (State s whole) next (State t whole') ->
  exists phase' local' region' frame', private_environment active owner invariant phase' t local' region' frame' whole' /\
    memory_flushes active frame frame' /\ thread_spec active owner invariant phase' next post t local'.
Proof.
  intros [Hmemory [pre [Hp Hd]]] Henv Hstep.
  destruct (private_derivation_step _ _ _ _ _ _ _ _ Hd _ _ _ _ _ _ _ _ Henv Hp Hstep)
    as [phase' [pre' [local' [region' [frame' [Henv' [Hflush [Hdom [Hp' Hd']]]]]]]]].
  exists phase', local', region', frame'. split; [exact Henv' |]. split; [exact Hflush |].
  split; [exact (proj1 (memory_only_step _ _ _ _ _ _ _ Hmemory Hstep)) |exists pre'; auto].
Qed.

Lemma thread_spec_no_abort active owner invariant phase command post s local region frame whole :
  thread_spec active owner invariant phase command post s local ->
  private_environment active owner invariant phase s local region frame whole -> ~ abort active command (State s whole).
Proof.
  intros [_ [pre [Hp Hd]]] Henv.
  pose proof (private_calculus_sound _ _ _ _ _ _ _ _ Hd _ _ _
    (private_region_ok _ _ _ _ _ _ _ _ _ Henv) Hp 1) as [_ [_ [Hnoabort _]]].
  exact (Hnoabort _ _ Henv).
Qed.

Lemma held_blocks_other active whole owner other : lock_held active whole owner ->
  active other -> other <> owner -> blocked whole other.
Proof. intros [_ Hheld] Hi Hneq; apply Hheld; auto. Qed.

(** A closed thread may take structural control steps while another owner
    holds the lock. Its acquire and load instructions cannot proceed or fault.
    This does not assume that other processors stop executing altogether. *)
Theorem waiting_derivation_step active observer invariant start pre command finish post :
  private_derivation active observer invariant start pre command finish post ->
  start = Closed -> forall holder s whole next t whole', observer <> holder ->
  lock_held active whole holder -> step active command (State s whole) next (State t whole') ->
  (next = command /\ t = s /\ flush active whole whole') \/
  (t = s /\ whole' = whole /\ private_derivation active observer invariant Closed pre next finish post).
Proof.
  intros Hd. induction Hd; intros E holder s whole next t whole' Hneq Hheld Hstep; try discriminate.
  - subst phase. inversion Hstep; subst.
    + match goal with H : primitive_step _ _ _ _ _ |- _ => inversion H end.
    + left; auto.
  - inversion Hstep; subst.
    + match goal with H : eval_expr _ (EVal _) = Z.pos _ |- _ => simpl in H; inversion H; subst end.
      match goal with H : primitive_step _ _ _ _ _ |- _ => inversion H; subst end.
      exfalso. match goal with H : lock_free _, Hn : ?i <> _ |- _ => apply (H i) end.
      eapply held_blocks_other; eassumption.
    + left; auto.
  - inversion Hstep; subst.
    + match goal with H : eval_expr _ (EVal _) = Z.pos _ |- _ => simpl in H; inversion H; subst end.
      match goal with H : primitive_step _ _ _ _ _ |- _ => inversion H; subst end.
      exfalso. match goal with H : ~ blocked _ _ |- _ => apply H end.
      eapply held_blocks_other; eassumption.
    + left; auto.
  - subst start. inversion Hstep; subst.
    + left; auto.
    + match goal with H : step _ first _ _ _ |- _ =>
        destruct (IHHd1 eq_refl _ _ _ _ _ _ Hneq Hheld H) as [[Ec [Et Hflush]] |[Et [Em Hderive]]] end; subst.
      * left; auto.
      * right; split; [reflexivity |]. split; [reflexivity |]. eapply PrivateSequence; eassumption.
    + destruct (private_derivation_skip _ _ _ _ _ _ _ _ Hd1) as [Ephase Epre]; subst.
      right; auto.
Qed.

Theorem waiting_derivation_no_abort active observer invariant start pre command finish post :
  private_derivation active observer invariant start pre command finish post -> start = Closed ->
  forall holder s whole, observer <> holder -> lock_held active whole holder -> ~ abort active command (State s whole).
Proof.
  intros Hd. induction Hd; intros E holder s whole Hneq Hheld Hfault; try discriminate.
  - inversion Hfault; subst; match goal with H : primitive_abort _ _ _ _ |- _ => inversion H end.
  - inversion Hfault; subst; match goal with H : primitive_abort _ _ _ _ |- _ => inversion H end.
  - inversion Hfault; subst.
    match goal with H : eval_expr _ (EVal _) = Z.pos _ |- _ => simpl in H; inversion H; subst end.
    match goal with H : primitive_abort _ _ _ _ |- _ => inversion H; subst end.
    match goal with H : ~ blocked _ _ |- _ => apply H end.
    eapply held_blocks_other; eassumption.
  - inversion Hfault; subst; eapply IHHd1; eassumption || reflexivity.
Qed.
