From Stdlib Require Import List ZArith.
From WMLR Require Import Expressions Languages Machine Separation FrameDecomposition OperationalSemantics
  Assertions AssertionSemantics PersistentAssertions Safety OwnershipProtocol PrivateOwnership PrivateRules
  PrivateCalculus SpatialExchange VariableSupport ThreadProgress.
Import ListNotations.

(** Exactly one global ownership decision. A waiting thread retains its
    private assertion but has no independent copy of the protected pool. *)
Inductive joint_state active left right invariant left_interface right_interface q r c d s whole : Prop :=
| JointClosed a region b :
    private_environment active left invariant Closed s a region b whole ->
    thread_spec active left invariant left_interface Closed c q s a ->
    thread_spec active right invariant right_interface Closed d r s b ->
    joint_state active left right invariant left_interface right_interface q r c d s whole
| JointLeft a b :
    private_environment active left invariant Open s a a b whole ->
    thread_spec active left invariant left_interface Open c q s a ->
    thread_spec active right invariant right_interface Closed d r s b ->
    joint_state active left right invariant left_interface right_interface q r c d s whole
| JointRight a b :
    private_environment active right invariant Open s b b a whole ->
    thread_spec active left invariant left_interface Closed c q s a ->
    thread_spec active right invariant right_interface Open d r s b ->
    joint_state active left right invariant left_interface right_interface q r c d s whole.

Lemma private_open_whole_held active owner invariant s local region frame whole :
  private_environment active owner invariant Open s local region frame whole -> lock_held active whole owner.
Proof.
  intros [[Hl [Hr [E [Hi Hheld]]]] Hf Hw Hfree [_ [_ [_ Hk]]]]. split; [exact Hi |].
  intros i; rewrite Hk. split.
  - intros [H |H]; [exfalso; apply (Hfree i H) |apply Hheld, H].
  - intros H; right; apply Hheld, H.
Qed.

Theorem joint_state_sym active left right invariant left_interface right_interface q r c d s whole :
  joint_state active left right invariant left_interface right_interface q r c d s whole ->
  joint_state active right left invariant right_interface left_interface r q d c s whole.
Proof.
  intros Hjoint; destruct Hjoint.
  - destruct (private_closed_exchange _ _ right _ _ _ _ _ _ H) as [region' Henv].
    eapply JointClosed; eassumption.
  - eapply JointRight; eassumption.
  - eapply JointLeft; eassumption.
Qed.

Theorem joint_state_flush active left right invariant left_interface right_interface q r c d s whole whole' :
  joint_state active left right invariant left_interface right_interface q r c d s whole -> flush active whole whole' ->
  joint_state active left right invariant left_interface right_interface q r c d s whole'.
Proof.
  intros Hjoint Hflush; destruct Hjoint as [a region b Henv Ha Hb |a b Henv Ha Hb |a b Henv Ha Hb].
  - destruct (private_environment_flush _ _ _ _ _ _ _ _ _ _ Henv Hflush)
      as [a' [region' [b' [Henv' [Haf [Hbf Hdom]]]]]].
    eapply JointClosed; [exact Henv' | |]; eapply thread_spec_transport; eauto; intros x Hx; reflexivity.
  - destruct (private_environment_flush _ _ _ _ _ _ _ _ _ _ Henv Hflush)
      as [a' [region' [b' [Henv' [Haf [Hbf Hdom]]]]]].
    destruct (private_region_ok _ _ _ _ _ _ _ _ _ Henv') as [_ [_ [E _]]]; subst region'.
    eapply JointLeft; [exact Henv' | |]; eapply thread_spec_transport; eauto; intros x Hx; reflexivity.
  - destruct (private_environment_flush _ _ _ _ _ _ _ _ _ _ Henv Hflush)
      as [b' [region' [a' [Henv' [Hbf [Haf Hdom]]]]]].
    destruct (private_region_ok _ _ _ _ _ _ _ _ _ Henv') as [_ [_ [E _]]]; subst region'.
    eapply JointRight; [exact Henv' | |]; eapply thread_spec_transport; eauto; intros x Hx; reflexivity.
Qed.

Theorem joint_left_no_abort active left right invariant left_interface right_interface q r c d s whole :
  left <> right -> joint_state active left right invariant left_interface right_interface q r c d s whole -> ~ abort active c (State s whole).
Proof.
  intros Hneq Hjoint; destruct Hjoint as [a region b Henv Ha Hb |a b Henv Ha Hb |a b Henv Ha Hb].
  - eapply thread_spec_no_abort; eassumption.
  - eapply thread_spec_no_abort; eassumption.
  - destruct Ha as [_ _ _ _ [pre [Hp [Hd HF]]]]. eapply waiting_derivation_no_abort;
      [exact Hd |reflexivity |exact Hneq |exact (private_open_whole_held _ _ _ _ _ _ _ _ Henv)].
Qed.

Theorem joint_left_step active left right invariant left_interface right_interface q r c d s whole next t whole' :
  left <> right -> interfaces_compatible left_interface right_interface ->
  joint_state active left right invariant left_interface right_interface q r c d s whole ->
  step active c (State s whole) next (State t whole') ->
  joint_state active left right invariant left_interface right_interface q r next d t whole'.
Proof.
  intros Hneq Hcompatible Hjoint Hstep; destruct Hjoint as [a region b Henv Ha Hb |a b Henv Ha Hb |a b Henv Ha Hb].
  - pose proof (thread_step_agrees _ _ _ _ _ _ _ _ _ _ _ _ _ _ Ha (proj1 Hcompatible) Hstep) as Hstack.
    destruct (thread_spec_progress _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Ha Henv Hstep)
      as [phase' [a' [region' [b' [Henv' [Hbf Ha']]]]]].
    pose proof (thread_spec_transport _ _ _ _ _ _ _ _ _ _ _ Hstack Hbf Hb) as Hb'.
    destruct phase'.
    + eapply JointClosed; eassumption.
    + destruct (private_region_ok _ _ _ _ _ _ _ _ _ Henv') as [_ [_ [E _]]]; subst region'.
      eapply JointLeft; eassumption.
  - pose proof (thread_step_agrees _ _ _ _ _ _ _ _ _ _ _ _ _ _ Ha (proj1 Hcompatible) Hstep) as Hstack.
    destruct (thread_spec_progress _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Ha Henv Hstep)
      as [phase' [a' [region' [b' [Henv' [Hbf Ha']]]]]].
    pose proof (thread_spec_transport _ _ _ _ _ _ _ _ _ _ _ Hstack Hbf Hb) as Hb'.
    destruct phase'.
    + eapply JointClosed; eassumption.
    + destruct (private_region_ok _ _ _ _ _ _ _ _ _ Henv') as [_ [_ [E _]]]; subst region'.
      eapply JointLeft; eassumption.
  - destruct Ha as [Hw HJ HC HQ [pre [Hp [Hd HF]]]].
    destruct (waiting_derivation_step _ _ _ _ _ _ _ _ Hd eq_refl _ _ _ _ _ _ Hneq
      (private_open_whole_held _ _ _ _ _ _ _ _ Henv) Hstep) as [[Ec [Et Hflush]] |[Et [Em Hd']]]; subst.
    + eapply joint_state_flush; [eapply JointRight; [exact Henv |constructor; try assumption; exists pre; auto |exact Hb] |exact Hflush].
    + eapply JointRight; [exact Henv | |exact Hb]. constructor; try assumption.
      * intros x Hx; apply Hw; eapply step_modifies_subset; eassumption.
      * intros x Hx; apply HC; eapply step_fv_subset; eassumption.
      * exists pre; auto.
Qed.

Theorem joint_right_step active left right invariant left_interface right_interface q r c d s whole next t whole' :
  left <> right -> interfaces_compatible left_interface right_interface ->
  joint_state active left right invariant left_interface right_interface q r c d s whole ->
  step active d (State s whole) next (State t whole') ->
  joint_state active left right invariant left_interface right_interface q r c next t whole'.
Proof.
  intros Hneq Hcompatible Hjoint Hstep. apply joint_state_sym. eapply joint_left_step;
    [congruence |apply interfaces_compatible_sym, Hcompatible |apply joint_state_sym, Hjoint |exact Hstep].
Qed.

Theorem joint_left_done active left right invariant left_interface right_interface q r annotation d s whole :
  joint_state active left right invariant left_interface right_interface q r (Concurrent.skip annotation) d s whole ->
  exists phase local region frame, private_environment active right invariant phase s local region frame whole /\
    thread_spec active right invariant right_interface phase d r s local /\ persistent_full_satisfies active s frame q /\
    incl (A.fv q) (interface_variables left_interface).
Proof.
  intros Hjoint; destruct Hjoint as [a region b Henv Ha Hb |a b Henv Ha Hb |a b Henv Ha Hb].
  - pose proof (thread_post_variables _ _ _ _ _ _ _ _ _ Ha) as HF.
    destruct (thread_spec_terminal _ _ _ _ _ _ _ _ _ Ha) as [_ HQ].
    destruct (private_closed_exchange _ _ right _ _ _ _ _ _ Henv) as [region' Henv'].
    exists Closed, b, region', a; auto.
  - destruct (thread_spec_terminal _ _ _ _ _ _ _ _ _ Ha) as [E _]; discriminate.
  - pose proof (thread_post_variables _ _ _ _ _ _ _ _ _ Ha) as HF.
    destruct (thread_spec_terminal _ _ _ _ _ _ _ _ _ Ha) as [_ HQ].
    exists Open, b, b, a; auto.
Qed.
