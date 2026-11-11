From Stdlib Require Import List ZArith.
From WMLR Require Import Expressions Languages Machine Separation FrameDecomposition OperationalSemantics
  Assertions AssertionSemantics PersistentAssertions Safety OwnershipProtocol PrivateOwnership PrivateRules
  PrivateCalculus SpatialExchange ThreadProgress SharedViews.
Import ListNotations.

(** The operational semantics erases a parallel node when either side is
    skip. The retired thread's postcondition remains a spatial frame. *)
Inductive parallel_certificate active left right invariant q r : Concurrent.command -> stack -> memory -> Prop :=
| CertificatePair c d s whole :
    joint_state active left right invariant q r c d s whole ->
    parallel_certificate active left right invariant q r (Concurrent.Parallel c d) s whole
| CertificateLeft phase local region frame c s whole :
    private_environment active left invariant phase s local region frame whole ->
    thread_spec active left invariant phase c q s local ->
    persistent_full_satisfies active s frame r ->
    parallel_certificate active left right invariant q r c s whole
| CertificateRight phase local region frame d s whole :
    private_environment active right invariant phase s local region frame whole ->
    thread_spec active right invariant phase d r s local ->
    persistent_full_satisfies active s frame q ->
    parallel_certificate active left right invariant q r d s whole.

Theorem parallel_certificate_no_abort active left right invariant q r c s whole :
  left <> right -> parallel_certificate active left right invariant q r c s whole ->
  ~ abort active c (State s whole).
Proof.
  intros Hneq Hcert; destruct Hcert.
  - intros Habort; inversion Habort; subst.
    + eapply joint_left_no_abort; eassumption.
    + eapply (joint_left_no_abort active right left); [congruence |apply joint_state_sym; eassumption |eassumption].
  - eapply thread_spec_no_abort; eassumption.
  - eapply thread_spec_no_abort; eassumption.
Qed.

Lemma full_model_transport active p s t local local' :
  (forall x, s x = t x) -> memory_flushes active local local' ->
  persistent_full_satisfies active s local p -> persistent_full_satisfies active t local' p.
Proof.
  intros Hstack Hflush Hp. eapply persistent_full_agrees; [intros x _; apply Hstack |].
  eapply persistent_full_flushing_closed; eassumption.
Qed.

Theorem parallel_certificate_step active left right invariant q r c s whole next t whole' :
  left <> right -> parallel_certificate active left right invariant q r c s whole ->
  step active c (State s whole) next (State t whole') ->
  parallel_certificate active left right invariant q r next t whole'.
Proof.
  intros Hneq Hcert Hstep; destruct Hcert as
    [c d s whole Hjoint |phase local region frame c s whole Henv Hthread Hr |
     phase local region frame d s whole Henv Hthread Hq].
  - inversion Hstep; subst.
    + apply CertificatePair. eapply joint_state_flush; eassumption.
    + apply CertificatePair. eapply joint_left_step; eassumption.
    + apply CertificatePair. eapply joint_right_step; eassumption.
    + destruct (joint_left_done _ _ _ _ _ _ _ _ _ _ Hjoint) as [phase [local [region [frame [Henv [Hd Hq]]]]]].
      eapply CertificateRight; eassumption.
    + destruct (joint_left_done _ _ _ _ _ _ _ _ _ _ (joint_state_sym _ _ _ _ _ _ _ _ _ _ Hjoint))
        as [phase [local [region [frame [Henv [Hc Hr]]]]]].
      eapply CertificateLeft; eassumption.
  - pose proof (proj2 (memory_only_step _ _ _ _ _ _ _ (proj1 Hthread) Hstep)) as Hstack.
    destruct (thread_spec_progress _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hthread Henv Hstep)
      as [phase' [local' [region' [frame' [Henv' [Hframe Hthread']]]]]].
    eapply CertificateLeft; [exact Henv' |exact Hthread' |eapply full_model_transport; eassumption].
  - pose proof (proj2 (memory_only_step _ _ _ _ _ _ _ (proj1 Hthread) Hstep)) as Hstack.
    destruct (thread_spec_progress _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hthread Henv Hstep)
      as [phase' [local' [region' [frame' [Henv' [Hframe Hthread']]]]]].
    eapply CertificateRight; [exact Henv' |exact Hthread' |eapply full_model_transport; eassumption].
Qed.

Theorem parallel_certificate_execution active left right invariant q r n c s whole last t final :
  left <> right -> execution active n c s whole last t final ->
  parallel_certificate active left right invariant q r c s whole ->
  parallel_certificate active left right invariant q r last t final.
Proof.
  intros Hneq Hrun; induction Hrun; intros Hcert; [exact Hcert |].
  apply IHHrun. eapply parallel_certificate_step; eassumption.
Qed.

(** Recombine the two private posts without duplicating the invariant. *)
Lemma closed_pair_post active owner invariant q r s local region frame whole :
  private_environment active owner invariant Closed s local region frame whole ->
  persistent_full_satisfies active s local q -> persistent_full_satisfies active s frame r ->
  exists pool combined, memory_spatial pool combined whole /\
    persistent_full_satisfies active s pool invariant /\
    persistent_full_satisfies active s combined (A.Spatial q r) /\ lock_free whole.
Proof.
  intros [[Hl [Hr [Hfree [pool [HJ Hinner]]]]] Hf Hw Hframe Houter] Hq Hrpost.
  destruct (proj2 (memory_spatial_associative pool local frame whole)
    (ex_intro _ region (conj Hinner (memory_spatial_comm _ _ _ Houter))))
    as [combined [Hpair Hpool]].
  exists pool, combined. split; [exact Hpool |]. split; [exact HJ |]. split.
  - eapply full_spatial_intro; eassumption.
  - exact (spatial_free_union _ _ _ Houter Hframe Hfree).
Qed.

Theorem parallel_certificate_post active left right invariant q r c s whole :
  parallel_certificate active left right invariant q r c s whole -> terminal c ->
  exists pool combined, memory_spatial pool combined whole /\
    persistent_full_satisfies active s pool invariant /\
    persistent_full_satisfies active s combined (A.Spatial q r) /\ lock_free whole.
Proof.
  intros Hcert [annotation Ec]; subst c. inversion Hcert; subst.
  - destruct (thread_spec_terminal _ _ _ _ _ _ _ _ H0) as [E HQ]; subst phase.
    eapply closed_pair_post; eassumption.
  - destruct (thread_spec_terminal _ _ _ _ _ _ _ _ H0) as [E HR]; subst phase.
    destruct (private_closed_exchange _ _ left _ _ _ _ _ _ H) as [region' Henv].
    eapply closed_pair_post; eassumption.
Qed.

(** Two distinct processors, a single shared invariant, and disjoint private
    resources. This first parallel rule excludes register modifications;
    that restriction supplies the interference condition for all assertions. *)
Theorem private_parallel_rule active left right invariant p q r u c d s local region frame whole :
  left <> right -> memory_only c -> memory_only d ->
  private_derivation active left invariant Closed p c Closed q ->
  private_derivation active right invariant Closed r d Closed u ->
  private_environment active left invariant Closed s local region frame whole ->
  persistent_full_satisfies active s local p -> persistent_full_satisfies active s frame r ->
  forall n last t final, execution active n (Concurrent.Parallel c d) s whole last t final ->
    ~ abort active last (State t final) /\
    (terminal last -> exists pool combined, memory_spatial pool combined final /\
      persistent_full_satisfies active t pool invariant /\
      persistent_full_satisfies active t combined (A.Spatial q u) /\ lock_free final).
Proof.
  intros Hneq Hc Hd Hderivec Hderived Henv Hp Hr n last t final Hrun.
  assert (Hcert : parallel_certificate active left right invariant q u (Concurrent.Parallel c d) s whole).
  { apply CertificatePair. eapply JointClosed; [exact Henv |split; [exact Hc |exists p; auto] |
      split; [exact Hd |exists r; auto]]. }
  pose proof (parallel_certificate_execution _ _ _ _ _ _ _ _ _ _ _ _ _ Hneq Hrun Hcert) as Hfinal.
  split; [eapply parallel_certificate_no_abort; eassumption |eapply parallel_certificate_post; eassumption].
Qed.
