From Stdlib Require Import List ZArith.
From WMLR Require Import Expressions Languages Machine BufferRelations Separation
  OperationalSemantics Assertions AssertionSemantics PersistentAssertions Safety Specifications
  HeapRules OwnershipProtocol OwnershipRules OwnershipHeap PrivateOwnership TemporalSafety SeparatedHeap
  TransferredCells RetiredHeaps RetiredSafety RetiredTransfer.
Import ListNotations.

Theorem retired_safe_sequence active owner invariant n first second s phase local protected
    middle protected_mid mid finish protected_post post :
  retired_safe active owner invariant n first s phase local protected middle protected_mid mid ->
  retired_valid active owner invariant middle protected_mid mid second finish protected_post post ->
  retired_safe active owner invariant n (Concurrent.Seq first second) s phase local protected finish protected_post post.
Proof.
  intros Hfirst Hsecond; revert first s phase local protected Hfirst.
  induction n; intros first s phase local protected Hfirst; [exact I |].
  destruct Hfirst as [Hr [Hb [Hdone [Habort Hprogress]]]].
  split; [exact Hr |]. split; [exact Hb |]. split; [intros [ann E]; discriminate |]. split.
  - intros history whole Henv Hfault; inversion Hfault; subst; eapply Habort; eassumption.
  - intros history whole next t whole' Henv Hstep; inversion Hstep; subst.
    + exfalso; eapply retired_no_flush; eassumption.
    + match goal with H : step _ first _ _ _ |- _ =>
        destruct (Hprogress _ _ _ _ _ Henv H) as (phase' & local' & protected' & Henv' & Hsafe') end.
      exists phase', local', protected'; split; [exact Henv' |apply IHn, Hsafe'].
    + destruct (Hdone ltac:(eexists; reflexivity)) as [E [HS HP]]; subst phase.
      exists middle, local, protected; split; [exact Henv |apply Hsecond; assumption].
Qed.

Theorem retired_sequence_valid active owner invariant start protected_pre pre first middle protected_mid mid
    second finish protected_post post :
  retired_valid active owner invariant start protected_pre pre first middle protected_mid mid ->
  retired_valid active owner invariant middle protected_mid mid second finish protected_post post ->
  retired_valid active owner invariant start protected_pre pre (Concurrent.Seq first second) finish protected_post post.
Proof.
  intros Hfirst Hsecond s local protected Hr Hb HS HP n; eapply retired_safe_sequence;
    [apply Hfirst; eassumption |exact Hsecond].
Qed.

Theorem retired_acquire_valid active owner invariant pre :
  retired_valid active owner invariant Closed A.Emp pre
    (Concurrent.Prim Concurrent.Lock (EVal (Z.pos owner))) Open (owned_assertion owner invariant) pre.
Proof.
  apply retired_primitive_rule; [discriminate | |].
  - intros s local protected history whole Henv HS HP i E Hfault; inversion Hfault.
  - intros s local protected history whole [[Hwf [Hfree HJ]] Hb [combined [Htm Hsp]]] HS HP i t whole' E Hstep.
    simpl in E; inversion E; subst i; inversion Hstep; subst.
    exists local, (acquire active protected owner); split.
    + constructor.
      * split; [apply acquire_well_formed, Hwf |]. split; [assumption |intros j; reflexivity].
      * exact Hb.
      * exists combined; split; [exact Htm |]. apply protocol_spatial_reblock; [intros j H; contradiction |exact Hsp].
    + split; [apply acquire_exposes_invariant; assumption |exact HP].
Qed.

Lemma retired_private_read active owner invariant phase s local protected history whole loc v i :
  retired_environment active owner invariant phase s local protected history whole ->
  RH.live_heap local loc = Some v -> local_read whole i (Z.pos loc) = Some v.
Proof.
  intros Henv Hlocal; pose proof (retired_whole_flushed _ _ _ _ _ _ _ _ _ Henv i) as Hb.
  destruct Henv as [_ _ [combined [Htm [[Hd _] [Hh _]]]]].
  assert (Hcurrent : RH.live_heap combined loc = Some v) by (eapply RH.temporal_live_right; eassumption).
  assert (Hpool : shared_heap protected loc = None).
  { destruct (shared_heap protected loc) eqn:E; [|reflexivity].
    exfalso; apply (Hd loc); left; eexists; eassumption. }
  unfold local_read; rewrite Hb; cbn [buffer_lookup]; rewrite Hh.
  unfold heap_override; rewrite Hpool; exact Hcurrent.
Qed.

Theorem retired_load_valid active owner invariant phase protected_assertion cell_owner loc v x :
  ~ In x (A.fv invariant) -> ~ In x (A.fv protected_assertion) ->
  retired_valid active owner invariant phase protected_assertion (processor_cell cell_owner loc v)
    (Concurrent.Prim (Concurrent.Common (Sequential.Load x (EVal (Z.pos loc)))) (EVal (Z.pos owner)))
    phase protected_assertion (A.And (processor_cell cell_owner loc v) (A.Pure (BEq (EVar x) (EVal v)))).
Proof.
  intros HJ HSfresh; apply retired_primitive_rule; [discriminate | |].
  - intros s local protected history whole Henv HS HP i E Hfault.
    destruct (RH.processor_cell_shape _ _ _ _ _ _ HP) as [_ [Hheap _]].
    inversion Hfault; subst.
    pose proof (retired_private_read _ _ _ _ _ _ _ _ _ loc v i Henv
      ltac:(rewrite Hheap; apply heap_update_same)) as Hread.
    cbn [eval_expr] in *; congruence.
  - intros s local protected history whole Henv HS HP i t whole' E Hstep.
    destruct (RH.processor_cell_shape _ _ _ _ _ _ HP) as [_ [Hheap _]].
    inversion Hstep; subst.
    pose proof (retired_private_read _ _ _ _ _ _ _ _ _ loc v i Henv
      ltac:(rewrite Hheap; apply heap_update_same)) as Hread.
    assert (Evalue : v0 = v) by (cbn [eval_expr] in *; congruence); subst v0.
    exists local, protected; split.
    + destruct Henv as [Hr Hb Hcomp]; constructor; try assumption.
      apply protocol_region_update; assumption.
    + split.
      * eapply persistent_full_agrees; [apply agrees_update_irrelevant, HSfresh |exact HS].
      * split.
        -- apply (proj1 (satisfies_agrees (RH.interpretation active) _ _ _
             (agrees_update_irrelevant _ s x v (processor_cell_fresh cell_owner loc v x)) local)), HP.
        -- change (Z.eqb (update s x v x) v = true); rewrite update_same; apply Z.eqb_refl.
Qed.

(** A small calculus for the experiment. Constructors require assertion
    premises and syntax, never the desired validity or safety conclusion. *)
Inductive retired_derivation (active : processor_domain) (owner : processor) (invariant : A.assertion) :
    ownership_phase -> A.assertion -> A.assertion ->
    Concurrent.command -> ownership_phase -> A.assertion -> A.assertion -> Prop :=
| RetiredSkip phase protected p annotation : retired_derivation active owner invariant phase protected p
    (Concurrent.skip annotation) phase protected p
| RetiredAcquire p : retired_derivation active owner invariant Closed A.Emp p
    (Concurrent.Prim Concurrent.Lock (EVal (Z.pos owner))) Open (owned_assertion owner invariant) p
| RetiredRelease p : retired_derivation active owner invariant Open (owned_assertion owner invariant) p
    (Concurrent.Prim Concurrent.Unlock (EVal (Z.pos owner))) Closed A.Emp p
| RetiredDonateFence rest loc v : retired_derivation active owner invariant Open
    (owned_assertion owner rest) (processor_cell owner loc v)
    (Concurrent.Prim (Concurrent.Common Sequential.Fence) (EVal (Z.pos owner)))
    Open (owned_assertion owner (A.Spatial rest (processor_cell owner loc v))) A.Emp
| RetiredDonateRelease rest loc v : invariant = A.Spatial rest (processor_cell owner loc v) ->
    retired_derivation active owner invariant Open (owned_assertion owner rest) (processor_cell owner loc v)
      (Concurrent.Prim Concurrent.Unlock (EVal (Z.pos owner))) Closed A.Emp A.Emp
| RetiredTakeRelease loc v : retired_derivation active owner invariant Open
    (owned_assertion owner (A.Spatial invariant (processor_cell owner loc v))) A.Emp
    (Concurrent.Prim Concurrent.Unlock (EVal (Z.pos owner))) Closed A.Emp (processor_cell owner loc v)
| RetiredLoad phase protected cell_owner loc v x : ~ In x (A.fv invariant) -> ~ In x (A.fv protected) ->
    retired_derivation active owner invariant phase protected (processor_cell cell_owner loc v)
      (Concurrent.Prim (Concurrent.Common (Sequential.Load x (EVal (Z.pos loc)))) (EVal (Z.pos owner)))
      phase protected (A.And (processor_cell cell_owner loc v) (A.Pure (BEq (EVar x) (EVal v))))
| RetiredSequence start protected_pre pre first middle protected_mid mid second finish protected_post post :
    retired_derivation active owner invariant start protected_pre pre first middle protected_mid mid ->
    retired_derivation active owner invariant middle protected_mid mid second finish protected_post post ->
    retired_derivation active owner invariant start protected_pre pre (Concurrent.Seq first second) finish protected_post post
| RetiredFrameTM start protected_pre pre command finish protected_post post frame :
    retired_derivation active owner invariant start protected_pre pre command finish protected_post post ->
    frame_variable_condition command frame ->
    retired_derivation active owner invariant start protected_pre (A.Temporal frame pre) command finish
      protected_post (A.Temporal frame post).

Theorem retired_calculus_sound active owner invariant start protected_pre pre command finish protected_post post :
  retired_derivation active owner invariant start protected_pre pre command finish protected_post post ->
  retired_valid active owner invariant start protected_pre pre command finish protected_post post.
Proof.
  induction 1.
  - intros s local pool Hr Hb HS HP n; apply retired_skip_safe; assumption.
  - apply retired_acquire_valid.
  - apply retired_release_valid.
  - apply retired_donate_fence_valid.
  - subst invariant; apply retired_donate_release_valid.
  - apply retired_take_release_valid.
  - apply retired_load_valid; assumption.
  - eapply retired_sequence_valid; eassumption.
  - apply retired_FRAME_TM; assumption.
Qed.
