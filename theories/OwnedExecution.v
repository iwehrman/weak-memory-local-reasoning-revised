From Stdlib Require Import List ZArith.
From WMLR Require Import Expressions Languages Machine BufferRelations OrderedBuffers Separation RepairedSeparation GeneralizedFlushing
  OperationalSemantics ProgramSteps Assertions AssertionSemantics ConcreteAssertions PersistentAssertions
  Safety TemporalSafety RegionalResources InvariantFragment LockRepresentation FlushAttribution
  OwnershipProtocol OwnedSafety OwnedResources OwnedAdequacy OwnedCalculus.

(** Along an actual execution, the chosen external frame changes only by
    its own futures. The safety definition still quantifies frames afresh. *)
Theorem owned_execution_frame active mode invariant n command s whole last t final :
  invariant_fragment invariant -> execution active n command s whole last t final ->
  forall local pool frame phase post,
    owned_safe active mode invariant (S n) command s local post ->
    owned_environment active mode invariant s local pool frame whole phase ->
    exists local' pool' frame' phase',
      owned_environment active mode invariant t local' pool' frame' final phase' /\
      resource_future active frame frame' /\ owned_safe active mode invariant 1 last t local' post.
Proof.
  intros Hfragment Hrun; induction Hrun; intros local pool frame phase post Hsafe Henv.
  - exists local,pool,frame,phase; split; [exact Henv |]. split; [constructor |exact Hsafe].
  - destruct (state_step_program_or_flush _ _ _ _ _ _ _ H) as [[action Hprogram] |[-> [-> Hflush]]].
    + destruct (owned_safe_program_step _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hsafe Henv Hprogram)
        as (local' & pool' & phase' & Henv' & _ & Hsafe').
      exact (IHHrun local' pool' frame phase' post Hsafe' Henv').
    + destruct (flush_at_exists _ _ _ Hflush) as [i Hi].
      destruct (owned_environment_flush_attribution _ _ _ _ _ _ _ _ _ _ _ Hfragment Henv Hi)
        as [(frame' & Henv' & Hfuture & HF) |(local' & Henv' & Hfuture & HL)].
      * destruct (IHHrun local pool frame' phase post (owned_safe_weaken_one _ _ _ _ _ _ _ _ Hsafe) Henv')
          as (last_local & last_pool & last_frame & last_phase & Hlast & Hff & Hs).
        exists last_local,last_pool,last_frame,last_phase; split; [exact Hlast |].
        split; [eapply generalized_future_trans; eassumption |exact Hs].
      * apply (IHHrun local' pool frame phase post); [|exact Henv'].
        apply owned_safe_weaken_one; eapply owned_safe_future; eassumption.
Qed.

Lemma owned_empty_local_free_frame_pool active mode invariant s local pool frame whole phase :
  two_active_processors active ->
  owned_environment active mode invariant s local pool frame whole phase ->
  empty_atom (proj1_sig local) -> lock_free (resource_memory active frame) ->
  lock_free whole /\ persistent_full_satisfies active s pool invariant.
Proof.
  intros Htwo Henv [_ [_ Hlocal]] Hframe.
  pose proof (owned_pool_status _ _ _ _ _ _ _ _ _ Henv) as Hstatus.
  destruct phase as [|owner]; [exact Hstatus |].
  destruct Hstatus as [Hheld Epool].
  assert (Hfree : lock_free whole).
  { intros i H; apply (owned_blocked_union _ _ _ _ _ _ _ _ _ i Henv) in H.
    destruct H as [H |[H |H]]; [rewrite Epool in H; exact H |exact (Hframe i H) |exact (Hlocal i H)]. }
  destruct Htwo as (first & second & Hfirst & Hsecond & Hne).
  exfalso; exact (two_processors_separate_free_held active first second whole owner
    Hfirst Hsecond Hne Hfree Hheld).
Qed.

Lemma owned_empty_local_frame_split active mode invariant s local pool frame whole phase :
  owned_environment active mode invariant s local pool frame whole phase -> empty_atom (proj1_sig local) ->
  memory_spatial pool (resource_memory active frame) whole.
Proof.
  intros Henv [Hheap [Hbuffers Hfree]].
  destruct (owned_composition _ _ _ _ _ _ _ _ _ Henv) as (combined & [[_ [Eh [Eb Ek]]] _] & Hsp).
  eapply protocol_spatial_equiv_right; [|exact Hsp]. split.
  - intros loc; unfold resource_memory; rewrite Eh; unfold heap_override; rewrite Hheap; reflexivity.
  - split.
    + intros i; specialize (Eb i); apply ordered_interleaves in Eb; rewrite Hbuffers in Eb.
      apply interleaves_nil_right, Eb.
    + intros i; rewrite Ek; split; [intros [H |H]; [exact H |exfalso; exact (Hfree i H)] |auto].
Qed.

(** A useful strengthening for lock-balanced clients specified emp-to-emp:
    every completed execution has a free lock and restored invariant pool.
    The lock-free external frame is an initial-state condition here,
    not a new calculus side condition. *)
Theorem owned_emp_derivation_restores active invariant :
  invariant_fragment invariant -> two_active_processors active ->
  forall mode command, owned_derivation active invariant mode A.Emp command A.Emp ->
  forall n s whole last t final local pool frame phase,
    persistent_models active s local A.Emp ->
    lock_free (resource_memory active frame) ->
    owned_environment active mode invariant s local pool frame whole phase ->
    execution active n command s whole last t final ->
    ~ abort active last (State t final) /\
    (terminal last -> exists pool' frame',
      resource_future active frame frame' /\ memory_spatial pool' (resource_memory active frame') final /\
      lock_free final /\ persistent_full_satisfies active t pool' invariant).
Proof.
  intros Hfragment Htwo mode command Hderive n s whole last t final local pool frame phase HP HF Henv Hrun.
  destruct (owned_execution_frame _ _ _ _ _ _ _ _ _ _ Hfragment Hrun local pool frame phase A.Emp
    (owned_calculus_sound _ _ Hfragment Htwo _ _ _ _ Hderive _ _ HP _) Henv)
    as (local' & pool' & frame' & phase' & Henv' & Hfuture & Hsafe').
  split; [eapply owned_safe_no_abort; eassumption |].
  intros Hterminal; exists pool',frame'. split; [exact Hfuture |]. split.
  - eapply owned_empty_local_frame_split; [exact Henv' |].
    change (persistent_models active t local' A.Emp); eapply owned_safe_terminal; eassumption.
  -
  eapply owned_empty_local_free_frame_pool; [exact Htwo |exact Henv' | |].
  + change (persistent_models active t local' A.Emp).
    eapply owned_safe_terminal; eassumption.
  + intros i H; apply (HF i), (resource_future_blocks _ _ _ Hfuture i), H.
Qed.
