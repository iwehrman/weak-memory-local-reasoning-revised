From Stdlib Require Import List Arith ZArith.
From WMLR Require Import Expressions Languages Machine BufferRelations Separation
  RepairedSeparation GeneralizedFlushing FrameDecomposition OperationalSemantics
  ProgramSteps Assertions AssertionSemantics ConcreteAssertions PersistentAssertions Safety
  SpatialExchange TemporalSafety InvariantFragment FlushAttribution OwnershipProtocol OwnedSafety.
Import ListNotations.

Lemma owned_pool_buffers_empty active mode invariant s local pool frame whole phase :
  invariant_fragment invariant ->
  owned_environment active mode invariant s local pool frame whole phase ->
  forall i, buffers pool i = [].
Proof.
  intros Hfragment Henv.
  pose proof (owned_pool_status _ _ _ _ _ _ _ _ _ Henv) as Hstatus.
  destruct phase; cbn [pool_status] in Hstatus.
  - destruct Hstatus as [_ [r [Er Hmodel]]].
    pose proof (proj1 (invariant_fragment_shape _ Hfragment _ _ _ Hmodel)) as Hbuffers.
    unfold resource_memory in Hbuffers; rewrite Er in Hbuffers; exact Hbuffers.
  - destruct Hstatus as [_ ->]; intros; reflexivity.
Qed.

Lemma pool_status_flush active invariant s pool whole phase whole' :
  pool_status active invariant s pool whole phase -> flush active whole whole' ->
  pool_status active invariant s pool whole' phase.
Proof.
  intros Hstatus Hflush; destruct phase; destruct Hstatus as [Hlock Hpool];
    split; [inversion Hflush; exact Hlock |exact Hpool |
            inversion Hflush; exact Hlock |exact Hpool].
Qed.

Theorem owned_environment_flush_attribution active mode invariant s local pool frame whole phase i whole' :
  invariant_fragment invariant ->
  owned_environment active mode invariant s local pool frame whole phase ->
  flush_at active i whole whole' ->
  (exists frame',
    owned_environment active mode invariant s local pool frame' whole' phase /\
    resource_future active frame frame' /\
    flush_at active i (resource_memory active frame) (resource_memory active frame')) \/
  (exists local',
    owned_environment active mode invariant s local' pool frame whole' phase /\
    resource_future active local local' /\
    flush_at active i (resource_memory active local) (resource_memory active local')).
Proof.
  intros Hfragment Henv Hflush.
  pose proof (owned_pool_buffers_empty _ _ _ _ _ _ _ _ _ Hfragment Henv) as Hempty.
  destruct Henv as [Hp Hw [combined [Hinner Houter]] Hmode Hstatus].
  pose proof (flush_at_forget _ _ _ _ Hflush) as Hphysical.
  destruct (pooled_resource_flush_attribution _ _ _ _ _ _ _ _ Hempty Houter Hinner Hflush)
    as [(frame' & combined' & HF & Hfuture & Hmarks & Hinner' & Houter') |
        (local' & combined' & HL & Hfuture & Hmarks & Hinner' & Houter')].
  - left; exists frame'; split.
    + constructor; [exact Hp |eapply flush_preserves_well_formed; eassumption | | |].
      * exists combined'; auto.
      * destruct mode; [exact I |]. intros loc Hf Hl; apply (Hmode loc); [|exact Hl].
        eapply flush_domain_subset; [eapply flush_at_forget; exact HF |exact Hf].
      * eapply pool_status_flush; eassumption.
    + split; [apply generalized_future_one, Hfuture |exact HF].
  - right; exists local'; split.
    + constructor; [exact Hp |eapply flush_preserves_well_formed; eassumption | | |].
      * exists combined'; auto.
      * destruct mode; [exact I |]. intros loc Hf Hl; apply (Hmode loc Hf).
        eapply flush_domain_subset; [eapply flush_at_forget; exact HL |exact Hl].
      * eapply pool_status_flush; eassumption.
    + split; [apply generalized_future_one, Hfuture |exact HL].
Qed.

Lemma owned_empty_frame_flush active mode invariant s local pool frame whole phase whole' :
  invariant_fragment invariant -> empty_atom (proj1_sig frame) ->
  owned_environment active mode invariant s local pool frame whole phase ->
  flush active whole whole' -> exists local',
    owned_environment active mode invariant s local' pool frame whole' phase /\
    resource_future active local local'.
Proof.
  intros Hfragment [_ [Hbuffers _]] Henv Hflush.
  destruct (flush_at_exists _ _ _ Hflush) as [i Hi].
  destruct (owned_environment_flush_attribution _ _ _ _ _ _ _ _ _ _ _ Hfragment Henv Hi)
    as [(frame' & _ & _ & HF) |(local' & Henv' & Hfuture & _)]; [|eauto].
  exfalso; exact (empty_buffer_cannot_flush _ _ _ _ (Hbuffers i) HF).
Qed.

(** Counting every machine step gives a sufficient bound on the number of
    program steps. A flush uses closure and then index weakening, never an
    existential buffer repartition. The empty frame stays exactly fixed. *)
Theorem owned_execution_empty_frame active mode invariant n command s whole last t final :
  invariant_fragment invariant -> execution active n command s whole last t final ->
  forall local pool frame phase post,
  empty_atom (proj1_sig frame) ->
  owned_safe active mode invariant (S n) command s local post ->
  owned_environment active mode invariant s local pool frame whole phase ->
  exists local' pool' phase',
    owned_environment active mode invariant t local' pool' frame final phase' /\
    owned_safe active mode invariant 1 last t local' post.
Proof.
  intros Hfragment Hrun; induction Hrun; intros local pool frame phase post Hempty Hsafe Henv.
  - exists local, pool, phase; auto.
  - destruct (state_step_program_or_flush _ _ _ _ _ _ _ H)
      as [[action Hprogram] |[-> [-> Hflush]]].
    + destruct (owned_safe_program_step _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hsafe Henv Hprogram)
        as (local' & pool' & phase' & Henv' & _ & Hsafe').
      exact (IHHrun local' pool' frame phase' post Hempty Hsafe' Henv').
    + destruct (owned_empty_frame_flush _ _ _ _ _ _ _ _ _ _ Hfragment Hempty Henv Hflush)
        as (local' & Henv' & Hfuture).
      apply (IHHrun local' pool frame phase post Hempty); [|exact Henv'].
      apply owned_safe_weaken_one.
      exact (owned_safe_future _ _ _ _ _ _ _ _ _ Hfuture Hsafe).
Qed.

Lemma owned_empty_frame_intro active mode invariant s local pool whole phase :
  memory_well_formed active pool ->
  memory_spatial pool (resource_memory active local) whole ->
  pool_status active invariant s pool whole phase ->
  owned_environment active mode invariant s local pool (empty_resource_value active) whole phase.
Proof.
  intros Hpool Hsp Hstatus; constructor; [exact Hpool | | | |exact Hstatus].
  - eapply raw_spatial_well_formed; [exact Hpool |exact (proj1 (proj2_sig local)) |exact Hsp].
  - exists local; split; [apply repaired_empty_left |exact Hsp].
  - destruct mode; [exact I |]. intros loc [[v H] |[i [v H]]] _; discriminate || contradiction.
Qed.

Lemma owned_empty_frame_elim active mode invariant s local pool whole phase :
  owned_environment active mode invariant s local pool (empty_resource_value active) whole phase ->
  memory_spatial pool (resource_memory active local) whole /\
  pool_status active invariant s pool whole phase.
Proof.
  intros [_ _ [combined [Hinner Houter]] _ Hstatus]; split; [|exact Hstatus].
  eapply protocol_spatial_equiv_right; [|exact Houter].
  exact (proj1 (repaired_empty_left_unique _ _ _ Hinner)).
Qed.

Lemma owned_final_ownership active invariant s local pool whole phase :
  memory_spatial pool (resource_memory active local) whole ->
  pool_status active invariant s pool whole phase ->
  (lock_free whole /\ persistent_full_satisfies active s pool invariant) \/
  (exists owner, lock_held active (resource_memory active local) owner /\ pool = empty_memory).
Proof.
  intros [_ [_ [_ Hblocks]]] Hstatus; destruct phase; [left; exact Hstatus |].
  destruct Hstatus as [[Hi Hheld] ->]; right; exists owner; split; [|reflexivity].
  split; [exact Hi |]. intros i; specialize (Hblocks i); cbn in Hblocks.
  unfold no_blocked in Hblocks; rewrite <- (Hheld i); tauto.
Qed.

(** Client-facing partial correctness. The two-processor scope is explicit
    here, not a global axiom or a constraint in the resource universe. There
    is no mode-specific disjointness/frame premise. *)
Theorem owned_valid_adequacy active mode invariant pre command post n s whole last t final local pool :
  two_active_processors active -> invariant_fragment invariant ->
  owned_valid active mode invariant pre command post ->
  persistent_models active s local pre ->
  persistent_full_satisfies active s pool invariant -> lock_free whole ->
  memory_spatial pool (resource_memory active local) whole ->
  execution active n command s whole last t final ->
  ~ abort active last (State t final) /\
  (terminal last -> exists local' pool',
    memory_spatial pool' (resource_memory active local') final /\
    persistent_models active t local' post /\
    ((lock_free final /\ persistent_full_satisfies active t pool' invariant) \/
      exists owner, lock_held active (resource_memory active local') owner /\ pool' = empty_memory)).
Proof.
  intros Hdomain Hfragment Hvalid HP HJ Hfree Hsp Hrun.
  assert (Hpool : memory_well_formed active pool).
  { destruct HJ as [r [Er _]]; pose proof (proj1 (proj2_sig r)) as Hwf.
    rewrite Er in Hwf; exact Hwf. }
  assert (Henv : owned_environment active mode invariant s local pool
    (empty_resource_value active) whole PoolFree).
  { apply owned_empty_frame_intro; auto; split; assumption. }
  assert (Hempty : empty_atom (proj1_sig (empty_resource_value active))).
  { split; [intros; reflexivity |]. split; [intros; reflexivity |intros i H; exact H]. }
  destruct (owned_execution_empty_frame _ _ _ _ _ _ _ _ _ _ Hfragment Hrun
      local pool (empty_resource_value active) PoolFree post Hempty (Hvalid _ _ HP _) Henv)
    as (local' & pool' & phase' & Henv' & Hsafe').
  split.
  - eapply owned_safe_no_abort; eassumption.
  - intros Hterminal; exists local', pool'.
    destruct (owned_empty_frame_elim _ _ _ _ _ _ _ _ Henv') as [Hsp' Hstatus].
    split; [exact Hsp' |]. split.
    + eapply owned_safe_terminal; eassumption.
    + eapply owned_final_ownership; eassumption.
Qed.
