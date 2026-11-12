From Stdlib Require Import List Arith Lia ZArith.
From WMLR Require Import Expressions Languages Machine BufferRelations Separation
  RepairedSeparation GeneralizedFlushing FrameDecomposition OperationalSemantics
  ProgramSteps Assertions AssertionSemantics PersistentAssertions Safety
  TemporalSafety InvariantFragment FlushAttribution LockRepresentation.
Import ListNotations.

(** The single target approved at checkpoint 5. This replaces the separated
    protected/private development path; earlier predicates keep their meanings.
    No processor-domain assumption is built into resources or safety. *)
Definition two_active_processors (active : processor_domain) : Prop :=
  exists first second, active first /\ active second /\ first <> second.

Inductive ownership_mode := OverlapMode | DisjointMode.
Inductive pool_phase := PoolFree | PoolHeld (owner : processor).

Definition mode_compatible active mode (frame local : resource active) : Prop :=
  match mode with
  | OverlapMode => True
  | DisjointMode => disjoint (memory_domain (resource_memory active frame))
      (memory_domain (resource_memory active local))
  end.

Definition pool_status active invariant s pool whole phase : Prop :=
  match phase with
  | PoolFree => lock_free whole /\ persistent_full_satisfies active s pool invariant
  | PoolHeld owner => lock_held active whole owner /\ pool = empty_memory
  end.

(** Held states include local tokens, external tokens, and split blocked
    sets. Only release tests that the complete token is owned locally. *)
Record owned_environment active mode invariant s (local : resource active)
    pool (frame : resource active) whole phase : Prop := {
  owned_pool_wf : memory_well_formed active pool;
  owned_whole_wf : memory_well_formed active whole;
  owned_composition : exists combined : resource active,
    repaired_spatiotemporal active (proj1_sig frame) (proj1_sig local) (proj1_sig combined) /\
    memory_spatial pool (resource_memory active combined) whole;
  owned_mode : mode_compatible active mode frame local;
  owned_pool_status : pool_status active invariant s pool whole phase
}.

Definition action_earns action (i : processor) : Prop :=
  match action with
  | OrdinaryAction => False
  | FenceAction actor | AcquireAction actor | ReleaseAction actor => i = actor
  end.

Definition action_transfer active action phase phase' (local : resource active)
    pool (local' : resource active) pool' : Prop :=
  match action with
  | AcquireAction i => phase = PoolFree /\ phase' = PoolHeld i /\
      pool' = empty_memory /\ lock_held active (resource_memory active local') i
  | ReleaseAction i => phase = PoolHeld i /\ phase' = PoolFree /\
      lock_held active (resource_memory active local) i /\
      lock_free (resource_memory active local')
  | _ => phase' = phase /\ pool' = pool /\
      forall i, blocked (resource_memory active local') i <-> blocked (resource_memory active local) i
  end.

Record owned_update active action phase phase' (local : resource active)
    pool (local' : resource active) pool' : Prop := {
  owned_action_transfer : action_transfer active action phase phase' local pool local' pool';
  owned_footprint : forall loc,
    memory_domain pool' loc \/ memory_domain (resource_memory active local') loc ->
    memory_domain pool loc \/ memory_domain (resource_memory active local) loc;
  owned_mark_budget : forall i, complete (proj1_sig local') i ->
    complete (proj1_sig local) i \/ action_earns action i
}.

(** Frames and pools are quantified afresh at every recursive call. A
    program successor retains the exact input frame, not an arbitrary future.
    Closure quantifies over the existing full generalized-future relation,
    including mark-only steps and locally enabled but externally blocked flushes. *)
Fixpoint owned_safe active mode invariant n command s (local : resource active) post : Prop :=
  match n with
  | O => True
  | S remaining => forall future_local, resource_future active local future_local ->
      (terminal command -> persistent_models active s future_local post) /\
      (forall pool frame whole phase,
        owned_environment active mode invariant s future_local pool frame whole phase ->
        ~ abort active command (State s whole) /\
        (forall action next t whole',
          program_step active action command (State s whole) next (State t whole') ->
          exists local' pool' phase',
            owned_environment active mode invariant t local' pool' frame whole' phase' /\
            owned_update active action phase phase' future_local pool local' pool' /\
            owned_safe active mode invariant remaining next t local' post))
  end.

Definition owned_valid active mode invariant pre command post : Prop :=
  forall s (local : resource active), persistent_models active s local pre ->
    forall n, owned_safe active mode invariant n command s local post.

Theorem owned_safe_future active mode invariant n command s local later post :
  resource_future active local later ->
  owned_safe active mode invariant n command s local post ->
  owned_safe active mode invariant n command s later post.
Proof.
  destruct n; [intros; exact I |].
  intros Hfuture Hsafe last Hlast; apply Hsafe.
  eapply generalized_future_trans; eassumption.
Qed.

Lemma owned_safe_weaken_one active mode invariant n command s local post :
  owned_safe active mode invariant (S n) command s local post ->
  owned_safe active mode invariant n command s local post.
Proof.
  revert command s local; induction n; intros command s local Hsafe; [exact I |].
  intros later Hfuture; destruct (Hsafe later Hfuture) as [Hdone Henvs].
  split; [exact Hdone |]. intros pool frame whole phase Henv.
  destruct (Henvs _ _ _ _ Henv) as [Habort Hstep]; split; [exact Habort |].
  intros action next t whole' Hprogram.
  destruct (Hstep _ _ _ _ Hprogram) as (local' & pool' & phase' & Henv' & Hupdate & Hsafe').
  exists local', pool', phase'; split; [exact Henv' |].
  split; [exact Hupdate |exact (IHn next t local' Hsafe')].
Qed.

Theorem owned_safe_index_mono active mode invariant n m command s local post :
  n <= m -> owned_safe active mode invariant m command s local post ->
  owned_safe active mode invariant n command s local post.
Proof.
  intros Hle; induction Hle; intros Hsafe; [exact Hsafe |].
  apply IHHle, owned_safe_weaken_one, Hsafe.
Qed.

Lemma owned_safe_terminal active mode invariant n command s local post :
  owned_safe active mode invariant (S n) command s local post ->
  terminal command -> persistent_models active s local post.
Proof. intros Hsafe; exact (proj1 (Hsafe local (GeneralizedRefl _ _))). Qed.

Lemma owned_safe_no_abort active mode invariant n command s local post pool frame whole phase :
  owned_safe active mode invariant (S n) command s local post ->
  owned_environment active mode invariant s local pool frame whole phase ->
  ~ abort active command (State s whole).
Proof.
  intros Hsafe Henv; exact (proj1 (proj2 (Hsafe local (GeneralizedRefl _ _)) _ _ _ _ Henv)).
Qed.

Lemma owned_safe_program_step active mode invariant n command s local post pool frame whole phase
    action next t whole' :
  owned_safe active mode invariant (S n) command s local post ->
  owned_environment active mode invariant s local pool frame whole phase ->
  program_step active action command (State s whole) next (State t whole') ->
  exists local' pool' phase',
    owned_environment active mode invariant t local' pool' frame whole' phase' /\
    owned_update active action phase phase' local pool local' pool' /\
    owned_safe active mode invariant n next t local' post.
Proof.
  intros Hsafe Henv; exact (proj2 (proj2 (Hsafe local (GeneralizedRefl _ _)) _ _ _ _ Henv)
    action next t whole').
Qed.

Theorem owned_safe_mark_extension active mode invariant n command s local later post :
  resource_memory active later = resource_memory active local ->
  (forall i, complete (proj1_sig local) i -> complete (proj1_sig later) i) ->
  owned_safe active mode invariant n command s local post ->
  owned_safe active mode invariant n command s later post.
Proof.
  intros Ememory Hmarks Hsafe; apply (owned_safe_future _ _ _ _ _ _ local later post); [|exact Hsafe].
  destruct local as [[before oldmarks] Hbefore], later as [[after newmarks] Hafter].
  cbn in *; unfold resource_memory in Ememory; cbn in Ememory; subst after.
  apply generalized_future_one, GeneralizedMark; [exact Hmarks |exact (proj1 (proj2 Hafter))].
Qed.
