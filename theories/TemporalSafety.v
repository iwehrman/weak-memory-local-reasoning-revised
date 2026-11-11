From Stdlib Require Import List ZArith.
From WMLR Require Import Expressions Languages Machine BufferRelations Separation StableCompatibility
  RepairedSeparation RepairedFlushing GeneralizedFlushing FrameDecomposition OperationalSemantics
  Assertions AssertionSemantics PersistentAssertions Safety RepairedSafety Specifications SpatialExchange.
Import ListNotations.

(** A separate candidate semantics for temporal framing. Local resources and
    external prefixes retain their completeness sets. Shared memory remains
    spatially separated. External composition is temporal here, not the full
    spatiotemporal relation of the dissertation or the private ownership model.
    Existing private/parallel theorems are not silently reinterpreted. *)
Definition resource_memory active (r : resource active) := underlying (proj1_sig r).

Record prefix_environment active (invariant : state_predicate) s
    (local : resource active) shared (frame : resource active) whole : Prop := {
  prefix_shared_wf : memory_well_formed active shared;
  prefix_whole_wf : memory_well_formed active whole;
  prefix_composition : exists combined : resource active,
    repaired_temporal active (proj1_sig frame) (proj1_sig local) (proj1_sig combined) /\
    memory_spatial shared (resource_memory active combined) whole;
  prefix_lock_complete : lock_complete active whole;
  prefix_invariant : invariant s shared \/ locked active whole
}.

Fixpoint prefix_safe active n command s (local : resource active) invariant post : Prop :=
  match n with
  | O => True
  | S remaining =>
    (terminal command -> persistent_models active s local post) /\
    (forall shared frame whole, prefix_environment active invariant s local shared frame whole ->
      ~ abort active command (State s whole)) /\
    (forall shared frame whole next t whole',
      prefix_environment active invariant s local shared frame whole ->
      step active command (State s whole) next (State t whole') ->
      exists local' shared' frame', prefix_environment active invariant t local' shared' frame' whole' /\
        resource_future active frame frame' /\
        ownership_preserved (resource_memory active local) shared (resource_memory active local') shared' /\
        prefix_safe active remaining next t local' invariant post)
  end.

Definition prefix_valid active invariant pre command post : Prop :=
  forall s (local : resource active), persistent_models active s local pre -> forall n,
    prefix_safe active n command s local
      (fun s m => persistent_full_satisfies active s m invariant) post.

Lemma generalized_future_memory_flushes active a b : generalized_future active a b ->
  memory_flushes active (underlying a) (underlying b).
Proof.
  induction 1; [constructor |]. destruct H.
  - exact IHgeneralized_future.
  - econstructor; [eapply flush_at_forget; eassumption |exact IHgeneralized_future].
Qed.

Lemma temporal_memory_domain active a b out : repaired_temporal active a b out ->
  forall loc, memory_domain (underlying out) loc <->
    memory_domain (underlying a) loc \/ memory_domain (underlying b) loc.
Proof.
  intros [_ [[_ [Hh [Hb _]]] _]] loc.
  unfold memory_domain.
  assert (Hheap : heap_domain (shared_heap (underlying out)) loc <->
    heap_domain (heap_override (shared_heap (underlying a)) (shared_heap (underlying b))) loc).
  { unfold heap_domain; setoid_rewrite Hh; reflexivity. }
  rewrite Hheap, heap_override_domain. setoid_rewrite Hb. setoid_rewrite buffer_app_domain. firstorder.
Qed.

Theorem prefix_safe_temporal_frame active n command s local invariant post
    (retained biglocal : resource active) frame_assertion :
  prefix_safe active n command s local invariant post ->
  frame_variable_condition command frame_assertion -> persistent_models active s retained frame_assertion ->
  repaired_temporal active (proj1_sig retained) (proj1_sig local) (proj1_sig biglocal) ->
  prefix_safe active n command s biglocal invariant (A.Temporal frame_assertion post).
Proof.
  revert command s local retained biglocal.
  induction n; intros command s local retained biglocal Hsafe Hvariables HR Hinner; [exact I |].
  destruct Hsafe as [Hdone [Hnoabort Hprogress]]. split.
  - intros Hlast; exists retained, local; split; [exact Hinner |].
    split; [exact HR |apply Hdone, Hlast].
  - split.
    + intros shared external whole [Hs Hw [combined [Houter Hsp]] Hlock Hinv].
      destruct (proj1 (repaired_temporal_resource_associative active external retained local combined)
        (ex_intro _ biglocal (conj Hinner Houter))) as (frame & Hframe & Hsep).
      apply (Hnoabort shared frame whole). constructor; try assumption; exists combined; auto.
    + intros shared external whole next t whole' [Hs Hw [combined [Houter Hsp]] Hlock Hinv] Hstep.
      destruct (proj1 (repaired_temporal_resource_associative active external retained local combined)
        (ex_intro _ biglocal (conj Hinner Houter))) as (frame & Hframe & Hsep).
      assert (Henv : prefix_environment active invariant s local shared frame whole).
      { constructor; try assumption; exists combined; auto. }
      destruct (Hprogress _ _ _ _ _ _ Henv Hstep)
        as (local' & shared' & frame' & Henv' & Hfuture & Howned & Hsafe').
      destruct (resource_temporal_future_split _ _ _ _ _ Hfuture Hframe)
        as (external' & retained' & Hef & Hrf & Hframe').
      destruct Henv' as [Hs' Hw' [combined' [Hsep' Hsp']] Hlock' Hinv'].
      destruct (proj2 (repaired_temporal_resource_associative active external' retained' local' combined')
        (ex_intro _ frame' (conj Hframe' Hsep'))) as (biglocal' & Hinner' & Houter').
      exists biglocal', shared', external'. split.
      * constructor; try assumption; exists combined'; auto.
      * split; [exact Hef |]. split.
        -- destruct Howned as [Hlocal Hshared]. split; intros loc Hloc.
           ++ apply (temporal_memory_domain _ _ _ _ Hinner') in Hloc.
              destruct Hloc as [Hret |Hloc].
              ** left. apply (temporal_memory_domain _ _ _ _ Hinner). left.
                 eapply flushes_domain_subset; [apply generalized_future_memory_flushes; exact Hrf |exact Hret].
              ** destruct (Hlocal _ Hloc) as [Hl |Hs0]; [left |right; exact Hs0].
                 apply (temporal_memory_domain _ _ _ _ Hinner); auto.
           ++ destruct (Hshared _ Hloc) as [Hl |Hs0]; [left |right; exact Hs0].
              apply (temporal_memory_domain _ _ _ _ Hinner); auto.
        -- eapply IHn; [exact Hsafe' | | |exact Hinner'].
           ++ intros x Hwrite Hx. apply (Hvariables x); [eapply step_modifies_subset; eassumption |exact Hx].
           ++ assert (Hagrees : agrees (A.fv frame_assertion) s t).
              { intros x Hx. apply (step_preserves_unmodified _ _ _ _ _ Hstep x).
                intros Hwrite; exact (Hvariables x Hwrite Hx). }
              apply (proj1 (future_satisfies_agrees _ _ frame_assertion s t Hagrees retained')).
              eapply persistent_assertion_flushing_closed; eassumption.
Qed.

Theorem prefix_temporal_frame_valid active invariant pre command post frame_assertion :
  prefix_valid active invariant pre command post -> frame_variable_condition command frame_assertion ->
  prefix_valid active invariant (A.Temporal frame_assertion pre) command (A.Temporal frame_assertion post).
Proof.
  intros Hvalid Hvariables s biglocal [retained [local [Hsep [HR HP]]]] n.
  eapply prefix_safe_temporal_frame; [apply Hvalid; exact HP |exact Hvariables |exact HR |exact Hsep].
Qed.

Lemma resource_actual_flush active (r : resource active) m' :
  flush active (resource_memory active r) m' -> exists r' : resource active,
    resource_memory active r' = m' /\ resource_future active r r'.
Proof.
  intros H. destruct (flush_at_exists _ _ _ H) as [i Hi].
  assert (Hfuture : generalized_future active (proj1_sig r) (Generalized m' active)).
  { destruct r as [[m marks] [Hwf [Hactive Hheap]]]; simpl in *.
    apply generalized_future_one. eapply GeneralizedFlush; [exact Hi |exact Hactive |auto |].
    destruct Hi; assumption. }
  exists (exist _ _ (generalized_future_well_formed _ _ _ Hfuture (proj2_sig r))); auto.
Qed.

Lemma prefix_environment_flush active invariant s local shared frame whole whole' :
  flush_closed active invariant -> prefix_environment active invariant s local shared frame whole ->
  flush active whole whole' -> exists local' shared' frame',
    prefix_environment active invariant s local' shared' frame' whole' /\
    resource_future active local local' /\ resource_future active frame frame' /\
    ownership_preserved (resource_memory active local) shared (resource_memory active local') shared'.
Proof.
  intros Hclosed [Hs Hw [combined [Htm Hsp]] Hlock Hinv] Hflush.
  assert (Hw' : memory_well_formed active whole') by (eapply flush_preserves_well_formed; eassumption).
  assert (Hlock' : lock_complete active whole') by (eapply flush_preserves_lock_complete; eassumption).
  destruct (spatial_flush_split _ _ _ _ _ Hsp Hflush) as [(shared' & Hsflush & Hsp') |(combined' & Hcflush & Hsp')].
  - exists local, shared', frame. split.
    + constructor; try assumption.
      * eapply flush_preserves_well_formed; [exact Hsflush |exact Hs].
      * exists combined; auto.
      * destruct Hinv; [left; eapply Hclosed; [econstructor; [exact Hsflush |constructor] |assumption] |
          right; eapply flush_preserves_locked; eassumption].
    + split; [constructor |]. split; [constructor |]. split; intros loc Hloc; [auto |right].
      exact (flush_domain_subset _ _ _ Hsflush loc Hloc).
  - destruct (resource_actual_flush _ _ _ Hcflush) as (out & Eout & Hfuture).
    destruct (resource_temporal_future_split _ _ _ _ _ Hfuture Htm) as (localframe & local' & Hff & Hlf & Htm').
    exists local', shared, localframe. split.
    + constructor; try assumption.
      * exists out; split; [exact Htm' |rewrite Eout; exact Hsp'].
      * destruct Hinv; [auto |right; eapply flush_preserves_locked; eassumption].
    + split; [exact Hlf |]. split; [exact Hff |]. split; intros loc Hloc; [left |auto].
      eapply flushes_domain_subset; [apply generalized_future_memory_flushes; exact Hlf |exact Hloc].
Qed.

Theorem prefix_skip_safe active invariant n annotation s local post :
  flush_closed active invariant -> persistent_models active s local post ->
  prefix_safe active n (Concurrent.skip annotation) s local invariant post.
Proof.
  intros Hclosed. revert s local. induction n; intros s local HP; [exact I |].
  split; [auto |]. split; [intros; apply skip_no_abort |].
  intros shared frame whole next t whole' Henv Hstep.
  destruct (skip_step_flush _ _ _ _ _ _ _ Hstep) as [-> [-> Hflush]].
  destruct (prefix_environment_flush _ _ _ _ _ _ _ _ Hclosed Henv Hflush)
    as (local' & shared' & frame' & Henv' & Hlf & Hff & Howned).
  exists local', shared', frame'. split; [exact Henv' |]. split; [exact Hff |]. split; [exact Howned |].
  apply IHn. eapply persistent_assertion_flushing_closed; eassumption.
Qed.

Theorem prefix_skip_valid active invariant pre annotation :
  prefix_valid active invariant pre (Concurrent.skip annotation) pre.
Proof.
  intros s local HP n. apply prefix_skip_safe; [|exact HP].
  intros t a b Hfuture HJ; eapply persistent_full_flushing_closed; eassumption.
Qed.

Theorem prefix_execution_residual active n command s whole last t final :
  execution active n command s whole last t final -> forall local shared frame invariant post,
    prefix_safe active (S n) command s local invariant post ->
    prefix_environment active invariant s local shared frame whole ->
    exists local' shared' frame', prefix_environment active invariant t local' shared' frame' final /\
      resource_future active frame frame' /\ prefix_safe active 1 last t local' invariant post.
Proof.
  induction 1; intros local shared frame invariant post Hsafe Henv.
  - exists local, shared, frame; split; [exact Henv |]. split; [constructor |exact Hsafe].
  - destruct Hsafe as [_ [_ Hprogress]].
    destruct (Hprogress _ _ _ _ _ _ Henv H) as (local' & shared' & frame' & Henv' & Hff & _ & Hsafe').
    destruct (IHexecution _ _ _ _ _ Hsafe' Henv') as (lastlocal & lastshared & lastframe & Henvlast & Hfuture & Hsafelast).
    exists lastlocal, lastshared, lastframe; split; [exact Henvlast |]. split; [|exact Hsafelast].
    eapply generalized_future_trans; eassumption.
Qed.

Theorem prefix_execution_no_abort active n command s whole last t final local shared frame invariant post :
  execution active n command s whole last t final ->
  prefix_safe active (S n) command s local invariant post ->
  prefix_environment active invariant s local shared frame whole -> ~ abort active last (State t final).
Proof.
  intros Hrun Hsafe Henv. destruct (prefix_execution_residual _ _ _ _ _ _ _ _ Hrun _ _ _ _ _ Hsafe Henv)
    as (local' & shared' & frame' & Henv' & _ & _ & Hnoabort & _).
  exact (Hnoabort _ _ _ Henv').
Qed.

Theorem prefix_execution_post active n command s whole last t final local shared frame invariant post :
  execution active n command s whole last t final ->
  prefix_safe active (S n) command s local invariant post ->
  prefix_environment active invariant s local shared frame whole -> terminal last ->
  exists local' shared' frame', prefix_environment active invariant t local' shared' frame' final /\
    memory_flushes active (resource_memory active frame) (resource_memory active frame') /\
    persistent_models active t local' post.
Proof.
  intros Hrun Hsafe Henv Hlast. destruct (prefix_execution_residual _ _ _ _ _ _ _ _ Hrun _ _ _ _ _ Hsafe Henv)
    as (local' & shared' & frame' & Henv' & Hfuture & Hpost & _).
  exists local', shared', frame'. split; [exact Henv' |]. split;
    [apply generalized_future_memory_flushes; exact Hfuture |apply Hpost, Hlast].
Qed.
