From Stdlib Require Import List ZArith.
From WMLR Require Import Expressions Languages Machine BufferRelations OrderedBuffers Separation
  RepairedSeparation GeneralizedFlushing FrameDecomposition OperationalSemantics ProgramSteps
  Assertions AssertionSemantics ConcreteAssertions PersistentAssertions AssertionResourceEquivalence
  OwnershipProtocol PrivateOwnership SpatialExchange Safety TemporalSafety InvariantFragment
  LockRepresentation OwnedSafety OwnedAdequacy OwnedResources OwnedFraming OwnedShareAdequacy.
Import ListNotations.

Definition spatial_output_resource active (a b : resource active) m
    (Hsp : memory_spatial (resource_memory active a) (resource_memory active b) m) : resource active.
Proof.
  refine (exist _ (Generalized m (fun i => complete (proj1_sig a) i \/ complete (proj1_sig b) i)) _).
  eapply spatial_well_formed; [exact (proj2_sig a) |exact (proj2_sig b) |].
  split; [exact Hsp |intros i; reflexivity].
Defined.

Lemma spatial_output_split active a b m Hsp :
  spatial (proj1_sig a) (proj1_sig b) (proj1_sig (spatial_output_resource active a b m Hsp)).
Proof. split; [exact Hsp |intros i; reflexivity]. Qed.

Lemma empty_memory_spatial_remove pool a whole :
  (forall loc, shared_heap pool loc = None) -> (forall i, buffers pool i = []) ->
  lock_free pool -> memory_spatial pool a whole -> memory_equiv whole a.
Proof.
  intros Hheap Hbuffers Hfree [_ [Eh [Eb Ek]]]; split.
  - intros loc; rewrite Eh; unfold heap_override; rewrite Hheap.
    destruct (shared_heap a loc); reflexivity.
  - split.
    + intros i; specialize (Eb i); rewrite Hbuffers in Eb; apply interleaves_nil_left,Eb.
    + intros i; rewrite Ek; split; [intros [H |H]; [exfalso; exact (Hfree i H) |exact H] |auto].
Qed.

Lemma owned_emp_pool_shape active mode s local pool frame whole phase :
  owned_environment active mode A.Emp s local pool frame whole phase ->
  (forall loc, shared_heap pool loc = None) /\ (forall i, buffers pool i = []) /\ lock_free pool.
Proof.
  intros Henv; pose proof (owned_pool_status _ _ _ _ _ _ _ _ _ Henv) as Hstatus.
  destruct phase; destruct Hstatus as [_ Hpool].
  - destruct Hpool as (r & E & H); change (empty_atom (proj1_sig r)) in H.
    rewrite E in H; exact H.
  - subst pool; split; [intros; reflexivity |].
    split; [intros; reflexivity |intros i H; exact H].
Qed.

Lemma owned_emp_environment_spatial active s local pool frame whole phase :
  owned_environment active DisjointMode A.Emp s local pool frame whole phase ->
  memory_spatial (resource_memory active frame) (resource_memory active local) whole.
Proof.
  intros Henv; destruct (owned_emp_pool_shape _ _ _ _ _ _ _ _ Henv) as [Hh [Hb Hk]].
  destruct (owned_composition _ _ _ _ _ _ _ _ _ Henv) as (combined & [Hinner Hmarks] & Houter).
  pose proof (empty_memory_spatial_remove _ _ _ Hh Hb Hk Houter) as E.
  split.
  - split; [exact (owned_mode _ _ _ _ _ _ _ _ _ Henv) |exact (proj1 (proj1 Hinner))].
  - eapply assertion_merge_equiv; [apply assertion_memory_equiv_refl |apply assertion_memory_equiv_refl
      |apply assertion_memory_equiv_sym,E |].
    exact (repaired_merge_interleaves active _ _ _ Hinner).
Qed.

Lemma spatial_pool_environment active invariant s local pool frame whole phase :
  memory_well_formed active pool ->
  (exists combined, memory_spatial (resource_memory active frame) (resource_memory active local) combined /\
    memory_spatial pool combined whole) ->
  pool_status active invariant s pool whole phase ->
  owned_environment active DisjointMode invariant s local pool frame whole phase.
Proof.
  intros Hpool (combined & Hinner & Houter) Hstatus.
  pose (r := spatial_output_resource active frame local combined Hinner).
  constructor.
  - exact Hpool.
  - eapply raw_spatial_well_formed; [exact Hpool |exact (proj1 (proj2_sig r)) |exact Houter].
  - exists r; split; [apply spatial_in_repaired,spatial_output_split |exact Houter].
  - exact (proj1 (proj1 Hinner)).
  - exact Hstatus.
Qed.

Lemma owned_share_unpool active invariant s (local retained big frame : resource active) whole :
  invariant_fragment invariant -> (exists i, active i) ->
  persistent_models active s retained invariant ->
  spatial (proj1_sig retained) (proj1_sig local) (proj1_sig big) ->
  memory_spatial (resource_memory active frame) (resource_memory active big) whole ->
  lock_free whole ->
  owned_environment active DisjointMode invariant s local (resource_memory active retained) frame whole PoolFree.
Proof.
  intros Hfragment [owner Hi] HJ Hinner Houter Hfree.
  destruct (spatial_exchange _ _ _ _ _ (proj1 Hinner) Houter) as (combined & Hfirst & Hsecond).
  (* Exchange gives P * (J * F); associate and commute to J * (F * P). *)
  destruct (proj2 (memory_spatial_associative (resource_memory active retained)
    (resource_memory active frame) (resource_memory active local) whole)
    (ex_intro _ combined (conj Hfirst (memory_spatial_comm _ _ _ Hsecond))))
    as (joined & Hjoin & Hpool).
  apply spatial_pool_environment; [exact (proj1 (proj2_sig retained)) |eauto |].
  split; [exact Hfree |]. eapply invariant_return_full_completeness; eassumption.
Qed.

Lemma owned_share_repool active invariant s local pool frame whole phase :
  invariant_fragment invariant -> phase = PoolFree ->
  owned_environment active DisjointMode invariant s local pool frame whole phase ->
  forall retained : resource active, resource_memory active retained = pool ->
  exists big : resource active,
    spatial (proj1_sig retained) (proj1_sig local) (proj1_sig big) /\
    memory_spatial (resource_memory active frame) (resource_memory active big) whole.
Proof.
  intros Hfragment -> Henv retained Epool.
  destruct (owned_composition _ _ _ _ _ _ _ _ _ Henv) as (combined & [Hinner Hmarks] & Houter).
  assert (Hsp : memory_spatial (resource_memory active frame) (resource_memory active local)
    (resource_memory active combined)).
  { split; [split; [exact (owned_mode _ _ _ _ _ _ _ _ _ Henv)
      |exact (proj1 (proj1 Hinner))] |exact (repaired_merge_interleaves active _ _ _ Hinner)]. }
  destruct (spatial_exchange _ _ _ _ _ (memory_spatial_comm _ _ _ Hsp) Houter) as (out & Hpo & Hfo).
  apply memory_spatial_comm in Hpo; rewrite <- Epool in Hpo.
  exists (spatial_output_resource active retained local out Hpo); split;
    [apply spatial_output_split |exact Hfo].
Qed.

Lemma empty_pool_spatial_intro pool m :
  (forall loc, shared_heap pool loc = None) -> (forall i, buffers pool i = []) ->
  lock_free pool -> memory_spatial pool m m.
Proof.
  intros Hh Hb Hk; split.
  - split.
    + intros loc [[v H] |[i [v H]]] _; [rewrite Hh in H; discriminate |rewrite Hb in H; contradiction].
    + intros i H _; exact (Hk i H).
  - split.
    + intros loc; unfold heap_override; rewrite Hh; destruct (shared_heap m loc); reflexivity.
    + split; [intros i; rewrite Hb; apply (interleaves_app [] (buffers m i)) |].
      intros i; split; [auto |intros [H |H]; [exfalso; exact (Hk i H) |exact H]].
Qed.

Lemma owned_emp_environment_intro active s local pool frame whole phase :
  memory_well_formed active pool ->
  (forall loc, shared_heap pool loc = None) -> (forall i, buffers pool i = []) ->
  lock_free pool ->
  memory_spatial (resource_memory active frame) (resource_memory active local) whole ->
  pool_status active A.Emp s pool whole phase ->
  owned_environment active DisjointMode A.Emp s local pool frame whole phase.
Proof.
  intros Hwf Hh Hb Hk Hsp Hstatus; apply spatial_pool_environment; [exact Hwf | |exact Hstatus].
  exists whole; split; [exact Hsp |apply empty_pool_spatial_intro; assumption].
Qed.

Lemma owned_environment_held_invariant active mode invariant invariant' s local pool frame whole owner :
  owned_environment active mode invariant s local pool frame whole (PoolHeld owner) ->
  owned_environment active mode invariant' s local pool frame whole (PoolHeld owner).
Proof. intros [Hp Hw Hc Hmode Hstatus]; constructor; assumption. Qed.

Lemma no_free_held active m owner :
  two_active_processors active -> lock_free m -> lock_held active m owner -> False.
Proof. intros (first & second & Hfirst & Hsecond & Hne).
  exact (two_processors_separate_free_held active first second m owner Hfirst Hsecond Hne). Qed.

Lemma source_update_free active action phase phase' local pool local' pool' :
  owned_update active action phase phase' local pool local' pool' ->
  lock_free (resource_memory active local) -> two_active_processors active ->
  match action with
  | AcquireAction owner => lock_held active (resource_memory active local') owner
  | ReleaseAction _ => False
  | _ => lock_free (resource_memory active local')
  end.
Proof.
  intros [Ht _ _] Hfree Htwo; destruct action; cbn [action_transfer] in Ht.
  - destruct Ht as [_ [_ Hb]]; intros i H; apply (Hfree i),Hb,H.
  - destruct Ht as [_ [_ Hb]]; intros i H; apply (Hfree i),Hb,H.
  - exact (proj2 (proj2 (proj2 Ht))).
  - eapply no_free_held; [exact Htwo |exact Hfree |exact (proj1 (proj2 (proj2 Ht)))].
Qed.
