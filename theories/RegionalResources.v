From Stdlib Require Import List ZArith.
From WMLR Require Import Expressions Languages Machine BufferRelations Separation StableCompatibility
  RepairedSeparation GeneralizedFlushing FrameDecomposition OperationalSemantics Assertions AssertionSemantics
  ConcreteAssertions PersistentAssertions Safety OwnershipProtocol OwnershipHeap TemporalSafety TemporalTransfer.
Import ListNotations.

Definition bare_resource active : resource active :=
  exist _ empty_generalized (empty_generalized_well_formed active).

Definition acquired_resource active (r : resource active) (owner : processor) : resource active.
Proof.
  refine (exist _ (Generalized (acquire active (resource_memory active r) owner) (complete (proj1_sig r))) _).
  destruct (proj2_sig r) as [Hwf [Hactive Hheap]]. split.
  - apply acquire_well_formed, Hwf.
  - split; [exact Hactive |exact Hheap].
Defined.

Lemma bare_resource_models active s : persistent_models active s (bare_resource active) A.Emp.
Proof. split; [intros; reflexivity |]. split; [intros; reflexivity |intros i H; contradiction]. Qed.

Lemma repaired_temporal_bare_left active (r : resource active) :
  repaired_temporal active (proj1_sig (bare_resource active)) (proj1_sig r) (proj1_sig r).
Proof.
  split; [|apply temporal_empty_left]. split; [intros i H; contradiction |]. split;
    [intros i _ loc [v H]; contradiction |intros i j _ _ _ loc [v H]; contradiction].
Qed.

Lemma repaired_temporal_bare_right active (r : resource active) :
  repaired_temporal active (proj1_sig r) (proj1_sig (bare_resource active)) (proj1_sig r).
Proof.
  split; [|apply temporal_empty_right]. split; [intros i _ H; contradiction |]. split;
    [intros i _ loc _ [v H]; discriminate |intros i j _ _ _ loc _ [v H]; contradiction].
Qed.

Lemma temporal_emp_right_intro active s (r : resource active) p : persistent_models active s r p ->
  persistent_models active s r (A.Temporal p A.Emp).
Proof.
  intros H; exists r, (bare_resource active); split; [apply repaired_temporal_bare_right |].
  split; [exact H |apply bare_resource_models].
Qed.

Lemma memory_flushes_blocks active a b : memory_flushes active a b ->
  forall i, blocked a i <-> blocked b i.
Proof.
  induction 1; intros i; [reflexivity |]. rewrite <- IHmemory_flushes. destruct H; reflexivity.
Qed.

Lemma resource_future_blocks active (a b : resource active) : resource_future active a b ->
  forall i, blocked (resource_memory active a) i <-> blocked (resource_memory active b) i.
Proof. intros H; apply (memory_flushes_blocks active), generalized_future_memory_flushes, H. Qed.

Lemma acquire_marked_payload active owner s (payload : resource active) p : active owner ->
  lock_free (resource_memory active payload) -> persistent_models active s payload p ->
  persistent_models active s (acquired_resource active payload owner) (owned_assertion owner p).
Proof.
  intros Hi Hfree Hp.
  exists (acquired_resource active (bare_resource active) owner), payload. split.
  - split.
    + split.
      * split.
        -- intros loc [[v Hv] |[i [v Hv]]] _; discriminate || contradiction.
        -- intros i _ H; exact (Hfree i H).
      * split.
        -- intros loc; change (shared_heap (resource_memory active payload) loc =
             heap_override empty_heap (shared_heap (resource_memory active payload)) loc).
           unfold heap_override; destruct (shared_heap (resource_memory active payload) loc); reflexivity.
        -- split.
           ++ intros i; exact (interleaves_app [] (buffers (resource_memory active payload) i)).
           ++ intros i; change (blocked_except active owner i <-> blocked_except active owner i \/
                blocked (resource_memory active payload) i).
              split; [auto |intros [H |H]; [exact H |exfalso; exact (Hfree i H)]].
    + intros i; change (complete (proj1_sig payload) i <-> False \/ complete (proj1_sig payload) i); tauto.
  - split; [|exact Hp]. split; [intros; reflexivity |]. split; [intros; reflexivity |].
    split; [exact Hi |intros i; reflexivity].
Qed.

Lemma temporal_acquire_recompose active owner (past region whole : resource active) :
  lock_free (resource_memory active past) ->
  repaired_temporal active (proj1_sig past) (proj1_sig region) (proj1_sig whole) ->
  repaired_temporal active (proj1_sig past) (proj1_sig (acquired_resource active region owner))
    (proj1_sig (acquired_resource active whole owner)).
Proof.
  intros Hfree [[Hblocks [Hheap Hbuffers]] [[Hcompatible [Hh [Hb Hk]]] [Hbefore Hmarks]]].
  assert (Hs : stable_compatible active (resource_memory active past)
    (resource_memory active (acquired_resource active region owner))).
  { split; [intros i H _; exact (Hfree i H) |]. split; assumption. }
  split; [exact Hs |]. split.
  - split; [apply stable_implies_printed_compatible, Hs |]. split; [exact Hh |]. split; [exact Hb |].
    intros i; change (blocked_except active owner i <-> blocked (resource_memory active past) i \/ blocked_except active owner i).
    split; [auto |intros [H |H]; [exfalso; exact (Hfree i H) |exact H]].
  - split; assumption.
Qed.

Lemma temporal_release_recompose active (past owned pool whole : resource active) :
  lock_free (resource_memory active past) ->
  memory_equiv (release (resource_memory active owned)) (resource_memory active pool) ->
  (forall i, complete (proj1_sig pool) i <-> complete (proj1_sig owned) i) ->
  repaired_temporal active (proj1_sig past) (proj1_sig owned) (proj1_sig whole) ->
  repaired_temporal active (proj1_sig past) (proj1_sig pool) (proj1_sig (released_resource active whole)).
Proof.
  intros Hfree [Eh [Eb Ek]] Hpoolmarks [Hstable [[Hcompatible [Hh [Hb Hk]]] [Hbefore Hmarks]]].
  assert (Hpoolfree : lock_free (resource_memory active pool)).
  { intros i H; apply (proj2 (Ek i)), H. }
  assert (Hs : stable_compatible active (resource_memory active past) (resource_memory active pool)).
  { split; [intros i H _; exact (Hfree i H) |]. split.
    - intros i Hi loc Hbuf [v Hv]. apply (proj1 (proj2 Hstable) i Hi loc Hbuf).
      exists v; rewrite <- Eh in Hv; exact Hv.
    - intros i j Hi Hj Hneq loc Hp [v Hv]. apply (proj2 (proj2 Hstable) i j Hi Hj Hneq loc Hp).
      exists v; rewrite <- Eb in Hv; exact Hv. }
  split; [exact Hs |]. split.
  - split; [apply stable_implies_printed_compatible, Hs |]. split.
    + intros loc; change (shared_heap (resource_memory active whole) loc =
        heap_override (shared_heap (resource_memory active past)) (shared_heap (resource_memory active pool)) loc).
      unfold heap_override; rewrite <- Eh; exact (Hh loc).
    + split.
      * intros i; change (buffers (resource_memory active whole) i =
          buffers (resource_memory active past) i ++ buffers (resource_memory active pool) i).
        rewrite <- Eb; exact (Hb i).
      * intros i; change (False <-> blocked (resource_memory active past) i \/ blocked (resource_memory active pool) i).
        split; [contradiction |intros [H |H]; [exact (Hfree i H) |exact (Hpoolfree i H)]].
  - split.
    + intros i H; apply Hbefore, Hpoolmarks, H.
    + intros i; change (complete (proj1_sig whole) i <-> complete (proj1_sig past) i \/ complete (proj1_sig pool) i).
      rewrite Hpoolmarks; exact (Hmarks i).
Qed.

(** Shared/private resources are generalized throughout. The temporal history
    is outside this region, not spatially disjoint from its shared pool. *)
Definition marked_region active owner invariant phase s (local region : resource active) : Prop :=
  match phase with
  | Closed => lock_free (resource_memory active region) /\ exists pool : resource active,
      persistent_models active s pool invariant /\ spatial (proj1_sig pool) (proj1_sig local) (proj1_sig region)
  | Open => local = region /\ lock_held active (resource_memory active region) owner
  end.

Theorem marked_region_future active owner invariant phase s local region region' :
  marked_region active owner invariant phase s local region -> resource_future active region region' ->
  exists local', marked_region active owner invariant phase s local' region' /\ resource_future active local local'.
Proof.
  destruct phase; intros Hregion Hfuture.
  - destruct Hregion as [Hfree [pool [HJ Hsp]]].
    destruct (resource_spatial_future_split _ _ _ _ _ Hfuture Hsp) as (pool' & local' & Hpf & Hlf & Hsp').
    exists local'; split; [|exact Hlf]. split.
    + intros i H; apply (Hfree i), (resource_future_blocks _ _ _ Hfuture i), H.
    + exists pool'; split; [eapply persistent_assertion_flushing_closed; eassumption |exact Hsp'].
  - destruct Hregion as [-> [Hi Hheld]]. exists region'; split; [|exact Hfuture].
    split; [reflexivity |]. split; [exact Hi |]. intros i; rewrite <- (resource_future_blocks _ _ _ Hfuture i); apply Hheld.
Qed.

Record regional_environment active owner invariant phase s
    (local region history : resource active) whole : Prop := {
  regional_region_ok : marked_region active owner invariant phase s local region;
  regional_history_free : lock_free (resource_memory active history);
  regional_composition : exists combined : resource active,
    resource_memory active combined = whole /\
    repaired_temporal active (proj1_sig history) (proj1_sig region) (proj1_sig combined)
}.

Lemma regional_empty_history active owner invariant phase s local region :
  marked_region active owner invariant phase s local region ->
  regional_environment active owner invariant phase s local region (bare_resource active) (resource_memory active region).
Proof.
  intros H; constructor; [exact H |intros i H0; contradiction |].
  exists region; split; [reflexivity |apply repaired_temporal_bare_left].
Qed.

Theorem regional_environment_flush active owner invariant phase s local region history whole whole' :
  regional_environment active owner invariant phase s local region history whole -> flush active whole whole' ->
  exists local' region' history', regional_environment active owner invariant phase s local' region' history' whole' /\
    resource_future active local local' /\ resource_future active history history' /\
    domain_included (resource_memory active region') (resource_memory active region).
Proof.
  intros [Hregion Hfree [combined [E Htm]]] Hflush.
  rewrite <- E in Hflush. destruct (resource_actual_flush _ _ _ Hflush) as (out & Eout & Hfuture).
  destruct (resource_temporal_future_split _ _ _ _ _ Hfuture Htm) as (history' & region' & Hhf & Hrf & Htm').
  destruct (marked_region_future _ _ _ _ _ _ _ _ Hregion Hrf) as (local' & Hregion' & Hlf).
  exists local', region', history'; split.
  - constructor; [exact Hregion' | |exists out; auto].
    intros i H; apply (Hfree i), (resource_future_blocks _ _ _ Hhf i), H.
  - split; [exact Hlf |]. split; [exact Hhf |].
    eapply flushes_domain_subset; apply generalized_future_memory_flushes, Hrf.
Qed.
