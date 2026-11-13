From Stdlib Require Import List ZArith.
From WMLR Require Import Expressions Languages Machine BufferRelations Separation StableCompatibility
  RepairedSeparation GeneralizedFlushing OperationalSemantics Assertions AssertionSemantics ConcreteAssertions
  RepairedAssertions PersistentAssertions Safety OwnershipProtocol TemporalSafety.
Import ListNotations.

(** Keep the region's completeness when transferring its protected payload.
    In contrast to release_returns_invariant, no promotion to full marks is used. *)
Theorem release_marked_invariant active owner s (owned : resource active) invariant :
  lock_held active (resource_memory active owned) owner ->
  persistent_models active s owned (A.Spatial (A.Lock (EVal (Z.pos owner))) invariant) ->
  exists pool : resource active, persistent_models active s pool invariant /\
    lock_free (resource_memory active pool) /\
    memory_equiv (release (resource_memory active owned)) (resource_memory active pool) /\
    (forall i, complete (proj1_sig pool) i <-> complete (proj1_sig owned) i).
Proof.
  intros [Hi Hheld] (token & payload & [[Hd Hmerge] Hmarks] & Htoken & Hpayload).
  change (lock_atom active (Z.pos owner) (proj1_sig token)) in Htoken.
  destruct Htoken as [Hth [Htb [Hactive Htk]]].
  destruct Hmerge as [Hh [Hb Hk]].
  assert (Hfree : lock_free (resource_memory active payload)).
  { intros i Hp. assert (Hout : blocked (resource_memory active owned) i) by (apply Hk; auto).
    apply Hheld in Hout. apply (proj2 Hd i); [apply Htk, Hout |exact Hp]. }
  assert (Hfuture : generalized_future active (proj1_sig payload)
    (Generalized (resource_memory active payload) (complete (proj1_sig owned)))).
  { destruct payload as [[m marks] Hwf]; cbn [proj1_sig resource_memory underlying] in *.
    apply generalized_future_one, GeneralizedMark.
    - intros i Hp; apply (Hmarks i); auto.
    - exact (proj1 (proj2 (proj2_sig owned))). }
  pose (pool := exist _ _ (generalized_future_well_formed _ _ _ Hfuture (proj2_sig payload)) : resource active).
  exists pool; split.
  - eapply persistent_assertion_flushing_closed; [exact Hfuture |exact Hpayload].
  - split; [exact Hfree |]. split; [|intros i; reflexivity].
    split.
    + intros loc; change (shared_heap (resource_memory active owned) loc =
        shared_heap (resource_memory active payload) loc).
      unfold resource_memory; rewrite Hh. unfold heap_override.
      rewrite Hth. destruct (shared_heap (underlying (proj1_sig payload)) loc); reflexivity.
    + split.
      * intros i; specialize (Hb i); rewrite Htb in Hb. apply interleaves_nil_left, Hb.
      * intros i; cbn [release blocked]; split; [contradiction |intros H; exact (Hfree i H)].
Qed.

Definition released_resource active (whole : resource active) : resource active.
Proof.
  refine (exist _ (Generalized (release (resource_memory active whole)) (complete (proj1_sig whole))) _).
  destruct (proj2_sig whole) as [Hwf [Hactive Hheap]]. split.
  - apply release_well_formed, Hwf.
  - split; [exact Hactive |exact Hheap].
Defined.

(** Place temporal history before the combined ownership region. On release
    the region becomes the restored pool, behind the same history; there is
    no spatial-disjointness obligation between the history and that pool.
    This is a transfer lemma, not yet a complete shared/private safety model. *)
Theorem temporal_history_release_transfer active owner s invariant
    (past owned whole : resource active) :
  lock_free (resource_memory active past) -> lock_held active (resource_memory active owned) owner ->
  persistent_models active s owned (A.Spatial (A.Lock (EVal (Z.pos owner))) invariant) ->
  repaired_temporal active (proj1_sig past) (proj1_sig owned) (proj1_sig whole) ->
  buffers (resource_memory active whole) owner = [] ->
  step active (Concurrent.Prim Concurrent.Unlock (EVal (Z.pos owner)))
    (State s (resource_memory active whole)) halt (State s (release (resource_memory active whole))) /\
  exists pool : resource active, persistent_models active s pool invariant /\
    repaired_temporal active (proj1_sig past) (proj1_sig pool)
      (proj1_sig (released_resource active whole)).
Proof.
  intros Hpast Hheld HP [Hstable [Hmemory [Hbefore Hmarks]]] Hdrained.
  destruct (release_marked_invariant _ _ _ _ _ Hheld HP)
    as (pool & HJ & Hfree & [Eh [Eb Ek]] & Hpoolmarks).
  destruct Hmemory as [Hcompat [Hh [Hb Hk]]].
  split.
  - eapply StepPrimitive; [reflexivity |]. apply PrimitiveUnlock;
      [exact (proj1 Hheld) |exact Hdrained |]. split; [exact (proj1 Hheld) |].
    intros i; rewrite Hk. split.
    + intros [H |H]; [exfalso; exact (Hpast i H) |apply (proj2 Hheld i), H].
    + intros H; right; apply (proj2 Hheld i), H.
  - exists pool; split; [exact HJ |].
    assert (Hnewstable : stable_compatible active (resource_memory active past) (resource_memory active pool)).
    { split; [intros i H _; exact (Hpast i H) |]. split.
      - intros i Hi loc Hbuf [v Hv]. apply (proj1 (proj2 Hstable) i Hi loc Hbuf).
        exists v; rewrite <- Eh in Hv; exact Hv.
      - intros i j Hi Hj Hneq loc Hp [v Hv]. apply (proj2 (proj2 Hstable) i j Hi Hj Hneq loc Hp).
        exists v; rewrite <- Eb in Hv; exact Hv. }
    split; [exact Hnewstable |]. split.
    + split; [apply stable_implies_original_compatible, Hnewstable |]. split.
      * intros loc; change (shared_heap (resource_memory active whole) loc =
          heap_override (shared_heap (resource_memory active past)) (shared_heap (resource_memory active pool)) loc).
        unfold heap_override; rewrite <- Eh; exact (Hh loc).
      * split.
        -- intros i; change (buffers (resource_memory active whole) i =
            buffers (resource_memory active past) i ++ buffers (resource_memory active pool) i).
           rewrite <- Eb; exact (Hb i).
        -- intros i; change (False <-> blocked (resource_memory active past) i \/ blocked (resource_memory active pool) i).
           split; [contradiction |intros [H |H]; [exact (Hpast i H) |exact (Hfree i H)]].
    + split.
      * intros i H; apply Hbefore, Hpoolmarks, H.
      * intros i; change (complete (proj1_sig whole) i <->
          complete (proj1_sig past) i \/ complete (proj1_sig pool) i).
        rewrite Hpoolmarks; exact (Hmarks i).
Qed.
