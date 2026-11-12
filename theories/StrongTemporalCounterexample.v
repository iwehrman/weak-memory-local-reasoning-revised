From Stdlib Require Import List ZArith.
From WMLR Require Import Expressions Languages Machine BufferRelations OrderedBuffers Separation
  StableCompatibility RepairedSeparation GeneralizedFlushing FrameDecomposition
  OperationalSemantics ProgramSteps ExecutionExamples Assertions AssertionSemantics ConcreteAssertions
  RepairedAssertions PersistentAssertions Safety Specifications HeapRules OwnershipProtocol
  OwnershipHeap PrivateOwnership SpatialExchange TemporalSafety TemporalFence TemporalTransfer
  RegionalResources InvariantFragment OwnedSafety OwnedAdequacy OwnedResources OwnedRules
  OwnedAcceptance OwnershipTransfer.
Import ListNotations.

(** FRAME-STM uses conjunction, hence independently existential spatial and
    temporal splits. Donation can preserve the first split and destroy the
    second. All formulas below belong to the existing assertion language. *)

Lemma stm_wand_free_equiv active p : wand_free p ->
  forall s (a b : resource active), generalized_equiv (proj1_sig a) (proj1_sig b) ->
  persistent_models active s a p -> persistent_models active s b p.
Proof.
  induction p; intros Hwf s a b Hequiv Hp;
    pose proof Hequiv as [[Hh [Hb Hk]] Hmarks];
    cbn [wand_free] in Hwf;
    cbn [persistent_models future_satisfies repaired_interpretation] in *; try contradiction.
  - exact Hp.
  - destruct Hwf as [Hwf1 Hwf2]. destruct Hp; [left; eapply IHp1 |right; eapply IHp2]; eauto.
  - destruct Hwf as [Hwf1 Hwf2]. destruct Hp; split; [eapply IHp1 |eapply IHp2]; eauto.
  - destruct Hp as [v Hv]; exists v; exact (IHp Hwf _ a b Hequiv Hv).
  - intros v; exact (IHp Hwf _ a b Hequiv (Hp v)).
  - destruct Hp as [Hheap [Hbuffers Hfree]]; split.
    + intros loc; rewrite <- Hh; apply Hheap.
    + split; [intros i; rewrite <- Hb; apply Hbuffers |intros i H; apply (Hfree i), Hk, H].
  - destruct Hp as [Hempty Hmark]; split.
    + destruct Hempty as [Hheap [Hbuffers Hfree]]; split.
      * intros loc; rewrite <- Hh; apply Hheap.
      * split; [intros i; rewrite <- Hb; apply Hbuffers |intros i H; apply (Hfree i), Hk, H].
    + destruct (eval_expr s processor); try exact I.
      destruct Hmark; [left; assumption |right; apply Hmarks; assumption].
  - destruct (eval_expr s processor); try contradiction.
    destruct Hp as [Hheap [Hbuffers [Hi Hheld]]]; split.
    + intros loc; rewrite <- Hh; apply Hheap.
    + split; [intros i; rewrite <- Hb; apply Hbuffers |].
      split; [exact Hi |intros i; rewrite <- Hk; apply Hheld].
  - destruct (eval_expr s address); try contradiction;
      destruct (eval_expr s processor); try contradiction.
    destruct Hp as [Hi [Hpending |Hflushed]]; split; [exact Hi | |exact Hi |].
    + left; destruct Hpending as [Hheap [Hbuffers Hblocks]]; split.
      * intros loc; rewrite <- Hh; apply Hheap.
      * split; [intros i; rewrite <- Hb; apply Hbuffers |intros i H; apply Hblocks, Hk, H].
    + right; destruct Hflushed as [Hheap [Hbuffers [Hfree Hmark]]]; split.
      * intros loc; rewrite <- Hh; apply Hheap.
      * split; [intros i; rewrite <- Hb; apply Hbuffers |].
        split; [intros i H; apply (Hfree i), Hk, H |apply Hmarks, Hmark].
  - destruct Hp as (x & y & [[Hcompat [Hheap [Hbuffers Hblocks]]] Hunion] & Hx & Hy).
    exists x, y; split; [|auto]. split.
    + split; [exact Hcompat |]. split; [intros loc; rewrite <- Hh; apply Hheap |].
      split; [intros i; rewrite <- Hb; apply Hbuffers |intros i; rewrite <- Hk; apply Hblocks].
    + intros i; rewrite <- Hmarks; apply Hunion.
  - destruct Hp as (x & y & [Hstable [[Hcompat [Hheap [Hbuffers Hblocks]]] [Hbefore Hunion]]] & Hx & Hy).
    exists x, y; split; [|auto]. split; [exact Hstable |]. split.
    + split; [exact Hcompat |]. split; [intros loc; rewrite <- Hh; apply Hheap |].
      split; [intros i; rewrite <- Hb; apply Hbuffers |intros i; rewrite <- Hk; apply Hblocks].
    + split; [exact Hbefore |intros i; rewrite <- Hmarks; apply Hunion].
Qed.

Lemma stm_wand_free_mark_extension active p s (a b : resource active) :
  wand_free p -> memory_equiv (resource_memory active a) (resource_memory active b) ->
  (forall i, complete (proj1_sig a) i -> complete (proj1_sig b) i) ->
  persistent_models active s a p -> persistent_models active s b p.
Proof.
  intros Hwf Hequiv Hmarks HP.
  assert (Hfuture : generalized_future active (proj1_sig a)
    (Generalized (resource_memory active a) (complete (proj1_sig b)))).
  { destruct a as [[m marks] Ha]; cbn in *.
    apply generalized_future_one, GeneralizedMark; [exact Hmarks |exact (proj1 (proj2 (proj2_sig b)))]. }
  pose (marked := exist _ _ (generalized_future_well_formed _ _ _ Hfuture (proj2_sig a)) : resource active).
  apply (stm_wand_free_equiv active p Hwf s marked b).
  - split; [exact Hequiv |intros i; reflexivity].
  - eapply persistent_assertion_flushing_closed; [exact Hfuture |exact HP].
Qed.

Lemma stm_wand_free_barrier_elim active p s (r : resource active) owner :
  wand_free p ->
  persistent_models active s r (A.Temporal p (A.Barrier (EVal (Z.pos owner)))) ->
  persistent_models active s r p.
Proof.
  intros Hwf (a & b & Htm & HP & [Hempty _]).
  destruct (temporal_emp_memory_right _ _ _ _ Hempty Htm) as [Hh [Hb Hk]].
  eapply stm_wand_free_mark_extension; [exact Hwf | | |exact HP].
  - split; [intros loc; symmetry; apply Hh |].
    split; [intros i; symmetry; apply Hb |intros i; symmetry; apply Hk].
  - intros i H; apply (proj2 (proj2 (proj2 Htm)) i); auto.
Qed.

Definition stm_write (loc : location) := A.LeadsTo (EVal (Z.pos loc)) (EVal 2%Z) (EVal 0%Z).
Definition stm_cell := writer_points_to (EVal 3%Z) (EVal 0%Z).
Definition stm_post := A.Or (stm_write 1%positive)
  (A.Temporal (stm_write 1%positive) (stm_write 2%positive)).
Definition stm_pre := A.Spatial (A.Lock (EVal 1%Z)) (A.Spatial stm_cell stm_post).
Definition stm_frame := A.Or (stm_write 2%positive) stm_cell.

Theorem stm_unframed_release_valid :
  owned_valid two_processors DisjointMode stm_cell stm_pre acceptance_release stm_post.
Proof.
  apply owned_unlock_valid; [apply acceptance_two_active |constructor |].
  intros s r H; eapply stm_wand_free_barrier_elim; [|exact H].
  cbn [stm_cell writer_points_to stm_post stm_write wand_free]; tauto.
Qed.

Definition stm_pending (ws : write_buffer) : resource two_processors.
Proof.
  refine (exist _ (Generalized (Memory empty_heap
    (buffer_update empty_buffers 2%positive ws) no_blocked) no_blocked) _).
  split.
  - split; [intros i H; contradiction |]. intros i Hnot.
    cbn; rewrite buffer_update_other; [reflexivity |intros ->; apply Hnot; right; reflexivity].
  - split; [intros i H; contradiction |intros; reflexivity].
Defined.

Definition stm_payload (ws : write_buffer) : resource two_processors.
Proof.
  refine (exist _ (Generalized (Memory (heap_update empty_heap 3%positive 0%Z)
    (buffer_update empty_buffers 2%positive ws) no_blocked) (fun i => i = 1%positive)) _).
  split.
  - split; [intros i H; contradiction |]. intros i Hnot.
    cbn; rewrite buffer_update_other; [reflexivity |intros ->; apply Hnot; right; reflexivity].
  - split; [intros i ->; left; reflexivity |].
    intros Hnone loc; exfalso; exact (Hnone 1%positive eq_refl).
Defined.

Definition stm_holder ws := acquired_resource two_processors (stm_payload ws) 1%positive.
Definition stm_initial := resource_memory two_processors (stm_holder [(1%positive,0%Z);(2%positive,0%Z)]).

Lemma stm_singleton_models s loc :
  persistent_models two_processors s (stm_pending [(loc,0%Z)]) (stm_write loc).
Proof.
  split; [right; reflexivity |left].
  split; [intros; reflexivity |]. split; [intros; reflexivity |intros i H; contradiction].
Qed.

Lemma stm_cell_models s : persistent_models two_processors s (stm_payload []) stm_cell.
Proof.
  eapply writer_points_to_from_shape with (loc := 3%positive) (owner := 1%positive).
  - reflexivity.
  - left; reflexivity.
  - intros; reflexivity.
  - intros i; unfold resource_memory; cbn [stm_payload proj1_sig underlying buffers].
    unfold buffer_update; destruct (Pos.eq_dec i 2%positive); reflexivity.
  - intros i H; exact H.
  - reflexivity.
Qed.

Lemma stm_pending_pair_models s :
  persistent_models two_processors s (stm_pending [(1%positive,0%Z);(2%positive,0%Z)])
    (A.Temporal (stm_write 1%positive) (stm_write 2%positive)).
Proof.
  exists (stm_pending [(1%positive,0%Z)]), (stm_pending [(2%positive,0%Z)]); split.
  - assert (Hstable : stable_compatible two_processors
      (resource_memory two_processors (stm_pending [(1%positive,0%Z)]))
      (resource_memory two_processors (stm_pending [(2%positive,0%Z)]))).
    { split; [intros i H; contradiction |]. split.
      - intros i _ loc _ [v H]; discriminate.
      - intros i j _ _ Hne loc [v Hv] [w Hw].
        unfold resource_memory in Hv, Hw; cbn [stm_pending proj1_sig underlying buffers] in Hv, Hw.
        unfold buffer_update in Hv, Hw.
        destruct (Pos.eq_dec i 2%positive), (Pos.eq_dec j 2%positive); subst; contradiction. }
    split; [exact Hstable |]. split.
    + split; [apply stable_implies_printed_compatible, Hstable |].
      split; [intros; reflexivity |]. split.
      * intros i; cbn [stm_pending proj1_sig underlying buffers].
        unfold buffer_update; destruct (Pos.eq_dec i 2%positive); reflexivity.
      * intros i; cbn; unfold no_blocked; tauto.
    + split; [intros i H; contradiction |intros i; cbn; unfold no_blocked; tauto].
  - split; apply stm_singleton_models.
Qed.

Lemma stm_pending_domain ws loc :
  memory_domain (resource_memory two_processors (stm_pending ws)) loc <->
  exists v, In (loc,v) ws.
Proof.
  split.
  - intros [[v H] |[i [v H]]]; [discriminate |].
    change (In (loc,v) (buffer_update empty_buffers 2%positive ws i)) in H.
    unfold buffer_update in H; destruct (Pos.eq_dec i 2%positive); [eauto |contradiction].
  - intros [v H]; right; exists 2%positive, v; exact H.
Qed.

Lemma stm_payload_domain ws loc :
  memory_domain (resource_memory two_processors (stm_payload ws)) loc <->
  loc = 3%positive \/ exists v, In (loc,v) ws.
Proof.
  split.
  - intros [[v H] |[i [v H]]].
    + change (heap_update empty_heap 3%positive 0%Z loc = Some v) in H.
      unfold heap_update, empty_heap in H; destruct (Pos.eq_dec loc 3%positive); [auto |discriminate].
    + right; apply (stm_pending_domain ws loc); right; exists i, v; exact H.
  - intros [-> |H].
    + left; exists 0%Z; reflexivity.
    + right; destruct H as [v H]; exists 2%positive, v; exact H.
Qed.

Lemma stm_payload_spatial ws : (forall v, ~ In (3%positive,v) ws) ->
  spatial (proj1_sig (stm_payload [])) (proj1_sig (stm_pending ws)) (proj1_sig (stm_payload ws)).
Proof.
  intros Haway; split.
  - split.
    + split.
      * intros loc Hcell Hpending.
        apply stm_payload_domain in Hcell; apply stm_pending_domain in Hpending.
        destruct Hcell as [-> |[v H]]; [destruct Hpending as [v H]; exact (Haway v H) |contradiction].
      * intros i H; contradiction.
    + split; [intros; reflexivity |]. split.
      * intros i; cbn [stm_payload stm_pending proj1_sig underlying buffers].
        unfold buffer_update; destruct (Pos.eq_dec i 2%positive); apply (interleaves_app []).
      * intros i; cbn; unfold no_blocked; tauto.
  - intros i; cbn; unfold no_blocked; tauto.
Qed.

Lemma stm_holder_one_models s :
  persistent_models two_processors s (stm_holder [(1%positive,0%Z)]) stm_pre.
Proof.
  apply acquire_marked_payload; [left; reflexivity |intros i H; exact H |].
  exists (stm_payload []), (stm_pending [(1%positive,0%Z)]); split.
  - apply stm_payload_spatial; intros v [H |H]; [discriminate |contradiction].
  - split; [apply stm_cell_models |left; apply stm_singleton_models].
Qed.

Lemma stm_holder_two_models s :
  persistent_models two_processors s (stm_holder [(1%positive,0%Z);(2%positive,0%Z)]) stm_pre.
Proof.
  apply acquire_marked_payload; [left; reflexivity |intros i H; exact H |].
  exists (stm_payload []), (stm_pending [(1%positive,0%Z);(2%positive,0%Z)]); split.
  - apply stm_payload_spatial; intros v [H |[H |H]]; discriminate || contradiction.
  - split; [apply stm_cell_models |right; apply stm_pending_pair_models].
Qed.

Lemma stm_initial_spatial_split :
  spatial (proj1_sig (stm_pending [(2%positive,0%Z)]))
    (proj1_sig (stm_holder [(1%positive,0%Z)]))
    (proj1_sig (stm_holder [(1%positive,0%Z);(2%positive,0%Z)])).
Proof.
  split.
  - split.
    + split.
      * intros loc Hleft Hright.
        apply stm_pending_domain in Hleft.
        change (memory_domain (resource_memory two_processors (stm_payload [(1%positive,0%Z)])) loc) in Hright.
        apply stm_payload_domain in Hright.
        destruct Hleft as [v [E |H]]; [inversion E; subst |contradiction].
        destruct Hright as [Er |[w [Er |H]]]; discriminate || contradiction.
      * intros i H; contradiction.
    + split.
      * intros loc; cbn [stm_pending stm_holder acquired_resource stm_payload resource_memory proj1_sig underlying acquire shared_heap].
        unfold heap_override, heap_update, empty_heap; destruct (Pos.eq_dec loc 3%positive); reflexivity.
      * split.
        -- intros i; cbn [stm_pending stm_holder acquired_resource stm_payload resource_memory proj1_sig underlying acquire buffers].
           unfold buffer_update; destruct (Pos.eq_dec i 2%positive); [|constructor].
           apply InterleaveRight, InterleaveLeft, InterleaveNil.
        -- intros i; change (blocked_except two_processors 1%positive i <->
             False \/ blocked_except two_processors 1%positive i); tauto.
  - intros i; change (i = 1%positive <-> False \/ i = 1%positive); tauto.
Qed.

Lemma stm_initial_temporal_split :
  repaired_temporal two_processors (proj1_sig (stm_payload []))
    (proj1_sig (stm_holder [(1%positive,0%Z);(2%positive,0%Z)]))
    (proj1_sig (stm_holder [(1%positive,0%Z);(2%positive,0%Z)])).
Proof.
  assert (Hempty : forall i, buffers (resource_memory two_processors (stm_payload [])) i = []).
  { intros i; cbn [resource_memory stm_payload proj1_sig underlying buffers].
    unfold buffer_update; destruct (Pos.eq_dec i 2%positive); reflexivity. }
  assert (Hstable : stable_compatible two_processors
    (resource_memory two_processors (stm_payload []))
    (resource_memory two_processors (stm_holder [(1%positive,0%Z);(2%positive,0%Z)]))).
  { split; [intros i H; contradiction |]. split;
      [intros i _ loc [v H] |intros i j _ _ _ loc [v H]]; rewrite Hempty in H; contradiction. }
  split; [exact Hstable |]. split.
  - split; [apply stable_implies_printed_compatible, Hstable |]. split.
    + intros loc; cbn [stm_payload stm_holder acquired_resource resource_memory proj1_sig underlying acquire shared_heap].
      unfold heap_override, heap_update, empty_heap; destruct (Pos.eq_dec loc 3%positive); reflexivity.
    + split.
      * intros i; change (buffers (resource_memory two_processors
          (stm_holder [(1%positive,0%Z);(2%positive,0%Z)])) i =
          buffers (resource_memory two_processors (stm_payload [])) i ++
          buffers (resource_memory two_processors (stm_holder [(1%positive,0%Z);(2%positive,0%Z)])) i).
        rewrite Hempty; reflexivity.
      * intros i; change (blocked_except two_processors 1%positive i <->
          False \/ blocked_except two_processors 1%positive i); tauto.
  - split; [intros i _; apply Hempty |].
    intros i; change (i = 1%positive <-> i = 1%positive \/ i = 1%positive); tauto.
Qed.

Theorem stm_framed_precondition s :
  persistent_models two_processors s (stm_holder [(1%positive,0%Z);(2%positive,0%Z)])
    (A.strong_temporal stm_frame stm_pre).
Proof.
  split.
  - exists (stm_pending [(2%positive,0%Z)]), (stm_holder [(1%positive,0%Z)]).
    split; [apply stm_initial_spatial_split |].
    split; [left; apply stm_singleton_models |apply stm_holder_one_models].
  - exists (stm_payload []), (stm_holder [(1%positive,0%Z);(2%positive,0%Z)]).
    split; [apply stm_initial_temporal_split |].
    split; [right; apply stm_cell_models |apply stm_holder_two_models].
Qed.

Lemma stm_initial_environment s :
  owned_environment two_processors DisjointMode stm_cell s
    (stm_holder [(1%positive,0%Z);(2%positive,0%Z)]) empty_memory
    (empty_resource_value two_processors) stm_initial (PoolHeld 1%positive).
Proof.
  apply owned_empty_frame_intro.
  - exact (proj1 (empty_generalized_well_formed two_processors)).
  - exact (proj1 (spatial_empty_left (proj1_sig (stm_holder [(1%positive,0%Z);(2%positive,0%Z)])))).
  - split; [split; [left; reflexivity |intros i; reflexivity] |reflexivity].
Qed.

Lemma stm_release_step s :
  program_step two_processors (ReleaseAction 1%positive) acceptance_release
    (State s stm_initial) halt (State s (release stm_initial)).
Proof.
  eapply ProgramPrimitive with (p := C.Unlock) (i := 1%positive); [reflexivity |].
  apply PrimitiveUnlock; [left; reflexivity |reflexivity |].
  split; [left; reflexivity |intros i; reflexivity].
Qed.

Lemma stm_temporal_post_impossible s (local : resource two_processors) post :
  (forall loc, shared_heap (resource_memory two_processors local) loc = None) ->
  buffers (resource_memory two_processors local) 2%positive = [(1%positive,0%Z);(2%positive,0%Z)] ->
  ~ persistent_models two_processors s local (A.Temporal stm_frame post).
Proof.
  intros Hempty Hbuffer (past & future & [_ [[_ [Hheap [Hbuffers _]]] _]] & HR & _).
  assert (Hpastempty : forall loc, shared_heap (resource_memory two_processors past) loc = None).
  { intros loc; specialize (Hheap loc).
    change (shared_heap (resource_memory two_processors local) loc =
      heap_override (shared_heap (resource_memory two_processors past))
        (shared_heap (resource_memory two_processors future)) loc) in Hheap.
    rewrite Hempty in Hheap; unfold heap_override in Hheap.
    destruct (shared_heap (resource_memory two_processors future) loc); congruence. }
  destruct HR as [[_ [Hpending |Hflushed]] |Hcell].
  - destruct Hpending as [_ [Hpending _]].
    specialize (Hbuffers 2%positive).
    change (buffers (resource_memory two_processors local) 2%positive =
      buffers (resource_memory two_processors past) 2%positive ++
      buffers (resource_memory two_processors future) 2%positive) in Hbuffers.
    rewrite Hbuffer, Hpending in Hbuffers; cbn in Hbuffers; discriminate.
  - destruct Hflushed as [Hflushedheap _]. specialize (Hflushedheap 2%positive).
    rewrite Hpastempty in Hflushedheap; discriminate.
  - destruct (writer_points_to_shape _ _ _ _ _ Hcell)
      as (loc & owner & _ & _ & Hcellheap & _).
    specialize (Hcellheap loc); rewrite Hpastempty, heap_update_same in Hcellheap; discriminate.
Qed.

Lemma stm_returned_local_shape s local pool :
  memory_spatial pool (resource_memory two_processors local) (release stm_initial) ->
  persistent_full_satisfies two_processors s pool stm_cell ->
  (forall loc, shared_heap (resource_memory two_processors local) loc = None) /\
  buffers (resource_memory two_processors local) 2%positive = [(1%positive,0%Z);(2%positive,0%Z)].
Proof.
  intros [[Hdomains _] [Hheap [Hbuffers _]]] (returned & Ereturned & HJ).
  destruct (writer_points_to_shape _ _ _ _ _ HJ)
    as (address & owner & Eaddress & _ & Hreturnedheap & Hreturnedbuffers & _).
  cbn in Eaddress; injection Eaddress as Eaddress; subst address.
  unfold resource_memory in Hreturnedheap, Hreturnedbuffers; rewrite Ereturned in Hreturnedheap, Hreturnedbuffers.
  cbn [underlying] in Hreturnedheap, Hreturnedbuffers.
  split.
  - intros loc; destruct (shared_heap (resource_memory two_processors local) loc) eqn:E; [|reflexivity].
    exfalso.
    assert (Eloc : loc = 3%positive).
    { specialize (Hheap loc); unfold heap_override in Hheap; rewrite E in Hheap.
      change (heap_update empty_heap 3%positive 0%Z loc = Some v) in Hheap.
      unfold heap_update, empty_heap in Hheap; destruct (Pos.eq_dec loc 3%positive); [assumption |discriminate]. }
    subst loc; apply (Hdomains 3%positive).
    + left; exists 0%Z; rewrite Hreturnedheap; reflexivity.
    + left; exists v; exact E.
  - specialize (Hbuffers 2%positive); rewrite Hreturnedbuffers in Hbuffers.
    symmetry; apply interleaves_nil_left, Hbuffers.
Qed.

Theorem owned_disjoint_strong_temporal_frame_invalid :
  ~ owned_valid two_processors DisjointMode stm_cell (A.strong_temporal stm_frame stm_pre)
    acceptance_release (A.strong_temporal stm_frame stm_post).
Proof.
  intros Hvalid.
  pose proof (Hvalid initial_registers (stm_holder [(1%positive,0%Z);(2%positive,0%Z)])
    (stm_framed_precondition _) 2) as Hsafe.
  destruct (owned_safe_program_step _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    Hsafe (stm_initial_environment _) (stm_release_step _))
    as (local' & pool' & phase' & Henv' & Hupdate & Hsafe').
  destruct (owned_action_transfer _ _ _ _ _ _ _ _ Hupdate) as [_ [-> _]].
  destruct (owned_empty_frame_elim _ _ _ _ _ _ _ _ Henv') as [Hsp [_ HJ]].
  destruct (stm_returned_local_shape _ _ _ Hsp HJ) as [Hheap Hbuffers].
  pose proof (owned_safe_terminal _ _ _ _ _ _ _ _ Hsafe' ltac:(eexists; reflexivity)) as [_ Htemporal].
  exact (stm_temporal_post_impossible _ _ _ Hheap Hbuffers Htemporal).
Qed.

Theorem owned_strong_temporal_counterexample :
  two_active_processors two_processors /\ invariant_fragment stm_cell /\
  frame_variable_condition acceptance_release stm_frame /\
  owned_valid two_processors DisjointMode stm_cell stm_pre acceptance_release stm_post /\
  ~ owned_valid two_processors DisjointMode stm_cell (A.strong_temporal stm_frame stm_pre)
    acceptance_release (A.strong_temporal stm_frame stm_post).
Proof.
  split; [apply acceptance_two_active |]. split; [constructor |].
  split; [intros x H; contradiction |].
  split; [apply stm_unframed_release_valid |apply owned_disjoint_strong_temporal_frame_invalid].
Qed.
