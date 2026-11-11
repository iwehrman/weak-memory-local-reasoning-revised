From Stdlib Require Import List ZArith.
From WMLR Require Import Expressions Languages Machine BufferRelations OrderedBuffers
  Separation StableCompatibility RepairedSeparation GeneralizedFlushing
  FrameDecomposition OperationalSemantics ExecutionExamples TemporalSafety
  Assertions AssertionSemantics PersistentAssertions HeapRules InvariantFragment.
Import ListNotations.

Module FrameShapeCounterexample.

Definition xwrite : location * value := (1%positive, 0%Z).
Definition ywrite : location * value := (2%positive, 0%Z).
Definition one_buffer ws := buffer_update empty_buffers 1%positive ws.
Definition xheap : heap := heap_update empty_heap 1%positive 0%Z.
Definition first_mark : processor -> Prop := fun i => i = 1%positive.

Definition buffered_resource (has_heap : bool) (ws : write_buffer) : resource two_processors.
Proof.
  refine (exist _ (Generalized
    (Memory (if has_heap then xheap else empty_heap) (one_buffer ws) no_blocked)
    (if has_heap then first_mark else no_blocked)) _).
  split.
  - split; [intros i H; contradiction |]. intros i Hinactive.
    unfold one_buffer; cbn [underlying buffers]; rewrite buffer_update_other; [reflexivity |].
    intros ->; apply Hinactive; left; reflexivity.
  - destruct has_heap; split.
    + intros i H; left; exact H.
    + intros Hnone loc; exfalso; apply (Hnone 1%positive); reflexivity.
    + intros i H; contradiction.
    + intros; reflexivity.
Defined.

Definition frame := buffered_resource true [xwrite].
Definition retained := buffered_resource false [ywrite].
Definition local := buffered_resource false [xwrite].
Definition framed_local := buffered_resource false [ywrite; xwrite].
Definition grouped := buffered_resource true [xwrite; ywrite].
Definition whole := buffered_resource true [xwrite; ywrite; xwrite].
Definition local_after := buffered_resource false [xwrite; xwrite].

(** The abstract frame can flush its first x-write while the whole machine
    takes an assume-true step. The alternative local residual then absorbs
    the still-pending occurrence of that write. *)
Definition grouped_after_raw := Generalized
  (flush_write (resource_memory two_processors grouped) 1%positive 1%positive 0%Z [ywrite]) first_mark.

Lemma grouped_flush_step : generalized_step two_processors (proj1_sig grouped) grouped_after_raw.
Proof.
  apply GeneralizedFlush with (i := 1%positive).
  - constructor; [left; reflexivity |intros H; contradiction |apply buffer_update_same].
  - intros i H; exact H.
  - intros i H; left; exact H.
  - reflexivity.
Qed.

Definition grouped_after : resource two_processors := exist _ grouped_after_raw
  (generalized_step_well_formed _ _ _ grouped_flush_step (proj2_sig grouped)).

Lemma grouped_future : resource_future two_processors grouped grouped_after.
Proof. apply generalized_future_one, grouped_flush_step. Qed.

Lemma single_buffer_stable active h k a b blocks :
  (forall loc v, In (loc,v) a -> k loc = None) ->
  stable_compatible active (Memory h (one_buffer a) no_blocked) (Memory k (one_buffer b) blocks).
Proof.
  intros Hfresh; split; [intros i H; contradiction |]. split.
  - intros i _ loc [v Hv] [w Hw].
    change (In (loc,v) (one_buffer a i)) in Hv.
    unfold one_buffer, buffer_update in Hv.
    destruct (Pos.eq_dec i 1%positive); [|contradiction].
    change (k loc = Some w) in Hw; rewrite (Hfresh loc v Hv) in Hw; discriminate.
  - intros i j _ _ Hneq loc [v Hv] [w Hw].
    change (In (loc,v) (one_buffer a i)) in Hv.
    change (In (loc,w) (one_buffer b j)) in Hw.
    unfold one_buffer, buffer_update in Hv, Hw.
    destruct (Pos.eq_dec i 1%positive); [|contradiction].
    destruct (Pos.eq_dec j 1%positive); [congruence |contradiction].
Qed.

Lemma single_buffer_override active h k outheap a b outbuffer blocks leftmarks rightmarks outmarks :
  (forall loc v, In (loc,v) a -> k loc = None) ->
  ordered_overrides a b outbuffer ->
  (forall loc, outheap loc = heap_override h k loc) ->
  (forall i, outmarks i <-> leftmarks i \/ rightmarks i) ->
  repaired_spatiotemporal active
    (Generalized (Memory h (one_buffer a) no_blocked) leftmarks)
    (Generalized (Memory k (one_buffer b) blocks) rightmarks)
    (Generalized (Memory outheap (one_buffer outbuffer) blocks) outmarks).
Proof.
  intros Hfresh Hbuffer Hheap Hmarks; split; [|exact Hmarks]. split.
  - apply single_buffer_stable, Hfresh.
  - split; [exact Hheap |]. split.
    + intros i; change (ordered_overrides (one_buffer a i) (one_buffer b i) (one_buffer outbuffer i)).
      unfold one_buffer, buffer_update.
      destruct (Pos.eq_dec i 1%positive); [exact Hbuffer |constructor].
    + intros i; cbn [underlying blocked]; unfold no_blocked; tauto.
Qed.

Lemma bare_buffer_temporal a b :
  repaired_temporal two_processors (proj1_sig (buffered_resource false a))
    (proj1_sig (buffered_resource false b)) (proj1_sig (buffered_resource false (a ++ b))).
Proof.
  assert (Hstable : stable_compatible two_processors
    (resource_memory two_processors (buffered_resource false a))
    (resource_memory two_processors (buffered_resource false b))).
  { apply single_buffer_stable; intros; reflexivity. }
  split; [exact Hstable |]. split.
  - split; [apply stable_implies_printed_compatible, Hstable |].
    split; [intros; reflexivity |]. split.
    + intros i; change (one_buffer (a ++ b) i = one_buffer a i ++ one_buffer b i).
      unfold one_buffer, buffer_update; destruct (Pos.eq_dec i 1%positive); reflexivity.
    + intros i; change (False <-> False \/ False); tauto.
  - split; [intros i H; contradiction |intros i; change (False <-> False \/ False); tauto].
Qed.

Lemma initial_temporal : repaired_temporal two_processors
  (proj1_sig retained) (proj1_sig local) (proj1_sig framed_local).
Proof. exact (bare_buffer_temporal [ywrite] [xwrite]). Qed.

Lemma initial_outer : repaired_spatiotemporal two_processors
  (proj1_sig frame) (proj1_sig framed_local) (proj1_sig whole).
Proof.
  apply single_buffer_override; [intros; reflexivity |apply ordered_append |intros; reflexivity |].
  intros i; change (i = 1%positive <-> i = 1%positive \/ False); tauto.
Qed.

Lemma initial_group : repaired_spatiotemporal two_processors
  (proj1_sig frame) (proj1_sig retained) (proj1_sig grouped).
Proof.
  apply single_buffer_override; [intros; reflexivity |apply ordered_append |intros; reflexivity |].
  intros i; change (i = 1%positive <-> i = 1%positive \/ False); tauto.
Qed.

Lemma initial_small : repaired_spatiotemporal two_processors
  (proj1_sig grouped) (proj1_sig local) (proj1_sig whole).
Proof.
  apply single_buffer_override; [intros; reflexivity |apply ordered_append |intros; reflexivity |].
  intros i; change (i = 1%positive <-> i = 1%positive \/ False); tauto.
Qed.

Lemma after_small : repaired_spatiotemporal two_processors
  (proj1_sig grouped_after) (proj1_sig local_after) (proj1_sig whole).
Proof.
  split.
  - split.
    + change (stable_compatible two_processors
        (Memory (heap_update xheap 1%positive 0%Z)
          (buffer_update (one_buffer [xwrite; ywrite]) 1%positive [ywrite]) no_blocked)
        (Memory empty_heap (one_buffer [xwrite; xwrite]) no_blocked)).
      split; [intros i H; contradiction |]. split.
      * intros i _ loc _ [v H]; discriminate.
      * intros i j _ _ Hneq loc [v Hv] [w Hw].
        cbn [buffers] in Hv, Hw; unfold one_buffer, buffer_update in Hv, Hw.
        destruct (Pos.eq_dec i 1%positive); [|contradiction].
        destruct (Pos.eq_dec j 1%positive); [congruence |contradiction].
    + split.
      * intros loc; change (xheap loc = heap_override (heap_update xheap 1%positive 0%Z) empty_heap loc).
        unfold heap_override, empty_heap, xheap, heap_update; destruct (Pos.eq_dec loc 1%positive); reflexivity.
      * split.
        -- intros i; change (ordered_overrides
             (buffer_update (one_buffer [xwrite; ywrite]) 1%positive [ywrite] i)
             (one_buffer [xwrite; xwrite] i) (one_buffer [xwrite; ywrite; xwrite] i)).
           unfold one_buffer, buffer_update; destruct (Pos.eq_dec i 1%positive); [|constructor].
           apply OrderedRight; [intros [v [H |H]]; [discriminate |contradiction] |].
           apply OrderedLeft, OrderedRight; [intros [v H]; contradiction |constructor].
        -- intros i; change (False <-> False \/ False); tauto.
  - intros i; change (i = 1%positive <-> i = 1%positive \/ False); tauto.
Qed.

Lemma frame_excludes_y : ~ memory_domain (resource_memory two_processors frame) 2%positive.
Proof.
  intros [[v Hv] |[i [v Hv]]]; [discriminate |].
  change (In (2%positive,v) (one_buffer [xwrite] i)) in Hv.
  unfold one_buffer, buffer_update in Hv; destruct (Pos.eq_dec i 1%positive); [|contradiction].
  destruct Hv as [H |H]; [discriminate |contradiction].
Qed.

(** Stronger than the failed claim: no reconstruction exists even without
    requiring that the retained component be a future of [retained]. *)
Theorem no_reconstruction (suffix result : resource two_processors) :
  (exists tail, buffers (resource_memory two_processors result) 1%positive = xwrite :: tail) ->
  ~ exists frame_after retained_after middle : resource two_processors,
    resource_future two_processors frame frame_after /\
    repaired_spatiotemporal two_processors (proj1_sig frame_after) (proj1_sig retained_after) (proj1_sig grouped_after) /\
    repaired_temporal two_processors (proj1_sig retained_after) (proj1_sig suffix) (proj1_sig middle) /\
    repaired_spatiotemporal two_processors (proj1_sig frame_after) (proj1_sig middle) (proj1_sig result).
Proof.
  intros [tail Hhead] (f & r & middle & Hfuture & [[_ [_ [Hgb _]]] _] & [_ [[_ [_ [Htm _]]] _]] & [[_ [_ [Hout _]]] _]).
  assert (HnoY : ~ memory_domain (resource_memory two_processors f) 2%positive).
  { intros Hy; apply frame_excludes_y.
    exact (flushes_domain_subset _ _ _ (generalized_future_memory_flushes _ _ _ Hfuture) _ Hy). }
  specialize (Hgb 1%positive); apply ordered_interleaves in Hgb.
  change (interleaves (buffers (resource_memory two_processors f) 1%positive)
    (buffers (resource_memory two_processors r) 1%positive) [ywrite]) in Hgb.
  assert (Hfempty : buffers (resource_memory two_processors f) 1%positive = []).
  { destruct (buffers (resource_memory two_processors f) 1%positive) as [|w rest] eqn:E; [reflexivity |].
    assert (Hin : In w [ywrite]).
    { apply (proj2 (interleaves_in _ _ _ _ Hgb)); left; left; reflexivity. }
    destruct Hin as [Ew |Hfalse]; [subst w |contradiction].
    exfalso; apply HnoY; right; exists 1%positive, 0%Z; rewrite E; left; reflexivity. }
  rewrite Hfempty in Hgb; apply interleaves_nil_left in Hgb.
  specialize (Hout 1%positive); apply ordered_interleaves in Hout.
  change (interleaves (buffers (resource_memory two_processors f) 1%positive)
    (buffers (resource_memory two_processors middle) 1%positive)
    (buffers (resource_memory two_processors result) 1%positive)) in Hout.
  rewrite Hfempty in Hout; apply interleaves_nil_left in Hout.
  specialize (Htm 1%positive).
  change (buffers (resource_memory two_processors middle) 1%positive =
    buffers (resource_memory two_processors r) 1%positive ++
    buffers (resource_memory two_processors suffix) 1%positive) in Htm.
  rewrite Htm, <- Hgb, Hhead in Hout; discriminate.
Qed.

Lemma local_footprint_preserved :
  domain_included (resource_memory two_processors local_after) (resource_memory two_processors local).
Proof.
  intros loc [[v Hv] |[i [v Hv]]]; [discriminate |].
  change (In (loc,v) (one_buffer [xwrite; xwrite] i)) in Hv.
  unfold one_buffer, buffer_update in Hv; destruct (Pos.eq_dec i 1%positive); [|contradiction].
  destruct Hv as [H |[H |H]]; try contradiction; inversion H; subst.
  all: right; exists 1%positive, 0%Z; left; reflexivity.
Qed.

Lemma whole_assume_step s : step two_processors
  (Concurrent.Prim (Concurrent.Common (Sequential.Assume BTrue)) (EVal 1%Z))
  (State s (resource_memory two_processors whole)) halt (State s (resource_memory two_processors whole)).
Proof. eapply StepPrimitive; [reflexivity |apply PrimitiveAssume; [left; reflexivity |reflexivity]]. Qed.

Theorem overlap_frame_shape_counterexample s :
  repaired_temporal two_processors (proj1_sig retained) (proj1_sig local) (proj1_sig framed_local) /\
  repaired_spatiotemporal two_processors (proj1_sig frame) (proj1_sig framed_local) (proj1_sig whole) /\
  repaired_spatiotemporal two_processors (proj1_sig frame) (proj1_sig retained) (proj1_sig grouped) /\
  repaired_spatiotemporal two_processors (proj1_sig grouped) (proj1_sig local) (proj1_sig whole) /\
  resource_future two_processors grouped grouped_after /\
  repaired_spatiotemporal two_processors (proj1_sig grouped_after) (proj1_sig local_after) (proj1_sig whole) /\
  domain_included (resource_memory two_processors local_after) (resource_memory two_processors local) /\
  step two_processors (Concurrent.Prim (Concurrent.Common (Sequential.Assume BTrue)) (EVal 1%Z))
    (State s (resource_memory two_processors whole)) halt (State s (resource_memory two_processors whole)) /\
  ~ exists f r middle : resource two_processors,
    resource_future two_processors frame f /\ resource_future two_processors retained r /\
    repaired_spatiotemporal two_processors (proj1_sig f) (proj1_sig r) (proj1_sig grouped_after) /\
    repaired_temporal two_processors (proj1_sig r) (proj1_sig local_after) (proj1_sig middle) /\
    repaired_spatiotemporal two_processors (proj1_sig f) (proj1_sig middle) (proj1_sig whole).
Proof.
  split; [apply initial_temporal |]. split; [apply initial_outer |]. split; [apply initial_group |].
  split; [apply initial_small |]. split; [apply grouped_future |]. split; [apply after_small |].
  split; [apply local_footprint_preserved |]. split; [apply whole_assume_step |].
  intros (f & r & middle & HF & HR & HG & HT & HO).
  apply (no_reconstruction local_after whole); [exists [ywrite; xwrite]; reflexivity |].
  exists f, r, middle; auto.
Qed.

Definition zheap : heap := heap_update empty_heap 3%positive 0%Z.

Definition acquire_pool : resource two_processors.
Proof.
  refine (exist _ (Generalized (Memory zheap empty_buffers no_blocked) two_processors) _).
  apply (full_memory_valid_with_processor two_processors 2%positive); [right; reflexivity |].
  split; [intros i H; contradiction |intros; reflexivity].
Defined.

Definition acquire_before := Memory (heap_update xheap 3%positive 0%Z)
  (one_buffer [xwrite; ywrite; xwrite]) no_blocked.

Definition acquire_local_after : resource two_processors.
Proof.
  refine (exist _ (Generalized (Memory zheap (one_buffer [xwrite; xwrite])
    (blocked_except two_processors 2%positive)) (fun i => i = 2%positive)) _).
  split.
  - split; [intros i [H _]; exact H |]. intros i Hinactive.
    change (one_buffer [xwrite; xwrite] i = []); unfold one_buffer; rewrite buffer_update_other; [reflexivity |].
    intros ->; apply Hinactive; left; reflexivity.
  - split; [intros i H; right; exact H |].
    intros Hnone loc; exfalso; apply (Hnone 2%positive); reflexivity.
Defined.

Definition acquire_whole_after : resource two_processors.
Proof.
  refine (exist _ (Generalized (acquire two_processors acquire_before 2%positive) two_processors) _).
  apply (full_memory_valid_with_processor two_processors 2%positive); [right; reflexivity |].
  apply acquire_well_formed; exact (proj1 (proj2_sig whole)).
Defined.

Lemma whole_excludes_z : ~ memory_domain (resource_memory two_processors whole) 3%positive.
Proof.
  intros [[v Hv] |[i [v Hv]]]; [discriminate |].
  change (In (3%positive,v) (one_buffer [xwrite; ywrite; xwrite] i)) in Hv.
  unfold one_buffer, buffer_update in Hv; destruct (Pos.eq_dec i 1%positive); [|contradiction].
  destruct Hv as [H |[H |[H |H]]]; discriminate || contradiction.
Qed.

Lemma acquire_pool_spatial :
  memory_spatial (resource_memory two_processors acquire_pool) (resource_memory two_processors whole) acquire_before.
Proof.
  split.
  - split.
    + intros loc [[v Hv] |[i [v Hv]]] Hwhole; [|contradiction].
      change (heap_update empty_heap 3%positive 0%Z loc = Some v) in Hv.
      unfold heap_update, empty_heap in Hv; destruct (Pos.eq_dec loc 3%positive) as [-> |Hneq];
        [exact (whole_excludes_z Hwhole) |discriminate].
    + intros i H; contradiction.
  - split.
    + intros loc; change (heap_update xheap 3%positive 0%Z loc = heap_override zheap xheap loc).
      unfold heap_override, zheap, xheap, heap_update, empty_heap.
      destruct (Pos.eq_dec loc 1%positive); destruct (Pos.eq_dec loc 3%positive); congruence.
    + split.
      * intros i; exact (interleaves_app [] (one_buffer [xwrite; ywrite; xwrite] i)).
      * intros i; change (False <-> False \/ False); tauto.
Qed.

Lemma acquire_pool_invariant s :
  persistent_models two_processors s acquire_pool (writer_points_to (EVal 3%Z) (EVal 0%Z)).
Proof.
  eapply writer_points_to_from_shape with (loc := 3%positive) (owner := 2%positive);
    try reflexivity; [right; reflexivity |intros i H; contradiction |right; reflexivity].
Qed.

Lemma acquire_after_small : repaired_spatiotemporal two_processors
  (proj1_sig grouped_after) (proj1_sig acquire_local_after) (proj1_sig acquire_whole_after).
Proof.
  split.
  - split.
    + split; [intros i H; contradiction |]. split.
      * intros i _ loc [v Hv] [w Hw].
        change (In (loc,v) (buffer_update (one_buffer [xwrite; ywrite]) 1%positive [ywrite] i)) in Hv.
        unfold one_buffer, buffer_update in Hv; destruct (Pos.eq_dec i 1%positive); [|contradiction].
        destruct Hv as [E |H]; [inversion E; subst loc v |contradiction]. discriminate.
      * intros i j _ _ Hneq loc [v Hv] [w Hw].
        change (In (loc,v) (buffer_update (one_buffer [xwrite; ywrite]) 1%positive [ywrite] i)) in Hv.
        change (In (loc,w) (one_buffer [xwrite; xwrite] j)) in Hw.
        unfold one_buffer, buffer_update in Hv, Hw.
        destruct (Pos.eq_dec i 1%positive); [|contradiction].
        destruct (Pos.eq_dec j 1%positive); [congruence |contradiction].
    + split.
      * intros loc; change (heap_update xheap 3%positive 0%Z loc =
          heap_override (heap_update xheap 1%positive 0%Z) zheap loc).
        unfold heap_override, zheap, xheap, heap_update, empty_heap.
        destruct (Pos.eq_dec loc 3%positive); destruct (Pos.eq_dec loc 1%positive); reflexivity.
      * split.
        -- exact (proj1 (proj2 (proj2 (proj1 after_small)))).
        -- intros i; change (blocked_except two_processors 2%positive i <->
             False \/ blocked_except two_processors 2%positive i); tauto.
  - intros i; reflexivity.
Qed.

Lemma acquire_local_footprint : forall loc,
  memory_domain (resource_memory two_processors acquire_local_after) loc ->
  memory_domain (resource_memory two_processors local) loc \/
  memory_domain (resource_memory two_processors acquire_pool) loc.
Proof.
  intros loc [[v Hv] |[i [v Hv]]].
  - right; left; exists v; exact Hv.
  - change (In (loc,v) (one_buffer [xwrite; xwrite] i)) in Hv.
    unfold one_buffer, buffer_update in Hv; destruct (Pos.eq_dec i 1%positive); [|contradiction].
    destruct Hv as [H |[H |H]]; try contradiction; inversion H; subst.
    all: left; right; exists 1%positive, 0%Z; left; reflexivity.
Qed.

Lemma whole_acquire_step s : step two_processors
  (Concurrent.Prim Concurrent.Lock (EVal 2%Z)) (State s acquire_before) halt
  (State s (resource_memory two_processors acquire_whole_after)).
Proof.
  eapply StepPrimitive; [reflexivity |]. apply PrimitiveLock;
    [right; reflexivity |reflexivity |intros i H; contradiction].
Qed.

(** The search's acquisition witness has a real, nonempty, admissible pool,
    an actual lock step, exact owner-only new marks, and the combined
    local/pool footprint bound. It still fails the proposed reconstruction. *)
Theorem overlap_acquire_frame_shape_counterexample s :
  invariant_fragment (writer_points_to (EVal 3%Z) (EVal 0%Z)) /\
  persistent_models two_processors s acquire_pool (writer_points_to (EVal 3%Z) (EVal 0%Z)) /\
  memory_spatial (resource_memory two_processors acquire_pool) (resource_memory two_processors whole) acquire_before /\
  repaired_temporal two_processors (proj1_sig retained) (proj1_sig local) (proj1_sig framed_local) /\
  repaired_spatiotemporal two_processors (proj1_sig frame) (proj1_sig framed_local) (proj1_sig whole) /\
  repaired_spatiotemporal two_processors (proj1_sig frame) (proj1_sig retained) (proj1_sig grouped) /\
  repaired_spatiotemporal two_processors (proj1_sig grouped) (proj1_sig local) (proj1_sig whole) /\
  resource_future two_processors grouped grouped_after /\
  repaired_spatiotemporal two_processors (proj1_sig grouped_after) (proj1_sig acquire_local_after) (proj1_sig acquire_whole_after) /\
  (forall loc, memory_domain (resource_memory two_processors acquire_local_after) loc ->
    memory_domain (resource_memory two_processors local) loc \/ memory_domain (resource_memory two_processors acquire_pool) loc) /\
  (forall i, complete (proj1_sig acquire_local_after) i <-> i = 2%positive) /\
  lock_held two_processors (resource_memory two_processors acquire_local_after) 2%positive /\
  memory_spatial empty_memory (resource_memory two_processors acquire_whole_after)
    (resource_memory two_processors acquire_whole_after) /\
  step two_processors (Concurrent.Prim Concurrent.Lock (EVal 2%Z)) (State s acquire_before) halt
    (State s (resource_memory two_processors acquire_whole_after)) /\
  ~ exists f r middle : resource two_processors,
    resource_future two_processors frame f /\ resource_future two_processors retained r /\
    repaired_spatiotemporal two_processors (proj1_sig f) (proj1_sig r) (proj1_sig grouped_after) /\
    repaired_temporal two_processors (proj1_sig r) (proj1_sig acquire_local_after) (proj1_sig middle) /\
    repaired_spatiotemporal two_processors (proj1_sig f) (proj1_sig middle) (proj1_sig acquire_whole_after).
Proof.
  split; [apply InvariantCell |]. split; [apply acquire_pool_invariant |]. split; [apply acquire_pool_spatial |].
  split; [apply initial_temporal |]. split; [apply initial_outer |]. split; [apply initial_group |].
  split; [apply initial_small |]. split; [apply grouped_future |]. split; [apply acquire_after_small |].
  split; [apply acquire_local_footprint |]. split; [intros i; reflexivity |].
  split; [split; [right; reflexivity |intros i; reflexivity] |].
  split; [exact (proj1 (spatial_empty_left (proj1_sig acquire_whole_after))) |].
  split; [apply whole_acquire_step |].
  intros (f & r & middle & HF & HR & HG & HT & HO).
  apply (no_reconstruction acquire_local_after acquire_whole_after); [exists [ywrite; xwrite]; reflexivity |].
  exists f, r, middle; auto.
Qed.

End FrameShapeCounterexample.
