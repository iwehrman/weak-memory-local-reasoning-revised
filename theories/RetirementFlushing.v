From Stdlib Require Import List ZArith Bool.
From WMLR Require Import Expressions Machine BufferRelations Separation OrderedSeparation
  StableCompatibility RepairedSeparation GeneralizedFlushing ExecutionExamples.
Import ListNotations.

(** A bridge obligation for extending retirement to actual buffered histories.
    Mask only the history's HEAP observation, never its pending writes. This is
    a simulation lemma, not yet a replacement buffered resource algebra. *)
Definition mask_history (mask : location -> bool) (m : memory) := Memory
  (fun loc => if mask loc then None else shared_heap m loc) (buffers m) (blocked m).
Definition no_pending_mask (active : processor_domain) mask m := forall i, active i -> forall loc,
  mask loc = true -> ~ buffer_domain (buffers m i) loc.

Lemma mask_history_well_formed active mask m :
  memory_well_formed active m -> memory_well_formed active (mask_history mask m).
Proof. intros H; exact H. Qed.

Lemma no_pending_mask_flush active mask m m' : no_pending_mask active mask m ->
  flush active m m' -> no_pending_mask active mask m'.
Proof.
  intros Hsafe Hflush; destruct Hflush as [m i loc v rest Hi Hlive Hhead].
  intros j Hj address Hmask Hpending; apply (Hsafe j Hj address Hmask).
  eapply flushed_buffer_domain; eassumption.
Qed.

(** Existing repaired temporal compatibility supplies this condition whenever
    the retired addresses belong to the current cell's heap. No global drain
    or finite-processor premise is needed. *)
Theorem stable_history_can_retire active mask history current :
  stable_compatible active history current ->
  (forall loc, mask loc = true -> heap_domain (shared_heap current) loc) ->
  no_pending_mask active mask history.
Proof.
  intros [_ [Hheap _]] Hcovered i Hi loc Hmask Hpending.
  exact (Hheap i Hi loc Hpending (Hcovered loc Hmask)).
Qed.

Theorem retirement_flush_simulation active mask source source' target :
  no_pending_mask active mask source ->
  memory_equiv target (mask_history mask source) -> flush active source source' ->
  exists target', flush active target target' /\ memory_equiv target' (mask_history mask source') /\
    no_pending_mask active mask source'.
Proof.
  intros Hsafe [Hheap [Hbuffers Hblocks]] Hflush.
  pose proof (no_pending_mask_flush _ _ _ _ Hsafe Hflush) as Hsafe'.
  destruct Hflush as [source i loc v rest Hi Hlive Hhead].
  assert (Hmask : mask loc = false).
  { destruct (mask loc) eqn:E; [|reflexivity]. exfalso; apply (Hsafe i Hi loc E).
    exists v; rewrite Hhead; left; reflexivity. }
  exists (flush_write target i loc v rest); split.
  - constructor; [exact Hi |intros H; apply Hlive, Hblocks, H |rewrite Hbuffers; exact Hhead].
  - split; [|exact Hsafe']. split.
    + intros address; cbn [flush_write mask_history shared_heap].
      unfold heap_update; destruct (Pos.eq_dec address loc) as [-> |Hne].
      * rewrite Hmask; reflexivity.
      * apply Hheap.
    + split.
      * intros j; cbn [flush_write mask_history buffers]; unfold buffer_update.
        destruct (Pos.eq_dec j i); [reflexivity |apply Hbuffers].
      * exact Hblocks.
Qed.

Theorem retirement_flushes_simulation active mask source source' : memory_flushes active source source' ->
  no_pending_mask active mask source -> forall target, memory_equiv target (mask_history mask source) ->
  exists target', memory_flushes active target target' /\ memory_equiv target' (mask_history mask source') /\
    no_pending_mask active mask source'.
Proof.
  induction 1; intros Hsafe target Heq.
  - exists target; split; [constructor |auto].
  - destruct (retirement_flush_simulation _ _ _ _ _ Hsafe Heq H) as (middle & Hstep & Heq' & Hsafe').
    destruct (IHmemory_flushes Hsafe' middle Heq') as (last & Htail & Hlast & Hsafe'').
    exists last; split; [econstructor; eassumption |auto].
Qed.

Corollary retirement_flushes_from_mask active mask source source' :
  no_pending_mask active mask source -> memory_flushes active source source' ->
  exists target', memory_flushes active (mask_history mask source) target' /\
    memory_equiv target' (mask_history mask source').
Proof.
  intros Hsafe Hrun; destruct (retirement_flushes_simulation _ _ _ _ Hrun Hsafe (mask_history mask source)
    ltac:(split; [intros loc; reflexivity |split; [intros i; reflexivity |intros i; reflexivity]]))
    as (target' & Htarget & Heq & _); exists target'; auto.
Qed.

(** A pending write at a retired address cannot be erased as mere history:
    the real machine can flush it and change the current heap. *)
Theorem masking_a_pending_write_does_not_commute :
  exists source after masked_after,
    flush two_processors source after /\
    flush two_processors (mask_history (fun loc => Pos.eqb loc 1%positive) source) masked_after /\
    shared_heap masked_after 1%positive = Some 7%Z /\
    shared_heap (mask_history (fun loc => Pos.eqb loc 1%positive) after) 1%positive = None.
Proof.
  pose (source := Memory empty_heap (buffer_update empty_buffers 1%positive [(1%positive, 7%Z)]) no_blocked).
  exists source, (flush_write source 1%positive 1%positive 7%Z []),
    (flush_write (mask_history (fun loc => Pos.eqb loc 1%positive) source) 1%positive 1%positive 7%Z []).
  split.
  - constructor; [left; reflexivity |intros H; exact H |apply buffer_update_same].
  - split.
    + constructor; [left; reflexivity |intros H; exact H |apply buffer_update_same].
    + split; [apply heap_update_same |reflexivity].
Qed.
