From Stdlib Require Import List ZArith.
From WMLR Require Import Expressions Machine BufferRelations OrderedBuffers
  Separation StableCompatibility RepairedSeparation.
Import ListNotations.

Lemma head_in_buffer_domain w rest : buffer_domain (w :: rest) (fst w).
Proof. destruct w as [loc v]; exists v; left; reflexivity. Qed.

(** The left buffer and the output determine the entire right buffer, not
    just its lookup values or footprint. Duplicate writes are allowed. *)
Theorem ordered_residual_unique frame local whole :
  ordered_overrides frame local whole ->
  forall other, ordered_overrides frame other whole -> local = other.
Proof.
  intros H; induction H as [|w frame local whole H IH |w frame local whole Hfresh H IH];
    intros other Hother.
  - inversion Hother; reflexivity.
  - inversion Hother as [|w' frame' local' whole' Hleft |w' frame' local' whole' Hnot Hright]; subst.
    + eapply IH; eassumption.
    + exfalso; apply Hnot, head_in_buffer_domain.
  - inversion Hother as [|w' frame' local' whole' Hleft |w' frame' local' whole' Hnot Hright]; subst.
    + exfalso; apply Hfresh, head_in_buffer_domain.
    + f_equal; eapply IH; eassumption.
Qed.

Theorem repaired_residual_buffers_unique active frame local other whole other_whole :
  memory_repaired active frame local whole ->
  memory_repaired active frame other other_whole ->
  (forall i, buffers whole i = buffers other_whole i) ->
  forall i, buffers local i = buffers other i.
Proof.
  intros [_ [_ [Hbuffers _]]] [_ [_ [Hother _]]] Hequal i.
  eapply ordered_residual_unique; [exact (Hbuffers i) |]. rewrite Hequal; apply Hother.
Qed.

Corollary resource_residual_buffers_unique active (frame local other whole other_whole : resource active) :
  repaired_spatiotemporal active (proj1_sig frame) (proj1_sig local) (proj1_sig whole) ->
  repaired_spatiotemporal active (proj1_sig frame) (proj1_sig other) (proj1_sig other_whole) ->
  underlying (proj1_sig whole) = underlying (proj1_sig other_whole) ->
  forall i, buffers (underlying (proj1_sig local)) i = buffers (underlying (proj1_sig other)) i.
Proof.
  intros [Hleft _] [Hright _] Hequal.
  eapply repaired_residual_buffers_unique; [exact Hleft |exact Hright |].
  intros i; rewrite Hequal; reflexivity.
Qed.

(** Presence in the remaining frame buffer forces the next occurrence to
    come from that frame. A right occurrence at the same address cannot
    pass it, even when the values are identical. *)
Theorem ordered_head_frame_forced frame local w rest :
  ordered_overrides frame local (w :: rest) -> buffer_domain frame (fst w) ->
  exists tail, frame = w :: tail /\ ordered_overrides tail local rest.
Proof.
  intros H Hpresent; destruct (ordered_head_origin _ _ _ _ H)
    as [Hleft |(tail & Hhead & Habsent & Hright)]; [exact Hleft |contradiction].
Qed.

Theorem ordered_duplicate_head_from_frame w frame local rest :
  ordered_overrides (w :: frame) (w :: local) (w :: rest) ->
  ordered_overrides frame (w :: local) rest.
Proof.
  intros H; destruct (ordered_head_frame_forced _ _ _ _ H (head_in_buffer_domain w frame))
    as (tail & E & Htail); inversion E; subst; exact Htail.
Qed.

(** At memory level, flushing a local write while a frame write to the same
    address remains would violate stable compatibility: the local flush
    puts that address into the heap. No post-composition can justify it. *)
Theorem local_flush_cannot_pass_frame active frame local i loc v rest whole :
  active i -> buffer_domain (buffers frame i) loc ->
  ~ memory_repaired active frame (flush_write local i loc v rest) whole.
Proof.
  intros Hi Hpending [[_ [Hheap _]] _].
  apply (Hheap i Hi loc Hpending); exists v; apply heap_update_same.
Qed.
