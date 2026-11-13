From Stdlib Require Import List ZArith.
From WMLR Require Import Expressions Machine BufferRelations Separation OrderedBuffers.
Import ListNotations.

(** Candidate repair of the spatiotemporal separator: retain the original
    compatibility relation, but require ordered rather than lookup-only
    overriding. It is deliberately separate from the transcription. *)
Definition memory_ordered active a b out : Prop :=
  temporal_compatible active a b /\ memory_merge ordered_overrides a b out.

Theorem ordered_in_original active a b out :
  memory_ordered active a b out -> memory_spatiotemporal active a b out.
Proof.
  intros [Hcompat [Hh [Hb Hk]]]. split; [exact Hcompat |].
  split; [exact Hh |]. split; [intros i; apply ordered_is_override, Hb | exact Hk].
Qed.

Theorem spatial_in_ordered active a b out :
  memory_spatial a b out -> memory_ordered active a b out.
Proof.
  intros [Hcompat [Hh [Hb Hk]]]. split; [apply spatial_compatible_temporal, Hcompat |].
  split; [exact Hh |]. split; [|exact Hk]. intros i.
  apply disjoint_interleaves_ordered; [apply Hb |].
  intros loc Ha Hb'. apply (proj1 Hcompat loc); right; exists i; assumption.
Qed.

Theorem temporal_in_ordered active a b out :
  memory_temporal active a b out -> memory_ordered active a b out.
Proof.
  intros [Hcompat [Hh [Hb Hk]]]. split; [exact Hcompat |].
  split; [exact Hh |]. split; [|exact Hk]. intros i; rewrite Hb; apply ordered_append.
Qed.

Lemma flushed_buffer_domain m i loc v rest j address :
  buffers m i = (loc, v) :: rest ->
  buffer_domain (buffers (flush_write m i loc v rest) j) address ->
  buffer_domain (buffers m j) address.
Proof.
  intros Hhead [w Hw]. cbn [flush_write buffers] in Hw. unfold buffer_update in Hw.
  destruct (Pos.eq_dec j i); subst.
  - exists w. rewrite Hhead; right; exact Hw.
  - exists w; exact Hw.
Qed.

Lemma temporal_compatible_flush_left active a b i loc v rest :
  temporal_compatible active a b -> buffers a i = (loc, v) :: rest ->
  temporal_compatible active (flush_write a i loc v rest) b.
Proof.
  intros [Hk [Hh Hb]] Hhead. split; [exact Hk |]. split.
  - intros j Hj address Ha Hheap. apply (Hh j Hj address); [|exact Hheap].
    eapply flushed_buffer_domain; eassumption.
  - intros j k Hj Hk' Hneq address Ha Hbuffer. apply (Hb j k Hj Hk' Hneq address); [|exact Hbuffer].
    eapply flushed_buffer_domain; eassumption.
Qed.

Lemma temporal_compatible_flush_right active a b i loc v rest :
  temporal_compatible active a b -> jointly_unblocked active a b i ->
  buffers b i = (loc, v) :: rest -> ~ buffer_domain (buffers a i) loc ->
  temporal_compatible active a (flush_write b i loc v rest).
Proof.
  intros [Hk [Hh Hb]] Hi Hhead Hfresh. split; [exact Hk |]. split.
  - intros j Hj address Ha [w Hw]. cbn [flush_write shared_heap] in Hw.
    unfold heap_update in Hw. destruct (Pos.eq_dec address loc) as [Heq | Hneq].
    + subst address. destruct (Pos.eq_dec j i) as [Heq | Hneq].
      * subst j; apply Hfresh, Ha.
      * apply (Hb j i Hj Hi Hneq loc Ha). exists v; rewrite Hhead; left; reflexivity.
    + apply (Hh j Hj address Ha). exists w; exact Hw.
  - intros j k Hj Hk' Hneq address Ha Hbuffer.
    apply (Hb j k Hj Hk' Hneq address Ha).
    eapply flushed_buffer_domain; eassumption.
Qed.

Lemma heap_update_pointwise h h' loc v address :
  (forall x, h x = h' x) -> heap_update h loc v address = heap_update h' loc v address.
Proof. intros H; unfold heap_update; destruct (Pos.eq_dec address loc); auto. Qed.

Lemma heap_override_update_left a b loc v address : b loc = None ->
  heap_update (heap_override a b) loc v address =
  heap_override (heap_update a loc v) b address.
Proof.
  intros H. unfold heap_update, heap_override.
  destruct (Pos.eq_dec address loc); subst; [rewrite H | destruct (b address)]; reflexivity.
Qed.

Lemma heap_override_update_right a b loc v address :
  heap_update (heap_override a b) loc v address =
  heap_override a (heap_update b loc v) address.
Proof. unfold heap_update, heap_override; destruct (Pos.eq_dec address loc); reflexivity. Qed.

(** A replacement for Lemma 4: the global FIFO head belongs to one component,
    that component can really flush it, and the residuals still compose. *)
Theorem ordered_flush_split active a b whole whole' :
  memory_ordered active a b whole -> flush active whole whole' ->
  (exists a', flush active a a' /\ memory_ordered active a' b whole') \/
  (exists b', flush active b b' /\ memory_ordered active a b' whole').
Proof.
  intros [Hcompat [Hh [Hb Hk]]] Hflush.
  destruct Hflush as [whole i loc v rest Hi Hlive Hhead].
  assert (HliveA : ~ blocked a i).
  { intros H; apply Hlive, Hk; left; exact H. }
  assert (HliveB : ~ blocked b i).
  { intros H; apply Hlive, Hk; right; exact H. }
  assert (Hjoint : jointly_unblocked active a b i) by (repeat split; assumption).
  specialize (Hb i) as Hbuffer. rewrite Hhead in Hbuffer.
  destruct (ordered_head_origin _ _ _ _ Hbuffer) as
    [[tail [Ha Htail]] | [tail [Hb' [Hfresh Htail]]]].
  - left. exists (flush_write a i loc v tail). split.
    + constructor; assumption.
    + split; [apply temporal_compatible_flush_left; assumption |]. split.
      * intros address. cbn [flush_write shared_heap].
        rewrite (heap_update_pointwise _ _ _ _ _ Hh).
        apply heap_override_update_left.
        destruct (shared_heap b loc) eqn:Hvalue; [|reflexivity].
        exfalso. apply (proj1 (proj2 Hcompat) i Hjoint loc).
        -- exists v; rewrite Ha; left; reflexivity.
        -- eexists; exact Hvalue.
      * split.
        -- intros j. cbn [flush_write buffers]. unfold buffer_update.
           destruct (Pos.eq_dec j i); subst; [exact Htail | apply Hb].
        -- exact Hk.
  - right. exists (flush_write b i loc v tail). split.
    + constructor; assumption.
    + split; [apply temporal_compatible_flush_right; assumption |]. split.
      * intros address. cbn [flush_write shared_heap].
        rewrite (heap_update_pointwise _ _ _ _ _ Hh). apply heap_override_update_right.
      * split.
        -- intros j. cbn [flush_write buffers]. unfold buffer_update.
           destruct (Pos.eq_dec j i); subst; [exact Htail | apply Hb].
        -- exact Hk.
Qed.

(** Finite flushing decomposition, the role of Lemma 7 in frame proofs. *)
Theorem ordered_flushes_split active whole whole' : memory_flushes active whole whole' ->
  forall a b, memory_ordered active a b whole ->
  exists a' b', memory_flushes active a a' /\ memory_flushes active b b' /\
    memory_ordered active a' b' whole'.
Proof.
  intros H. induction H; intros left right Hsep.
  - exists left, right. split; [constructor |]. split; [constructor | exact Hsep].
  - destruct (ordered_flush_split _ _ _ _ _ Hsep H) as [[left' [Hl Hsep']] | [right' [Hr Hsep']]].
    + destruct (IHmemory_flushes _ _ Hsep') as [left'' [right'' [Hleft [Hright Hout]]]].
      exists left'', right''. split; [econstructor; eassumption |]. split; assumption.
    + destruct (IHmemory_flushes _ _ Hsep') as [left'' [right'' [Hleft [Hright Hout]]]].
      exists left'', right''. split; [exact Hleft |]. split; [econstructor; eassumption | exact Hout].
Qed.
