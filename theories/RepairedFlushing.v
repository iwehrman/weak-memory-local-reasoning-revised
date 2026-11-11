From Stdlib Require Import List ZArith.
From WMLR Require Import Expressions Machine BufferRelations Separation
  OrderedBuffers OrderedSeparation StableCompatibility RepairedSeparation FrameDecomposition.
Import ListNotations.

Lemma stable_compatible_flush_left active a b i loc v rest :
  stable_compatible active a b -> buffers a i = (loc, v) :: rest ->
  stable_compatible active (flush_write a i loc v rest) b.
Proof.
  intros [Hk [Hh Hb]] Hhead. split; [exact Hk |]. split.
  - intros j Hj address Ha Hheap. apply (Hh j Hj address); [|exact Hheap].
    eapply flushed_buffer_domain; eassumption.
  - intros j k Hj Hk' Hneq address Ha Hbuffer. apply (Hb j k Hj Hk' Hneq address); [|exact Hbuffer].
    eapply flushed_buffer_domain; eassumption.
Qed.

Lemma stable_compatible_flush_right active a b i loc v rest :
  stable_compatible active a b -> active i ->
  buffers b i = (loc, v) :: rest -> ~ buffer_domain (buffers a i) loc ->
  stable_compatible active a (flush_write b i loc v rest).
Proof.
  intros [Hk [Hh Hb]] Hi Hhead Hfresh. split; [exact Hk |]. split.
  - intros j Hj address Ha [w Hw]. cbn [flush_write shared_heap] in Hw.
    unfold heap_update in Hw. destruct (Pos.eq_dec address loc) as [Heq | Hneq].
    + subst address. destruct (Pos.eq_dec j i) as [Heq | Hneq].
      * subst j; apply Hfresh, Ha.
      * apply (Hb j i Hj Hi Hneq loc Ha). exists v; rewrite Hhead; left; reflexivity.
    + apply (Hh j Hj address Ha). exists w; exact Hw.
  - intros j k Hj Hk' Hneq address Ha Hbuffer.
    apply (Hb j k Hj Hk' Hneq address Ha). eapply flushed_buffer_domain; eassumption.
Qed.

(** A global flush is an actual flush of one component, with the stronger
    compatibility guard preserved. The other component is unchanged. *)
Theorem repaired_flush_split active a b whole whole' :
  memory_repaired active a b whole -> flush active whole whole' ->
  (exists a', flush active a a' /\ memory_repaired active a' b whole') \/
  (exists b', flush active b b' /\ memory_repaired active a b' whole').
Proof.
  intros [Hcompat [Hh [Hb Hk]]] Hflush.
  destruct Hflush as [whole i loc v rest Hi Hlive Hhead].
  assert (HliveA : ~ blocked a i).
  { intros H; apply Hlive, Hk; left; exact H. }
  assert (HliveB : ~ blocked b i).
  { intros H; apply Hlive, Hk; right; exact H. }
  specialize (Hb i) as Hbuffer. rewrite Hhead in Hbuffer.
  destruct (ordered_head_origin _ _ _ _ Hbuffer) as
    [[tail [Ha Htail]] | [tail [Hb' [Hfresh Htail]]]].
  - left. exists (flush_write a i loc v tail). split.
    + constructor; assumption.
    + split; [apply stable_compatible_flush_left; assumption |]. split.
      * intros address. cbn [flush_write shared_heap].
        rewrite (heap_update_pointwise _ _ _ _ _ Hh). apply heap_override_update_left.
        destruct (shared_heap b loc) eqn:Hvalue; [|reflexivity].
        exfalso. apply (proj1 (proj2 Hcompat) i Hi loc).
        -- exists v; rewrite Ha; left; reflexivity.
        -- eexists; exact Hvalue.
      * split.
        -- intros j. cbn [flush_write buffers]. unfold buffer_update.
           destruct (Pos.eq_dec j i); subst; [exact Htail | apply Hb].
        -- exact Hk.
  - right. exists (flush_write b i loc v tail). split.
    + constructor; assumption.
    + split; [apply stable_compatible_flush_right; assumption |]. split.
      * intros address. cbn [flush_write shared_heap].
        rewrite (heap_update_pointwise _ _ _ _ _ Hh). apply heap_override_update_right.
      * split.
        -- intros j. cbn [flush_write buffers]. unfold buffer_update.
           destruct (Pos.eq_dec j i); subst; [exact Htail | apply Hb].
        -- exact Hk.
Qed.

Theorem repaired_flushes_split active whole whole' : memory_flushes active whole whole' ->
  forall a b, memory_repaired active a b whole ->
  exists a' b', memory_flushes active a a' /\ memory_flushes active b b' /\
    memory_repaired active a' b' whole'.
Proof.
  intros H. induction H; intros left right Hsep.
  - exists left, right. split; [constructor |]. split; [constructor | exact Hsep].
  - destruct (repaired_flush_split _ _ _ _ _ Hsep H) as [[a' [Ha Hsep']] | [b' [Hb Hsep']]].
    + destruct (IHmemory_flushes _ _ Hsep') as [a'' [b'' [Ha' [Hb' Hout]]]].
      exists a'', b''. split; [econstructor; eassumption |]. split; assumption.
    + destruct (IHmemory_flushes _ _ Hsep') as [a'' [b'' [Ha' [Hb' Hout]]]].
      exists a'', b''. split; [exact Ha' |]. split; [econstructor; eassumption | exact Hout].
Qed.

Lemma memory_spatial_in_repaired active a b out :
  memory_spatial a b out -> memory_repaired active a b out.
Proof.
  intros H. split; [apply spatial_compatible_stable, (proj1 H) |].
  exact (proj2 (spatial_in_ordered active _ _ _ H)).
Qed.

Lemma memory_repaired_in_printed active a b out :
  memory_repaired active a b out -> memory_spatiotemporal active a b out.
Proof.
  intros [Hcompat Hmerge]. apply ordered_in_printed.
  split; [apply stable_implies_printed_compatible, Hcompat | exact Hmerge].
Qed.

Theorem spatial_flush_split active a b whole whole' :
  memory_spatial a b whole -> flush active whole whole' ->
  (exists a', flush active a a' /\ memory_spatial a' b whole') \/
  (exists b', flush active b b' /\ memory_spatial a b' whole').
Proof.
  intros Hsp Hflush.
  destruct (repaired_flush_split _ _ _ _ _ (memory_spatial_in_repaired active _ _ _ Hsp) Hflush)
    as [[a' [Ha Hsep]] | [b' [Hb Hsep]]].
  - left; exists a'; split; [exact Ha |].
    eapply spatial_frame_recombination; [exact Hsp | | |apply memory_repaired_in_printed, Hsep].
    + apply (flush_domain_subset _ _ _ Ha).
    + intros loc H; exact H.
  - right; exists b'; split; [exact Hb |].
    eapply spatial_frame_recombination; [exact Hsp | | |apply memory_repaired_in_printed, Hsep].
    + intros loc H; exact H.
    + apply (flush_domain_subset _ _ _ Hb).
Qed.
