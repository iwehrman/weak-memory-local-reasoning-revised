From Stdlib Require Import List ZArith.
From WMLR Require Import Expressions Machine BufferRelations OrderedBuffers Separation
  OrderedSeparation StableCompatibility RepairedSeparation RepairedFlushing FrameDecomposition.
Import ListNotations.

(** Preserve the flushing processor when decomposing a transition. Its
    completeness mark must follow that same processor into the residual. *)
Inductive flush_at (active : processor_domain) i : memory -> memory -> Prop :=
| FlushAt m loc v rest : active i -> ~ blocked m i ->
    buffers m i = (loc, v) :: rest ->
    flush_at active i m (flush_write m i loc v rest).

Lemma flush_at_forget active i m m' : flush_at active i m m' -> flush active m m'.
Proof. destruct 1; constructor; assumption. Qed.

Lemma flush_at_exists active m m' : flush active m m' -> exists i, flush_at active i m m'.
Proof. destruct 1; eexists; constructor; eassumption. Qed.

Inductive generalized_step active : generalized_memory -> generalized_memory -> Prop :=
| GeneralizedMark m before after :
    (forall i, before i -> after i) -> (forall i, after i -> active i) ->
    generalized_step active (Generalized m before) (Generalized m after)
| GeneralizedFlush m m' before after i :
    flush_at active i m m' ->
    (forall j, before j -> after j) -> (forall j, after j -> active j) -> after i ->
    generalized_step active (Generalized m before) (Generalized m' after).

(** Marking alone exposes monotonicity in completeness. Flush steps are
    Definition 6's indexed transitions; both are closed under finite chains. *)
Inductive generalized_future active : generalized_memory -> generalized_memory -> Prop :=
| GeneralizedRefl a : generalized_future active a a
| GeneralizedNext a b c : generalized_step active a b ->
    generalized_future active b c -> generalized_future active a c.

Lemma generalized_future_one active a b : generalized_step active a b -> generalized_future active a b.
Proof. intros H; econstructor; [exact H | constructor]. Qed.

Lemma generalized_future_trans active a b c :
  generalized_future active a b -> generalized_future active b c -> generalized_future active a c.
Proof. induction 1; intros Htail; [exact Htail | econstructor; eauto]. Qed.

Lemma generalized_step_well_formed active a b :
  generalized_step active a b -> generalized_well_formed active a -> generalized_well_formed active b.
Proof.
  intros Hstep Hwf. destruct Hstep as [m before after Hinc Hactive |m m' before after i Hflush Hinc Hactive Hi];
    destruct Hwf as [Hmemory [Hbefore Hheap]]; split.
  - exact Hmemory.
  - split; [exact Hactive |]. intros Hnone; apply Hheap. intros j Hj; apply (Hnone j), Hinc, Hj.
  - eapply flush_preserves_well_formed; [exact (flush_at_forget _ _ _ _ Hflush) | exact Hmemory].
  - split; [exact Hactive |]. intros Hnone loc; exfalso; apply (Hnone i Hi).
Qed.

Theorem generalized_future_well_formed active a b :
  generalized_future active a b -> generalized_well_formed active a -> generalized_well_formed active b.
Proof. induction 1; intros Hwf; [exact Hwf | apply IHgeneralized_future; eapply generalized_step_well_formed; eassumption]. Qed.

Definition resource_future active (a b : resource active) :=
  generalized_future active (proj1_sig a) (proj1_sig b).

Lemma indexed_repaired_flush_split active i a b whole whole' :
  memory_repaired active a b whole -> flush_at active i whole whole' ->
  (exists a', flush_at active i a a' /\ memory_repaired active a' b whole') \/
  (exists b', flush_at active i b b' /\ memory_repaired active a b' whole').
Proof.
  intros [Hcompat [Hh [Hb Hk]]] Hflush.
  destruct Hflush as [whole loc v rest Hi Hlive Hhead].
  assert (HliveA : ~ blocked a i) by (intros H; apply Hlive, Hk; left; exact H).
  assert (HliveB : ~ blocked b i) by (intros H; apply Hlive, Hk; right; exact H).
  specialize (Hb i) as Hbuffer. rewrite Hhead in Hbuffer.
  destruct (ordered_head_origin _ _ _ _ Hbuffer) as
    [[tail [Ha Htail]] | [tail [Hb' [Hfresh Htail]]]].
  - left. exists (flush_write a i loc v tail). split; [constructor; assumption |].
    split; [apply stable_compatible_flush_left; assumption |]. split.
    + intros address. cbn [flush_write shared_heap].
      rewrite (heap_update_pointwise _ _ _ _ _ Hh). apply heap_override_update_left.
      destruct (shared_heap b loc) eqn:Hvalue; [|reflexivity].
      exfalso. apply (proj1 (proj2 Hcompat) i Hi loc).
      * exists v; rewrite Ha; left; reflexivity.
      * eexists; exact Hvalue.
    + split.
      * intros j. cbn [flush_write buffers]. unfold buffer_update.
        destruct (Pos.eq_dec j i); subst; [exact Htail | apply Hb].
      * exact Hk.
  - right. exists (flush_write b i loc v tail). split; [constructor; assumption |].
    split; [apply stable_compatible_flush_right; assumption |]. split.
    + intros address. cbn [flush_write shared_heap].
      rewrite (heap_update_pointwise _ _ _ _ _ Hh). apply heap_override_update_right.
    + split.
      * intros j. cbn [flush_write buffers]. unfold buffer_update.
        destruct (Pos.eq_dec j i); subst; [exact Htail | apply Hb].
      * exact Hk.
Qed.

Lemma indexed_spatial_flush_split active i a b whole whole' :
  memory_spatial a b whole -> flush_at active i whole whole' ->
  (exists a', flush_at active i a a' /\ memory_spatial a' b whole') \/
  (exists b', flush_at active i b b' /\ memory_spatial a b' whole').
Proof.
  intros Hsp Hflush.
  destruct (indexed_repaired_flush_split _ _ _ _ _ _ (memory_spatial_in_repaired active _ _ _ Hsp) Hflush)
    as [[a' [Ha Hsep]] | [b' [Hb Hsep]]].
  - left; exists a'; split; [exact Ha |].
    eapply spatial_frame_recombination; [exact Hsp | | |apply memory_repaired_in_printed, Hsep].
    + apply (flush_domain_subset _ _ _ (flush_at_forget _ _ _ _ Ha)).
    + intros loc H; exact H.
  - right; exists b'; split; [exact Hb |].
    eapply spatial_frame_recombination; [exact Hsp | | |apply memory_repaired_in_printed, Hsep].
    + intros loc H; exact H.
    + apply (flush_domain_subset _ _ _ (flush_at_forget _ _ _ _ Hb)).
Qed.

Definition stable_temporal_memory active a b out :=
  stable_compatible active a b /\ memory_merge (fun x y z => z = x ++ y) a b out.

Lemma indexed_temporal_flush_split active i a b whole whole' :
  stable_temporal_memory active a b whole -> flush_at active i whole whole' ->
  (exists a', flush_at active i a a' /\ stable_temporal_memory active a' b whole') \/
  (exists b', flush_at active i b b' /\ buffers a i = [] /\ stable_temporal_memory active a b' whole').
Proof.
  intros [Hcompat [Hh [Hb Hk]]] Hflush.
  destruct Hflush as [whole loc v rest Hi Hlive Hhead].
  assert (HliveA : ~ blocked a i) by (intros H; apply Hlive, Hk; left; exact H).
  assert (HliveB : ~ blocked b i) by (intros H; apply Hlive, Hk; right; exact H).
  pose proof (Hb i) as Hbuffer. rewrite Hhead in Hbuffer.
  destruct (buffers a i) as [|w tail] eqn:Ha.
  - right. simpl in Hbuffer. exists (flush_write b i loc v rest). split.
    + constructor; [exact Hi | exact HliveB | symmetry; exact Hbuffer].
    + split; [reflexivity |]. split.
      * apply stable_compatible_flush_right; [exact Hcompat | exact Hi | symmetry; exact Hbuffer |].
        rewrite Ha. intros [x H]; contradiction.
      * split.
        -- intros address. cbn [flush_write shared_heap].
           rewrite (heap_update_pointwise _ _ _ _ _ Hh). apply heap_override_update_right.
        -- split; [|exact Hk]. intros j; cbn [flush_write buffers]; unfold buffer_update.
           destruct (Pos.eq_dec j i); subst; [rewrite Ha; reflexivity | apply Hb].
  - simpl in Hbuffer. inversion Hbuffer; subst w rest.
    left. exists (flush_write a i loc v tail). split; [constructor; assumption |]. split.
    + apply stable_compatible_flush_left; assumption.
    + split.
      * intros address. cbn [flush_write shared_heap].
        rewrite (heap_update_pointwise _ _ _ _ _ Hh). apply heap_override_update_left.
        destruct (shared_heap b loc) eqn:Hvalue; [|reflexivity].
        exfalso. apply (proj1 (proj2 Hcompat) i Hi loc).
        -- exists v; rewrite Ha; left; reflexivity.
        -- eexists; exact Hvalue.
      * split; [|exact Hk]. intros j; cbn [flush_write buffers]; unfold buffer_update.
        destruct (Pos.eq_dec j i); subst; [reflexivity | apply Hb].
Qed.

Lemma flush_at_empty_buffer active i m m' j :
  flush_at active i m m' -> buffers m j = [] -> buffers m' j = [].
Proof.
  intros Hflush Hempty. destruct Hflush as [m loc v rest Hi Hlive Hhead].
  cbn [flush_write buffers]. unfold buffer_update. destruct (Pos.eq_dec j i) as [-> | Hneq].
  - rewrite Hempty in Hhead; discriminate.
  - exact Hempty.
Qed.

Lemma generalized_spatial_step_split active out out' : generalized_step active out out' ->
  forall a b, spatial a b out ->
  exists a' b', generalized_future active a a' /\ generalized_future active b b' /\ spatial a' b' out'.
Proof.
  intros Hstep. destruct Hstep as [m before after Hinc Hactive |m m' before after i Hflush Hinc Hactive Hi];
    intros [ma ga] [mb gb] [Hmemory Hcomplete]; cbn in *.
  - exists (Generalized ma after), (Generalized mb gb). split.
    + apply generalized_future_one, GeneralizedMark; [|exact Hactive].
      intros j Hj; apply Hinc, (Hcomplete j); left; exact Hj.
    + split; [constructor |]. split; [exact Hmemory |].
      intros j; simpl; split; [intros H; left; exact H | intros [H | H]; [exact H |]].
      apply Hinc, (Hcomplete j); right; exact H.
  - destruct (indexed_spatial_flush_split _ _ _ _ _ _ Hmemory Hflush) as
      [[ma' [Ha Hsep]] | [mb' [Hb Hsep]]].
    + exists (Generalized ma' after), (Generalized mb gb). split.
      * apply generalized_future_one. eapply GeneralizedFlush; [exact Ha | |exact Hactive | exact Hi].
        intros j Hj; apply Hinc, (Hcomplete j); left; exact Hj.
      * split; [constructor |]. split; [exact Hsep |].
        intros j; simpl; split; [intros H; left; exact H | intros [H | H]; [exact H |]].
        apply Hinc, (Hcomplete j); right; exact H.
    + exists (Generalized ma ga), (Generalized mb' after). split; [constructor |]. split.
      * apply generalized_future_one. eapply GeneralizedFlush; [exact Hb | |exact Hactive | exact Hi].
        intros j Hj; apply Hinc, (Hcomplete j); right; exact Hj.
      * split; [exact Hsep |].
        intros j; simpl; split; [intros H; right; exact H | intros [H | H]; [|exact H]].
        apply Hinc, (Hcomplete j); left; exact H.
Qed.

Lemma stable_temporal_lift active ma mb out ga gb gout :
  stable_temporal_memory active ma mb out ->
  (forall i, gb i -> buffers ma i = []) -> (forall i, gout i <-> ga i \/ gb i) ->
  repaired_temporal active (Generalized ma ga) (Generalized mb gb) (Generalized out gout).
Proof.
  intros [Hstable Hmerge] Hbefore Hcomplete. split; [exact Hstable |]. split.
  - split; [apply stable_implies_printed_compatible, Hstable | exact Hmerge].
  - split; assumption.
Qed.

Lemma generalized_temporal_step_split active out out' : generalized_step active out out' ->
  forall a b, repaired_temporal active a b out ->
  exists a' b', generalized_future active a a' /\ generalized_future active b b' /\ repaired_temporal active a' b' out'.
Proof.
  intros Hstep. destruct Hstep as [m before after Hinc Hactive |m m' before after i Hflush Hinc Hactive Hi];
    intros [ma ga] [mb gb] [Hstable [[_ Hmerge] [Hbefore Hcomplete]]]; cbn in *.
  - exists (Generalized ma after), (Generalized mb gb). split.
    + apply generalized_future_one, GeneralizedMark; [|exact Hactive].
      intros j Hj; apply Hinc, (Hcomplete j); left; exact Hj.
    + split; [constructor |]. apply stable_temporal_lift; [split; assumption |exact Hbefore |].
      intros j; split; [intros H; left; exact H | intros [H | H]; [exact H |]].
      apply Hinc, (Hcomplete j); right; exact H.
  - destruct (indexed_temporal_flush_split _ _ _ _ _ _ (conj Hstable Hmerge) Hflush) as
      [[ma' [Ha Hsep]] | [mb' [Hb [Hempty Hsep]]]].
    + exists (Generalized ma' after), (Generalized mb gb). split.
      * apply generalized_future_one. eapply GeneralizedFlush; [exact Ha | |exact Hactive |exact Hi].
        intros j Hj; apply Hinc, (Hcomplete j); left; exact Hj.
      * split; [constructor |]. apply stable_temporal_lift; [exact Hsep | |].
        -- intros j Hj; eapply flush_at_empty_buffer; [exact Ha |apply Hbefore, Hj].
        -- intros j; split; [intros H; left; exact H |intros [H | H]; [exact H |]].
           apply Hinc, (Hcomplete j); right; exact H.
    + exists (Generalized ma after), (Generalized mb' (fun j => gb j \/ j = i)). split.
      * apply generalized_future_one, GeneralizedMark; [|exact Hactive].
        intros j Hj; apply Hinc, (Hcomplete j); left; exact Hj.
      * split.
        -- apply generalized_future_one. eapply GeneralizedFlush; [exact Hb | | |right; reflexivity].
           ++ intros j Hj; left; exact Hj.
           ++ intros j [Hj | ->]; apply Hactive; [apply Hinc, (Hcomplete j); right; exact Hj |exact Hi].
        -- apply stable_temporal_lift; [exact Hsep | |].
           ++ intros j [Hj | ->]; [apply Hbefore, Hj |exact Hempty].
           ++ intros j; split; [intros H; left; exact H |intros [H | [H | ->]]; [exact H | |exact Hi]].
              apply Hinc, (Hcomplete j); right; exact H.
Qed.

Lemma future_split_from_steps active (R : generalized_memory -> generalized_memory -> generalized_memory -> Prop) :
  (forall out out', generalized_step active out out' -> forall a b, R a b out ->
    exists a' b', generalized_future active a a' /\ generalized_future active b b' /\ R a' b' out') ->
  forall out out', generalized_future active out out' -> forall a b, R a b out ->
    exists a' b', generalized_future active a a' /\ generalized_future active b b' /\ R a' b' out'.
Proof.
  intros Hsplit out out' Hfuture. induction Hfuture; intros left right Hsep.
  - exists left, right. split; [constructor |]. split; [constructor |exact Hsep].
  - destruct (Hsplit _ _ H _ _ Hsep) as [left' [right' [Hl [Hr Hsep']]]].
    destruct (IHHfuture _ _ Hsep') as [left'' [right'' [Hl' [Hr' Hsep'']]]].
    exists left'', right''. split; [eapply generalized_future_trans; eassumption |].
    split; [eapply generalized_future_trans; eassumption |exact Hsep''].
Qed.

Theorem generalized_spatial_future_split active out out' : generalized_future active out out' ->
  forall a b, spatial a b out ->
  exists a' b', generalized_future active a a' /\ generalized_future active b b' /\ spatial a' b' out'.
Proof. apply future_split_from_steps, generalized_spatial_step_split. Qed.

Theorem generalized_temporal_future_split active out out' : generalized_future active out out' ->
  forall a b, repaired_temporal active a b out ->
  exists a' b', generalized_future active a a' /\ generalized_future active b b' /\ repaired_temporal active a' b' out'.
Proof. apply future_split_from_steps, generalized_temporal_step_split. Qed.

Theorem resource_spatial_future_split active (out out' a b : resource active) :
  resource_future active out out' -> spatial (proj1_sig a) (proj1_sig b) (proj1_sig out) ->
  exists a' b' : resource active, resource_future active a a' /\ resource_future active b b' /\
    spatial (proj1_sig a') (proj1_sig b') (proj1_sig out').
Proof.
  intros Hfuture Hsep.
  destruct (generalized_spatial_future_split _ _ _ Hfuture _ _ Hsep) as [a' [b' [Ha [Hb Hout]]]].
  exists (exist _ a' (generalized_future_well_formed _ _ _ Ha (proj2_sig a))),
    (exist _ b' (generalized_future_well_formed _ _ _ Hb (proj2_sig b))).
  split; [exact Ha |]. split; assumption.
Qed.

Theorem resource_temporal_future_split active (out out' a b : resource active) :
  resource_future active out out' -> repaired_temporal active (proj1_sig a) (proj1_sig b) (proj1_sig out) ->
  exists a' b' : resource active, resource_future active a a' /\ resource_future active b b' /\
    repaired_temporal active (proj1_sig a') (proj1_sig b') (proj1_sig out').
Proof.
  intros Hfuture Hsep.
  destruct (generalized_temporal_future_split _ _ _ Hfuture _ _ Hsep) as [a' [b' [Ha [Hb Hout]]]].
  exists (exist _ a' (generalized_future_well_formed _ _ _ Ha (proj2_sig a))),
    (exist _ b' (generalized_future_well_formed _ _ _ Hb (proj2_sig b))).
  split; [exact Ha |]. split; assumption.
Qed.
