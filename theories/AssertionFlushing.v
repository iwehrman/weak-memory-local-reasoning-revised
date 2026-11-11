From Stdlib Require Import List ZArith.
From WMLR Require Import Expressions Machine BufferRelations Separation
  OrderedSeparation GeneralizedFlushing ConcreteAssertions.
Import ListNotations.

Lemma generalized_future_complete active a b : generalized_future active a b ->
  forall i, complete a i -> complete b i.
Proof.
  induction 1; intros i Hi; [exact Hi |]. apply IHgeneralized_future.
  destruct H as [m before after Hinc Hactive |m m' before after j Hflush Hinc Hactive Hj];
    apply Hinc, Hi.
Qed.

Lemma no_buffers_cannot_flush active i m m' :
  (forall j, buffers m j = []) -> ~ flush_at active i m m'.
Proof. intros Hempty Hflush; destruct Hflush; rewrite Hempty in H1; discriminate. Qed.

Lemma future_without_buffers active a b : generalized_future active a b ->
  (forall i, buffers (underlying a) i = []) -> underlying b = underlying a.
Proof.
  induction 1; intros Hempty; [reflexivity |].
  destruct H.
  - apply IHgeneralized_future, Hempty.
  - exfalso; eapply no_buffers_cannot_flush; [exact Hempty | exact H].
Qed.

Theorem empty_atom_future active a b :
  generalized_future active a b -> empty_atom a -> empty_atom b.
Proof.
  intros Hfuture [Hheap [Hbuffers Hfree]].
  pose proof (future_without_buffers _ _ _ Hfuture Hbuffers) as Hsame.
  unfold empty_atom; rewrite Hsame. split; [exact Hheap |]. split; assumption.
Qed.

Theorem barrier_atom_future active value a b :
  generalized_future active a b -> barrier_atom active value a -> barrier_atom active value b.
Proof.
  intros Hfuture [Hempty Hbar]. split; [eapply empty_atom_future; eassumption |].
  destruct value; try exact I. destruct Hbar as [Hi | Hi]; [left; exact Hi |right].
  exact (generalized_future_complete _ _ _ Hfuture _ Hi).
Qed.

Theorem lock_atom_future active value a b :
  generalized_future active a b -> lock_atom active value a -> lock_atom active value b.
Proof.
  intros Hfuture Hlock. destruct value; try contradiction.
  destruct Hlock as [Hheap [Hbuffers Hheld]].
  pose proof (future_without_buffers _ _ _ Hfuture Hbuffers) as Hsame.
  change ((forall loc, shared_heap (underlying b) loc = None) /\
    (forall i, buffers (underlying b) i = []) /\ lock_held active (underlying b) p).
  rewrite Hsame. split; [exact Hheap |]. split; assumption.
Qed.

Lemma write_atom_step active address processor_value contents a b :
  generalized_step active a b -> write_atom active address processor_value contents a ->
  write_atom active address processor_value contents b.
Proof.
  intros Hstep Hwrite. destruct address as [|loc|negative]; try contradiction;
    destruct processor_value as [|owner|negative_owner]; try contradiction.
  destruct Hwrite as [Howner Hwrite]. split; [exact Howner |].
  destruct Hstep as [m before after Hinc Hactive |m m' before after i Hflush Hinc Hactive Hi].
  - destruct Hwrite as [Hpending |[Hheap [Hbuffers [Hfree Hcomplete]]]].
    + left; exact Hpending.
    + right; split; [exact Hheap |]. split; [exact Hbuffers |]. split; [exact Hfree |apply Hinc, Hcomplete].
  - destruct Hwrite as [[Hheap [Hbuffers Hblocks]] |[Hheap [Hbuffers Hrest]]].
    + destruct Hflush as [m address v rest Hprocessor Hlive Hhead].
      cbn [underlying] in Hheap, Hbuffers, Hblocks.
      rewrite Hbuffers in Hhead. unfold buffer_update in Hhead.
      destruct (Pos.eq_dec i owner) as [-> | Hneq]; [|discriminate].
      inversion Hhead; subst address v rest. right. split.
      * intros address. cbn [underlying flush_write shared_heap].
        apply heap_update_pointwise, Hheap.
      * split.
        -- intros j. cbn [underlying flush_write buffers]. unfold buffer_update.
           destruct (Pos.eq_dec j owner) as [-> | Hneq]; [reflexivity |].
           rewrite Hbuffers. unfold buffer_update. destruct (Pos.eq_dec j owner); [contradiction |reflexivity].
        -- split.
           ++ intros j Hj. pose proof (Hblocks j Hj) as Heq; subst j. apply Hlive, Hj.
           ++ exact Hi.
    + exfalso; eapply no_buffers_cannot_flush; [exact Hbuffers | exact Hflush].
Qed.

Theorem write_atom_future active address processor_value contents a b :
  generalized_future active a b -> write_atom active address processor_value contents a ->
  write_atom active address processor_value contents b.
Proof.
  induction 1; intros Hwrite; [exact Hwrite |].
  apply IHgeneralized_future; eapply write_atom_step; eassumption.
Qed.
