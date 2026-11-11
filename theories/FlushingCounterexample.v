From Stdlib Require Import List ZArith.
From WMLR Require Import Expressions Machine Separation StableCompatibility RepairedSeparation
  Assertions AssertionSemantics ConcreteAssertions ExecutionExamples RepairedAssertions.
Import ListNotations.

(** The pointwise temporal wand is not flushing closed. A pending buffer
    cannot precede a complete barrier, so the wand to false holds vacuously.
    Flushing enables that composition and falsifies the wand. This problem
    comes from the temporal completeness condition, not the stable guard. *)
Definition wand_pending_memory := Memory empty_heap
  (buffer_update empty_buffers 1%positive [(1%positive, 7%Z)]) no_blocked.
Definition wand_flushed_memory := flush_write wand_pending_memory 1%positive 1%positive 7%Z [].
Definition impossible_future := ConcurrentAssertion.TemporalWandRight
  (ConcurrentAssertion.Pure BFalse) (ConcurrentAssertion.Barrier (EVal 1%Z)).

Lemma wand_pending_valid : generalized_well_formed two_processors
  (Generalized wand_pending_memory two_processors).
Proof.
  split; [split | split].
  - intros i H; contradiction.
  - intros i H. cbn [underlying wand_pending_memory buffers]; unfold buffer_update.
    destruct (Pos.eq_dec i 1%positive) as [-> |Hneq]; [exfalso; apply H; left; reflexivity |reflexivity].
  - intros i Hi; exact Hi.
  - intros H loc; exfalso; apply (H 1%positive); left; reflexivity.
Qed.

Lemma wand_actual_flush : flush two_processors wand_pending_memory wand_flushed_memory.
Proof. constructor; [left; reflexivity | intros H; contradiction | apply buffer_update_same]. Qed.

Definition wand_pending_resource : resource two_processors :=
  exist _ (Generalized wand_pending_memory two_processors) wand_pending_valid.
Definition wand_flushed_resource : resource two_processors :=
  exist _ (Generalized wand_flushed_memory two_processors)
    (full_generalized_flush_well_formed _ _ _ wand_pending_valid wand_actual_flush).

Lemma wand_barrier_valid : generalized_well_formed two_processors (Generalized empty_memory two_processors).
Proof.
  split; [exact (proj1 (empty_generalized_well_formed two_processors)) |].
  split; [intros i Hi; exact Hi |intros; reflexivity].
Qed.

Definition wand_barrier_resource : resource two_processors :=
  exist _ (Generalized empty_memory two_processors) wand_barrier_valid.

Lemma impossible_future_before s : repaired_models two_processors s wand_pending_resource impossible_future.
Proof.
  intros future out [_ Hbar] [_ [_ [Hbefore _]]].
  destruct Hbar as [Hinactive | Hcomplete]; [exfalso; apply Hinactive; left; reflexivity |].
  specialize (Hbefore 1%positive Hcomplete).
  change (buffer_update empty_buffers 1%positive [(1%positive, 7%Z)] 1%positive = []) in Hbefore.
  rewrite buffer_update_same in Hbefore; discriminate.
Qed.

Lemma wand_flushed_buffers i : buffers wand_flushed_memory i = [].
Proof.
  unfold wand_flushed_memory, wand_pending_memory, flush_write; simpl.
  unfold buffer_update. destruct (Pos.eq_dec i 1%positive); reflexivity.
Qed.

Lemma wand_after_barrier_composition :
  repaired_temporal two_processors (proj1_sig wand_flushed_resource)
    (proj1_sig wand_barrier_resource) (proj1_sig wand_flushed_resource).
Proof.
  split.
  - split; [intros i H; contradiction |]. split.
    + intros i _ loc [v H]; rewrite wand_flushed_buffers in H; contradiction.
    + intros i j _ _ _ loc [v H]; rewrite wand_flushed_buffers in H; contradiction.
  - split.
    + split.
      * apply stable_implies_printed_compatible. split; [intros i H; contradiction |]. split.
        -- intros i _ loc [v H]; rewrite wand_flushed_buffers in H; contradiction.
        -- intros i j _ _ _ loc [v H]; rewrite wand_flushed_buffers in H; contradiction.
      * split; [intros loc; reflexivity |]. split.
        -- intros i; change (buffers wand_flushed_memory i = buffers wand_flushed_memory i ++ []).
           rewrite app_nil_r; reflexivity.
        -- intros i; simpl; unfold no_blocked; tauto.
    + split; [intros i _; apply wand_flushed_buffers |].
      intros i; simpl; tauto.
Qed.

Lemma impossible_future_after s : ~ repaired_models two_processors s wand_flushed_resource impossible_future.
Proof.
  intros Hwand.
  assert (Hbar : repaired_models two_processors s wand_barrier_resource
    (ConcurrentAssertion.Barrier (EVal 1%Z))).
  { split.
    - split; [intros; reflexivity |]. split; [intros; reflexivity | intros i H; contradiction].
    - right; left; reflexivity. }
  specialize (Hwand _ _ Hbar wand_after_barrier_composition). discriminate.
Qed.

Theorem pointwise_temporal_wand_not_flush_closed s :
  flush two_processors (underlying (proj1_sig wand_pending_resource))
    (underlying (proj1_sig wand_flushed_resource)) /\
  repaired_models two_processors s wand_pending_resource impossible_future /\
  ~ repaired_models two_processors s wand_flushed_resource impossible_future.
Proof. split; [apply wand_actual_flush |]. split; [apply impossible_future_before | apply impossible_future_after]. Qed.
