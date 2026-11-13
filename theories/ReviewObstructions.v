(** Audited copy of review/Review.v. The historical review file is retained unchanged. *)
From Stdlib Require Import List ZArith.
From WMLR Require Import Expressions Languages Machine BufferRelations Separation
  Assertions AssertionSemantics ConcreteAssertions TransferredCells RetiredHeaps.
Import ListNotations.
Module A := ConcurrentAssertion.

(** * R1. Abstract trilemma: FRAME-TM + consequence + right unit + transfer-out. *)
Section Trilemma.
  Variables (assn cmd state : Type).
  Variable tseq : assn -> assn -> assn.
  Variable emp : assn.
  Variable entails : assn -> assn -> Prop.
  Variable triple : assn -> cmd -> assn -> Prop.
  Variable sat : state -> assn -> Prop.
  Variable run : cmd -> state -> state -> Prop.
  Hypothesis frame_tm : forall R P c Q, triple P c Q -> triple (tseq R P) c (tseq R Q).
  Hypothesis cons_post : forall P c Q Q', triple P c Q -> entails Q Q' -> triple P c Q'.
  Hypothesis emp_right_unit : forall R, entails (tseq R emp) R.
  Hypothesis adequacy : forall P c Q a b, triple P c Q -> sat a P -> run c a b -> sat b Q.

  (** Any transfer-out contract {P} c {emp} can be framed by stale history. *)
  Lemma stale_frame R P c : triple P c emp -> triple (tseq R P) c R.
  Proof. intros H. eapply cons_post; [apply frame_tm, H | apply emp_right_unit]. Qed.

  (** Hence a single execution that starts in [R ; P] and ends outside [R]
      refutes the conjunction of the four hypotheses. *)
  Theorem trilemma R P c a b :
    triple P c emp -> sat a (tseq R P) -> run c a b -> ~ sat b R -> False.
  Proof. intros H Ha Hr Hb. apply Hb. eapply adequacy; [apply stale_frame, H | exact Ha | exact Hr]. Qed.
End Trilemma.

(** * R2. In the retirement interpretation, an ordinary later cell can erase
    an earlier, unrelated live cell: [cell(y) ; cell(x)] does not own [y]. *)
Theorem retired_later_cell_can_erase_earlier active i y x s :
  active i -> x <> y ->
  exists r, RH.models active s r
      (A.Temporal (processor_cell i y 3%Z) (processor_cell i x 7%Z)) /\
    RH.live_heap r y = None.
Proof.
  intros Hi Hne.
  pose (a := RH.singleton i y 3%Z).
  pose (b := RH.take (RH.retire RH.empty y) i x 7%Z).
  assert (Ha : RH.cell i y 3%Z a) by (apply RH.take_vacant_cell; intros l; reflexivity).
  assert (Hb : RH.cell i x 7%Z b).
  { apply RH.take_vacant_cell. intros l. unfold RH.live_heap, RH.retire.
    destruct (Pos.eq_dec l y) as [-> | Hl].
    - rewrite RH.set_same; reflexivity.
    - rewrite RH.set_other by exact Hl; reflexivity. }
  exists (RH.compose a b). split.
  - exists a, b. split; [apply RH.temporal_compose |].
    split; apply RH.processor_cell_intro; assumption.
  - unfold RH.live_heap, RH.compose, b, RH.take; cbn [RH.entries].
    rewrite RH.set_other by (intros E; apply Hne; symmetry; exact E).
    unfold RH.retire. rewrite RH.set_same. reflexivity.
Qed.

(** * R3. History invention in the ORIGINAL interpretation: the model does not
    record history, so a current flushed cell entails any stale earlier value
    at the same address.  Hence [C(x,7)] and [C(x,5) ; C(x,7)] are equivalent. *)
Definition cellm loc v := Memory (heap_update empty_heap loc v) empty_buffers no_blocked.

Theorem original_history_invention active s (r : resource active) i x old v :
  models active s r (processor_cell i x v) ->
  models active s r (A.Temporal (processor_cell i x old) (processor_cell i x v)).
Proof.
  intros Hr. pose proof Hr as Hr0.
  destruct Hr as (a & b & Hab & Ha & Hb).
  change (write_atom active (Z.pos x) (Z.pos i) v (proj1_sig a)) in Ha.
  change (barrier_atom active (Z.pos i) (proj1_sig b)) in Hb.
  destruct Ha as [Hi Ha]. destruct Hb as [[Hbh [Hbb Hbk]] Hbi].
  destruct Hbi as [Hn | Hbi]; [contradiction |].
  destruct Hab as [[_ [Hh [Hbuf Hk]]] [Hbefore Hg]].
  assert (Hci : complete (proj1_sig r) i) by (apply Hg; right; exact Hbi).
  assert (Hheap : forall l, shared_heap (underlying (proj1_sig r)) l = heap_update empty_heap x v l).
  { intros l. rewrite Hh. unfold heap_override. rewrite Hbh.
    destruct Ha as [[_ [Hp _]] | [Hf _]]; [| apply Hf].
    specialize (Hbefore i Hbi). rewrite Hp, buffer_update_same in Hbefore. discriminate. }
  destruct (proj2_sig r) as [_ [Hact _]].
  assert (Hcw : generalized_well_formed active (Generalized (cellm x old) (complete (proj1_sig r)))).
  { split; [split; simpl; [intros j H; contradiction | reflexivity] |].
    split; [exact Hact | intros Hnone; exfalso; exact (Hnone i Hci)]. }
  assert (Hew : generalized_well_formed active (Generalized empty_memory (complete (proj1_sig r)))).
  { split; [split; simpl; [intros j H; contradiction | reflexivity] |].
    split; [exact Hact | reflexivity]. }
  exists (exist _ _ Hcw), r. split; [| split; [| exact Hr0]].
  - simpl. split; [split | split].
    + split; [intros j H; contradiction |]. split.
      * intros j _ l [w Hw]; contradiction.
      * intros j k _ _ _ l [w Hw]; contradiction.
    + split.
      * intros l. unfold heap_override. simpl. rewrite (Hheap l).
        unfold heap_update, empty_heap. destruct (Pos.eq_dec l x); reflexivity.
      * split; [intros j; reflexivity | intros j; simpl; unfold no_blocked; tauto].
    + intros j _; reflexivity.
    + intros j; simpl; tauto.
  - exists (exist _ _ Hcw), (exist _ _ Hew). split; [| split].
    + simpl. split; [split | split].
      * split; [intros j H; contradiction |]. split.
        -- intros j _ l [w Hw]; contradiction.
        -- intros j k _ _ _ l [w Hw]; contradiction.
      * split; [intros l; reflexivity |].
        split; [intros j; reflexivity | intros j; simpl; unfold no_blocked; tauto].
      * intros j _; reflexivity.
      * intros j; simpl; tauto.
    + change (write_atom active (Z.pos x) (Z.pos i) old (Generalized (cellm x old) (complete (proj1_sig r)))).
      split; [exact Hi |]. right. repeat split; simpl; auto. intros j H; exact H.
    + change (barrier_atom active (Z.pos i) (Generalized empty_memory (complete (proj1_sig r)))).
      split; [repeat split; simpl; auto; intros j H; exact H | right; exact Hci].
Qed.
