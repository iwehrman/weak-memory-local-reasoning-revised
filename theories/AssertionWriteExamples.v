From Stdlib Require Import List ZArith.
From WMLR Require Import Expressions Machine Separation Assertions AssertionSemantics ConcreteAssertions
  PersistentAssertions PersistentRules TemporalSafety ExecutionExamples InvariantFragment InvariantFragmentExamples
  OwnedAcceptance OwnedHeapExamples AssertionBarrierAlgebra AssertionWriteAlgebra.
Import ListNotations.

Lemma assertion_full_cell_points_to s :
  persistent_models two_processors s checkpoint_full_cell (A.points_to (EVal 2%Z) (EVal 7%Z)).
Proof.
  exists checkpoint_full_cell,(assertion_empty_mark_meet two_processors checkpoint_full_cell checkpoint_full_cell).
  split.
  - apply assertion_empty_suffix_intro.
    + split; [intros; reflexivity |]. split; [intros; reflexivity |intros i H; exact H].
    + intros; reflexivity.
    + intros i [H _]; exact H.
  - split.
    + exists 1%Z; change (write_atom two_processors 2%Z 1%Z 7%Z (proj1_sig checkpoint_full_cell)).
      split; [left; reflexivity |right]. split; [intros; reflexivity |].
      split; [intros; reflexivity |]. split; [intros i H; exact H |left; reflexivity].
    + intros v; change (barrier_atom two_processors v
        (proj1_sig (assertion_empty_mark_meet two_processors checkpoint_full_cell checkpoint_full_cell))).
      split.
      * split; [intros; reflexivity |]. split; [intros; reflexivity |intros i H; exact H].
      * destruct v as [|owner|neg]; try exact I.
        destruct (Pos.eq_dec owner 1%positive) as [-> |H1].
        -- right; split; left; reflexivity.
        -- destruct (Pos.eq_dec owner 2%positive) as [-> |H2].
           ++ right; split; right; reflexivity.
           ++ left; intros [H |H]; contradiction.
Qed.

(** T4 as literally printed fails for a nonprocessor or inactive annotation,
    despite an inhabited all-processor cell. EVal 0 and EVal 3 are examples. *)
Theorem assertion_points_to_invalid_writer_refuted annotation :
  (forall owner, annotation = Z.pos owner -> ~ two_processors owner) ->
  ~ persistent_entails two_processors (A.points_to (EVal 2%Z) (EVal 7%Z))
      (A.LeadsTo (EVal 2%Z) (EVal annotation) (EVal 7%Z)).
Proof.
  intros Hinvalid H; specialize (H (fun _ => 0%Z) checkpoint_full_cell
    (assertion_full_cell_points_to (fun _ => 0%Z))).
  destruct annotation as [|owner|neg]; try contradiction.
  exact (Hinvalid owner eq_refl (proj1 H)).
Qed.

(** The weaker cell's failure already occurs for a different active writer. *)
Theorem assertion_writer_cell_foreign_write_refuted :
  ~ persistent_entails two_processors (writer_points_to (EVal 2%Z) (EVal 7%Z))
      (A.LeadsTo (EVal 2%Z) (EVal 2%Z) (EVal 7%Z)).
Proof.
  intros H; apply (heap_foreign_cell_not_second_write (fun _ => 0%Z)),H,acceptance_cell_models.
Qed.
