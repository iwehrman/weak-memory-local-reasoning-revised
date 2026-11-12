From Stdlib Require Import List ZArith Bool.
From WMLR Require Import Expressions Machine BufferRelations Separation RepairedSeparation
  Assertions AssertionSemantics PersistentAssertions PersistentRules TemporalSafety
  InvariantFragment AssertionAlgebra.
Import ListNotations.

(** The two additional cell schemas in the approved assertion basis.
    Neither proof changes marks or requires a particular writer. *)
Lemma assertion_cell_domain active s r address value loc :
  persistent_models active s r (writer_points_to address value) ->
  eval_expr s address = Z.pos loc ->
  forall l, memory_domain (resource_memory active r) l -> l = loc.
Proof.
  intros HC Eaddress l Hdomain.
  destruct (writer_points_to_shape _ _ _ _ _ HC)
    as (a & owner & Ea & Hi & Hheap & Hbuffers & Hfree & Hmark).
  assert (a = loc) by congruence; subst a.
  destruct Hdomain as [[v Hv] |[i [v Hv]]].
  - rewrite Hheap in Hv; unfold heap_update,empty_heap in Hv.
    destruct (Pos.eq_dec l loc); congruence.
  - rewrite Hbuffers in Hv; contradiction.
Qed.

Theorem assertion_cells_separate active address other old next s r :
  eval_bexpr s (BNot (BEq address other)) = true ->
  (persistent_models active s r
     (A.Temporal (writer_points_to address old) (writer_points_to other next)) <->
   persistent_models active s r
     (A.Spatial (writer_points_to address old) (writer_points_to other next))).
Proof.
  intros Hne. cbn [eval_bexpr] in Hne; apply negb_true_iff in Hne; apply Z.eqb_neq in Hne.
  split; intros (a & b & Hsep & HA & HB);
    pose proof (writer_points_to_shape _ _ _ _ _ HA)
      as (la & ia & Ea & Hia & Hah & Hab & Hak & Ham);
    pose proof (writer_points_to_shape _ _ _ _ _ HB)
      as (lb & ib & Eb & Hib & Hbh & Hbb & Hbk & Hbm);
    exists a,b; split; [|auto | |auto].
  - destruct Hsep as [[Hblocks Hstable] [[_ [Hheap [Hbuffers Hblocked]]] [_ Hmarks]]].
    split; [|exact Hmarks]. split; [split; [|exact Hblocks] |].
    + intros l Hl Hl'.
      pose proof (assertion_cell_domain _ _ _ _ _ _ HA Ea l Hl).
      pose proof (assertion_cell_domain _ _ _ _ _ _ HB Eb l Hl'); congruence.
    + split; [exact Hheap |]. split; [|exact Hblocked].
      intros i; rewrite Hbuffers; apply interleaves_app.
  - apply assertion_spatial_empty_buffers_temporal; assumption.
Qed.

Theorem assertion_cell_overwrite active address old next :
  persistent_entails active
    (A.Temporal (writer_points_to address old) (writer_points_to address next))
    (writer_points_to address next).
Proof.
  intros s r (a & b & [_ [[_ [Hheap [Hbuffers Hblocks]]] [_ Hmarks]]] & HA & HB).
  destruct (writer_points_to_shape _ _ _ _ _ HA)
    as (loc & ia & Ea & Hia & Hah & Hab & Hak & Ham).
  destruct (writer_points_to_shape _ _ _ _ _ HB)
    as (loc' & ib & Eb & Hib & Hbh & Hbb & Hbk & Hbm).
  assert (loc' = loc) by congruence; subst loc'.
  eapply writer_points_to_from_shape with (loc := loc) (owner := ib); [exact Ea |exact Hib | | | |].
  - intros l; rewrite Hheap; unfold heap_override; rewrite Hah,Hbh.
    unfold heap_update,empty_heap; destruct (Pos.eq_dec l loc); reflexivity.
  - intros i; rewrite Hbuffers,Hab,Hbb; reflexivity.
  - intros i H; apply Hblocks in H; destruct H; [exact (Hak i H) |exact (Hbk i H)].
  - apply Hmarks; right; exact Hbm.
Qed.
