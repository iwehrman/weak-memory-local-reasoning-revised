From Stdlib Require Import List ZArith.
From WMLR Require Import Expressions Languages Machine Separation RepairedSeparation
  OperationalSemantics Assertions AssertionSemantics ConcreteAssertions PersistentAssertions
  PersistentRules Specifications InvariantFragment OwnedSafety OwnedCalculus OwnedHeap
  OwnedContainerEntailments AssertionResourceEquivalence AssertionUnits AssertionAlgebra
  AssertionBarrierAlgebra.
Import ListNotations.

(** Exact all-processor LOAD-P and the corrected STORE-P (a store command,
    with a temporal, not strong-temporal, write suffix). No new axiom.
    The proof carries completeness as an empty spatial frame. *)
Definition alternative_all_barriers := A.Forall 0 (A.Barrier (EVar 0)).

Lemma alternative_all_barriers_shape active s r :
  persistent_models active s r alternative_all_barriers <->
  empty_atom (proj1_sig r) /\ (forall i, ~ active i \/ complete (proj1_sig r) i).
Proof.
  split.
  - intros H; split.
    + exact (proj1 (H 0%Z)).
    + intros i; specialize (H (Z.pos i)).
      change (barrier_atom active (update s 0 (Z.pos i) 0) (proj1_sig r)) in H.
      rewrite update_same in H; exact (proj2 H).
  - intros [HE HM] v; change (barrier_atom active (update s 0 v 0) (proj1_sig r)).
    rewrite update_same; split; [exact HE |destruct v; try exact I; apply HM].
Qed.

Lemma alternative_all_barriers_frame active p s r :
  persistent_models active s r (A.Spatial alternative_all_barriers p) <->
  persistent_models active s r p /\ (forall i, ~ active i \/ complete (proj1_sig r) i).
Proof.
  split.
  - intros H; split.
    + apply (proj1 (assertion_unit_spatial_left active p s r)).
      eapply container_spatial_mono; [|intros t a HP; exact HP |exact H].
      intros t a HA; exact (proj1 (proj1 (alternative_all_barriers_shape _ _ _) HA)).
    + destruct H as (a & b & Hsp & HA & HP).
      intros i; destruct (proj2 (proj1 (alternative_all_barriers_shape _ _ _) HA) i) as [H |H].
      * left; exact H.
      * right; apply (proj2 Hsp); left; exact H.
  - intros [HP HM].
    exists (assertion_empty_mark_meet active r r),r; split.
    + split; [exact (proj1 (spatial_empty_left (proj1_sig r))) |].
      intros i; cbn; tauto.
    + split; [apply alternative_all_barriers_shape |exact HP].
      split; [split; [intros; reflexivity |split; [intros; reflexivity |intros i H; exact H]] |].
      intros i; destruct (HM i); [left; assumption |right; split; assumption].
Qed.

Lemma alternative_points_to_complete active address value s r :
  persistent_models active s r (A.points_to address value) ->
  forall i, ~ active i \/ complete (proj1_sig r) i.
Proof.
  intros (a & b & [_ [_ [_ Hmarks]]] & HW & HB) i.
  specialize (HB (Z.pos i)).
  change (barrier_atom active
    (update s (fresh (expr_fv address ++ expr_fv value)) (Z.pos i)
      (fresh (expr_fv address ++ expr_fv value))) (proj1_sig b)) in HB.
  rewrite update_same in HB; destruct (proj2 HB); [left; assumption |right; apply Hmarks; auto].
Qed.

Lemma alternative_points_to_writer active address value :
  persistent_entails active (A.points_to address value) (writer_points_to address value).
Proof.
  intros s r HP; apply assertion_wand_free_in_printed in HP;
    [|cbn [A.points_to wand_free]; tauto].
  destruct (points_to_requires_flushed _ _ _ _ _ HP)
    as (loc & owner & E & Hi & [Hh [Hb [Hk Hm]]] & Hall).
  eapply writer_points_to_from_shape; eassumption.
Qed.

Lemma alternative_writer_complete_points_to active address value s r :
  persistent_models active s r (writer_points_to address value) ->
  (forall i, ~ active i \/ complete (proj1_sig r) i) ->
  persistent_models active s r (A.points_to address value).
Proof.
  intros HC HM; destruct (writer_points_to_shape _ _ _ _ _ HC)
    as (loc & owner & E & Hi & Hh & Hb & Hk & Hm).
  pose (bar := assertion_empty_mark_meet active r r).
  assert (HE : empty_atom (proj1_sig bar)).
  { split; [intros; reflexivity |split; [intros; reflexivity |intros i H; exact H]]. }
  exists r,bar; split.
  - apply assertion_empty_suffix_intro; [exact HE |intros; apply Hb |intros i H; exact (proj1 H)].
  - split.
    + exists (Z.pos owner).
      change (write_atom active
        (eval_expr (update s (fresh (expr_fv address ++ expr_fv value)) (Z.pos owner)) address)
        (update s (fresh (expr_fv address ++ expr_fv value)) (Z.pos owner)
          (fresh (expr_fv address ++ expr_fv value)))
        (eval_expr (update s (fresh (expr_fv address ++ expr_fv value)) (Z.pos owner)) value) (proj1_sig r)).
      destruct (A.points_to_binder_fresh address value) as [HA HV].
      rewrite update_same,!eval_expr_update_irrelevant by assumption.
      rewrite E; split; [exact Hi |right; split; [exact Hh |split; [exact Hb |split; assumption]]].
    + intros v.
      change (barrier_atom active
        (update s (fresh (expr_fv address ++ expr_fv value)) v
          (fresh (expr_fv address ++ expr_fv value))) (proj1_sig bar)).
      rewrite update_same; split; [exact HE |].
      destruct v; try exact I; destruct (HM p); [left; assumption |right; split; assumption].
Qed.

Lemma alternative_strong_points_to_complete active address value tail s r :
  persistent_models active s r (A.strong_temporal (writer_points_to address value) tail) ->
  (forall i, ~ active i \/ complete (proj1_sig r) i) ->
  persistent_models active s r (A.strong_temporal (A.points_to address value) tail).
Proof.
  intros [Hsp Htm] HM; split.
  - destruct Hsp as (a & b & [Hmerge Hmarks] & HC & HP).
    exists (assertion_add_marks active a r),b; split.
    + split; [exact Hmerge |intros i; cbn; rewrite (Hmarks i); tauto].
    + split; [apply alternative_writer_complete_points_to |exact HP].
      * apply assertion_models_add_marks,HC.
      * intros i; destruct (HM i); [left; assumption |right; right; assumption].
  - destruct Htm as (a & b & [Hstable [Hmerge [Hbefore Hmarks]]] & HC & HP).
    exists (assertion_add_marks active a r),b; split.
    + split; [exact Hstable |split; [exact Hmerge |split; [exact Hbefore |]]].
      intros i; cbn; rewrite (Hmarks i); tauto.
    + split; [apply alternative_writer_complete_points_to |exact HP].
      * apply assertion_models_add_marks,HC.
      * intros i; destruct (HM i); [left; assumption |right; right; assumption].
Qed.

Lemma alternative_points_to_strong_frame active address value tail s r :
  persistent_models active s r (A.strong_temporal (A.points_to address value) tail) <->
  persistent_models active s r
    (A.Spatial alternative_all_barriers (A.strong_temporal (writer_points_to address value) tail)).
Proof.
  rewrite alternative_all_barriers_frame; split.
  - intros H; split.
    + eapply assertion_conjunction_mono with (kind := StrongKind);
        [apply alternative_points_to_writer |intros t a HP; exact HP |exact H].
    + destruct H as [(a & b & Hsp & HC & HP) Htm]; intros i.
      destruct (alternative_points_to_complete _ _ _ _ _ HC i); [left; assumption |].
      right; apply (proj2 Hsp); left; assumption.
  - intros [H HM]; apply alternative_strong_points_to_complete; assumption.
Qed.

Lemma alternative_all_barriers_temporal_left active p q :
  persistent_entails active (A.Spatial alternative_all_barriers (A.Temporal p q))
    (A.Temporal (A.Spatial alternative_all_barriers p) q).
Proof.
  intros s r H; apply alternative_all_barriers_frame in H.
  destruct H as [(a & b & [Hstable [Hmerge [Hbefore Hmarks]]] & HP & HQ) HM].
  exists (assertion_add_marks active a r),b; split.
  - split; [exact Hstable |split; [exact Hmerge |split; [exact Hbefore |]]].
    intros i; cbn; rewrite (Hmarks i); tauto.
  - split; [apply alternative_all_barriers_frame |exact HQ].
    split; [apply assertion_models_add_marks,HP |].
    intros i; destruct (HM i); [left; assumption |right; right; assumption].
Qed.

Theorem owned_derive_load_points_to active invariant mode address value annotation tail x :
  ~ In x (A.fv invariant) -> ~ In x (expr_fv address ++ expr_fv value ++ A.fv tail) ->
  owned_derivation active invariant mode
    (A.strong_temporal (A.points_to address value) tail)
    (C.Prim (C.Common (S.Load x address)) annotation)
    (A.And (A.strong_temporal (A.points_to address value) tail) (A.Pure (BEq (EVar x) value))).
Proof.
  intros HJ Hfresh; eapply OwnedConsequence with
    (pre' := A.Spatial alternative_all_barriers (A.strong_temporal (writer_points_to address value) tail)).
  - intros s r H; apply alternative_points_to_strong_frame,H.
  - apply OwnedFrameSP; [apply OwnedLoadAny; assumption |].
    intros y Hy Hfv; cbn [alternative_all_barriers A.fv expr_fv] in Hfv; contradiction.
  - intros s r (a & b & Hsp & HA & HP & Hb); split; [|exact Hb].
    apply alternative_points_to_strong_frame; exists a,b; auto.
Qed.

Theorem owned_derive_store_points_to active invariant mode address old value annotation tail :
  owned_derivation active invariant mode
    (A.strong_temporal (A.points_to address old) tail)
    (C.Prim (C.Common (S.Store address value)) annotation)
    (A.Temporal (A.strong_temporal (A.points_to address old) tail)
      (A.LeadsTo address annotation value)).
Proof.
  eapply OwnedConsequence with
    (pre' := A.Spatial alternative_all_barriers (A.strong_temporal (writer_points_to address old) tail)).
  - intros s r H; apply alternative_points_to_strong_frame,H.
  - apply OwnedFrameSP; [apply OwnedStoreAny |intros x H; contradiction].
  - intros s r H; apply alternative_all_barriers_temporal_left in H.
    eapply container_temporal_mono; [|intros t a HW; exact HW |exact H].
    intros t a HP; apply alternative_points_to_strong_frame,HP.
Qed.
