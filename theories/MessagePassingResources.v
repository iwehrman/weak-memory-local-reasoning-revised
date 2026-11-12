From Stdlib Require Import List ZArith.
From WMLR Require Import Expressions Languages Machine BufferRelations Separation
  OperationalSemantics ExecutionExamples Assertions AssertionSemantics PersistentAssertions
  TemporalSafety InvariantFragment PrivateOwnership SpatialExchange LockRepresentation
  OwnedAcceptance HeapExtension MessagePassingSyntax.
Import ListNotations.

Definition mp_plain (h : heap) := Memory h empty_buffers no_blocked.
Definition mp_single loc value := heap_update empty_heap loc value.
Definition mp_tokens t r := heap_override (mp_single t 0%Z) (mp_single r 0%Z).
Definition mp_initial loc := mp_plain (mp_single loc 0%Z).
Definition mp_augmented loc t r := mp_plain (heap_override (mp_single loc 0%Z) (mp_tokens t r)).

Definition mp_full (h : heap) : resource two_processors.
Proof.
  refine (exist _ (Generalized (mp_plain h) two_processors) _).
  split; [split; [intros i H; contradiction |intros; reflexivity] |].
  split; [intros i H; exact H |].
  intros Hnone loc; exfalso; exact (Hnone 1%positive (or_introl eq_refl)).
Defined.

Lemma mp_plain_domain h loc : memory_domain (mp_plain h) loc <-> heap_domain h loc.
Proof. split; [intros [H |[i [v H]]]; [exact H |contradiction] |intros H; left; exact H]. Qed.

Lemma mp_single_domain loc value address : heap_domain (mp_single loc value) address <-> address = loc.
Proof.
  unfold heap_domain,mp_single,heap_update; destruct (Pos.eq_dec address loc); split;
    intros H; try assumption; try contradiction; try (exists value; reflexivity).
  destruct H as [v H]; discriminate.
Qed.

Lemma mp_plain_spatial a b : BufferRelations.disjoint (heap_domain a) (heap_domain b) ->
  memory_spatial (mp_plain a) (mp_plain b) (mp_plain (heap_override a b)).
Proof.
  intros HD; split.
  - split; [intros l Ha Hb; apply (HD l); apply mp_plain_domain; assumption |intros i H _; exact H].
  - split; [intros; reflexivity |split; [intros; constructor |intros i; cbn; unfold no_blocked; tauto]].
Qed.

Lemma mp_full_cell s address value loc : eval_expr s address = Z.pos loc ->
  persistent_models two_processors s (mp_full (mp_single loc (eval_expr s value)))
    (writer_points_to address value).
Proof.
  intros E; eapply writer_points_to_from_shape with (loc := loc) (owner := 1%positive);
    [exact E |left; reflexivity |intros; reflexivity |intros; reflexivity |intros i H; exact H |left; reflexivity].
Qed.

Lemma mp_tokens_models s t r : t <> r ->
  persistent_models two_processors s (mp_full (mp_tokens t r)) (A.Spatial (mp_token t) (mp_token r)).
Proof.
  intros Hne; exists (mp_full (mp_single t 0%Z)),(mp_full (mp_single r 0%Z)); split.
  - split; [apply mp_plain_spatial |intros i; cbn; tauto].
    intros l HT HR; apply mp_single_domain in HT; apply mp_single_domain in HR; congruence.
  - split; apply mp_full_cell; reflexivity.
Qed.

Lemma mp_augmented_split loc t r : loc <> t -> loc <> r ->
  memory_spatial (mp_initial loc) (mp_plain (mp_tokens t r)) (mp_augmented loc t r).
Proof.
  intros Ht Hr; apply mp_plain_spatial; intros l HD [v HV].
  apply mp_single_domain in HD; subst l.
  unfold mp_tokens,mp_single,heap_override,heap_update,empty_heap in HV.
  destruct (Pos.eq_dec loc r), (Pos.eq_dec loc t); congruence.
Qed.

Lemma mp_augmented_extension loc t r : loc <> t -> loc <> r ->
  heap_extension (mp_tokens t r) (mp_initial loc) (mp_augmented loc t r).
Proof.
  intros Ht Hr; split.
  - intros l; cbn [mp_augmented mp_initial mp_plain shared_heap].
    unfold mp_tokens,mp_single,heap_override,heap_update.
    destruct (Pos.eq_dec l loc), (Pos.eq_dec l t), (Pos.eq_dec l r); subst; try congruence; reflexivity.
  - split; intros; reflexivity.
Qed.

Lemma mp_cell_shape active s local address value loc : eval_expr s address = Z.pos loc ->
  persistent_models active s local (writer_points_to address value) ->
  memory_equiv (resource_memory active local) (mp_plain (mp_single loc (eval_expr s value))).
Proof.
  intros E HC; destruct (writer_points_to_shape _ _ _ _ _ HC)
    as (l & owner & El & Hi & Hh & Hb & Hfree & Hmark).
  assert (l = loc) by congruence; subst l; split; [exact Hh |split; [exact Hb |]].
  intros i; split; [intros H; exfalso; exact (Hfree i H) |intros H; contradiction].
Qed.

Lemma mp_spatial_shape a b out ha hb : memory_spatial a b out ->
  memory_equiv a (mp_plain ha) -> memory_equiv b (mp_plain hb) ->
  memory_equiv out (mp_plain (heap_override ha hb)).
Proof.
  intros [_ [Hh [Hb Hk]]] [Ha [Ba Ka]] [Hbb [Bb Kb]]; split.
  - intros l; rewrite Hh; unfold heap_override; rewrite Ha,Hbb; reflexivity.
  - split.
    + intros i; specialize (Hb i); rewrite Ba,Bb in Hb; apply interleaves_nil_left,Hb.
    + intros i; rewrite Hk,Ka,Kb; cbn; unfold no_blocked; tauto.
Qed.

Lemma mp_invariant_shape s pool loc t r : s 1 = Z.pos loc ->
  persistent_full_satisfies two_processors s pool (mp_invariant t r) ->
  memory_equiv pool (mp_plain (mp_single loc 0%Z)) \/
  memory_equiv pool (mp_plain (heap_override (mp_single loc 1%Z) (mp_single t 0%Z))) \/
  memory_equiv pool (mp_plain (mp_tokens t r)).
Proof.
  intros E [local [El HJ]].
  assert (Em : resource_memory two_processors local = pool) by (unfold resource_memory; rewrite El; reflexivity).
  destruct HJ as [HD |[HT |HR]].
  - left; rewrite <- Em; exact (mp_cell_shape two_processors s local mp_address (EVal 0%Z) loc E HD).
  - right; left; destruct HT as (a & b & [HS HM] & HA & HB); rewrite <- Em.
    eapply mp_spatial_shape; [exact HS |exact (mp_cell_shape two_processors s a mp_address (EVal 1%Z) loc E HA)
      |exact (mp_cell_shape two_processors s b (EVal (Z.pos t)) (EVal 0%Z) t eq_refl HB)].
  - right; right; destruct HR as (a & b & [HS HM] & HA & HB); rewrite <- Em.
    eapply mp_spatial_shape; [exact HS |exact (mp_cell_shape two_processors s a (EVal (Z.pos t)) (EVal 0%Z) t eq_refl HA)
      |exact (mp_cell_shape two_processors s b (EVal (Z.pos r)) (EVal 0%Z) r eq_refl HB)].
Qed.

Lemma mp_received_shape s local loc r value : s 1 = Z.pos loc ->
  persistent_models two_processors s local (mp_received r value) ->
  (s 0 = 0%Z /\ memory_equiv (resource_memory two_processors local) (mp_plain (mp_single r 0%Z))) \/
  (s 0 = 1%Z /\ memory_equiv (resource_memory two_processors local) (mp_plain (mp_single loc value))).
Proof.
  intros E [[HC HB] |[HC HB]]; [left |right]; split.
  - apply Z.eqb_eq,HB.
  - exact (mp_cell_shape two_processors s local (EVal (Z.pos r)) (EVal 0%Z) r eq_refl HC).
  - apply Z.eqb_eq,HB.
  - exact (mp_cell_shape two_processors s local mp_address (EVal value) loc E HC).
Qed.

Lemma mp_shape_domain m h loc : memory_equiv m (mp_plain h) ->
  (memory_domain m loc <-> heap_domain h loc).
Proof.
  intros [Hh [Hb Hk]]; split.
  - intros [[v H] |[i [v H]]]; [exists v; rewrite <- Hh; exact H |rewrite Hb in H; contradiction].
  - intros [v H]; left; exists v; rewrite Hh; exact H.
Qed.

Lemma mp_shapes_disjoint a b out ha hb : memory_spatial a b out ->
  memory_equiv a (mp_plain ha) -> memory_equiv b (mp_plain hb) ->
  BufferRelations.disjoint (heap_domain ha) (heap_domain hb).
Proof.
  intros [[HD HK] HM] HA HB l HLa HLb; apply (HD l);
    [apply (proj2 (mp_shape_domain _ _ _ HA)),HLa |apply (proj2 (mp_shape_domain _ _ _ HB)),HLb].
Qed.

Lemma mp_shape_free m h : memory_equiv m (mp_plain h) -> lock_free m.
Proof. intros [Hh [Hb Hk]] i H; apply Hk in H; exact H. Qed.
