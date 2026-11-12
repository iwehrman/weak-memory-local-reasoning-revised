From Stdlib Require Import List ZArith.
From WMLR Require Import Expressions Languages Machine BufferRelations Separation
  RepairedSeparation GeneralizedFlushing SpatialExchange Assertions AssertionSemantics
  ConcreteAssertions RepairedAssertions PersistentAssertions PersistentRules Safety
  PrivateOwnership TemporalSafety TemporalFence RegionalResources InvariantFragment
  InvariantCompleteness OwnershipTransfer TemporalTransfer OwnershipHeap OwnedRules OwnedHeap StrongTemporalCounterexample.
Import ListNotations.

(** Assertion lemmas used by the container. These are entailments in the
    existing interpretation, not additional assertion or validity predicates. *)
Lemma container_spatial_mono active p p' q q' :
  persistent_entails active p p' -> persistent_entails active q q' ->
  persistent_entails active (A.Spatial p q) (A.Spatial p' q').
Proof.
  intros HP HQ s r (a & b & Hsp & Ha & Hb); exists a, b; split; [exact Hsp |].
  split; [apply HP, Ha |apply HQ, Hb].
Qed.

Lemma container_temporal_mono active p p' q q' :
  persistent_entails active p p' -> persistent_entails active q q' ->
  persistent_entails active (A.Temporal p q) (A.Temporal p' q').
Proof.
  intros HP HQ s r (a & b & Htm & Ha & Hb); exists a, b; split; [exact Htm |].
  split; [apply HP, Ha |apply HQ, Hb].
Qed.

Lemma container_spatial_comm active p q :
  persistent_entails active (A.Spatial p q) (A.Spatial q p).
Proof.
  intros s r (a & b & Hsp & Ha & Hb); exists b, a; split; [apply spatial_comm, Hsp |auto].
Qed.

Lemma container_spatial_assoc active p q t s r :
  persistent_models active s r (A.Spatial p (A.Spatial q t)) <->
  persistent_models active s r (A.Spatial (A.Spatial p q) t).
Proof.
  split.
  - intros (a & bc & [Hout Gout] & Ha & b & c & [Hbc Gbc] & Hb & Hc).
    destruct (proj1 (memory_spatial_associative _ _ _ _)
      (ex_intro _ _ (conj Hbc Hout))) as (ab & Hab & Hout').
    pose (g := Generalized ab (fun i => complete (proj1_sig a) i \/ complete (proj1_sig b) i)).
    assert (Hsp : spatial (proj1_sig a) (proj1_sig b) g) by (split; [exact Hab |intros i; reflexivity]).
    pose (middle := exist _ g (spatial_well_formed active _ _ _ (proj2_sig a) (proj2_sig b) Hsp)).
    exists middle, c; split.
    + split; [exact Hout' |intros i; rewrite (Gout i), (Gbc i); cbn; tauto].
    + split; [exists a, b; auto |exact Hc].
  - intros (ab & c & [Hout Gout] & (a & b & [Hab Gab] & Ha & Hb) & Hc).
    destruct (proj2 (memory_spatial_associative _ _ _ _)
      (ex_intro _ _ (conj Hab Hout))) as (bc & Hbc & Hout').
    pose (g := Generalized bc (fun i => complete (proj1_sig b) i \/ complete (proj1_sig c) i)).
    assert (Hsp : spatial (proj1_sig b) (proj1_sig c) g) by (split; [exact Hbc |intros i; reflexivity]).
    pose (middle := exist _ g (spatial_well_formed active _ _ _ (proj2_sig b) (proj2_sig c) Hsp)).
    exists a, middle; split.
    + split; [exact Hout' |intros i; rewrite (Gout i), (Gab i); cbn; tauto].
    + split; [exact Ha |exists b, c; auto].
Qed.

Lemma container_spatial_emp_elim active p : wand_free p ->
  persistent_entails active (A.Spatial p A.Emp) p.
Proof.
  intros Hwf s r (a & b & [[_ [Hheap [Hbuffers Hblocks]]] Hmarks] & HP & [Hh [Hb Hk]]).
  eapply stm_wand_free_mark_extension; [exact Hwf | | |exact HP].
  - split.
    + intros loc; symmetry; rewrite Hheap; unfold heap_override; rewrite Hh; reflexivity.
    + split.
      * intros i; specialize (Hbuffers i); rewrite Hb in Hbuffers.
        symmetry; apply interleaves_nil_right, Hbuffers.
      * intros i; rewrite Hblocks; split; [auto |intros [H |H]; [exact H |exfalso; exact (Hk i H)]].
  - intros i H; apply Hmarks; auto.
Qed.

Lemma container_barrier_spatial active p q owner : active owner -> wand_free p -> wand_free q ->
  persistent_entails active (A.Temporal (A.Spatial p q) (A.Barrier (EVal (Z.pos owner))))
    (A.Spatial (A.Temporal p (A.Barrier (EVal (Z.pos owner))))
      (A.Temporal q (A.Barrier (EVal (Z.pos owner))))).
Proof.
  intros Hi HPwf HQwf s r (ab & bar & Htm & (a & b & [Hsp Hmarks] & HP & HQ) & Hbar).
  assert (Hmark : complete (proj1_sig r) owner).
  { apply (proj2 (proj2 (proj2 Htm)) owner); right; destruct Hbar as [_ [Hno |H]]; tauto. }
  assert (Hempty : buffers (resource_memory active ab) owner = []).
  { apply (proj1 (proj2 (proj2 Htm))); destruct Hbar as [_ [Hno |H]]; tauto. }
  destruct (spatial_empty_buffer_parts _ _ _ _ Hsp Hempty) as [Haempty Hbempty].
  pose (a' := remark_resource active a (complete (proj1_sig r))
    (proj1 (proj2 (proj2_sig r))) (ex_intro _ owner Hmark)).
  pose (b' := remark_resource active b (complete (proj1_sig r))
    (proj1 (proj2 (proj2_sig r))) (ex_intro _ owner Hmark)).
  destruct (temporal_emp_memory_right _ _ _ _ (proj1 Hbar) Htm) as [Eh [Eb Ek]].
  exists a', b'; split.
  - split.
    + destruct Hsp as [Hcompatible [Hh [Hb Hk]]]; split; [exact Hcompatible |].
      split; [intros loc; rewrite Eh; apply Hh |].
      split; [intros i; rewrite Eb; apply Hb |intros i; rewrite Ek; apply Hk].
    + intros i; change (complete (proj1_sig r) i <-> complete (proj1_sig r) i \/ complete (proj1_sig r) i); tauto.
  - split; apply owned_barrier_suffix_intro with (Hi := Hi); try assumption; try exact Hmark.
    + eapply stm_wand_free_mark_extension; [exact HPwf | | |exact HP].
      * split; [intros; reflexivity |split; intros; reflexivity].
      * intros i H; apply (proj2 (proj2 (proj2 Htm)) i); left; apply Hmarks; auto.
    + eapply stm_wand_free_mark_extension; [exact HQwf | | |exact HQ].
      * split; [intros; reflexivity |split; intros; reflexivity].
      * intros i H; apply (proj2 (proj2 (proj2 Htm)) i); left; apply Hmarks; auto.
Qed.

Definition container_cell loc value := writer_points_to (EVal (Z.pos loc)) (EVal value).
Definition container_some_cell loc := A.Exists 0 (writer_points_to (EVal (Z.pos loc)) (EVar 0)).
Definition container_write loc owner value := A.LeadsTo (EVal (Z.pos loc)) (EVal (Z.pos owner)) (EVal value).
Definition container_history loc owner value := A.Temporal (container_some_cell loc) (container_write loc owner value).

Lemma container_cell_shape active s r loc value :
  persistent_models active s r (container_cell loc value) ->
  exists owner, active owner /\
    (forall l, shared_heap (resource_memory active r) l = heap_update empty_heap loc value l) /\
    (forall i, buffers (resource_memory active r) i = []) /\
    lock_free (resource_memory active r) /\ complete (proj1_sig r) owner.
Proof.
  intros H; destruct (writer_points_to_shape _ _ _ _ _ H) as (l & i & E & Hshape).
  cbn in E; inversion E; subst l; exists i; exact Hshape.
Qed.

Lemma container_some_cell_models active s r loc :
  persistent_models active s r (container_some_cell loc) <->
  exists value, persistent_models active s r (container_cell loc value).
Proof.
  split; intros [value H]; exists value;
    destruct (writer_points_to_shape _ _ _ _ _ H) as (l & owner & E & Hi & Hh & Hb & Hk & Hm);
    cbn in E; inversion E; subst l;
    eapply writer_points_to_from_shape with (loc := loc) (owner := owner);
    try exact Hi; try exact Hb; try exact Hk; try exact Hm; try reflexivity;
    intros address; rewrite Hh; cbn [eval_expr]; rewrite ?update_same; reflexivity.
Qed.

Lemma container_cell_some active loc value :
  persistent_entails active (container_cell loc value) (container_some_cell loc).
Proof. intros s r H; apply container_some_cell_models; exists value; exact H. Qed.

Lemma container_history_complete active loc owner value : active owner ->
  persistent_entails active (A.Temporal (container_history loc owner value) (A.Barrier (EVal (Z.pos owner))))
    (container_cell loc value).
Proof.
  intros Hi s r (history & bar & Houter & (old & new & Hinner & Hold & Hnew) & Hbar).
  apply container_some_cell_models in Hold; destruct Hold as [v Hold].
  destruct (container_cell_shape _ _ _ _ _ Hold) as (writer & Hw & Hoh & Hob & Hok & Hom).
  assert (Hnewempty : buffers (resource_memory active new) owner = []).
  { assert (Hhempty : buffers (resource_memory active history) owner = []).
    { apply (proj1 (proj2 (proj2 Houter))); destruct Hbar as [_ [Hno |H]]; tauto. }
    destruct Hinner as [_ [[_ [_ [Hb _]]] _]].
    specialize (Hb owner).
    change (buffers (resource_memory active history) owner =
      buffers (resource_memory active old) owner ++ buffers (resource_memory active new) owner) in Hb.
    rewrite Hhempty in Hb; symmetry in Hb; apply app_eq_nil in Hb; tauto. }
  destruct Hnew as [_ [Hpending |Hflushed]].
  - destruct Hpending as [_ [Hb _]]; specialize (Hb owner).
    change (buffers (resource_memory active new) owner = buffer_update empty_buffers owner [(loc,value)] owner) in Hb.
    rewrite Hnewempty, buffer_update_same in Hb; discriminate.
  - destruct Hflushed as [Hnh [Hnb [Hnk Hnm]]].
    destruct Hinner as [_ [[_ [Hh [Hb Hk]]] _]].
    destruct (temporal_emp_memory_right _ _ _ _ (proj1 Hbar) Houter) as [Eh [Eb Ek]].
    eapply writer_points_to_from_shape with (loc := loc) (owner := owner); [reflexivity |exact Hi | | | |].
    + intros address; rewrite Eh, Hh; unfold heap_override; rewrite Hnh, Hoh.
      unfold heap_update; destruct (Pos.eq_dec address loc); reflexivity.
    + intros i; rewrite Eb, Hb, Hob, Hnb; reflexivity.
    + intros i H; apply Ek, Hk in H; destruct H; [apply (Hok i) |apply (Hnk i)]; assumption.
    + apply (proj2 (proj2 (proj2 Houter)) owner); right; destruct Hbar as [_ [Hno |H]]; tauto.
Qed.

Lemma container_history_drained active s r loc owner value :
  persistent_models active s r (container_history loc owner value) ->
  buffers (resource_memory active r) owner = [] ->
  persistent_models active s r (container_cell loc value).
Proof.
  intros (old & new & [_ [[_ [Hh [Hb Hk]]] [_ Hmarks]]] & Hold & [Hi [Hpending |Hflushed]]) Hempty.
  - destruct Hpending as [_ [Hnb _]]; specialize (Hb owner); specialize (Hnb owner).
    unfold resource_memory in Hempty; rewrite Hempty, Hnb, buffer_update_same in Hb.
    symmetry in Hb; apply app_eq_nil in Hb; destruct Hb as [_ E]; discriminate.
  - apply container_some_cell_models in Hold; destruct Hold as [v Hold].
    destruct (container_cell_shape _ _ _ _ _ Hold) as (writer & Hw & Hoh & Hob & Hok & Hom).
    destruct Hflushed as [Hnh [Hnb [Hnk Hnm]]].
    eapply writer_points_to_from_shape with (loc := loc) (owner := owner); [reflexivity |exact Hi | | | |].
    + intros address; unfold resource_memory; rewrite Hh; unfold heap_override; rewrite Hnh, Hoh.
      unfold heap_update; destruct (Pos.eq_dec address loc); reflexivity.
    + intros i; unfold resource_memory; rewrite Hb, Hob, Hnb; reflexivity.
    + intros i H; apply Hk in H; destruct H; [apply (Hok i) |apply (Hnk i)]; assumption.
    + apply Hmarks; auto.
Qed.

Definition container_heap_resource active (source : resource active) owner
    (Hmark : complete (proj1_sig source) owner) (loc : location) (value : Z) : resource active.
Proof.
  refine (exist _ (Generalized (Memory (heap_update empty_heap loc value) empty_buffers no_blocked)
    (complete (proj1_sig source))) _).
  split; [split; [intros i H; contradiction |intros; reflexivity] |].
  split; [exact (proj1 (proj2 (proj2_sig source))) |].
  intros Hnone address; exfalso; exact (Hnone owner Hmark).
Defined.

Lemma container_heap_models active s source owner Hmark loc value :
  persistent_models active s (container_heap_resource active source owner Hmark loc value)
    (container_cell loc value).
Proof.
  eapply writer_points_to_from_shape with (loc := loc) (owner := owner);
    try reflexivity; try (intros; reflexivity).
  - exact (proj1 (proj2 (proj2_sig source)) owner Hmark).
  - intros i H; exact H.
  - exact Hmark.
Qed.

Lemma container_heap_domain active source owner Hmark loc value address :
  memory_domain (resource_memory active (container_heap_resource active source owner Hmark loc value)) address ->
  address = loc.
Proof.
  intros [[v H] |[i [v H]]]; [|contradiction].
  change (heap_update empty_heap loc value address = Some v) in H.
  unfold heap_update in H; destruct (Pos.eq_dec address loc); [assumption |discriminate].
Qed.

Lemma container_locked_pair_from_shape active s (r : resource active) owner left right v w :
  left <> right -> active owner ->
  (forall address, shared_heap (resource_memory active r) address =
    heap_update (heap_update empty_heap right w) left v address) ->
  (forall i, buffers (resource_memory active r) i = []) ->
  lock_held active (resource_memory active r) owner -> complete (proj1_sig r) owner ->
  persistent_models active s r
    (A.Spatial (A.Lock (EVal (Z.pos owner))) (A.Spatial (container_cell left v) (container_cell right w))).
Proof.
  intros Hne Hi Hheap Hbuffers Hheld Hmark.
  pose (a := container_heap_resource active r owner Hmark left v).
  pose (b := container_heap_resource active r owner Hmark right w).
  pose (payload := released_resource active r).
  assert (HP : persistent_models active s payload (A.Spatial (container_cell left v) (container_cell right w))).
  { exists a, b; split; [|split; apply container_heap_models].
    split.
    - split.
      + split; [|intros i H _; exact H]. intros loc Ha Hb; apply Hne.
        pose proof (container_heap_domain _ _ _ _ _ _ _ Ha); pose proof (container_heap_domain _ _ _ _ _ _ _ Hb); congruence.
      + split.
        * intros loc; change (shared_heap (resource_memory active r) loc =
            heap_override (heap_update empty_heap left v) (heap_update empty_heap right w) loc).
          rewrite Hheap; unfold heap_override, heap_update; destruct (Pos.eq_dec loc left), (Pos.eq_dec loc right); subst; try congruence; reflexivity.
        * split; [intros i; change (interleaves [] [] (buffers (resource_memory active r) i)); rewrite Hbuffers; constructor |intros i; cbn; unfold no_blocked; tauto].
    - intros i; change (complete (proj1_sig r) i <-> complete (proj1_sig r) i \/ complete (proj1_sig r) i); tauto. }
  pose proof (acquire_marked_payload active owner s payload _ Hi (fun i H => H) HP) as Howned.
  eapply stm_wand_free_equiv; [| |exact Howned].
  - cbn [wand_free owned_assertion container_cell writer_points_to]; tauto.
  - split; [split; [intros; reflexivity |split; [intros; reflexivity |]] |intros i; reflexivity].
    intros i; change (blocked_except active owner i <-> blocked (resource_memory active r) i).
    symmetry; exact (proj2 Hheld i).
Qed.
