From Stdlib Require Import List ZArith.
From WMLR Require Import Expressions Languages Machine BufferRelations Separation RepairedSeparation
  OperationalSemantics ProgramSteps ExecutionExamples Assertions AssertionSemantics ConcreteAssertions
  RepairedAssertions PersistentAssertions PersistentRules Safety Specifications PrivateOwnership
  TemporalSafety TemporalFence RegionalResources InvariantFragment OwnedSafety OwnedResources
  OwnedRules OwnedFraming OwnedStructural OwnedPrimitives OwnedHeap OwnedAcceptance
  StrongTemporalCounterexample OwnedContainerEntailments.
Import ListNotations.

Definition container_flag v := container_cell 1%positive v.
Definition container_item := container_some_cell 2%positive.
Definition container_invariant := A.Or (container_flag 0%Z) (A.Spatial (container_flag 1%Z) container_item).
Definition container_token := A.Lock (EVal 1%Z).
Definition container_held p := A.Spatial container_token p.
Definition container_guard v := BEq (EVar 0) (EVal v).
Definition container_load_flag := load_command 1%positive 1%positive 0.
Definition container_select v := C.Seq container_load_flag
  (C.Prim (C.Common (S.Assume (container_guard v))) (EVal 1%Z)).
Definition container_acquire := C.Prim C.Lock (EVal 1%Z).
Definition container_release := C.Prim C.Unlock (EVal 1%Z).
Definition container_flag_history v := container_history 1%positive 1%positive v.
Definition container_private_history := container_history 2%positive 1%positive 9%Z.

Lemma container_invariant_fragment : invariant_fragment container_invariant.
Proof. constructor; [constructor |constructor; [constructor |constructor; constructor]]. Qed.

Lemma container_invariant_closed x : ~ In x (A.fv container_invariant).
Proof. cbn [container_invariant container_flag container_cell container_item container_some_cell writer_points_to A.fv expr_fv fresh]; tauto. Qed.

Lemma container_held_swap p q :
  persistent_entails two_processors (container_held (A.Spatial p q)) (A.Spatial (container_held q) p).
Proof.
  intros s r H; apply container_spatial_assoc.
  eapply container_spatial_mono; [intros t a Ha; exact Ha |apply container_spatial_comm |exact H].
Qed.

Lemma container_held_restore p q :
  persistent_entails two_processors (A.Spatial (container_held q) p) (container_held (A.Spatial p q)).
Proof.
  intros s r H; apply container_spatial_assoc in H.
  eapply container_spatial_mono; [intros t a Ha; exact Ha |apply container_spatial_comm |exact H].
Qed.

Lemma container_spatial_pure p q b :
  persistent_entails two_processors (A.Spatial p (A.And q (A.Pure b)))
    (A.And (A.Spatial p q) (A.Pure b)).
Proof. intros s r (a & c & Hsp & HP & HQ & Hb); split; [exists a,c; auto |exact Hb]. Qed.

Lemma container_read_flag_valid mode tail v : ~ In 0 (A.fv tail) ->
  owned_valid two_processors mode container_invariant (container_held (A.Spatial (container_flag v) tail))
    container_load_flag (A.And (container_held (A.Spatial (container_flag v) tail)) (A.Pure (container_guard v))).
Proof.
  intros Hfresh; eapply owned_consequence_valid.
  - apply container_held_swap.
  - apply owned_spatial_frame_valid.
    + apply owned_load_cell_valid; [apply container_invariant_closed |intros H; contradiction].
    + intros x Hx; cbn [container_load_flag load_command C.modifies] in Hx.
      destruct Hx as [E |Hfalse]; [subst x |contradiction]. exact Hfresh.
  - intros s r H; apply container_spatial_pure in H; destruct H as [H Hb].
    split; [apply container_held_restore, H |exact Hb].
Qed.

Definition container_cases p q := A.Or (container_held (A.Spatial (container_flag 0%Z) p))
  (container_held (A.Spatial (container_flag 1%Z) q)).
Definition container_read_cases p q := A.Or
  (A.And (container_held (A.Spatial (container_flag 0%Z) p)) (A.Pure (container_guard 0%Z)))
  (A.And (container_held (A.Spatial (container_flag 1%Z) q)) (A.Pure (container_guard 1%Z))).

Lemma container_read_cases_valid mode p q : ~ In 0 (A.fv p) -> ~ In 0 (A.fv q) ->
  owned_valid two_processors mode container_invariant (container_cases p q) container_load_flag (container_read_cases p q).
Proof.
  intros Hp Hq; apply owned_disjunction_valid.
  - eapply owned_consequence_valid; [intros s r H; exact H |apply container_read_flag_valid, Hp |intros s r H; left; exact H].
  - eapply owned_consequence_valid; [intros s r H; exact H |apply container_read_flag_valid, Hq |intros s r H; right; exact H].
Qed.

Lemma container_select_one_valid mode p q : ~ In 0 (A.fv p) -> ~ In 0 (A.fv q) ->
  owned_valid two_processors mode container_invariant (container_cases p q) (container_select 1%Z)
    (container_held (A.Spatial (container_flag 1%Z) q)).
Proof.
  intros Hp Hq; eapply owned_sequence_valid; [apply container_read_cases_valid; assumption |].
  eapply owned_consequence_valid; [|apply owned_assume_valid |intros s r H; exact H].
  intros s r [[H Hb] |[H Hb]]; [left |right; exact H].
  change (Z.eqb (s 0) 0%Z = true) in Hb; apply Z.eqb_eq in Hb.
  change (negb (Z.eqb (s 0) 1%Z) = true); rewrite Hb; reflexivity.
Qed.

Lemma container_select_zero_valid mode p q : ~ In 0 (A.fv p) -> ~ In 0 (A.fv q) ->
  owned_valid two_processors mode container_invariant (container_cases p q) (container_select 0%Z)
    (container_held (A.Spatial (container_flag 0%Z) p)).
Proof.
  intros Hp Hq; eapply owned_sequence_valid; [apply container_read_cases_valid; assumption |].
  eapply owned_consequence_valid; [|apply owned_assume_valid |intros s r H; exact H].
  intros s r [[H Hb] |[H Hb]]; [right; exact H |left].
  change (Z.eqb (s 0) 1%Z = true) in Hb; apply Z.eqb_eq in Hb.
  change (negb (Z.eqb (s 0) 0%Z) = true); rewrite Hb; reflexivity.
Qed.

Lemma container_store_known_valid mode loc old value :
  owned_valid two_processors mode container_invariant (container_cell loc old)
    (store_command 1%positive loc value) (container_history loc 1%positive value).
Proof.
  eapply owned_consequence_valid; [intros s r H; exact H |apply owned_store_cell_valid |].
  apply container_temporal_mono; [apply container_cell_some |intros s r H; exact H].
Qed.

Lemma container_store_some_valid mode loc value :
  owned_valid two_processors mode container_invariant (container_some_cell loc)
    (store_command 1%positive loc value) (container_history loc 1%positive value).
Proof.
  intros s r H n; apply container_some_cell_models in H; destruct H as [old H].
  exact (container_store_known_valid mode loc old value s r H n).
Qed.

Lemma container_store_flag_valid mode tail old value :
  owned_valid two_processors mode container_invariant (container_held (A.Spatial (container_flag old) tail))
    (store_command 1%positive 1%positive value) (container_held (A.Spatial (container_flag_history value) tail)).
Proof.
  eapply owned_consequence_valid; [apply container_held_swap | |apply container_held_restore].
  apply owned_spatial_frame_valid; [apply container_store_known_valid |intros x H; contradiction].
Qed.

Lemma container_first_acquire_entails :
  persistent_entails two_processors
    (A.Temporal (container_held container_invariant) (A.Barrier (EVal 1%Z)))
    (container_cases A.Emp container_item).
Proof.
  intros s r H; apply stm_wand_free_barrier_elim in H;
    [|cbn [container_held container_token container_invariant container_flag container_cell container_item container_some_cell writer_points_to wand_free]; tauto].
  destruct H as (token & payload & Hsp & Htoken & [HJ |HJ]).
  - left; exists token,payload; split; [exact Hsp |]. split; [exact Htoken |apply persistent_spatial_emp_right, HJ].
  - right; exists token,payload; auto.
Qed.

Lemma container_remove_unlock_entails :
  persistent_entails two_processors
    (A.Temporal (A.Spatial (container_flag_history 0%Z) container_item) (A.Barrier (EVal 1%Z)))
    (A.Spatial container_invariant container_item).
Proof.
  intros s r H; apply (container_barrier_spatial two_processors (container_flag_history 0%Z) container_item 1%positive) in H;
    [|left; reflexivity |cbn [container_flag_history container_history container_some_cell container_write writer_points_to wand_free]; tauto
     |cbn [container_item container_some_cell writer_points_to wand_free]; tauto].
  eapply container_spatial_mono; [| |exact H].
  - intros t a Ha; left; apply container_history_complete with (owner := 1%positive); [left; reflexivity |exact Ha].
  - intros t a Ha; eapply stm_wand_free_barrier_elim;
      [cbn [container_item container_some_cell writer_points_to wand_free]; tauto |exact Ha].
Qed.

Lemma container_return_unlock_entails :
  persistent_entails two_processors
    (A.Temporal (A.Spatial (container_flag_history 1%Z) (container_cell 2%positive 9%Z)) (A.Barrier (EVal 1%Z)))
    (A.Spatial container_invariant A.Emp).
Proof.
  intros s r H; apply (container_barrier_spatial two_processors (container_flag_history 1%Z) (container_cell 2%positive 9%Z) 1%positive) in H;
    [|left; reflexivity |cbn [container_flag_history container_history container_some_cell container_write writer_points_to wand_free]; tauto
     |cbn [container_cell writer_points_to wand_free]; tauto].
  apply persistent_spatial_emp_right; right.
  eapply container_spatial_mono; [| |exact H].
  - apply container_history_complete; left; reflexivity.
  - intros t a Ha; apply container_cell_some with (value := 9%Z).
    eapply stm_wand_free_barrier_elim; [cbn [container_cell writer_points_to wand_free]; tauto |exact Ha].
Qed.

Definition container_remove := C.Seq container_acquire
  (C.Seq (container_select 1%Z) (C.Seq (store_command 1%positive 1%positive 0%Z) container_release)).

Theorem container_remove_valid :
  owned_valid two_processors DisjointMode container_invariant A.Emp container_remove container_item.
Proof.
  eapply owned_sequence_valid with (middle := container_cases A.Emp container_item).
  - eapply owned_consequence_valid; [intros s r H; exact H | |apply container_first_acquire_entails].
    apply owned_lock_valid; [apply acceptance_two_active |apply container_invariant_fragment].
  - eapply owned_sequence_valid.
    + apply container_select_one_valid; cbn [container_item container_some_cell writer_points_to A.fv expr_fv fresh]; tauto.
    + eapply owned_sequence_valid; [apply container_store_flag_valid |].
      apply owned_unlock_valid; [apply acceptance_two_active |apply container_invariant_fragment |apply container_remove_unlock_entails].
Qed.

(** The temporal frame on the second LOCK accounts for the pending private
    store. Its barrier forces that store to drain. The unrelated foreign
    write is outside this lemma, in a spatial frame around the whole program. *)
Lemma container_reacquire_entails :
  persistent_entails two_processors
    (A.Temporal container_private_history
      (A.Temporal (container_held container_invariant) (A.Barrier (EVal 1%Z))))
    (container_cases (container_cell 2%positive 9%Z) container_item).
Proof.
  intros s r (history & acquired & Houter & Hhistory & locked & bar & Hinner & Hlocked & Hbar).
  destruct Houter as [_ [[_ [Hrh [Hrb Hrk]]] [Hbefore Hrm]]].
  destruct Hinner as [_ [[_ [Hah [Hab Hak]]] [_ Ham]]].
  destruct Hbar as [[Hbarh [Hbarb Hbark]] [Hno |Hbarm]];
    [exfalso; apply Hno; left; reflexivity |].
  assert (Hacqm : complete (proj1_sig acquired) 1%positive) by (apply Ham; auto).
  assert (Hhistempty : buffers (resource_memory two_processors history) 1%positive = []) by (apply Hbefore, Hacqm).
  pose proof (container_history_drained _ _ _ _ _ _ Hhistory Hhistempty) as Hcell.
  destruct (container_cell_shape _ _ _ _ _ Hcell) as (writer & Hwriter & Hhh & Hhb & Hhk & Hhm).
  destruct Hlocked as (token & payload & [[_ [Hlh [Hlb Hlk]]] Hlm] & Htoken & HJ).
  destruct Htoken as [Hth [Htb [Hi Htk]]].
  destruct (invariant_fragment_shape _ container_invariant_fragment _ _ _ HJ) as [Hpb Hpk].
  assert (Hlockedb : forall i, buffers (resource_memory two_processors locked) i = []).
  { intros i; specialize (Hlb i); rewrite Htb, Hpb in Hlb; apply interleaves_nil_left, Hlb. }
  assert (Hbuffers : forall i, buffers (resource_memory two_processors r) i = []).
  { intros i; unfold resource_memory; rewrite Hrb, Hhb, Hab, Hlockedb, Hbarb; reflexivity. }
  assert (Hheld : lock_held two_processors (resource_memory two_processors r) 1%positive).
  { split; [exact Hi |]. intros i; rewrite Hrk, Hak, Hlk, Htk.
    split.
    - intros [H |[[H |H] |H]]; [exfalso; exact (Hhk i H) |exact H |exfalso; exact (Hpk i H) |exfalso; exact (Hbark i H)].
    - intros H; auto. }
  assert (Hmark : complete (proj1_sig r) 1%positive) by (apply Hrm; auto).
  assert (Hheap : forall address, shared_heap (resource_memory two_processors r) address =
    heap_override (heap_update empty_heap 2%positive 9%Z) (shared_heap (resource_memory two_processors payload)) address).
  { intros address; unfold resource_memory; rewrite Hrh.
    unfold heap_override; rewrite Hah; unfold heap_override; rewrite Hbarh, Hlh.
    unfold heap_override; rewrite Hth, Hhh.
    destruct (shared_heap (underlying (proj1_sig payload)) address); reflexivity. }
  destruct HJ as [HJ |(flag & item & [[_ [Hph [Hbuf Hblock]]] Hpm] & HF & HX)].
  - left; apply container_locked_pair_from_shape; try assumption; [discriminate |].
    destruct (container_cell_shape _ _ _ _ _ HJ) as (i & Hia & Hf & _).
    intros address; rewrite Hheap; unfold heap_override; rewrite Hf.
    unfold heap_update; destruct (Pos.eq_dec address 1%positive); reflexivity.
  - apply container_some_cell_models in HX; destruct HX as [value HX].
    destruct (container_cell_shape _ _ _ _ _ HF) as (i & Hia & Hf & _).
    destruct (container_cell_shape _ _ _ _ _ HX) as (j & Hja & Hx & _).
    assert (Hpair : persistent_models two_processors s r
      (container_held (A.Spatial (container_flag 1%Z) (container_cell 2%positive value)))).
    { apply container_locked_pair_from_shape; try assumption; [discriminate |].
      intros address; rewrite Hheap; unfold heap_override; rewrite Hph; unfold heap_override; rewrite Hf, Hx.
      unfold heap_update; destruct (Pos.eq_dec address 1%positive), (Pos.eq_dec address 2%positive); subst; try congruence; reflexivity. }
    right; eapply container_spatial_mono; [intros t a Ha; exact Ha | |exact Hpair].
    apply container_spatial_mono; [intros t a Ha; exact Ha |apply container_cell_some].
Qed.

Definition container_return := C.Seq container_acquire
  (C.Seq (container_select 0%Z) (C.Seq (store_command 1%positive 1%positive 1%Z) container_release)).

Theorem container_return_valid :
  owned_valid two_processors DisjointMode container_invariant container_private_history container_return A.Emp.
Proof.
  eapply owned_sequence_valid with (middle := container_cases (container_cell 2%positive 9%Z) container_item).
  - apply owned_valid_overlap_disjoint.
    eapply owned_consequence_valid; [intros s r H; apply temporal_emp_right_intro, H | |apply container_reacquire_entails].
    apply owned_temporal_frame_valid; [apply container_invariant_fragment | |intros x H; contradiction].
    apply owned_lock_valid; [apply acceptance_two_active |apply container_invariant_fragment].
  - eapply owned_sequence_valid.
    + apply container_select_zero_valid;
        cbn [container_item container_some_cell container_cell writer_points_to A.fv expr_fv fresh]; tauto.
    + eapply owned_sequence_valid; [apply container_store_flag_valid |].
      apply owned_unlock_valid; [apply acceptance_two_active |apply container_invariant_fragment |apply container_return_unlock_entails].
Qed.

Definition container_program := C.Seq container_remove
  (C.Seq (store_command 1%positive 2%positive 9%Z) container_return).

Theorem container_core_valid :
  owned_valid two_processors DisjointMode container_invariant A.Emp container_program A.Emp.
Proof.
  eapply owned_sequence_valid; [apply container_remove_valid |].
  eapply owned_sequence_valid; [apply container_store_some_valid |apply container_return_valid].
Qed.

Definition container_foreign := container_write 3%positive 2%positive 17%Z.

Theorem owned_container_valid :
  owned_valid two_processors DisjointMode container_invariant container_foreign container_program container_foreign.
Proof.
  eapply owned_consequence_valid; [intros s r H; apply persistent_spatial_emp_right, H | |].
  - apply owned_spatial_frame_valid; [apply container_core_valid |intros x _ H; contradiction].
  - apply container_spatial_emp_elim; exact I.
Qed.
