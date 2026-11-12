From Stdlib Require Import List ZArith.
From WMLR Require Import Expressions Machine BufferRelations Separation SpatialExchange
  Assertions AssertionSemantics ConcreteAssertions PersistentAssertions PersistentRules
  TemporalSafety ExecutionExamples InvariantFragmentExamples OwnedContainerEntailments
  AssertionAlgebra AssertionAlgebraCounterexamples AssertionWriteExamples AssertionExchange
  AssertionExchangeCounterexamples AssertionExchangeRight AssertionExchangeTemporal
  AssertionExchangeTemporalRight.
Import ListNotations.

(** Remaining 4A countermodels in the original [models] interpretation.
    Positive witnesses transport from the final interpretation because their
    formulas are wand-free. Negative proofs use the original relations
    directly: no converse transport of satisfaction is assumed. *)
Lemma original_barrier_suffix_buffer active p s r owner : active owner ->
  models active s r (A.Temporal p (A.Barrier (EVal (Z.pos owner)))) ->
  buffers (resource_memory active r) owner = [].
Proof.
  intros Hi (a & b & [[_ [_ [Hb _]]] [Hbefore Hmarks]] & HP & HE & [Hno |Hmark]);
    [contradiction |].
  unfold resource_memory; rewrite Hb,Hbefore by exact Hmark.
  rewrite (proj1 (proj2 HE) owner); reflexivity.
Qed.

Lemma original_spatial_emp_left_memory a b r : spatial a b r -> empty_atom a ->
  memory_equiv (underlying r) (underlying b).
Proof.
  intros [[Hcompat [Hh [Hb Hk]]] Hmarks] [Hah [Hab Hak]].
  split.
  - intros loc; rewrite Hh; unfold heap_override; rewrite Hah.
    destruct (shared_heap (underlying b) loc); reflexivity.
  - split.
    + intros i; specialize (Hb i); rewrite Hab in Hb; apply interleaves_nil_left,Hb.
    + intros i; rewrite Hk; split; [intros [H |H]; [exfalso; exact (Hak i H) |exact H] |auto].
Qed.

Lemma original_emp_spatial_write_or_emp active s r address annotation value :
  models active s r (A.Spatial A.Emp (A.Or A.Emp (A.LeadsTo address annotation value))) ->
  models active s r (A.Or A.Emp (A.LeadsTo address annotation value)).
Proof.
  intros (a & b & Hsp & HE & HB).
  destruct (original_spatial_emp_left_memory _ _ _ Hsp HE) as [Eh [Eb Ek]].
  destruct HB as [[Hh [Hb Hk]] |HW].
  - left; split; [intros loc; rewrite Eh; apply Hh |].
    split; [intros i; rewrite Eb; apply Hb |intros i H; apply (Hk i),Ek,H].
  - right; change (write_atom active (eval_expr s address) (eval_expr s annotation)
      (eval_expr s value) (proj1_sig r)).
    change (write_atom active (eval_expr s address) (eval_expr s annotation)
      (eval_expr s value) (proj1_sig b)) in HW.
    destruct (eval_expr s address), (eval_expr s annotation); try contradiction.
    destruct HW as [Hi [[Hh [Hb Hk]] |[Hh [Hb [Hk Hmark]]]]]; split; [exact Hi | |exact Hi |].
    + left; split; [intros loc; rewrite Eh; apply Hh |].
      split; [intros i; rewrite Eb; apply Hb |intros i H; apply Hk,Ek,H].
    + right; split; [intros loc; rewrite Eh; apply Hh |].
      split; [intros i; rewrite Eb; apply Hb |].
      split; [intros i H; apply (Hk i),Ek,H |apply (proj2 Hsp); right; exact Hmark].
Qed.

Theorem original_points_to_invalid_writer_refuted annotation :
  (forall owner, annotation = Z.pos owner -> ~ two_processors owner) ->
  ~ (forall s r, models two_processors s r (A.points_to (EVal 2%Z) (EVal 7%Z)) ->
    models two_processors s r (A.LeadsTo (EVal 2%Z) (EVal annotation) (EVal 7%Z))).
Proof.
  intros Hinvalid H.
  assert (HC : models two_processors (fun _ => 0%Z) checkpoint_full_cell
    (A.points_to (EVal 2%Z) (EVal 7%Z))).
  { apply assertion_wand_free_in_printed; [cbn [A.points_to wand_free]; tauto |apply assertion_full_cell_points_to]. }
  specialize (H _ _ HC); destruct annotation as [|owner|neg]; try contradiction.
  exact (Hinvalid owner eq_refl (proj1 H)).
Qed.

Lemma original_exchange_strong_spatial_left_not_model s :
  ~ models two_processors s algebra_whole (A.Spatial (A.strong_temporal algebra_P algebra_Q) algebra_R).
Proof.
  intros (a & b & [[Hdis [Hheap [Hbuffers Hblocks]]] Hmarks] & [_ Hbar] & HR).
  assert (Ha : buffers (resource_memory two_processors a) 1%positive = []).
  { eapply original_barrier_suffix_buffer; [left; reflexivity |exact Hbar]. }
  specialize (Hbuffers 1%positive); change (interleaves
    (buffers (resource_memory two_processors a) 1%positive)
    (buffers (resource_memory two_processors b) 1%positive) [(1%positive,0%Z)]) in Hbuffers.
  rewrite Ha in Hbuffers; apply interleaves_nil_left in Hbuffers.
  destruct HR as [[Hh [Hb Hk]] |[_ [[Hh [Hb Hk]] |[Hh [Hb Hk]]]]].
  - rewrite Hb in Hbuffers; discriminate.
  - apply (proj1 Hdis 1%positive).
    + left; exists 0%Z; specialize (Hheap 1%positive).
      change (Some 0%Z = heap_override (shared_heap (resource_memory two_processors a))
        (shared_heap (resource_memory two_processors b)) 1%positive) in Hheap.
      unfold heap_override in Hheap; rewrite Hh in Hheap; symmetry; exact Hheap.
    + right; exists 1%positive,0%Z.
      change (In (1%positive,0%Z) (buffers (resource_memory two_processors b) 1%positive)).
      rewrite <- Hbuffers; left; reflexivity.
  - rewrite Hb in Hbuffers; discriminate.
Qed.

Theorem original_exchange_strong_spatial_right_not_model s :
  ~ models two_processors s exchange_right_whole
    (A.Spatial algebra_P (A.strong_temporal exchange_right_Q exchange_right_R)).
Proof.
  intros (outer & inner & [Hout Gout] & HP &
    (a & b & [Hinner Ginner] & HQ & HR) & HT).
  destruct HR as [HB |HW].
  - pose proof (proj1 HB) as [Hbh [Hbb Hbk]].
    destruct Hinner as [Hcompat [Hh [Hb Hk]]].
    destruct HQ as [Hi [Hpending |Hflushed]].
    + destruct Hpending as [Hah [Hab Hak]].
      assert (HemptyHeap : forall loc, shared_heap (underlying (proj1_sig inner)) loc = None).
      { intros loc; rewrite Hh; unfold heap_override; rewrite Hbh,Hah; reflexivity. }
      assert (Hbuf : forall i, buffers (underlying (proj1_sig inner)) i =
        buffer_update empty_buffers 1%positive [(1%positive,0%Z)] i).
      { intros i; specialize (Hb i); rewrite Hbb in Hb; apply interleaves_nil_right in Hb; rewrite Hb; apply Hab. }
      destruct HT as (c & d & Htm & HC & [HD |HD]).
      * assert (E : buffers (resource_memory two_processors inner) 1%positive = []).
        { eapply original_barrier_suffix_buffer with (p := exchange_right_Q);
            [left; reflexivity |exists c,d; split; [exact Htm |split; [exact HC |exact HD]]]. }
        unfold resource_memory in E; rewrite Hbuf,buffer_update_same in E; discriminate.
      * destruct Htm as [[_ [Hheap [Hbuffers Hblocks]]] _].
        destruct HD as [_ [[Hdh [Hdb Hdk]] |[Hdh [Hdb Hdk]]]].
        -- specialize (Hbuffers 2%positive); rewrite Hbuf,Hdb,buffer_update_same in Hbuffers.
           cbn [buffer_update empty_buffers] in Hbuffers.
           symmetry in Hbuffers; apply app_eq_nil in Hbuffers; destruct Hbuffers as [_ Hbad]; discriminate.
        -- specialize (Hheap 2%positive); rewrite HemptyHeap in Hheap.
           unfold heap_override in Hheap; rewrite Hdh,heap_update_same in Hheap; discriminate.
    + destruct Hflushed as [Hah [Hab HK]].
      destruct Hout as [_ [Hheap Hrest]]; specialize (Hheap 1%positive).
      change (None = heap_override (shared_heap (underlying (proj1_sig outer)))
        (shared_heap (underlying (proj1_sig inner))) 1%positive) in Hheap.
      unfold heap_override in Hheap; rewrite Hh in Hheap.
      unfold heap_override in Hheap; rewrite Hbh,Hah,heap_update_same in Hheap; discriminate.
  - destruct (proj1 (memory_spatial_associative _ _ _ _)
      (ex_intro _ (underlying (proj1_sig inner)) (conj Hinner Hout))) as (combined & Hcombined & Hfinal).
    eapply assertion_spatial_write_cannot_mix with (a := Generalized combined no_blocked)
      (b := proj1_sig b) (loc := 2%positive) (owner := 2%positive) (value := 0%Z).
    + exact Hfinal.
    + exact HW.
    + exists 0%Z; reflexivity.
    + exists 0%Z; left; reflexivity.
Qed.

Theorem original_exchange_strong_temporal_left_not_model s :
  ~ models two_processors s exchange_temporal_whole
    (A.Temporal (A.strong_temporal algebra_P exchange_temporal_Q) exchange_temporal_R).
Proof.
  intros (a & b & Htm & Hinner & [HB |HL]).
  - assert (E : buffers (resource_memory two_processors exchange_temporal_whole) 1%positive = []).
    { eapply original_barrier_suffix_buffer with (p := A.strong_temporal algebra_P exchange_temporal_Q);
        [left; reflexivity |exists a,b; auto]. }
    discriminate.
  - destruct HL as [Hbh [Hbb [Hi Hbheld]]].
    destruct Htm as [[[Hdis Hrest] [Hheap [Hbuffers Hblocks]]] [Hbefore Hmarks]].
    destruct Hinner as [(c & d & [[Hcd [Hch [Hcb Hck]]] Ginner] & HP & [HD |HW]) Hother].
    + apply (Hdis 2%positive).
      * apply Hck; right; destruct HD as [_ [_ [_ HDheld]]]; apply HDheld.
        split; [right; reflexivity |discriminate].
      * apply Hbheld; split; [right; reflexivity |discriminate].
    + eapply assertion_spatial_write_cannot_mix with (a := proj1_sig c) (b := proj1_sig d)
        (whole := underlying (proj1_sig a)) (loc := 1%positive) (owner := 1%positive) (value := 0%Z).
      * split; [exact Hcd |split; [exact Hch |split; assumption]].
      * exact HW.
      * exists 0%Z; specialize (Hheap 1%positive).
        change (Some 0%Z = heap_override (shared_heap (underlying (proj1_sig a)))
          (shared_heap (underlying (proj1_sig b))) 1%positive) in Hheap.
        unfold heap_override in Hheap; rewrite Hbh in Hheap; symmetry; exact Hheap.
      * exists 0%Z; specialize (Hbuffers 1%positive); rewrite Hbb,app_nil_r in Hbuffers.
        change ([(1%positive,0%Z)] = buffers (underlying (proj1_sig a)) 1%positive) in Hbuffers.
        rewrite <- Hbuffers; left; reflexivity.
  Unshelve. all: try assumption.
Qed.

Lemma original_strong_write_single_mark_heap_empty active owner loc value s r p :
  (forall i, complete (proj1_sig r) i -> i = owner) ->
  buffer_domain (buffers (resource_memory active r) owner) loc ->
  models active s r
    (A.strong_temporal (A.LeadsTo (EVal (Z.pos loc)) (EVal (Z.pos owner)) (EVal value)) p) ->
  forall address, shared_heap (resource_memory active r) address = None.
Proof.
  intros Hmarks Hpending [(a & b & [Hsp Hspmarks] & HW & HP) HT].
  assert (Habsent : shared_heap (resource_memory active r) loc = None).
  { destruct (shared_heap (resource_memory active r) loc) as [v|] eqn:E; [|reflexivity].
    exfalso; eapply assertion_spatial_write_cannot_mix with (a := proj1_sig b) (b := proj1_sig a).
    - exact (proj1 (spatial_comm _ _ _ (conj Hsp Hspmarks))).
    - exact HW.
    - exists v; exact E.
    - exact Hpending. }
  destruct HT as (c & d & [[Hcompat [Hheap [Hbuffers Hblocks]]] [Hbefore Hunion]] & HC & HD).
  destruct HC as [_ [[Hch [Hcb Hck]] |[Hch [Hcb Hck]]]].
  - assert (Hnone : forall i, ~ complete (proj1_sig d) i).
    { intros i Hi; assert (E : i = owner) by (apply Hmarks,Hunion; right; exact Hi).
      subst i; specialize (Hbefore owner Hi); rewrite Hcb,buffer_update_same in Hbefore; discriminate. }
    pose proof (proj2 (proj2 (proj2_sig d)) Hnone) as Hdh.
    intros address; unfold resource_memory; rewrite Hheap; unfold heap_override; rewrite Hdh,Hch; reflexivity.
  - specialize (Hheap loc); unfold resource_memory in Habsent; rewrite Habsent in Hheap.
    unfold heap_override in Hheap; rewrite Hch,heap_update_same in Hheap.
    destruct (shared_heap (underlying (proj1_sig d)) loc); discriminate.
Qed.

Theorem original_exchange_strong_temporal_right_not_model s :
  ~ models two_processors s exchange_temporal_right_whole
    (A.Temporal algebra_W (A.strong_temporal algebra_W algebra_P)).
Proof.
  intros (a & b & [[Hcompat [Hheap [Hbuffers Hblocks]]] [Hbefore Hmarks]] & HW & Hinner).
  assert (Hbmarks : forall i, complete (proj1_sig b) i -> i = 1%positive).
  { intros i Hi; apply (proj2 (Hmarks i)); right; exact Hi. }
  assert (Hbcell : shared_heap (resource_memory two_processors b) 2%positive = Some 0%Z).
  { destruct HW as [_ [[Hh _] |[Hh _]]]; specialize (Hheap 2%positive);
      change (Some 0%Z = heap_override (shared_heap (underlying (proj1_sig a)))
        (shared_heap (underlying (proj1_sig b))) 2%positive) in Hheap;
      unfold heap_override in Hheap; rewrite Hh in Hheap;
      destruct (shared_heap (underlying (proj1_sig b)) 2%positive) eqn:E;
      try discriminate; unfold resource_memory; congruence. }
  destruct HW as [_ [[Hh [Hb HK]] |[Hh [Hb HK]]]].
  - assert (Hnone : forall i, ~ complete (proj1_sig b) i).
    { intros i Hi; pose proof (Hbmarks i Hi); subst i.
      specialize (Hbefore 1%positive Hi); rewrite Hb,buffer_update_same in Hbefore; discriminate. }
    pose proof (proj2 (proj2 (proj2_sig b)) Hnone 2%positive) as E.
    change (shared_heap (resource_memory two_processors b) 2%positive = None) in E.
    rewrite E in Hbcell; discriminate.
  - assert (Hpending : buffer_domain (buffers (resource_memory two_processors b) 1%positive) 1%positive).
    { exists 0%Z; specialize (Hbuffers 1%positive); rewrite Hb in Hbuffers.
      change ([(1%positive,0%Z)] = buffers (resource_memory two_processors b) 1%positive) in Hbuffers.
      rewrite <- Hbuffers; left; reflexivity. }
    pose proof (original_strong_write_single_mark_heap_empty two_processors 1%positive 1%positive 0%Z
      s b algebra_P Hbmarks Hpending Hinner 2%positive) as E; rewrite E in Hbcell; discriminate.
Qed.

Lemma original_strong_inclusion kind active p q s r :
  models active s r (A.strong_temporal p q) ->
  models active s r (assertion_conjunction kind p q).
Proof. destruct kind; intros [Hsp Htm]; [exact Hsp |exact Htm |split; assumption]. Qed.

(** Both premise readings are defeated: the uniform inclusion is true for
    every choice of the inner connective, while the exchange schema fails. *)
Theorem original_small_exchange_strong_left_refuted kind :
  (forall p q s r, models two_processors s r (A.strong_temporal p q) ->
    models two_processors s r (assertion_conjunction kind p q)) /\
  ~ (forall p q t s r,
    models two_processors s r (A.strong_temporal p (assertion_conjunction kind q t)) ->
    models two_processors s r (assertion_conjunction kind (A.strong_temporal p q) t)).
Proof.
  split; [apply original_strong_inclusion |]. intros H; destruct kind.
  - apply (original_exchange_strong_spatial_left_not_model (fun _ => 0%Z)),H.
    apply assertion_wand_free_in_printed; [repeat split; exact I |apply assertion_exchange_strong_spatial_left_model].
  - apply (original_exchange_strong_temporal_left_not_model (fun _ => 0%Z)),H.
    apply assertion_wand_free_in_printed; [repeat split; exact I |apply assertion_exchange_strong_temporal_left_model].
  - apply (assertion_strong_associativity_printed_left_not_model (fun _ => 0%Z)),H,
      assertion_strong_associativity_printed_right_model.
Qed.

Theorem original_strong_associativity_left_model s :
  models two_processors s exchange_right_whole
    (A.strong_temporal (A.strong_temporal algebra_P exchange_right_Q) exchange_right_R).
Proof.
  apply assertion_wand_free_in_printed; [repeat split; exact I |apply assertion_strong_associativity_left_model].
Qed.

Theorem original_strong_associativity_right_not_model s :
  ~ models two_processors s exchange_right_whole
    (A.strong_temporal algebra_P (A.strong_temporal exchange_right_Q exchange_right_R)).
Proof. intros [H _]; exact (original_exchange_strong_spatial_right_not_model s H). Qed.

Theorem original_small_exchange_strong_right_refuted kind :
  (forall p q s r, models two_processors s r (A.strong_temporal p q) ->
    models two_processors s r (assertion_conjunction kind p q)) /\
  ~ (forall p q t s r,
    models two_processors s r (A.strong_temporal (assertion_conjunction kind p q) t) ->
    models two_processors s r (assertion_conjunction kind p (A.strong_temporal q t))).
Proof.
  split; [apply original_strong_inclusion |]. intros H; destruct kind.
  - apply (original_exchange_strong_spatial_right_not_model (fun _ => 0%Z)),H.
    apply assertion_wand_free_in_printed; [repeat split; exact I |].
    eapply assertion_conjunction_mono with (kind := StrongKind);
      [apply assertion_strong_entails_spatial |intros t r HP; exact HP |apply assertion_strong_associativity_left_model].
  - apply (original_exchange_strong_temporal_right_not_model (fun _ => 0%Z)),H.
    apply assertion_wand_free_in_printed; [repeat split; exact I |apply assertion_exchange_strong_temporal_right_model].
  - apply (original_strong_associativity_right_not_model (fun _ => 0%Z)),H,
      original_strong_associativity_left_model.
Qed.

Theorem original_full_exchange_left_model s :
  models two_processors s algebra_whole
    (A.strong_temporal (A.Spatial algebra_P A.Emp) (A.Spatial algebra_Q algebra_R)).
Proof.
  apply assertion_wand_free_in_printed; [repeat split; exact I |apply assertion_full_exchange_left_model].
Qed.

Theorem original_full_exchange_right_not_model s :
  ~ models two_processors s algebra_whole
    (A.Spatial (A.strong_temporal algebra_P algebra_Q) (A.strong_temporal A.Emp algebra_R)).
Proof.
  intros (a & b & Hsp & HP & HB & Htm).
  apply (original_exchange_strong_spatial_left_not_model s).
  exists a,b; split; [exact Hsp |].
  split; [exact HP |apply original_emp_spatial_write_or_emp,HB].
Qed.

Theorem original_full_exchange_refuted :
  ~ (forall s r, models two_processors s r
      (A.strong_temporal (A.Spatial algebra_P A.Emp) (A.Spatial algebra_Q algebra_R)) ->
    models two_processors s r
      (A.Spatial (A.strong_temporal algebra_P algebra_Q) (A.strong_temporal A.Emp algebra_R))).
Proof.
  intros H; apply (original_full_exchange_right_not_model (fun _ => 0%Z)),H,original_full_exchange_left_model.
Qed.
