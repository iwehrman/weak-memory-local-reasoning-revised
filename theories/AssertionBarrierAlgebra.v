From Stdlib Require Import List ZArith.
From WMLR Require Import Expressions Machine BufferRelations Separation StableCompatibility
  RepairedSeparation GeneralizedFlushing Assertions AssertionSemantics ConcreteAssertions
  PersistentAssertions PersistentRules TemporalSafety OwnershipTransfer PrivateOwnership
  OwnedContainerEntailments AssertionResourceEquivalence AssertionUnits AssertionAlgebra.
Import ListNotations.

(** Existing resource operations for audit E8. These add no transitions,
    assertion atoms or validity predicates. *)
Definition assertion_add_marks active (a b : resource active) : resource active.
Proof.
  refine (exist _ (Generalized (resource_memory active a)
    (fun i => complete (proj1_sig a) i \/ complete (proj1_sig b) i)) _).
  split; [exact (proj1 (proj2_sig a)) |]. split.
  - intros i [H |H]; [exact (proj1 (proj2 (proj2_sig a)) i H)
    |exact (proj1 (proj2 (proj2_sig b)) i H)].
  - intros Hnone; apply (proj2 (proj2 (proj2_sig a))); intros i H; apply (Hnone i); left; exact H.
Defined.

Lemma assertion_models_add_marks active p s a b :
  persistent_models active s a p -> persistent_models active s (assertion_add_marks active a b) p.
Proof.
  apply persistent_models_mark_extension; [apply assertion_memory_equiv_refl |intros i H; left; exact H].
Qed.

Definition assertion_empty_mark_meet active (a b : resource active) : resource active.
Proof.
  refine (exist _ (Generalized empty_memory
    (fun i => complete (proj1_sig a) i /\ complete (proj1_sig b) i)) _).
  split; [exact (proj1 (empty_generalized_well_formed active)) |]. split.
  - intros i [H _]; exact (proj1 (proj2 (proj2_sig a)) i H).
  - intros; reflexivity.
Defined.

Lemma assertion_barrier_meet active annotation s a b :
  persistent_models active s a (A.Barrier annotation) ->
  persistent_models active s b (A.Barrier annotation) ->
  persistent_models active s (assertion_empty_mark_meet active a b) (A.Barrier annotation).
Proof.
  intros [_ HA] [_ HB]; split.
  - split; [intros; reflexivity |]. split; [intros; reflexivity |intros i H; exact H].
  - destruct (eval_expr s annotation); try exact I; cbn in *; tauto.
Qed.

Lemma assertion_empty_suffix_intro active (a b : resource active) :
  empty_atom (proj1_sig b) ->
  (forall i, complete (proj1_sig b) i -> buffers (resource_memory active a) i = []) ->
  (forall i, complete (proj1_sig b) i -> complete (proj1_sig a) i) ->
  repaired_temporal active (proj1_sig a) (proj1_sig b) (proj1_sig a).
Proof.
  intros [Hh [Hb Hk]] Hdrain Hmarks.
  assert (Hstable : stable_compatible active (resource_memory active a) (resource_memory active b)).
  { split; [intros i _ H; exact (Hk i H) |]. split.
    - intros i _ loc _ [v H]; rewrite Hh in H; discriminate.
    - intros i j _ _ _ loc _ [v H]; rewrite Hb in H; contradiction. }
  split; [exact Hstable |]. split.
  - split; [apply stable_implies_original_compatible,Hstable |].
    split; [intros loc; unfold heap_override; rewrite Hh; reflexivity |].
    split; [intros i; rewrite Hb,app_nil_r; reflexivity |].
    intros i; split; [auto |intros [H |H]; [exact H |exfalso; exact (Hk i H)]].
  - split; [exact Hdrain |intros i; split; [auto |intros [H |H]; auto]].
Qed.

(** A barrier suffix preserves P and can be witnessed by an empty barrier
    whose marks are already present and whose processors are drained. *)
Lemma assertion_barrier_suffix_shape active p annotation s r :
  persistent_models active s r (A.Temporal p (A.Barrier annotation)) <->
  persistent_models active s r p /\ exists bar : resource active,
    persistent_models active s bar (A.Barrier annotation) /\
    (forall i, complete (proj1_sig bar) i -> buffers (resource_memory active r) i = []) /\
    (forall i, complete (proj1_sig bar) i -> complete (proj1_sig r) i).
Proof.
  split.
  - intros H; split; [eapply assertion_barrier_suffix_elim; exact H |].
    destruct H as (a & bar & [_ [[_ [_ [Hb _]]] [Hbefore Hmarks]]] & HP & HB).
    exists bar; split; [exact HB |]. split.
    + intros i Hi; unfold resource_memory; rewrite Hb,Hbefore by exact Hi.
      rewrite (proj1 (proj2 (proj1 HB)) i); reflexivity.
    + intros i Hi; apply Hmarks; right; exact Hi.
  - intros [HP (bar & HB & Hdrain & Hmarks)]; exists r,bar; split; [|auto].
    apply assertion_empty_suffix_intro; [exact (proj1 HB) |exact Hdrain |exact Hmarks].
Qed.

Lemma assertion_barrier_suffix_add active p annotation s a bar :
  persistent_models active s a p -> persistent_models active s bar (A.Barrier annotation) ->
  (forall i, complete (proj1_sig bar) i -> buffers (resource_memory active a) i = []) ->
  persistent_models active s (assertion_add_marks active a bar) (A.Temporal p (A.Barrier annotation)).
Proof.
  intros HP HB Hdrain; apply assertion_barrier_suffix_shape; split.
  - apply assertion_models_add_marks,HP.
  - exists bar; split; [exact HB |]. split; [exact Hdrain |intros i H; right; exact H].
Qed.

(** E8 for spatial conjunction, both directions and the full grammar. *)
Theorem assertion_barrier_distributes_spatial active p q annotation s r :
  persistent_models active s r (A.Temporal (A.Spatial p q) (A.Barrier annotation)) <->
  persistent_models active s r
    (A.Spatial (A.Temporal p (A.Barrier annotation)) (A.Temporal q (A.Barrier annotation))).
Proof.
  split.
  - intros (middle & bar & Houter & (a & b & [Hsp Hmarks] & HP & HQ) & HB).
    pose proof (temporal_emp_memory_right _ _ _ _ (proj1 HB) Houter) as [Eh [Eb Ek]].
    assert (Hdrain : forall i, complete (proj1_sig bar) i ->
      buffers (resource_memory active a) i = [] /\ buffers (resource_memory active b) i = []).
    { intros i Hi; apply (spatial_empty_buffer_parts _ _ _ _ Hsp).
      exact (proj1 (proj2 (proj2 Houter)) i Hi). }
    exists (assertion_add_marks active a bar),(assertion_add_marks active b bar); split.
    + split.
      * destruct Hsp as [Hcompat [Hh [Hb Hk]]]; split; [exact Hcompat |].
        split; [intros loc; rewrite Eh; apply Hh |].
        split; [intros i; rewrite Eb; apply Hb |intros i; rewrite Ek; apply Hk].
      * intros i; rewrite (proj2 (proj2 (proj2 Houter)) i),(Hmarks i); cbn; tauto.
    + split; apply assertion_barrier_suffix_add; try assumption;
        intros i Hi; exact (proj1 (Hdrain i Hi)) || exact (proj2 (Hdrain i Hi)).
  - intros (a & b & Hsp & HP & HQ).
    apply assertion_barrier_suffix_shape in HP; destruct HP as [HP (ba & HBA & Hda & Hma)].
    apply assertion_barrier_suffix_shape in HQ; destruct HQ as [HQ (bb & HBB & Hdb & Hmb)].
    apply assertion_barrier_suffix_shape; split; [exists a,b; auto |].
    exists (assertion_empty_mark_meet active ba bb); split; [apply assertion_barrier_meet; assumption |].
    split.
    + intros i [HA HB]; destruct Hsp as [[_ [_ [Hbuf _]]] _].
      unfold resource_memory in Hda,Hdb |- *.
      specialize (Hbuf i); rewrite (Hda i HA),(Hdb i HB) in Hbuf; apply interleaves_nil_left,Hbuf.
    + intros i [HA HB]; apply (proj2 Hsp i); left; apply Hma,HA.
Qed.

(** E8 for temporal conjunction. Adding the barrier's marks to the later
    part is justified because the entire earlier concatenation is drained. *)
Theorem assertion_barrier_distributes_temporal active p q annotation s r :
  persistent_models active s r (A.Temporal (A.Temporal p q) (A.Barrier annotation)) <->
  persistent_models active s r
    (A.Temporal (A.Temporal p (A.Barrier annotation)) (A.Temporal q (A.Barrier annotation))).
Proof.
  split.
  - intros (middle & bar & Houter & (a & b & Hinner & HP & HQ) & HB).
    pose proof (temporal_emp_memory_right _ _ _ _ (proj1 HB) Houter) as [Eh [Eb Ek]].
    assert (Hdrain : forall i, complete (proj1_sig bar) i ->
      buffers (resource_memory active a) i = [] /\ buffers (resource_memory active b) i = []).
    { intros i Hi; pose proof (proj1 (proj2 (proj2 Houter)) i Hi) as Hempty.
      rewrite (proj1 (proj2 (proj2 (proj1 (proj2 Hinner)))) i) in Hempty.
      apply app_eq_nil,Hempty. }
    exists (assertion_add_marks active a bar),(assertion_add_marks active b bar); split.
    + destruct Hinner as [Hstable [[Hcompat [Hh [Hb Hk]]] [Hbefore Hmarks]]].
      split; [exact Hstable |]. split.
      * split; [exact Hcompat |]. split; [intros loc; rewrite Eh; apply Hh |].
        split; [intros i; rewrite Eb; apply Hb |intros i; rewrite Ek; apply Hk].
      * split.
        -- intros i [Hi |Hi]; [apply Hbefore,Hi |exact (proj1 (Hdrain i Hi))].
        -- intros i; rewrite (proj2 (proj2 (proj2 Houter)) i),(Hmarks i); cbn; tauto.
    + split; apply assertion_barrier_suffix_add; try assumption;
        intros i Hi; exact (proj1 (Hdrain i Hi)) || exact (proj2 (Hdrain i Hi)).
  - intros (a & b & Htm & HP & HQ).
    apply assertion_barrier_suffix_shape in HP; destruct HP as [HP (ba & HBA & Hda & Hma)].
    apply assertion_barrier_suffix_shape in HQ; destruct HQ as [HQ (bb & HBB & Hdb & Hmb)].
    apply assertion_barrier_suffix_shape; split; [exists a,b; auto |].
    exists (assertion_empty_mark_meet active ba bb); split; [apply assertion_barrier_meet; assumption |].
    split.
    + intros i [HA HB]; destruct Htm as [_ [[_ [_ [Hbuf _]]] _]].
      unfold resource_memory in Hda,Hdb |- *.
      rewrite Hbuf,(Hda i HA),(Hdb i HB); reflexivity.
    + intros i [HA HB]; apply (proj2 (proj2 (proj2 Htm)) i); left; apply Hma,HA.
Qed.

(** E8 for the independent-witness abbreviation; no associativity of that
    abbreviation is used or claimed. *)
Theorem assertion_barrier_distributes_strong active p q annotation s r :
  persistent_models active s r (A.Temporal (A.strong_temporal p q) (A.Barrier annotation)) <->
  persistent_models active s r
    (A.strong_temporal (A.Temporal p (A.Barrier annotation)) (A.Temporal q (A.Barrier annotation))).
Proof.
  split.
  - intros H; split.
    + apply assertion_barrier_distributes_spatial; eapply container_temporal_mono;
        [apply assertion_strong_entails_spatial |intros t a Ha; exact Ha |exact H].
    + apply assertion_barrier_distributes_temporal; eapply container_temporal_mono;
        [apply assertion_strong_entails_temporal |intros t a Ha; exact Ha |exact H].
  - intros [Hsp Htm]; apply assertion_barrier_distributes_spatial in Hsp.
    apply assertion_barrier_suffix_shape in Hsp; destruct Hsp as [Hsp Hbar].
    apply assertion_barrier_suffix_shape; split; [|exact Hbar]. split; [exact Hsp |].
    eapply container_temporal_mono; [apply assertion_barrier_suffix_elim |apply assertion_barrier_suffix_elim |exact Htm].
Qed.

Theorem assertion_barrier_distribution kind active p q annotation s r :
  persistent_models active s r (A.Temporal (assertion_conjunction kind p q) (A.Barrier annotation)) <->
  persistent_models active s r (assertion_conjunction kind
    (A.Temporal p (A.Barrier annotation)) (A.Temporal q (A.Barrier annotation))).
Proof.
  destruct kind; [apply assertion_barrier_distributes_spatial
    |apply assertion_barrier_distributes_temporal |apply assertion_barrier_distributes_strong].
Qed.
