From Stdlib Require Import List ZArith.
From WMLR Require Import Expressions Machine BufferRelations Separation RepairedSeparation
  Assertions AssertionSemantics ConcreteAssertions RepairedAssertions PersistentAssertions PersistentRules
  TemporalSafety TemporalFence RegionalResources OwnedSafety OwnedRules OwnershipTransfer
  OwnedContainerEntailments AssertionResourceEquivalence AssertionUnits.
Import ListNotations.

(** Paper audit 4A. This index enumerates the three existing conjunctions;
    it is neither an assertion constructor nor an assertion proof system. *)
Inductive conjunction_kind := SpatialKind | TemporalKind | StrongKind.
Definition assertion_conjunction kind :=
  match kind with
  | SpatialKind => A.Spatial
  | TemporalKind => A.Temporal
  | StrongKind => A.strong_temporal
  end.

(** E1/E2, packaged for the schematic audit table. *)
Theorem assertion_conjunction_unit_right kind active p s r :
  persistent_models active s r (assertion_conjunction kind p A.Emp) <->
  persistent_models active s r p.
Proof. destruct kind; [apply assertion_unit_spatial_right |apply assertion_unit_temporal_right |apply assertion_unit_strong_right]. Qed.

Theorem assertion_conjunction_unit_left kind active p s r :
  persistent_models active s r (assertion_conjunction kind A.Emp p) <->
  persistent_models active s r p.
Proof. destruct kind; [apply assertion_unit_spatial_left |apply assertion_unit_temporal_left |apply assertion_unit_strong_left]. Qed.

(** T2/T3. *)
Theorem assertion_conjunction_mono kind active p p' q q' :
  persistent_entails active p p' -> persistent_entails active q q' ->
  persistent_entails active (assertion_conjunction kind p q) (assertion_conjunction kind p' q').
Proof.
  intros HP HQ; destruct kind.
  - apply container_spatial_mono; assumption.
  - apply container_temporal_mono; assumption.
  - intros s r [Hsp Htm]; split;
      [eapply container_spatial_mono |eapply container_temporal_mono]; eauto.
Qed.

(** E6's useful restricted form: two lock tokens cannot both block the
    same active processor. This is a law qualification, not a new rule or
    a change to the calculus's standing two-processor assumption. *)
Lemma assertion_lock_common_blocker active a b i j k :
  active k -> k <> i -> k <> j ->
  lock_atom active (Z.pos i) a -> lock_atom active (Z.pos j) b ->
  disjoint (blocked (underlying a)) (blocked (underlying b)) -> False.
Proof.
  intros Hk Hki Hkj [_ [_ [_ HA]]] [_ [_ [_ HB]]] Hdis.
  apply (Hdis k); [apply HA |apply HB]; auto.
Qed.

Theorem assertion_lock_multiplication_common_blocker kind active i j k :
  active k -> k <> i -> k <> j ->
  persistent_entails active
    (assertion_conjunction kind (A.Lock (EVal (Z.pos i))) (A.Lock (EVal (Z.pos j))))
    (A.Pure BFalse).
Proof.
  intros Hk Hki Hkj s r H; exfalso; destruct kind.
  - destruct H as (a & b & [[[Hd Hdis] Hmerge] Hmarks] & HA & HB).
    exact (assertion_lock_common_blocker active (proj1_sig a) (proj1_sig b) i j k Hk Hki Hkj HA HB Hdis).
  - destruct H as (a & b & [[Hdis Hrest] Htm] & HA & HB).
    exact (assertion_lock_common_blocker active (proj1_sig a) (proj1_sig b) i j k Hk Hki Hkj HA HB Hdis).
  - destruct H as [(a & b & [[[Hd Hdis] Hmerge] Hmarks] & HA & HB) Htm].
    exact (assertion_lock_common_blocker active (proj1_sig a) (proj1_sig b) i j k Hk Hki Hkj HA HB Hdis).
Qed.

Corollary assertion_same_lock_exclusive kind active owner :
  two_active_processors active ->
  persistent_entails active
    (assertion_conjunction kind (A.Lock (EVal (Z.pos owner))) (A.Lock (EVal (Z.pos owner))))
    (A.Pure BFalse).
Proof.
  intros (first & second & Hfirst & Hsecond & Hne).
  destruct (Pos.eq_dec first owner) as [-> |Hnot].
  - apply assertion_lock_multiplication_common_blocker with (k := second); [exact Hsecond |congruence |congruence].
  - apply assertion_lock_multiplication_common_blocker with (k := first); assumption.
Qed.

(** E3 for spatial and temporal conjunction; the strong case has a
    separate counterexample, not an associativity theorem. *)
Theorem assertion_spatial_associative active p q t s r :
  persistent_models active s r (A.Spatial (A.Spatial p q) t) <->
  persistent_models active s r (A.Spatial p (A.Spatial q t)).
Proof. symmetry; apply container_spatial_assoc. Qed.

Theorem assertion_temporal_associative active p q t s r :
  persistent_models active s r (A.Temporal (A.Temporal p q) t) <->
  persistent_models active s r (A.Temporal p (A.Temporal q t)).
Proof.
  split.
  - intros (ab & c & Hout & (a & b & Hab & HP & HQ) & HT).
    destruct (proj2 (repaired_temporal_resource_associative active a b c r)
      (ex_intro _ ab (conj Hab Hout))) as (bc & Hbc & Hout').
    exists a,bc; split; [exact Hout' |split; [exact HP |exists b,c; auto]].
  - intros (a & bc & Hout & HP & b & c & Hbc & HQ & HT).
    destruct (proj1 (repaired_temporal_resource_associative active a b c r)
      (ex_intro _ bc (conj Hbc Hout))) as (ab & Hab & Hout').
    exists ab,c; split; [exact Hout' |split; [exists a,b; auto |exact HT]].
Qed.

(** E4, T1, T5, T6. *)
Theorem assertion_spatial_commutative active p q s r :
  persistent_models active s r (A.Spatial p q) <-> persistent_models active s r (A.Spatial q p).
Proof. split; apply container_spatial_comm. Qed.

Theorem assertion_barrier_entails_emp active annotation :
  persistent_entails active (A.Barrier annotation) A.Emp.
Proof. intros s r [H _]; exact H. Qed.

Theorem assertion_strong_entails_spatial active p q :
  persistent_entails active (A.strong_temporal p q) (A.Spatial p q).
Proof. intros s r [H _]; exact H. Qed.

Theorem assertion_strong_entails_temporal active p q :
  persistent_entails active (A.strong_temporal p q) (A.Temporal p q).
Proof. intros s r [_ H]; exact H. Qed.

Lemma assertion_empty_domain g : empty_atom g -> forall loc, ~ memory_domain (underlying g) loc.
Proof.
  intros [Hh [Hb Hk]] loc [[v H] |[i [v H]]].
  - rewrite Hh in H; discriminate.
  - rewrite Hb in H; contradiction.
Qed.

Lemma assertion_temporal_empty_right_spatial active a b out :
  empty_atom b -> repaired_temporal active a b out -> spatial a b out.
Proof.
  intros HE [_ [[_ [Hh [Hb Hk]]] [_ Hmarks]]]; split; [|exact Hmarks].
  split.
  - split; [intros loc _ H; exact (assertion_empty_domain _ HE loc H)
    |intros i _ H; exact (proj2 (proj2 HE) i H)].
  - split; [exact Hh |]. split; [|exact Hk].
    intros i; rewrite Hb, (proj1 (proj2 HE) i).
    apply interleaves_app.
Qed.

Lemma assertion_temporal_empty_left_spatial active a b out :
  empty_atom a -> repaired_temporal active a b out -> spatial a b out.
Proof.
  intros HE [_ [[_ [Hh [Hb Hk]]] [_ Hmarks]]]; split; [|exact Hmarks].
  split.
  - split; [intros loc H _; exact (assertion_empty_domain _ HE loc H)
    |intros i H _; exact (proj2 (proj2 HE) i H)].
  - split; [exact Hh |]. split; [|exact Hk].
    intros i; rewrite (proj1 (proj2 HE) i), Hb, (proj1 (proj2 HE) i).
    apply interleaves_app.
Qed.

(** E9: arbitrary expressions and arbitrary assertions, including wands. *)
Theorem assertion_strong_barrier_temporal active p annotation s r :
  persistent_models active s r (A.strong_temporal p (A.Barrier annotation)) <->
  persistent_models active s r (A.Temporal p (A.Barrier annotation)).
Proof.
  split; [intros [_ H]; exact H |]. intros H; split; [|exact H].
  destruct H as (a & b & Htm & HP & HB); exists a,b; split; [|auto].
  eapply assertion_temporal_empty_right_spatial; [exact (proj1 HB) |exact Htm].
Qed.

Lemma assertion_barrier_suffix_elim active p annotation :
  persistent_entails active (A.Temporal p (A.Barrier annotation)) p.
Proof.
  intros s r H; apply (proj1 (assertion_unit_temporal_right active p s r)).
  eapply container_temporal_mono; [intros t a Ha; exact Ha
    |apply assertion_barrier_entails_emp |exact H].
Qed.

Lemma assertion_barrier_suffix_buffer active p s r owner : active owner ->
  persistent_models active s r (A.Temporal p (A.Barrier (EVal (Z.pos owner)))) ->
  buffers (resource_memory active r) owner = [].
Proof.
  intros Hi (a & b & [_ [[_ [_ [Hb _]]] [Hbefore _]]] & HP & HE & [Hno |Hmark]); [contradiction |].
  unfold resource_memory; rewrite Hb, Hbefore by exact Hmark.
  rewrite (proj1 (proj2 HE) owner); reflexivity.
Qed.

(** Positive formulas transfer from the final interpretation to the
    original one. This is one-way: stable compatibility is stronger. *)
Lemma assertion_wand_free_in_original active p : wand_free p -> forall s r,
  persistent_models active s r p -> models active s r p.
Proof.
  induction p; intros Hfree s r HP; cbn [wand_free] in Hfree;
    cbn [persistent_models future_satisfies models satisfies
      repaired_interpretation concrete_interpretation] in *; try exact HP; try contradiction.
  - destruct Hfree as [Hf Hg]; destruct HP; [left; eapply IHp1 |right; eapply IHp2]; eauto.
  - destruct Hfree as [Hf Hg]; destruct HP; split; [eapply IHp1 |eapply IHp2]; eauto.
  - destruct HP as [v Hv]; exists v; eapply IHp; eauto.
  - intros v; eapply IHp; [exact Hfree |apply HP].
  - destruct Hfree as [Hf Hg]; destruct HP as (a & b & Hsp & Ha & Hb).
    exists a,b; split; [exact Hsp |split; [eapply IHp1 |eapply IHp2]; eauto].
  - destruct Hfree as [Hf Hg]; destruct HP as (a & b & [_ Htm] & Ha & Hb).
    exists a,b; split; [exact Htm |split; [eapply IHp1 |eapply IHp2]; eauto].
Qed.

Lemma assertion_empty_self_spatial g : empty_atom g -> spatial g g g.
Proof.
  intros HE; pose proof HE as [Hh [Hb Hk]]; split; [|intros i; tauto].
  split.
  - split; [intros loc H _; exact (assertion_empty_domain g HE loc H) |intros i H _; exact (Hk i H)].
  - split.
    + intros loc; unfold heap_override; rewrite Hh; reflexivity.
    + split; [intros i; rewrite Hb; constructor |intros i; tauto].
Qed.

Lemma assertion_spatial_empty_buffers_temporal active a b out : spatial a b out ->
  (forall i, buffers (underlying a) i = []) ->
  (forall i, buffers (underlying b) i = []) -> repaired_temporal active a b out.
Proof.
  intros [[Hcompat [Hheap [Hbuffers Hblocks]]] Hmarks] Ha Hb.
  split; [apply spatial_compatible_stable,Hcompat |]. split.
  - split; [apply spatial_compatible_temporal,Hcompat |].
    split; [exact Hheap |]. split; [|exact Hblocks].
    intros i; specialize (Hbuffers i); rewrite Ha,Hb in *; apply interleaves_nil_left,Hbuffers.
  - split; [intros; apply Ha |exact Hmarks].
Qed.

(** E7, with arbitrary processor annotations. *)
Theorem assertion_barrier_idempotent kind active annotation s r :
  persistent_models active s r (assertion_conjunction kind (A.Barrier annotation) (A.Barrier annotation)) <->
  persistent_models active s r (A.Barrier annotation).
Proof.
  split.
  - intros H; apply (proj1 (assertion_conjunction_unit_right kind active (A.Barrier annotation) s r)).
    eapply assertion_conjunction_mono; [intros t a Ha; exact Ha |apply assertion_barrier_entails_emp |exact H].
  - intros HB.
    assert (Hsp : spatial (proj1_sig r) (proj1_sig r) (proj1_sig r))
      by (apply assertion_empty_self_spatial; exact (proj1 HB)).
    assert (Htm : repaired_temporal active (proj1_sig r) (proj1_sig r) (proj1_sig r)).
    { apply assertion_spatial_empty_buffers_temporal; [exact Hsp |exact (proj1 (proj2 (proj1 HB))) |exact (proj1 (proj2 (proj1 HB)))]. }
    destruct kind; cbn [assertion_conjunction]; try (exists r,r; auto).
    split; exists r,r; auto.
Qed.

(** E10, in fact for independently chosen lock/barrier annotations. *)
Theorem assertion_lock_barrier_temporal_spatial active lock_annotation barrier_annotation s r :
  persistent_models active s r (A.Temporal (A.Lock lock_annotation) (A.Barrier barrier_annotation)) <->
  persistent_models active s r (A.Spatial (A.Lock lock_annotation) (A.Barrier barrier_annotation)).
Proof.
  split; intros (a & b & Hsplit & HL & HB); exists a,b; split; [|auto | |auto].
  - eapply assertion_temporal_empty_right_spatial; [exact (proj1 HB) |exact Hsplit].
  - apply assertion_spatial_empty_buffers_temporal; [exact Hsplit | |exact (proj1 (proj2 (proj1 HB)))].
    change (lock_atom active (eval_expr s lock_annotation) (proj1_sig a)) in HL.
    destruct (eval_expr s lock_annotation); try contradiction; exact (proj1 (proj2 HL)).
Qed.

Lemma assertion_write_domain active loc annotation value g :
  write_atom active (Z.pos loc) annotation value g -> memory_domain (underlying g) loc.
Proof.
  destruct annotation as [|owner|neg]; try contradiction.
  intros [_ [[Hheap [Hbuffers Hblocks]] |[Hheap [Hbuffers Hrest]]]].
  - right; exists owner,value; rewrite Hbuffers,buffer_update_same; left; reflexivity.
  - left; exists value; rewrite Hheap; apply heap_update_same.
Qed.

(** E11: both sides of the displayed equivalence, for arbitrary expressions. *)
Theorem assertion_spatial_writes_exclusive active address actor other value next s r :
  persistent_models active s r (A.Spatial (A.LeadsTo address actor value) (A.LeadsTo address other next)) <->
  persistent_models active s r (A.Pure BFalse).
Proof.
  split; [|intros H; discriminate].
  intros (a & b & [[[Hd Hk] Hmerge] Hmarks] & HA & HB); exfalso.
  change (write_atom active (eval_expr s address) (eval_expr s actor) (eval_expr s value) (proj1_sig a)) in HA.
  change (write_atom active (eval_expr s address) (eval_expr s other) (eval_expr s next) (proj1_sig b)) in HB.
  destruct (eval_expr s address); try contradiction.
  apply (Hd p); eapply assertion_write_domain; eassumption.
Qed.
