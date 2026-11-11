From Stdlib Require Import List ZArith.
From WMLR Require Import Expressions Machine BufferRelations.
Import ListNotations.

(** Definition 5, pp. 99-100. Raw tuples are useful for stating algebraic
    facts; assertion models below use only the well-formed subtype. *)
Record generalized_memory := Generalized {
  underlying : memory;
  complete : processor -> Prop
}.

Definition generalized_well_formed active (g : generalized_memory) : Prop :=
  memory_well_formed active (underlying g) /\
  (forall i, complete g i -> active i) /\
  ((forall i, ~ complete g i) -> forall loc, shared_heap (underlying g) loc = None).

Definition resource (active : processor_domain) :=
  { g : generalized_memory | generalized_well_formed active g }.

Definition memory_domain (m : memory) (loc : location) : Prop :=
  heap_domain (shared_heap m) loc \/ exists i, buffer_domain (buffers m i) loc.

Definition spatial_compatible (a b : memory) : Prop :=
  disjoint (memory_domain a) (memory_domain b) /\ disjoint (blocked a) (blocked b).

Definition jointly_unblocked active (a b : memory) i : Prop :=
  active i /\ ~ blocked a i /\ ~ blocked b i.

(** Section 4.3.2: both processors in the cross-buffer condition must be
    unblocked in the union of the two blocked sets. *)
Definition temporal_compatible active (a b : memory) : Prop :=
  disjoint (blocked a) (blocked b) /\
  (forall i, jointly_unblocked active a b i ->
    disjoint (buffer_domain (buffers a i)) (heap_domain (shared_heap b))) /\
  (forall i j, jointly_unblocked active a b i ->
    jointly_unblocked active a b j -> i <> j ->
    disjoint (buffer_domain (buffers a i)) (buffer_domain (buffers b j))).

Definition memory_merge (R : write_buffer -> write_buffer -> write_buffer -> Prop)
    (a b c : memory) : Prop :=
  (forall loc, shared_heap c loc = heap_override (shared_heap a) (shared_heap b) loc) /\
  (forall i, R (buffers a i) (buffers b i) (buffers c i)) /\
  (forall i, blocked c i <-> blocked a i \/ blocked b i).

Definition memory_spatial a b c : Prop :=
  spatial_compatible a b /\ memory_merge interleaves a b c.

Definition memory_temporal active a b c : Prop :=
  temporal_compatible active a b /\
  memory_merge (fun x y z => z = x ++ y) a b c.

Definition memory_spatiotemporal active a b c : Prop :=
  temporal_compatible active a b /\ memory_merge buffer_overrides a b c.

Definition completeness_union (a b c : generalized_memory) : Prop :=
  forall i, complete c i <-> complete a i \/ complete b i.

Definition spatial (a b c : generalized_memory) : Prop :=
  memory_spatial (underlying a) (underlying b) (underlying c) /\
  completeness_union a b c.

Definition temporal active (a b c : generalized_memory) : Prop :=
  memory_temporal active (underlying a) (underlying b) (underlying c) /\
  (forall i, complete b i -> buffers (underlying a) i = []) /\
  completeness_union a b c.

(** Section 4.3.3 intentionally omits temporal's completeness side condition. *)
Definition spatiotemporal active (a b c : generalized_memory) : Prop :=
  memory_spatiotemporal active (underlying a) (underlying b) (underlying c) /\
  completeness_union a b c.

Definition empty_memory : memory := Memory empty_heap empty_buffers no_blocked.
Definition empty_generalized : generalized_memory := Generalized empty_memory no_blocked.

Definition memory_equiv (a b : memory) : Prop :=
  (forall loc, shared_heap a loc = shared_heap b loc) /\
  (forall i, buffers a i = buffers b i) /\
  (forall i, blocked a i <-> blocked b i).

Definition generalized_equiv (a b : generalized_memory) : Prop :=
  memory_equiv (underlying a) (underlying b) /\
  (forall i, complete a i <-> complete b i).

Lemma empty_generalized_well_formed active :
  generalized_well_formed active empty_generalized.
Proof. repeat split; simpl; intros; contradiction || reflexivity. Qed.

Definition empty_resource_value active : resource active :=
  exist _ empty_generalized (empty_generalized_well_formed active).

Lemma spatial_compatible_comm a b : spatial_compatible a b -> spatial_compatible b a.
Proof. intros [Hd Hk]. split; intros x Hb Ha; [eapply Hd | eapply Hk]; eauto. Qed.

Lemma spatial_compatible_temporal active a b :
  spatial_compatible a b -> temporal_compatible active a b.
Proof.
  intros [Hd Hk]. split; [exact Hk |]. split.
  - intros i _ loc Ha Hb. apply (Hd loc); [right; exists i | left]; assumption.
  - intros i j _ _ _ loc Ha Hb. apply (Hd loc); right; [exists i | exists j]; assumption.
Qed.

Lemma spatial_heap_override_comm a b loc : spatial_compatible a b ->
  heap_override (shared_heap a) (shared_heap b) loc =
  heap_override (shared_heap b) (shared_heap a) loc.
Proof.
  intros [Hd _]. unfold heap_override.
  destruct (shared_heap a loc) eqn:Ha; destruct (shared_heap b loc) eqn:Hb;
    try reflexivity.
  exfalso. apply (Hd loc); left; eexists; eassumption.
Qed.

Theorem spatial_comm a b c : spatial a b c -> spatial b a c.
Proof.
  intros [[Hcompat [Hh [Hb Hk]]] Hg]. split; [split |].
  - apply spatial_compatible_comm, Hcompat.
  - split; [intros loc; rewrite Hh; apply spatial_heap_override_comm, Hcompat |].
    split; [intros i; apply interleaves_comm, Hb | intros i; rewrite Hk; tauto].
  - intros i; rewrite (Hg i); tauto.
Qed.

Theorem spatial_in_spatiotemporal active a b c :
  spatial a b c -> spatiotemporal active a b c.
Proof.
  intros [[Hcompat [Hh [Hb Hk]]] Hg]. split; [split | exact Hg].
  - apply spatial_compatible_temporal, Hcompat.
  - split; [exact Hh |]. split; [|exact Hk].
    intros i. apply disjoint_interleaves_override; [|apply Hb].
    intros loc Ha Hb'. apply (proj1 Hcompat loc); right; exists i; assumption.
Qed.

Theorem temporal_in_spatiotemporal active a b c :
  temporal active a b c -> spatiotemporal active a b c.
Proof.
  intros [[Hcompat [Hh [Hb Hk]]] [_ Hg]]. split; [split | exact Hg].
  - exact Hcompat.
  - split; [exact Hh |]. split; [|exact Hk].
    intros i. rewrite Hb. apply append_overrides.
Qed.

Lemma generalized_merge_well_formed active R a b c :
  generalized_well_formed active a -> generalized_well_formed active b ->
  memory_merge R (underlying a) (underlying b) (underlying c) ->
  completeness_union a b c ->
  (forall z, R [] [] z -> z = []) -> generalized_well_formed active c.
Proof.
  intros [[Hak Hab] [Hac Hah]] [[Hbk Hbb] [Hbc Hbh]]
    [Hh [Hb Hk]] Hg Hnil.
  split.
  - split.
    + intros i Hi. apply Hk in Hi. destruct Hi; [apply Hak | apply Hbk]; assumption.
    + intros i Hi. apply Hnil. specialize (Hb i).
      rewrite (Hab i Hi), (Hbb i Hi) in Hb. exact Hb.
  - split.
    + intros i Hi. apply Hg in Hi. destruct Hi; [apply Hac | apply Hbc]; assumption.
    + intros Hempty loc. rewrite Hh.
      assert (Ha : forall i, ~ complete a i).
      { intros i Hi. apply (Hempty i), Hg. left; exact Hi. }
      assert (Hb' : forall i, ~ complete b i).
      { intros i Hi. apply (Hempty i), Hg. right; exact Hi. }
      unfold heap_override. rewrite (Hah Ha loc), (Hbh Hb' loc). reflexivity.
Qed.

Theorem spatial_well_formed active a b c :
  generalized_well_formed active a -> generalized_well_formed active b ->
  spatial a b c -> generalized_well_formed active c.
Proof.
  intros Ha Hb [[_ Hmerge] Hg].
  eapply (generalized_merge_well_formed active interleaves a b c);
    [exact Ha | exact Hb | exact Hmerge | exact Hg |].
  intros z Hz; apply interleaves_nil_left, Hz.
Qed.

Theorem temporal_well_formed active a b c :
  generalized_well_formed active a -> generalized_well_formed active b ->
  temporal active a b c -> generalized_well_formed active c.
Proof.
  intros Ha Hb [[_ Hmerge] [_ Hg]].
  eapply (generalized_merge_well_formed active (fun x y z => z = x ++ y) a b c);
    [exact Ha | exact Hb | exact Hmerge | exact Hg |].
  intros z Hz; exact Hz.
Qed.

Theorem spatiotemporal_well_formed active a b c :
  generalized_well_formed active a -> generalized_well_formed active b ->
  spatiotemporal active a b c -> generalized_well_formed active c.
Proof.
  intros Ha Hb [[_ Hmerge] Hg].
  eapply (generalized_merge_well_formed active buffer_overrides a b c);
    [exact Ha | exact Hb | exact Hmerge | exact Hg |].
  intros z [Hz _]; apply interleaves_nil_left, Hz.
Qed.

Lemma spatial_empty_left r : spatial empty_generalized r r.
Proof.
  split; [split | intros i; simpl; unfold no_blocked; tauto].
  - split.
    + intros loc [[v H] | [i [v H]]]; discriminate || contradiction.
    + intros i H; contradiction.
  - split.
    + intros loc. simpl. unfold heap_override, empty_heap.
      destruct (shared_heap (underlying r) loc); reflexivity.
    + split; [intros i; apply interleaves_app | intros i; simpl; unfold no_blocked; tauto].
Qed.

Lemma spatial_empty_right r : spatial r empty_generalized r.
Proof. apply spatial_comm, spatial_empty_left. Qed.

Lemma temporal_empty_left active r : temporal active empty_generalized r r.
Proof.
  split; [split | split].
  - apply spatial_compatible_temporal. exact (proj1 (proj1 (spatial_empty_left r))).
  - split.
    + exact (proj1 (proj2 (proj1 (spatial_empty_left r)))).
    + split; [intros i; reflexivity | intros i; simpl; unfold no_blocked; tauto].
  - intros i _; reflexivity.
  - intros i; simpl; unfold no_blocked; tauto.
Qed.

Lemma temporal_empty_right active r : temporal active r empty_generalized r.
Proof.
  split; [split | split].
  - apply spatial_compatible_temporal. exact (proj1 (proj1 (spatial_empty_right r))).
  - split; [intros loc; reflexivity |]. split.
    + intros i; simpl; rewrite app_nil_r; reflexivity.
    + intros i; simpl; unfold no_blocked; tauto.
  - intros i H; contradiction.
  - intros i; simpl; unfold no_blocked; tauto.
Qed.

Lemma spatial_empty_left_unique r out :
  spatial empty_generalized r out -> generalized_equiv out r.
Proof.
  intros [[_ [Hh [Hb Hk]]] Hg]. split; [split |].
  - intros loc. rewrite Hh. simpl. unfold heap_override, empty_heap.
    destruct (shared_heap (underlying r) loc); reflexivity.
  - split; [intros i; apply interleaves_nil_left, Hb | intros i; rewrite Hk; simpl; unfold no_blocked; tauto].
  - intros i; rewrite (Hg i); simpl; unfold no_blocked; tauto.
Qed.

Theorem temporal_functional active a b c d :
  temporal active a b c -> temporal active a b d -> generalized_equiv c d.
Proof.
  intros [[_ [Hch [Hcb Hck]]] [_ Hcg]] [[_ [Hdh [Hdb Hdk]]] [_ Hdg]].
  split; [split |].
  - intros loc; rewrite Hch, Hdh; reflexivity.
  - split; [intros i; rewrite Hcb, Hdb; reflexivity | intros i; rewrite Hck, Hdk; tauto].
  - intros i; rewrite (Hcg i), (Hdg i); tauto.
Qed.

Lemma spatial_empty_right_unique r out :
  spatial r empty_generalized out -> generalized_equiv out r.
Proof. intros H; apply spatial_empty_left_unique, spatial_comm, H. Qed.

Lemma temporal_empty_left_unique active r out :
  temporal active empty_generalized r out -> generalized_equiv out r.
Proof.
  intros H. exact (temporal_functional active _ _ _ _ H (temporal_empty_left active r)).
Qed.

Lemma temporal_empty_right_unique active r out :
  temporal active r empty_generalized out -> generalized_equiv out r.
Proof.
  intros H. exact (temporal_functional active _ _ _ _ H (temporal_empty_right active r)).
Qed.

Lemma spatiotemporal_empty_left active r : spatiotemporal active empty_generalized r r.
Proof. apply spatial_in_spatiotemporal, spatial_empty_left. Qed.

Lemma spatiotemporal_empty_right active r : spatiotemporal active r empty_generalized r.
Proof. apply spatial_in_spatiotemporal, spatial_empty_right. Qed.

Lemma spatiotemporal_spatial_when_compatible active a b c :
  spatial_compatible (underlying a) (underlying b) ->
  spatiotemporal active a b c -> spatial a b c.
Proof.
  intros Hcompat [[_ [Hh [Hb Hk]]] Hg]. split; [split | exact Hg].
  - exact Hcompat.
  - split; [exact Hh |]. split; [intros i; exact (proj1 (Hb i)) | exact Hk].
Qed.

Lemma spatiotemporal_empty_left_unique active r out :
  spatiotemporal active empty_generalized r out -> generalized_equiv out r.
Proof.
  intros H. apply spatial_empty_left_unique.
  eapply spatiotemporal_spatial_when_compatible; [|exact H].
  exact (proj1 (proj1 (spatial_empty_left r))).
Qed.

Lemma spatiotemporal_empty_right_unique active r out :
  spatiotemporal active r empty_generalized out -> generalized_equiv out r.
Proof.
  intros H. apply spatial_empty_right_unique.
  eapply spatiotemporal_spatial_when_compatible; [|exact H].
  exact (proj1 (proj1 (spatial_empty_right r))).
Qed.

(** Reflexive finite flushing, used in the printed frame conjecture. *)
Inductive memory_flushes active : memory -> memory -> Prop :=
| MemoryFlushesRefl m : memory_flushes active m m
| MemoryFlushesNext a b c :
    flush active a b -> memory_flushes active b c -> memory_flushes active a c.
