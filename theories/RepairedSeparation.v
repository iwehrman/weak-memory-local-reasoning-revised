From Stdlib Require Import List ZArith.
From WMLR Require Import Expressions Machine BufferRelations Separation
  OrderedBuffers BufferSelections OrderedSeparation StableCompatibility.
Import ListNotations.

(** The combined candidate repair. The transcription in Separation.v remains
    available for comparison; this model requires stable compatibility and
    event-ordered overriding together. *)
Definition memory_repaired active a b out : Prop :=
  stable_compatible active a b /\ memory_merge ordered_overrides a b out.

Definition repaired_spatiotemporal active a b out : Prop :=
  memory_repaired active (underlying a) (underlying b) (underlying out) /\
  completeness_union a b out.

Definition repaired_temporal active a b out : Prop :=
  stable_compatible active (underlying a) (underlying b) /\ temporal active a b out.

Theorem repaired_in_printed active a b out :
  repaired_spatiotemporal active a b out -> spatiotemporal active a b out.
Proof.
  intros [[Hcompat Hmerge] Hg]. split; [|exact Hg].
  apply ordered_in_printed. split; [apply stable_implies_printed_compatible, Hcompat | exact Hmerge].
Qed.

Lemma spatial_compatible_stable active a b :
  spatial_compatible a b -> stable_compatible active a b.
Proof.
  intros [Hd Hk]. split; [exact Hk |]. split.
  - intros i _ loc Ha Hb. apply (Hd loc); [right; exists i | left]; assumption.
  - intros i j _ _ _ loc Ha Hb. apply (Hd loc); right; [exists i | exists j]; assumption.
Qed.

Theorem spatial_in_repaired active a b out :
  spatial a b out -> repaired_spatiotemporal active a b out.
Proof.
  intros [Hsp Hg]. split; [|exact Hg]. split.
  - apply spatial_compatible_stable, (proj1 Hsp).
  - exact (proj2 (spatial_in_ordered active _ _ _ Hsp)).
Qed.

Theorem repaired_temporal_in_spatiotemporal active a b out :
  repaired_temporal active a b out -> repaired_spatiotemporal active a b out.
Proof.
  intros [Hcompat [Htemp [_ Hg]]]. split; [|exact Hg].
  split; [exact Hcompat | exact (proj2 (temporal_in_ordered active _ _ _ Htemp))].
Qed.

Theorem repaired_well_formed active a b out :
  generalized_well_formed active a -> generalized_well_formed active b ->
  repaired_spatiotemporal active a b out -> generalized_well_formed active out.
Proof.
  intros Ha Hb H. eapply spatiotemporal_well_formed; [exact Ha | exact Hb |].
  apply repaired_in_printed, H.
Qed.

Lemma repaired_empty_left active r : repaired_spatiotemporal active empty_generalized r r.
Proof. apply spatial_in_repaired, spatial_empty_left. Qed.

Lemma repaired_empty_right active r : repaired_spatiotemporal active r empty_generalized r.
Proof. apply spatial_in_repaired, spatial_empty_right. Qed.

Lemma repaired_empty_left_unique active r out :
  repaired_spatiotemporal active empty_generalized r out -> generalized_equiv out r.
Proof. intros H; apply (spatiotemporal_empty_left_unique active), repaired_in_printed, H. Qed.

Lemma repaired_empty_right_unique active r out :
  repaired_spatiotemporal active r empty_generalized out -> generalized_equiv out r.
Proof. intros H; apply (spatiotemporal_empty_right_unique active), repaired_in_printed, H. Qed.

(** Compatibility depends only on domains and blocking, not on the order of
    an intermediate merge. This transfers the compatibility theorem from
    concatenated buffers to every event-ordered merge. *)
Definition same_footprint a b : Prop :=
  (forall loc, heap_domain (shared_heap a) loc <-> heap_domain (shared_heap b) loc) /\
  (forall i loc, buffer_domain (buffers a i) loc <-> buffer_domain (buffers b i) loc) /\
  (forall i, blocked a i <-> blocked b i).

Lemma same_footprint_refl a : same_footprint a a.
Proof. repeat split; auto. Qed.

Lemma same_footprint_sym a b : same_footprint a b -> same_footprint b a.
Proof. intros [Hh [Hb Hk]]. repeat split; intros; [apply Hh | apply Hh | apply Hb | apply Hb | apply Hk | apply Hk]; assumption. Qed.

Lemma merge_footprint a b out :
  memory_merge ordered_overrides a b out -> same_footprint out (temporal_join a b).
Proof.
  intros [Hh [Hb Hk]]. split.
  - intros loc. unfold heap_domain. rewrite Hh; reflexivity.
  - split; [|exact Hk]. intros i loc. cbn [temporal_join buffers].
    rewrite buffer_app_domain. apply ordered_domain, Hb.
Qed.

Lemma stable_compatible_footprint active a a' b b' :
  same_footprint a a' -> same_footprint b b' ->
  stable_compatible active a b -> stable_compatible active a' b'.
Proof.
  intros [Hah [Hab Hak]] [Hbh [Hbb Hbk]] [Hk [Hh Hb]]. split.
  - intros i Ha Hb'. apply (Hk i); [apply Hak | apply Hbk]; assumption.
  - split.
    + intros i Hi loc Ha Hb'. apply (Hh i Hi loc); [apply Hab | apply Hbh]; assumption.
    + intros i j Hi Hj Hneq loc Ha Hb'. apply (Hb i j Hi Hj Hneq loc);
        [apply Hab | apply Hbb]; assumption.
Qed.

Lemma stable_merge_associative active a b c ab bc :
  memory_merge ordered_overrides a b ab -> memory_merge ordered_overrides b c bc ->
  (stable_compatible active a bc /\ stable_compatible active b c <->
   stable_compatible active a b /\ stable_compatible active ab c).
Proof.
  intros Hab Hbc. pose proof (merge_footprint _ _ _ Hab) as Fab.
  pose proof (merge_footprint _ _ _ Hbc) as Fbc. split.
  - intros [Ha Hbc']. assert (Hjoin : stable_compatible active a (temporal_join b c)).
    { eapply stable_compatible_footprint; [apply same_footprint_refl | exact Fbc | exact Ha]. }
    destruct (proj1 (stable_compatibility_associative active a b c) (conj Hjoin Hbc')) as [Hab' Hc].
    split; [exact Hab' |]. eapply stable_compatible_footprint;
      [apply same_footprint_sym, Fab | apply same_footprint_refl | exact Hc].
  - intros [Hab' Hc]. assert (Hjoin : stable_compatible active (temporal_join a b) c).
    { eapply stable_compatible_footprint; [exact Fab | apply same_footprint_refl | exact Hc]. }
    destruct (proj2 (stable_compatibility_associative active a b c) (conj Hab' Hjoin)) as [Ha Hbc'].
    split; [|exact Hbc']. eapply stable_compatible_footprint;
      [apply same_footprint_refl | apply same_footprint_sym, Fbc | exact Ha].
Qed.

Definition regroup_left a b c out := Memory
  (heap_override (shared_heap a) (shared_heap b))
  (fun i => select_left (buffers a i) (buffers b i) (buffers c i) (buffers out i))
  (fun i => blocked a i \/ blocked b i).

Definition regroup_right a b c out := Memory
  (heap_override (shared_heap b) (shared_heap c))
  (fun i => select_right (buffers a i) (buffers b i) (buffers c i) (buffers out i))
  (fun i => blocked b i \/ blocked c i).

Lemma merge_regroup_left a b c bc out :
  memory_merge ordered_overrides b c bc -> memory_merge ordered_overrides a bc out ->
  memory_merge ordered_overrides a b (regroup_left a b c out) /\
  memory_merge ordered_overrides (regroup_left a b c out) c out.
Proof.
  intros [Hbch [Hbcb Hbck]] [Hh [Hb Hk]].
  assert (Hbuffers : forall i,
    ordered_overrides (buffers a i) (buffers b i) (buffers (regroup_left a b c out) i) /\
    ordered_overrides (buffers (regroup_left a b c out) i) (buffers c i) (buffers out i)).
  { intros i. apply (select_left_spec _ _ _ (buffers bc i)); [apply Hbcb | apply Hb]. }
  split; split.
  - intros loc; reflexivity.
  - split; [intros i; exact (proj1 (Hbuffers i)) | intros i; reflexivity].
  - intros loc. rewrite Hh. cbn [regroup_left shared_heap].
    unfold heap_override. rewrite Hbch. unfold heap_override.
    destruct (shared_heap c loc); [reflexivity | destruct (shared_heap b loc); reflexivity].
  - split; [intros i; exact (proj2 (Hbuffers i)) |].
    intros i; rewrite Hk, Hbck; cbn [regroup_left blocked]; tauto.
Qed.

Lemma merge_regroup_right a b c ab out :
  memory_merge ordered_overrides a b ab -> memory_merge ordered_overrides ab c out ->
  memory_merge ordered_overrides b c (regroup_right a b c out) /\
  memory_merge ordered_overrides a (regroup_right a b c out) out.
Proof.
  intros [Habh [Habb Habk]] [Hh [Hb Hk]].
  assert (Hbuffers : forall i,
    ordered_overrides (buffers b i) (buffers c i) (buffers (regroup_right a b c out) i) /\
    ordered_overrides (buffers a i) (buffers (regroup_right a b c out) i) (buffers out i)).
  { intros i. apply (select_right_spec _ _ _ (buffers ab i)); [apply Habb | apply Hb]. }
  split; split.
  - intros loc; reflexivity.
  - split; [intros i; exact (proj1 (Hbuffers i)) | intros i; reflexivity].
  - intros loc. rewrite Hh. cbn [regroup_right shared_heap].
    unfold heap_override. rewrite Habh. unfold heap_override.
    destruct (shared_heap c loc); [reflexivity | destruct (shared_heap b loc); reflexivity].
  - split; [intros i; exact (proj2 (Hbuffers i)) |].
    intros i; rewrite Hk, Habk; cbn [regroup_right blocked]; tauto.
Qed.

Theorem memory_repaired_associative active a b c out :
  (exists bc, memory_repaired active b c bc /\ memory_repaired active a bc out) <->
  (exists ab, memory_repaired active a b ab /\ memory_repaired active ab c out).
Proof.
  split; intros [middle [[Hfirst Mfirst] [Hsecond Msecond]]].
  - destruct (merge_regroup_left _ _ _ _ _ Mfirst Msecond) as [Mab Mout].
    destruct (proj1 (stable_merge_associative active a b c _ _ Mab Mfirst)
      (conj Hsecond Hfirst)) as [Hab Hout].
    exists (regroup_left a b c out). split; split; assumption.
  - destruct (merge_regroup_right _ _ _ _ _ Mfirst Msecond) as [Mbc Mout].
    destruct (proj2 (stable_merge_associative active a b c _ _ Mfirst Mbc)
      (conj Hfirst Hsecond)) as [Hout Hbc].
    exists (regroup_right a b c out). split; split; assumption.
Qed.

Theorem repaired_associative active a b c out :
  (exists bc, repaired_spatiotemporal active b c bc /\ repaired_spatiotemporal active a bc out) <->
  (exists ab, repaired_spatiotemporal active a b ab /\ repaired_spatiotemporal active ab c out).
Proof.
  split; intros [middle [[Hfirst Gfirst] [Hsecond Gsecond]]].
  - destruct (proj1 (memory_repaired_associative active (underlying a) (underlying b)
      (underlying c) (underlying out)) (ex_intro _ (underlying middle) (conj Hfirst Hsecond)))
      as [ab [Hab Hout]].
    exists (Generalized ab (fun i => complete a i \/ complete b i)).
    split; split; try assumption.
    + intros i; reflexivity.
    + intros i; rewrite (Gsecond i), (Gfirst i); simpl; tauto.
  - destruct (proj2 (memory_repaired_associative active (underlying a) (underlying b)
      (underlying c) (underlying out)) (ex_intro _ (underlying middle) (conj Hfirst Hsecond)))
      as [bc [Hbc Hout]].
    exists (Generalized bc (fun i => complete b i \/ complete c i)).
    split; split; try assumption.
    + intros i; reflexivity.
    + intros i; rewrite (Gsecond i), (Gfirst i); simpl; tauto.
Qed.

(** The witnesses remain valid resources, not merely raw tuples. *)
Theorem repaired_resource_associative active (a b c out : resource active) :
  (exists bc : resource active,
    repaired_spatiotemporal active (proj1_sig b) (proj1_sig c) (proj1_sig bc) /\
    repaired_spatiotemporal active (proj1_sig a) (proj1_sig bc) (proj1_sig out)) <->
  (exists ab : resource active,
    repaired_spatiotemporal active (proj1_sig a) (proj1_sig b) (proj1_sig ab) /\
    repaired_spatiotemporal active (proj1_sig ab) (proj1_sig c) (proj1_sig out)).
Proof.
  split; intros [middle [Hfirst Hsecond]].
  - destruct (proj1 (repaired_associative active _ _ _ _)
      (ex_intro _ (proj1_sig middle) (conj Hfirst Hsecond))) as [ab [Hab Hout]].
    exists (exist _ ab (repaired_well_formed active _ _ _ (proj2_sig a) (proj2_sig b) Hab)).
    split; assumption.
  - destruct (proj2 (repaired_associative active _ _ _ _)
      (ex_intro _ (proj1_sig middle) (conj Hfirst Hsecond))) as [bc [Hbc Hout]].
    exists (exist _ bc (repaired_well_formed active _ _ _ (proj2_sig b) (proj2_sig c) Hbc)).
    split; assumption.
Qed.

Definition generalized_temporal_join a b := Generalized
  (temporal_join (underlying a) (underlying b)) (fun i => complete a i \/ complete b i).

Lemma temporal_join_ordered_merge a b : memory_merge ordered_overrides a b (temporal_join a b).
Proof. split; [intros loc; reflexivity |]. split; [intros i; apply ordered_append | intros i; reflexivity]. Qed.

Lemma repaired_temporal_join active a b :
  stable_compatible active (underlying a) (underlying b) ->
  (forall i, complete b i -> buffers (underlying a) i = []) ->
  repaired_temporal active a b (generalized_temporal_join a b).
Proof.
  intros Hstable Hcomplete. split; [exact Hstable |]. split.
  - split; [apply stable_implies_printed_compatible, Hstable |].
    split; [intros loc; reflexivity |]. split; intros i; reflexivity.
  - split; [exact Hcomplete | intros i; reflexivity].
Qed.

(** Temporal association also preserves its additional completeness side
    condition. This is distinct from the spatiotemporal law above. *)
Theorem repaired_temporal_associative active a b c out :
  (exists bc, repaired_temporal active b c bc /\ repaired_temporal active a bc out) <->
  (exists ab, repaired_temporal active a b ab /\ repaired_temporal active ab c out).
Proof.
  split; intros [middle [[Sfirst Tfirst] [Ssecond Tsecond]]].
  - pose proof (proj2 (temporal_in_ordered active _ _ _ (proj1 Tfirst))) as Mfirst.
    pose proof (temporal_join_ordered_merge (underlying a) (underlying b)) as Mab.
    destruct (proj1 (stable_merge_associative active _ _ _ _ _ Mab Mfirst)
      (conj Ssecond Sfirst)) as [Sab Sout].
    destruct Tfirst as [[_ [Hfh [Hfb Hfk]]] [Hfc Hfg]].
    destruct Tsecond as [[_ [Hsh [Hsb Hsk]]] [Hsc Hsg]].
    exists (generalized_temporal_join a b). split.
    + apply repaired_temporal_join; [exact Sab |].
      intros i Hi. apply Hsc, (Hfg i); left; exact Hi.
    + split; [exact Sout |]. split.
      * split; [apply stable_implies_printed_compatible, Sout |]. split.
        -- intros loc. rewrite Hsh. cbn [generalized_temporal_join underlying temporal_join shared_heap].
           unfold heap_override. rewrite Hfh. unfold heap_override.
           destruct (shared_heap (underlying c) loc); [reflexivity |].
           destruct (shared_heap (underlying b) loc); reflexivity.
        -- split.
           ++ intros i. rewrite Hsb, Hfb. cbn [generalized_temporal_join underlying temporal_join buffers].
              apply app_assoc.
           ++ intros i. rewrite Hsk, Hfk. cbn [generalized_temporal_join underlying temporal_join blocked]; tauto.
      * split.
        -- intros i Hi. cbn [generalized_temporal_join underlying temporal_join buffers].
           rewrite (Hfc i Hi). assert (Ha : buffers (underlying a) i = []).
           { apply Hsc, (Hfg i); right; exact Hi. }
           rewrite Ha; reflexivity.
        -- intros i; rewrite (Hsg i), (Hfg i); cbn [generalized_temporal_join complete]; tauto.
  - pose proof (proj2 (temporal_in_ordered active _ _ _ (proj1 Tfirst))) as Mfirst.
    pose proof (temporal_join_ordered_merge (underlying b) (underlying c)) as Mbc.
    destruct (proj2 (stable_merge_associative active _ _ _ _ _ Mfirst Mbc)
      (conj Sfirst Ssecond)) as [Sout Sbc].
    destruct Tfirst as [[_ [Hfh [Hfb Hfk]]] [Hfc Hfg]].
    destruct Tsecond as [[_ [Hsh [Hsb Hsk]]] [Hsc Hsg]].
    assert (Hempty : forall i, complete c i ->
      buffers (underlying a) i = [] /\ buffers (underlying b) i = []).
    { intros i Hi. specialize (Hsc i Hi). rewrite Hfb in Hsc. apply app_eq_nil, Hsc. }
    exists (generalized_temporal_join b c). split.
    + apply repaired_temporal_join; [exact Sbc |]. intros i Hi; exact (proj2 (Hempty i Hi)).
    + split; [exact Sout |]. split.
      * split; [apply stable_implies_printed_compatible, Sout |]. split.
        -- intros loc. rewrite Hsh. cbn [generalized_temporal_join underlying temporal_join shared_heap].
           unfold heap_override. rewrite Hfh. unfold heap_override.
           destruct (shared_heap (underlying c) loc); [reflexivity |].
           destruct (shared_heap (underlying b) loc); reflexivity.
        -- split.
           ++ intros i. rewrite Hsb, Hfb. cbn [generalized_temporal_join underlying temporal_join buffers].
              symmetry; apply app_assoc.
           ++ intros i. rewrite Hsk, Hfk. cbn [generalized_temporal_join underlying temporal_join blocked]; tauto.
      * split.
        -- intros i [Hi | Hi]; [apply Hfc, Hi | exact (proj1 (Hempty i Hi))].
        -- intros i; rewrite (Hsg i), (Hfg i); cbn [generalized_temporal_join complete]; tauto.
Qed.

Theorem repaired_temporal_resource_associative active (a b c out : resource active) :
  (exists bc : resource active,
    repaired_temporal active (proj1_sig b) (proj1_sig c) (proj1_sig bc) /\
    repaired_temporal active (proj1_sig a) (proj1_sig bc) (proj1_sig out)) <->
  (exists ab : resource active,
    repaired_temporal active (proj1_sig a) (proj1_sig b) (proj1_sig ab) /\
    repaired_temporal active (proj1_sig ab) (proj1_sig c) (proj1_sig out)).
Proof.
  split; intros [middle [Hfirst Hsecond]].
  - destruct (proj1 (repaired_temporal_associative active _ _ _ _)
      (ex_intro _ (proj1_sig middle) (conj Hfirst Hsecond))) as [ab [Hab Hout]].
    exists (exist _ ab (temporal_well_formed active _ _ _ (proj2_sig a) (proj2_sig b) (proj2 Hab))).
    split; assumption.
  - destruct (proj2 (repaired_temporal_associative active _ _ _ _)
      (ex_intro _ (proj1_sig middle) (conj Hfirst Hsecond))) as [bc [Hbc Hout]].
    exists (exist _ bc (temporal_well_formed active _ _ _ (proj2_sig b) (proj2_sig c) (proj2 Hbc))).
    split; assumption.
Qed.
