From Stdlib Require Import List ZArith.
From WMLR Require Import Expressions Machine BufferRelations OrderedBuffers Separation RepairedSeparation
  RepairedFlushing PersistentAssertions OwnershipProtocol PrivateOwnership.
Import ListNotations.

Lemma spatial_merge_domain a b out : memory_merge interleaves a b out -> forall loc,
  memory_domain out loc <-> memory_domain a loc \/ memory_domain b loc.
Proof.
  intros [Hh [Hb Hk]] loc. split.
  - intros [[v Hv] |[i [v Hv]]].
    + rewrite Hh in Hv; unfold heap_override in Hv. destruct (shared_heap b loc) eqn:E.
      * right; left; eexists; exact E.
      * left; left; exists v; exact Hv.
    + apply (interleaves_in _ _ _ _ (Hb i)) in Hv. destruct Hv;
        [left |right]; right; exists i, v; assumption.
  - intros [[[v Hv] |[i [v Hv]]] |[[v Hv] |[i [v Hv]]]].
    + left. unfold heap_domain; rewrite Hh; unfold heap_override.
      destruct (shared_heap b loc); eexists; reflexivity || exact Hv.
    + right; exists i, v; apply (interleaves_in _ _ _ _ (Hb i)); auto.
    + left; exists v; rewrite Hh; unfold heap_override; rewrite Hv; reflexivity.
    + right; exists i, v; apply (interleaves_in _ _ _ _ (Hb i)); auto.
Qed.

Lemma compatible_merge_right a b c bc : memory_merge interleaves b c bc ->
  (spatial_compatible a bc <-> spatial_compatible a b /\ spatial_compatible a c).
Proof.
  intros Hmerge. pose proof (spatial_merge_domain _ _ _ Hmerge) as Hd.
  destruct Hmerge as [_ [_ Hk]]. unfold spatial_compatible, disjoint.
  split.
  - intros [Hdomain Hblocks]. split; split; intros x Ha Hb;
      [apply (Hdomain x Ha), Hd; left |apply (Hblocks x Ha), Hk; left
       |apply (Hdomain x Ha), Hd; right |apply (Hblocks x Ha), Hk; right]; exact Hb.
  - intros [[Hab Kab] [Hac Kac]]. split; intros x Ha Hb.
    + apply Hd in Hb; destruct Hb; [apply (Hab x Ha) |apply (Hac x Ha)]; assumption.
    + apply Hk in Hb; destruct Hb; [apply (Kab x Ha) |apply (Kac x Ha)]; assumption.
Qed.

Lemma repaired_merge_interleaves active a b out : memory_repaired active a b out -> memory_merge interleaves a b out.
Proof. intros [_ [Hh [Hb Hk]]]; split; [exact Hh |]; split; [intros i; apply ordered_interleaves, Hb |exact Hk]. Qed.

Theorem memory_spatial_associative a b c out :
  (exists bc, memory_spatial b c bc /\ memory_spatial a bc out) <->
  (exists ab, memory_spatial a b ab /\ memory_spatial ab c out).
Proof.
  split.
  - intros [bc [Hbc Hout]].
    destruct (proj1 (compatible_merge_right _ _ _ _ (proj2 Hbc)) (proj1 Hout)) as [Hab Hac].
    destruct (proj1 (memory_repaired_associative (fun _ => True) a b c out)
      (ex_intro _ bc (conj (memory_spatial_in_repaired _ _ _ _ Hbc) (memory_spatial_in_repaired _ _ _ _ Hout))))
      as [ab [Mab Mout]].
    pose proof (repaired_merge_interleaves _ _ _ _ Mab) as Iab.
    assert (Habc : spatial_compatible ab c).
    { apply spatial_compatible_comm. apply (proj2 (compatible_merge_right _ _ _ _ Iab)).
      split; apply spatial_compatible_comm; [exact Hac |exact (proj1 Hbc)]. }
    exists ab; split; split; [exact Hab |exact Iab |exact Habc |exact (repaired_merge_interleaves _ _ _ _ Mout)].
  - intros [ab [Hab Hout]].
    destruct (proj1 (compatible_merge_right _ _ _ _ (proj2 Hab))
      (spatial_compatible_comm _ _ (proj1 Hout))) as [Hca Hcb].
    destruct (proj2 (memory_repaired_associative (fun _ => True) a b c out)
      (ex_intro _ ab (conj (memory_spatial_in_repaired _ _ _ _ Hab) (memory_spatial_in_repaired _ _ _ _ Hout))))
      as [bc [Mbc Mout]].
    pose proof (repaired_merge_interleaves _ _ _ _ Mbc) as Ibc.
    exists bc; split; split.
    + apply spatial_compatible_comm, Hcb.
    + exact Ibc.
    + apply (proj2 (compatible_merge_right _ _ _ _ Ibc)); split; [exact (proj1 Hab) |apply spatial_compatible_comm, Hca].
    + exact (repaired_merge_interleaves _ _ _ _ Mout).
Qed.

Theorem spatial_exchange pool a b region whole :
  memory_spatial pool a region -> memory_spatial b region whole ->
  exists region', memory_spatial pool b region' /\ memory_spatial a region' whole.
Proof.
  intros Hinner Houter.
  destruct (proj1 (memory_spatial_associative b pool a whole) (ex_intro _ region (conj Hinner Houter)))
    as [region' [Hfirst Hsecond]]. exists region'; split; apply memory_spatial_comm; assumption.
Qed.

Lemma raw_spatial_well_formed active a b out : memory_well_formed active a -> memory_well_formed active b ->
  memory_spatial a b out -> memory_well_formed active out.
Proof.
  intros [Ha Ba] [Hb Bb] [_ [_ [Hbuffers Hblocked]]]. split.
  - intros i Hi; apply Hblocked in Hi; destruct Hi; [apply Ha |apply Hb]; assumption.
  - intros i Hi; specialize (Hbuffers i); rewrite (Ba i Hi), (Bb i Hi) in Hbuffers.
    apply interleaves_nil_left, Hbuffers.
Qed.

Lemma spatial_free_union a b out : memory_spatial a b out -> lock_free a -> lock_free b -> lock_free out.
Proof.
  intros [_ [_ [_ Hk]]] Ha Hb i H; apply Hk in H; destruct H; [apply (Ha i) |apply (Hb i)]; assumption.
Qed.

Theorem private_closed_exchange active owner other invariant s a region b whole :
  private_environment active owner invariant Closed s a region b whole ->
  exists region', private_environment active other invariant Closed s b region' a whole.
Proof.
  intros [[Ha [Hr [Hfree [pool [HJ Hinner]]]]] Hb Hw Hbfree Houter].
  destruct (spatial_free_parts _ _ _ Hinner Hfree) as [Hpoolfree Hafree].
  destruct (spatial_exchange _ _ _ _ _ Hinner Houter) as [region' [Hinner' Houter']].
  exists region'. constructor; try assumption.
  split; [exact Hb |]. split.
  - eapply raw_spatial_well_formed; [exact (proj1 (persistent_full_well_formed _ _ _ _ HJ)) |exact Hb |exact Hinner'].
  - split; [eapply spatial_free_union; eassumption |exists pool; auto].
Qed.
