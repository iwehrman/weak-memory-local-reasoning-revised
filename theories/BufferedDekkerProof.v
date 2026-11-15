From Stdlib Require Import List ZArith.
From WMLR Require Import Expressions Languages Machine BufferRelations Separation GeneralizedFlushing
  OperationalSemantics ProgramSteps Assertions AssertionSemantics PersistentAssertions PersistentRules
  Specifications SpatialExchange TemporalSafety InvariantFragment OwnedSafety
  BufferedPoolCandidate BufferedPoolRules BufferedPoolParallel BufferedPoolAdequacy
  BufferedDekkerResources BufferedDekkerVerification.
Import ListNotations.

Module BDP.
Definition ghost l := BD.Cell l 0%Z.
Definition triple a b c := BD.Sep a (BD.Sep b c).
Definition finished f a t := triple (ghost a) (ghost t) (BD.Cell f 1%Z).
Definition stages second f a b q t := BD.Or (triple (ghost b) (ghost q) (BD.Cell f 0%Z))
  (BD.Or (triple (ghost a) (ghost q) (BD.History f 0%Z second 1%Z)) (finished f a t)).
Definition g0 := stages false 1%positive 4%positive 5%positive 6%positive 7%positive.
Definition g1 := stages true 2%positive 9%positive 10%positive 11%positive 12%positive.
Definition f0 := finished 1%positive 4%positive 7%positive.
Definition f1 := finished 2%positive 9%positive 12%positive.
Definition invariant := BD.Or (triple (ghost 3%positive) g0 g1)
  (BD.Or (triple (ghost 8%positive) f0 g1) (triple (ghost 13%positive) f1 g0)).
Definition start0 := triple (ghost 4%positive) (ghost 7%positive) (ghost 8%positive).
Definition start1 := triple (ghost 9%positive) (ghost 12%positive) (ghost 13%positive).
Definition stored0 := triple (ghost 5%positive) (ghost 7%positive) (ghost 8%positive).
Definition stored1 := triple (ghost 10%positive) (ghost 12%positive) (ghost 13%positive).
Definition fenced0 := triple (ghost 5%positive) (ghost 6%positive) (ghost 8%positive).
Definition fenced1 := triple (ghost 10%positive) (ghost 11%positive) (ghost 13%positive).
Definition loaded b q p (value : option Z) := triple (ghost b) (ghost q)
  (ghost (match value with Some 0%Z => 3%positive |_ => p end)).
Definition loaded0 := loaded 5%positive 6%positive 8%positive.
Definition loaded1 := loaded 10%positive 11%positive 13%positive.
End BDP.

Theorem buffered_dekker_store0_premise : BufferedDekker.store0_premise.
Proof.
  exact (BDV.certificate_sound BDP.invariant BDP.start0 (BDV.Store false 1%positive 1%Z)
    (fun _ => BDP.stored0) eq_refl).
Qed.
Theorem buffered_dekker_store1_premise : BufferedDekker.store1_premise.
Proof.
  exact (BDV.certificate_sound BDP.invariant BDP.start1 (BDV.Store true 2%positive 1%Z)
    (fun _ => BDP.stored1) eq_refl).
Qed.
Theorem buffered_dekker_fence0_premise : BufferedDekker.fence0_premise.
Proof.
  exact (BDV.certificate_sound BDP.invariant BDP.stored0 (BDV.Fence false)
    (fun _ => BDP.fenced0) eq_refl).
Qed.
Theorem buffered_dekker_fence1_premise : BufferedDekker.fence1_premise.
Proof.
  exact (BDV.certificate_sound BDP.invariant BDP.stored1 (BDV.Fence true)
    (fun _ => BDP.fenced1) eq_refl).
Qed.
Theorem buffered_dekker_load0_premise : BufferedDekker.load0_premise.
Proof.
  exact (BDV.certificate_sound BDP.invariant BDP.fenced0 (BDV.Load false 2%positive 0%nat) BDP.loaded0 eq_refl).
Qed.
Theorem buffered_dekker_load1_premise : BufferedDekker.load1_premise.
Proof.
  exact (BDV.certificate_sound BDP.invariant BDP.fenced1 (BDV.Load true 1%positive 1%nat) BDP.loaded1 eq_refl).
Qed.

Lemma buffered_description_fragment d : buffered_invariant_fragment (BD.assertion d).
Proof. induction d; cbn [BD.assertion]; constructor; assumption. Qed.

Theorem buffered_dekker_invariant_fragment : buffered_invariant_fragment BufferedDekker.invariant.
Proof. exact (buffered_description_fragment BDP.invariant). Qed.

Theorem buffered_dekker_thread0_valid : buffered_valid BufferedDekker.active BufferedDekker.invariant
  BufferedDekker.start0 BufferedDekker.thread0 BufferedDekker.loaded0.
Proof.
  eapply buffered_sequence_valid with (middle := BufferedDekker.stored0).
  - apply buffered_atomic_valid; [apply buffered_dekker_invariant_fragment |apply buffered_dekker_store0_premise].
  - eapply buffered_sequence_valid with (middle := BufferedDekker.fenced0).
    + apply buffered_atomic_valid; [apply buffered_dekker_invariant_fragment |apply buffered_dekker_fence0_premise].
    + apply buffered_atomic_valid; [apply buffered_dekker_invariant_fragment |apply buffered_dekker_load0_premise].
Qed.
Theorem buffered_dekker_thread1_valid : buffered_valid BufferedDekker.active BufferedDekker.invariant
  BufferedDekker.start1 BufferedDekker.thread1 BufferedDekker.loaded1.
Proof.
  eapply buffered_sequence_valid with (middle := BufferedDekker.stored1).
  - apply buffered_atomic_valid; [apply buffered_dekker_invariant_fragment |apply buffered_dekker_store1_premise].
  - eapply buffered_sequence_valid with (middle := BufferedDekker.fenced1).
    + apply buffered_atomic_valid; [apply buffered_dekker_invariant_fragment |apply buffered_dekker_fence1_premise].
    + apply buffered_atomic_valid; [apply buffered_dekker_invariant_fragment |apply buffered_dekker_load1_premise].
Qed.

Theorem buffered_dekker_valid : buffered_valid BufferedDekker.active BufferedDekker.invariant
  (A.Spatial BufferedDekker.start0 BufferedDekker.start1) BufferedDekker.program
  (A.Spatial BufferedDekker.loaded0 BufferedDekker.loaded1).
Proof.
  apply buffered_parallel_valid; [apply buffered_dekker_thread0_valid |apply buffered_dekker_thread1_valid | | |];
    vm_compute; intuition congruence.
Qed.

Lemma buffered_loaded_zero_owns_prize s r x b q p :
  persistent_models BufferedDekker.active s r (BufferedDekker.loaded x b q p) -> s x = 0%Z ->
  memory_domain (resource_memory BufferedDekker.active r) 3%positive.
Proof.
  intros [[Hone Hcells] |[Hzero Hcells]] E.
  - change (Z.eqb (s x) 1 = true) in Hone; rewrite E in Hone; discriminate.
  - destruct Hcells as (rb & rest & [Houter _] & Hb & rq & prize & [Hinner _] & Hq & Hprize).
    apply (spatial_merge_domain _ _ _ (proj2 Houter)); right.
    apply (spatial_merge_domain _ _ _ (proj2 Hinner)); right.
    destruct (writer_points_to_shape _ _ _ _ _ Hprize) as (loc & owner & Eloc & Hi & Hheap & _).
    cbn in Eloc; injection Eloc as Eloc; subst loc.
    left; exists 0%Z; rewrite Hheap; apply heap_update_same.
Qed.

Theorem buffered_dekker_post_excludes_zero_zero s r :
  persistent_models BufferedDekker.active s r (A.Spatial BufferedDekker.loaded0 BufferedDekker.loaded1) ->
  ~ (s 0%nat = 0%Z /\ s 1%nat = 0%Z).
Proof.
  intros (left & right & [[[HD _] _] _] & HL & HR) [E0 E1].
  apply (HD 3%positive); eapply buffered_loaded_zero_owns_prize; eassumption.
Qed.
