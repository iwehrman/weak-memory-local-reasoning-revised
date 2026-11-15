From WMLR Require Import Expressions Languages Assertions AssertionSemantics Specifications
  BufferedPoolCandidate BufferedPoolCalculus BufferedDekkerProof.

Theorem buffered_dekker_thread0_derived : buffered_derivation BufferedDekker.active BufferedDekker.invariant
  BufferedDekker.start0 BufferedDekker.thread0 BufferedDekker.loaded0.
Proof.
  eapply BufferedSequence with (M := BufferedDekker.stored0).
  - apply BufferedAtomic,buffered_dekker_store0_premise.
  - eapply BufferedSequence with (M := BufferedDekker.fenced0);
      apply BufferedAtomic; [apply buffered_dekker_fence0_premise |apply buffered_dekker_load0_premise].
Qed.
Theorem buffered_dekker_thread1_derived : buffered_derivation BufferedDekker.active BufferedDekker.invariant
  BufferedDekker.start1 BufferedDekker.thread1 BufferedDekker.loaded1.
Proof.
  eapply BufferedSequence with (M := BufferedDekker.stored1).
  - apply BufferedAtomic,buffered_dekker_store1_premise.
  - eapply BufferedSequence with (M := BufferedDekker.fenced1);
      apply BufferedAtomic; [apply buffered_dekker_fence1_premise |apply buffered_dekker_load1_premise].
Qed.

Theorem buffered_dekker_derived : buffered_derivation BufferedDekker.active BufferedDekker.invariant
  (A.Spatial BufferedDekker.start0 BufferedDekker.start1) BufferedDekker.program
  (A.Spatial BufferedDekker.loaded0 BufferedDekker.loaded1).
Proof.
  apply BufferedParallel; [apply buffered_dekker_thread0_derived |apply buffered_dekker_thread1_derived | | |];
    vm_compute; intuition congruence.
Qed.
