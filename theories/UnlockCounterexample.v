From Stdlib Require Import List ZArith.
From WMLR Require Import Expressions Languages Machine Separation RepairedSeparation
  OperationalSemantics ExecutionExamples Assertions AssertionSemantics PersistentAssertions
  Safety SafetyExamples RepairedSafety PersistentRules HeapRules LockRules.
Import ListNotations.

Definition owned_lock_memory := acquire two_processors empty_memory 1%positive.

Lemma owned_lock_valid : generalized_well_formed two_processors (Generalized owned_lock_memory two_processors).
Proof.
  apply (full_memory_valid_with_processor two_processors 1%positive); [left; reflexivity |].
  apply acquire_well_formed, empty_memory_well_formed.
Qed.

Definition owned_lock_resource : resource two_processors :=
  exist _ (Generalized owned_lock_memory two_processors) owned_lock_valid.

Lemma owned_lock_held : lock_held two_processors owned_lock_memory 1%positive.
Proof. split; [left; reflexivity |intros j; reflexivity]. Qed.

Lemma two_processor_empty_not_locked : ~ locked two_processors empty_memory.
Proof.
  intros [owner [_ Hblocks]]. destruct (Pos.eq_dec owner 1%positive) as [-> |Hneq].
  - apply (proj2 (Hblocks 2%positive)); split; [right; reflexivity |discriminate].
  - apply (proj2 (Hblocks 1%positive)); split; [left; reflexivity |congruence].
Qed.

(** A lock token alone does not promise that unlocking will restore J. The
    environment is concrete and the release is an enabled machine action. *)
Theorem arbitrary_invariant_unlock_invalid :
  ~ persistent_valid two_processors (A.Pure BFalse) (A.Lock (EVal 1%Z))
    (Concurrent.Prim Concurrent.Unlock (EVal 1%Z)) A.Emp.
Proof.
  intros Hvalid.
  assert (Hp : persistent_full_satisfies two_processors zero_stack owned_lock_memory (A.Lock (EVal 1%Z))).
  { exists owned_lock_resource. split; [reflexivity |].
    split; [intros; reflexivity |]. split; [intros; reflexivity |apply owned_lock_held]. }
  specialize (Hvalid _ _ Hp 1). destruct Hvalid as [_ [_ Hprogress]].
  assert (Henv : repaired_environment two_processors
    (fun s m => persistent_full_satisfies two_processors s m (A.Pure BFalse))
    zero_stack owned_lock_memory empty_memory empty_memory owned_lock_memory).
  { constructor.
    - exact (proj1 owned_lock_valid).
    - apply empty_memory_well_formed.
    - apply empty_memory_well_formed.
    - exact (proj1 owned_lock_valid).
    - exists owned_lock_memory. split.
      + exact (proj1 (repaired_empty_left two_processors (Generalized owned_lock_memory two_processors))).
      + exact (proj1 (spatial_empty_left (Generalized owned_lock_memory two_processors))).
    - right; exists 1%positive; apply owned_lock_held.
    - right; exists 1%positive; apply owned_lock_held. }
  assert (Hstep : step two_processors (Concurrent.Prim Concurrent.Unlock (EVal 1%Z))
    (State zero_stack owned_lock_memory) halt (State zero_stack empty_memory)).
  { eapply StepPrimitive; [reflexivity |]. apply PrimitiveUnlock;
      [left; reflexivity |reflexivity |apply owned_lock_held]. }
  destruct (Hprogress _ _ _ _ _ _ Henv Hstep) as [local [shared [frame [Hafter _]]]].
  destruct Hafter as [_ _ _ _ _ _ [Hinv |Hlocked]].
  - destruct Hinv as [r [Hr Hfalse]]; discriminate.
  - apply two_processor_empty_not_locked, Hlocked.
Qed.
