From Stdlib Require Import List ZArith.
From WMLR Require Import Expressions Languages Machine Separation OperationalSemantics Assertions AssertionSemantics
  PersistentAssertions Safety RepairedSafety PersistentRules HeapRules LockRules.
Import ListNotations.

(** A checked, explicitly bounded calculus. Load/store currently use constant
    cells; release is restricted to pure invariants with an explicit restoration
    precondition. No constructor assumes program safety or validity. *)
Inductive persistent_derivation active : A.assertion -> A.assertion -> Concurrent.command -> A.assertion -> Prop :=
| DeriveSkip invariant p annotation : persistent_derivation active invariant p (Concurrent.skip annotation) p
| DeriveAssign invariant b x rhs annotation : ~ In x (A.fv invariant) ->
    persistent_derivation active invariant (A.Pure (subst_bexpr x rhs b))
      (Concurrent.Prim (Concurrent.Common (Sequential.Assign x rhs)) annotation) (A.Pure b)
| DeriveAssume invariant p b annotation :
    persistent_derivation active invariant (A.Or (A.Pure (BNot b)) p)
      (Concurrent.Prim (Concurrent.Common (Sequential.Assume b)) annotation) p
| DeriveAssert invariant p b annotation :
    persistent_derivation active invariant (A.And (A.Pure b) p)
      (Concurrent.Prim (Concurrent.Common (Sequential.Assert b)) annotation) p
| DeriveLoadCell invariant loc v x annotation : ~ In x (A.fv invariant) ->
    persistent_derivation active invariant (cell_assertion loc v)
      (Concurrent.Prim (Concurrent.Common (Sequential.Load x (EVal (Z.pos loc)))) annotation)
      (A.And (cell_assertion loc v) (A.Pure (BEq (EVar x) (EVal v))))
| DeriveStoreCell invariant loc old i v :
    persistent_derivation active invariant (cell_assertion loc old)
      (Concurrent.Prim (Concurrent.Common (Sequential.Store (EVal (Z.pos loc)) (EVal v))) (EVal (Z.pos i)))
      (A.Temporal (cell_assertion loc old) (A.LeadsTo (EVal (Z.pos loc)) (EVal (Z.pos i)) (EVal v)))
| DeriveFence invariant i : persistent_derivation active invariant A.Emp
    (Concurrent.Prim (Concurrent.Common Sequential.Fence) (EVal (Z.pos i))) (A.Barrier (EVal (Z.pos i)))
| DeriveLock invariant i : persistent_derivation active invariant A.Emp
    (Concurrent.Prim Concurrent.Lock (EVal (Z.pos i))) (A.Lock (EVal (Z.pos i)))
| DeriveUnlockPure invariant i :
    persistent_derivation active (A.Pure invariant) (A.And (A.Lock (EVal (Z.pos i))) (A.Pure invariant))
      (Concurrent.Prim Concurrent.Unlock (EVal (Z.pos i))) A.Emp
| DeriveSequence invariant p middle q first second :
    persistent_derivation active invariant p first middle -> persistent_derivation active invariant middle second q ->
    persistent_derivation active invariant p (Concurrent.Seq first second) q
| DeriveConsequence invariant p p' q' q command :
    persistent_entails active p p' -> persistent_derivation active invariant p' command q' ->
    persistent_entails active q' q -> persistent_derivation active invariant p command q
| DeriveDisjunction invariant p p' q command :
    persistent_derivation active invariant p command q -> persistent_derivation active invariant p' command q ->
    persistent_derivation active invariant (A.Or p p') command q.

Theorem persistent_calculus_sound active invariant pre command post :
  persistent_derivation active invariant pre command post -> persistent_valid active invariant pre command post.
Proof.
  induction 1.
  - apply persistent_skip_valid.
  - apply persistent_assignment_valid, H.
  - apply persistent_assume_valid.
  - apply persistent_assert_valid.
  - apply persistent_load_cell_valid, H.
  - apply persistent_store_cell_valid.
  - apply persistent_fence_valid.
  - apply persistent_lock_valid.
  - apply persistent_unlock_pure_valid.
  - eapply persistent_sequence_valid; eassumption.
  - eapply persistent_consequence_valid; eassumption.
  - eapply persistent_disjunction_valid; eassumption.
Qed.

(** Adequacy follows for every derived specification and every actual
    execution covered by an initial environment; no separate safety premise. *)
Theorem persistent_derivation_no_abort active invariant pre command post s local shared frame whole n last t final :
  persistent_derivation active invariant pre command post ->
  persistent_full_satisfies active s local pre ->
  repaired_environment active (fun s m => persistent_full_satisfies active s m invariant)
    s local shared frame whole -> execution active n command s whole last t final ->
  ~ abort active last (State t final).
Proof.
  intros Hderive Hp Henv Hrun. eapply repaired_safe_execution_no_abort;
    [exact Hrun |apply (persistent_calculus_sound _ _ _ _ _ Hderive), Hp |exact Henv].
Qed.
