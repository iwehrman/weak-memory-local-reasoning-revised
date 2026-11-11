From WMLR Require Import Expressions Languages Machine Assertions AssertionSemantics HeapRules
  OwnershipProtocol OwnershipRules OwnershipHeap.

(** The extra indices belong to judgments, not assertions. This deliberately
    small calculus has no validity/safety premise hidden in a constructor. *)
Inductive ownership_derivation (active : processor_domain) (owner : processor) (invariant : A.assertion) :
    ownership_phase -> A.assertion -> Concurrent.command -> ownership_phase -> A.assertion -> Prop :=
| OwnSkip phase p annotation : ownership_derivation active owner invariant phase p
    (Concurrent.skip annotation) phase p
| OwnAcquire : ownership_derivation active owner invariant Closed A.Emp
    (Concurrent.Prim Concurrent.Lock (EVal (BinInt.Z.pos owner))) Open (owned_assertion owner invariant)
| OwnRelease : ownership_derivation active owner invariant Open (owned_assertion owner invariant)
    (Concurrent.Prim Concurrent.Unlock (EVal (BinInt.Z.pos owner))) Closed A.Emp
| OwnStore loc old v : ownership_derivation active owner invariant Open (owned_assertion owner (cell_assertion loc old))
    (Concurrent.Prim (Concurrent.Common (Sequential.Store (EVal (BinInt.Z.pos loc)) (EVal v)))
      (EVal (BinInt.Z.pos owner))) Open (owned_assertion owner (buffered_cell owner loc old v))
| OwnFence loc old v : ownership_derivation active owner invariant Open
    (owned_assertion owner (buffered_cell owner loc old v))
    (Concurrent.Prim (Concurrent.Common Sequential.Fence) (EVal (BinInt.Z.pos owner)))
    Open (owned_assertion owner (cell_assertion loc v))
| OwnReleaseBuffered loc old v : invariant = cell_assertion loc v ->
    ownership_derivation active owner invariant Open (owned_assertion owner (buffered_cell owner loc old v))
      (Concurrent.Prim Concurrent.Unlock (EVal (BinInt.Z.pos owner))) Closed A.Emp
| OwnSequence start pre first middle mid second finish post :
    ownership_derivation active owner invariant start pre first middle mid ->
    ownership_derivation active owner invariant middle mid second finish post ->
    ownership_derivation active owner invariant start pre (Concurrent.Seq first second) finish post.

Theorem ownership_calculus_sound active owner invariant start pre command finish post :
  ownership_derivation active owner invariant start pre command finish post ->
  protocol_valid active owner invariant start pre command finish post.
Proof.
  induction 1.
  - intros s region Hr Hp n; apply protocol_skip_safe; assumption.
  - apply protocol_acquire_valid.
  - apply protocol_release_valid.
  - apply protocol_store_cell_valid.
  - apply protocol_fence_cell_valid.
  - subst invariant; apply protocol_release_buffered_cell_valid.
  - eapply protocol_sequence_valid; eassumption.
Qed.
