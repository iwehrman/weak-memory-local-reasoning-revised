From Stdlib Require Import List ZArith.
From WMLR Require Import Expressions Languages Machine Assertions AssertionSemantics HeapRules
  OwnershipProtocol OwnershipHeap PrivateOwnership PrivateRules PrivateHeap.

Inductive private_derivation (active : processor_domain) (owner : processor) (invariant : A.assertion) :
    ownership_phase -> A.assertion -> Concurrent.command -> ownership_phase -> A.assertion -> Prop :=
| PrivateSkip phase p annotation : private_derivation active owner invariant phase p (Concurrent.skip annotation) phase p
| PrivateAcquire p : private_derivation active owner invariant Closed p
    (Concurrent.Prim Concurrent.Lock (EVal (Z.pos owner))) Open (owned_assertion owner (A.Spatial invariant p))
| PrivateRelease q : private_derivation active owner invariant Open (owned_assertion owner (A.Spatial invariant q))
    (Concurrent.Prim Concurrent.Unlock (EVal (Z.pos owner))) Closed q
| PrivateStore loc old v p : private_derivation active owner invariant Open
    (owned_assertion owner (A.Spatial (cell_assertion loc old) p))
    (Concurrent.Prim (Concurrent.Common (Sequential.Store (EVal (Z.pos loc)) (EVal v))) (EVal (Z.pos owner)))
    Open (owned_assertion owner (A.Spatial (buffered_cell owner loc old v) p))
| PrivateFence loc old v p : private_derivation active owner invariant Open
    (owned_assertion owner (A.Spatial (buffered_cell owner loc old v) p))
    (Concurrent.Prim (Concurrent.Common Sequential.Fence) (EVal (Z.pos owner)))
    Open (owned_assertion owner (A.Spatial (cell_assertion loc v) p))
| PrivateReleaseBuffered loc old v p : invariant = cell_assertion loc v ->
    private_derivation active owner invariant Open (owned_assertion owner (A.Spatial (buffered_cell owner loc old v) p))
      (Concurrent.Prim Concurrent.Unlock (EVal (Z.pos owner))) Closed p
| PrivateLoad loc v x : ~ In x (A.fv invariant) ->
    private_derivation active owner invariant Closed (cell_assertion loc v)
      (Concurrent.Prim (Concurrent.Common (Sequential.Load x (EVal (Z.pos loc)))) (EVal (Z.pos owner)))
      Closed (A.And (cell_assertion loc v) (A.Pure (BEq (EVar x) (EVal v))))
| PrivateSequence start pre first middle mid second finish post :
    private_derivation active owner invariant start pre first middle mid ->
    private_derivation active owner invariant middle mid second finish post ->
    private_derivation active owner invariant start pre (Concurrent.Seq first second) finish post.

Theorem private_calculus_sound active owner invariant start pre command finish post :
  private_derivation active owner invariant start pre command finish post ->
  private_valid active owner invariant start pre command finish post.
Proof.
  induction 1.
  - intros s local region Hr Hp n; apply private_skip_safe; assumption.
  - apply private_acquire_valid.
  - apply private_release_valid.
  - apply private_store_cell_valid.
  - apply private_fence_cell_valid.
  - subst invariant; apply private_release_buffered_cell_valid.
  - apply private_closed_load_valid, H.
  - eapply private_sequence_valid; eassumption.
Qed.

(** A whole critical section derived from the ordinary proof constructors.
    The body may change P to Q, provided it restores J. *)
Theorem private_critical_section_rule active owner invariant p q body :
  private_derivation active owner invariant Open (owned_assertion owner (A.Spatial invariant p)) body
    Open (owned_assertion owner (A.Spatial invariant q)) ->
  private_derivation active owner invariant Closed p
    (Concurrent.Seq (Concurrent.Prim Concurrent.Lock (EVal (Z.pos owner)))
      (Concurrent.Seq body (Concurrent.Prim Concurrent.Unlock (EVal (Z.pos owner))))) Closed q.
Proof.
  intros Hbody. eapply PrivateSequence; [apply PrivateAcquire |].
  eapply PrivateSequence; [exact Hbody |apply PrivateRelease].
Qed.
