From Stdlib Require Import List ZArith.
From WMLR Require Import Expressions Languages Machine Assertions AssertionSemantics Specifications
  HeapRules OwnershipProtocol OwnershipHeap PrivateCalculus.
Import ListNotations.

(** Static interfaces record variables a proof may depend on, and variables
    its command may write. They are proof bookkeeping, not new assertions. *)
Record thread_interface := ThreadInterface {
  interface_variables : list ident;
  interface_writes : list ident
}.

Definition interfaces_compatible a b :=
  Specifications.disjoint (interface_writes a) (interface_variables b) /\
  Specifications.disjoint (interface_writes b) (interface_variables a).

Lemma interfaces_compatible_sym a b : interfaces_compatible a b -> interfaces_compatible b a.
Proof. intros [H K]; split; assumption. Qed.

Lemma incl_app_parts {T} (xs ys zs : list T) : incl (xs ++ ys) zs -> incl xs zs /\ incl ys zs.
Proof. intros H; split; intros x Hin; apply H, in_or_app; auto. Qed.

(** No rule introduces an assertion variable absent from the invariant,
    its input assertion, and the command. In particular, this accounts for
    intermediate assertions hidden by sequencing. *)
Theorem private_derivation_support active owner invariant start pre command finish post :
  private_derivation active owner invariant start pre command finish post -> forall variables,
  incl (A.fv invariant) variables -> incl (A.fv pre) variables -> incl (Concurrent.fv command) variables ->
  incl (A.fv post) variables.
Proof.
  induction 1; intros variables HJ HP HC; simpl in *;
    try solve [unfold incl in *; intros z Hz; repeat rewrite in_app_iff in Hz;
      intuition (eauto using in_or_app)].
  destruct (incl_app_parts _ _ _ HC) as [Hfirst Hsecond].
  apply IHprivate_derivation2; [exact HJ | |exact Hsecond].
  apply IHprivate_derivation1; assumption.
Qed.

Theorem private_derivation_modifies_invariant active owner invariant start pre command finish post :
  private_derivation active owner invariant start pre command finish post ->
  Specifications.disjoint (Concurrent.modifies command) (A.fv invariant).
Proof.
  induction 1; unfold Specifications.disjoint in *; simpl in *; intros z Hz;
    try contradiction; try solve [destruct Hz as [<- |[]]; assumption].
  apply in_app_iff in Hz; destruct Hz; auto.
Qed.

Definition specification_interface (spec : concurrent_specification) :=
  ThreadInterface (A.fv (shared_invariant spec) ++ branch_fv spec) (Concurrent.modifies (concurrent_program spec)).

Theorem specification_interfaces_compatible active left right invariant p q r u c d :
  private_derivation active left invariant Closed p c Closed q ->
  private_derivation active right invariant Closed r d Closed u ->
  parallel_variable_condition
    (Build_concurrent_specification invariant p c q) (Build_concurrent_specification invariant r d u) ->
  interfaces_compatible
    (specification_interface (Build_concurrent_specification invariant p c q))
    (specification_interface (Build_concurrent_specification invariant r d u)).
Proof.
  intros Hc Hd [HL HR].
  pose proof (private_derivation_modifies_invariant _ _ _ _ _ _ _ _ Hc) as HJc.
  pose proof (private_derivation_modifies_invariant _ _ _ _ _ _ _ _ Hd) as HJd.
  split; intros x Hwrite Hread; apply in_app_iff in Hread; destruct Hread.
  - exact (HJc x Hwrite H).
  - exact (HR x H Hwrite).
  - exact (HJd x Hwrite H).
  - exact (HL x H Hwrite).
Qed.
