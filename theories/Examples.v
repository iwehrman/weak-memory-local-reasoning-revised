From Stdlib Require Import List Arith.PeanoNat ZArith.
From WMLR Require Import Expressions Languages Assertions AssertionSemantics Specifications.
Import ListNotations.

(** Chapter 1's message-passing example, with names chosen explicitly. *)
Definition flag : ident := 0.
Definition data : ident := 1.
Definition observed_flag : ident := 2.
Definition observed_data : ident := 3.

Definition sender : Sequential.command :=
  Sequential.Seq
    (Sequential.Prim (Sequential.Store (EVar data) (EVal 1%Z)))
    (Sequential.Prim (Sequential.Store (EVar flag) (EVal 1%Z))).

Definition receiver : Sequential.command :=
  Sequential.Seq
    (Sequential.Prim (Sequential.Load observed_flag (EVar flag)))
    (Sequential.Seq
      (Sequential.Prim (Sequential.Load observed_data (EVar data)))
      (Sequential.if_then_else (BEq (EVar observed_flag) (EVal 1%Z))
        (Sequential.Prim (Sequential.Assert
          (BEq (EVar observed_data) (EVal 1%Z))))
        Sequential.skip)).

Definition message_passing : Concurrent.command :=
  Concurrent.Parallel
    (Concurrent.of_sequential (EVal 1%Z) sender)
    (Concurrent.of_sequential (EVal 2%Z) receiver).

Example sender_has_no_variable_writes : Sequential.modifies sender = [].
Proof. reflexivity. Qed.

Example receiver_writes_only_results :
  Sequential.modifies receiver = [observed_flag; observed_data].
Proof. reflexivity. Qed.

Example message_passing_modifies :
  Concurrent.modifies message_passing = [observed_flag; observed_data].
Proof. reflexivity. Qed.

Example processor_annotation_counts_as_free :
  In 9 (Concurrent.fv (Concurrent.Prim Concurrent.Lock (EVar 9))).
Proof. simpl; auto. Qed.

Example processor_annotation_is_not_modified :
  Concurrent.modifies (Concurrent.Prim Concurrent.Lock (EVar 9)) = [].
Proof. reflexivity. Qed.

(** The bound processor variable in the example on p. 114 disappears from
    the free-variable set, while the address and contents stay free. *)
Example quantified_assertion_fv :
  ConcurrentAssertion.fv
    (ConcurrentAssertion.Exists 2
      (ConcurrentAssertion.Temporal
        (ConcurrentAssertion.LeadsTo (EVar 0) (EVar 2) (EVar 1))
        (ConcurrentAssertion.Barrier (EVar 2)))) = [0; 1].
Proof. reflexivity. Qed.

Example nested_shadowing_fv :
  ConcurrentAssertion.fv
    (ConcurrentAssertion.Exists 0
      (ConcurrentAssertion.And
        (ConcurrentAssertion.Pure (BEq (EVar 0) (EVar 1)))
        (ConcurrentAssertion.Forall 1
          (ConcurrentAssertion.Pure (BEq (EVar 0) (EVar 1)))))) = [1].
Proof. reflexivity. Qed.

Example points_to_preserves_address_and_value_names x :
  In x (ConcurrentAssertion.fv
    (ConcurrentAssertion.points_to (EVar 0) (EVar 1))) <-> x = 0 \/ x = 1.
Proof. rewrite ConcurrentAssertion.points_to_fv. simpl; intuition. Qed.

Example substitution_evaluates_in_original_stack :
  eval_expr (fun _ => 4%Z)
    (subst_expr 0 (EAdd (EVar 0) (EVal 1%Z)) (EAdd (EVar 0) (EVar 1))) = 9%Z.
Proof. reflexivity. Qed.

(** The pure-assertion part of the assignment issue is model-independent.
    A refutation of the full printed soundness theorem still needs the
    concrete safety predicate and derivation rules. *)
Example assignment_can_break_pure_invariant {resource}
    (model : interpretation resource) (r : resource) (s : stack) x :
  let invariant := ConcurrentAssertion.Pure (BEq (EVar x) (EVal 0%Z)) in
  let initial := update s x 0%Z in
  satisfies model initial r invariant /\
  ~ satisfies model (update initial x 1%Z) r invariant.
Proof.
  simpl. rewrite !update_same. simpl. split; [reflexivity | discriminate].
Qed.

Definition sender_spec : concurrent_specification :=
  {| shared_invariant := ConcurrentAssertion.Emp;
     concurrent_pre := ConcurrentAssertion.Emp;
     concurrent_program := Concurrent.of_sequential (EVal 1%Z) sender;
     concurrent_post := ConcurrentAssertion.Emp |}.

Definition receiver_spec : concurrent_specification :=
  {| shared_invariant := ConcurrentAssertion.Emp;
     concurrent_pre := ConcurrentAssertion.Emp;
     concurrent_program := Concurrent.of_sequential (EVal 2%Z) receiver;
     concurrent_post := ConcurrentAssertion.Emp |}.

(** This checks the syntactic side condition only. Emp is used as a syntax
    fixture here; no Hoare validity claim is made about these records. *)
Example message_passing_variable_condition :
  parallel_variable_condition sender_spec receiver_spec.
Proof.
  unfold parallel_variable_condition, branch_fv, disjoint.
  cbn. unfold data, flag, observed_flag, observed_data.
  split; intros x H; intuition congruence.
Qed.
