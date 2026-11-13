From Stdlib Require Import List.
From WMLR Require Import Expressions Languages Assertions AssertionSemantics.
Import ListNotations.

(** Specification languages, sections 3.6 and 4.5. These are syntactic
    judgements. Derivability and operational validity are later layers. *)
Record sequential_specification := {
  sequential_pre : SequentialAssertion.assertion;
  sequential_program : Sequential.command;
  sequential_post : SequentialAssertion.assertion
}.

Record concurrent_specification := {
  shared_invariant : ConcurrentAssertion.assertion;
  concurrent_pre : ConcurrentAssertion.assertion;
  concurrent_program : Concurrent.command;
  concurrent_post : ConcurrentAssertion.assertion
}.

Definition disjoint (xs ys : list ident) : Prop :=
  forall x, In x xs -> ~ In x ys.

(** The displayed concurrent rule's condition on a branch's precondition,
    program and postcondition versus its sibling's modified variables.
    Agreement of the two shared invariants is a separate rule premise. *)
Definition branch_fv (spec : concurrent_specification) : list ident :=
  ConcurrentAssertion.fv (concurrent_pre spec) ++
  Concurrent.fv (concurrent_program spec) ++
  ConcurrentAssertion.fv (concurrent_post spec).

Definition parallel_variable_condition
    (left right : concurrent_specification) : Prop :=
  disjoint (branch_fv left) (Concurrent.modifies (concurrent_program right)) /\
  disjoint (branch_fv right) (Concurrent.modifies (concurrent_program left)).

Definition frame_variable_condition
    (c : Concurrent.command) (frame : ConcurrentAssertion.assertion) : Prop :=
  disjoint (Concurrent.modifies c) (ConcurrentAssertion.fv frame).

(** A sufficient side condition for an assignment to preserve an invariant's
    stack-dependent meaning. This lemma supports a candidate repair of the
    original assignment rule; it does not impose a new global restriction. *)
Theorem assignment_preserves_invariant {resource}
    (model : interpretation resource) invariant s r x rhs :
  ~ In x (ConcurrentAssertion.fv invariant) ->
  satisfies model s r invariant ->
  satisfies model (update s x (eval_expr s rhs)) r invariant.
Proof.
  intros Hfresh Hsat.
  apply (proj1 (satisfies_update_irrelevant model _ _ _ _ _ Hfresh)), Hsat.
Qed.
