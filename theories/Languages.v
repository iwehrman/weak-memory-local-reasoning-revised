From Stdlib Require Import List Arith.PeanoNat.
From WMLR Require Import Expressions.
Import ListNotations.

(** Sequential syntax from sections 3.3 and 3.3's command abbreviations.
    The stray processor subscript in the grammar on p. 44 is omitted, in
    accordance with the surrounding sequential semantics. *)
Module Sequential.

Inductive primitive : Type :=
| Skip
| Assume (condition : bexpr)
| Assert (condition : bexpr)
| Assign (target : ident) (rhs : expr)
| Load (target : ident) (address : expr)
| Store (address rhs : expr)
| Fence.

Inductive command : Type :=
| Prim (p : primitive)
| Seq (first second : command)
| Choice (lhs rhs : command)
| Loop (body : command).

Definition primitive_fv (p : primitive) : list ident :=
  match p with
  | Skip | Fence => []
  | Assume b | Assert b => bexpr_fv b
  | Assign x e | Load x e => x :: expr_fv e
  | Store address rhs => expr_fv address ++ expr_fv rhs
  end.

Definition primitive_mod (p : primitive) : list ident :=
  match p with
  | Assign x _ | Load x _ => [x]
  | _ => []
  end.

Fixpoint fv (c : command) : list ident :=
  match c with
  | Prim p => primitive_fv p
  | Seq lhs rhs | Choice lhs rhs => fv lhs ++ fv rhs
  | Loop body => fv body
  end.

Fixpoint modifies (c : command) : list ident :=
  match c with
  | Prim p => primitive_mod p
  | Seq lhs rhs | Choice lhs rhs => modifies lhs ++ modifies rhs
  | Loop body => modifies body
  end.

Definition skip : command := Prim Skip.

Definition if_then_else (b : bexpr) (yes no : command) : command :=
  Choice (Seq (Prim (Assume b)) yes) (Seq (Prim (Assume (BNot b))) no).

Definition while_do (b : bexpr) (body : command) : command :=
  Seq (Loop (Seq (Prim (Assume b)) body)) (Prim (Assume (BNot b))).

End Sequential.

(** Concurrent syntax, section 4.2. Processor annotations are expressions,
    including expressions with variables, as in the printed grammar. *)
Module Concurrent.

Inductive primitive : Type :=
| Common (p : Sequential.primitive)
| Lock
| Unlock.

Inductive command : Type :=
| Prim (p : primitive) (processor : expr)
| Seq (first second : command)
| Choice (lhs rhs : command)
| Loop (body : command)
| Parallel (lhs rhs : command).

Definition primitive_fv (p : primitive) : list ident :=
  match p with
  | Common p => Sequential.primitive_fv p
  | Lock | Unlock => []
  end.

Definition primitive_mod (p : primitive) : list ident :=
  match p with
  | Common p => Sequential.primitive_mod p
  | Lock | Unlock => []
  end.

Fixpoint fv (c : command) : list ident :=
  match c with
  | Prim p processor => primitive_fv p ++ expr_fv processor
  | Seq lhs rhs | Choice lhs rhs | Parallel lhs rhs => fv lhs ++ fv rhs
  | Loop body => fv body
  end.

Fixpoint modifies (c : command) : list ident :=
  match c with
  | Prim p _ => primitive_mod p
  | Seq lhs rhs | Choice lhs rhs | Parallel lhs rhs =>
      modifies lhs ++ modifies rhs
  | Loop body => modifies body
  end.

Definition skip (processor : expr) : command :=
  Prim (Common Sequential.Skip) processor.

Definition if_then_else (processor : expr) (b : bexpr)
    (yes no : command) : command :=
  Choice
    (Seq (Prim (Common (Sequential.Assume b)) processor) yes)
    (Seq (Prim (Common (Sequential.Assume (BNot b))) processor) no).

Definition while_do (processor : expr) (b : bexpr) (body : command) : command :=
  Seq (Loop (Seq (Prim (Common (Sequential.Assume b)) processor) body))
      (Prim (Common (Sequential.Assume (BNot b))) processor).

Definition locked (processor : expr) (body : command) : command :=
  Seq (Prim Lock processor) (Seq body (Prim Unlock processor)).

(** This annotates a syntax tree. Semantic agreement with the sequential
    machine is a separate theorem, pending the machine semantics. *)
Fixpoint of_sequential (processor : expr) (c : Sequential.command) : command :=
  match c with
  | Sequential.Prim p => Prim (Common p) processor
  | Sequential.Seq first second =>
      Seq (of_sequential processor first) (of_sequential processor second)
  | Sequential.Choice lhs rhs =>
      Choice (of_sequential processor lhs) (of_sequential processor rhs)
  | Sequential.Loop body => Loop (of_sequential processor body)
  end.

End Concurrent.

Lemma sequential_primitive_mod_in_fv p x :
  In x (Sequential.primitive_mod p) -> In x (Sequential.primitive_fv p).
Proof. destruct p; simpl; intuition. Qed.

Theorem sequential_mod_in_fv c x :
  In x (Sequential.modifies c) -> In x (Sequential.fv c).
Proof.
  induction c; simpl.
  - apply sequential_primitive_mod_in_fv.
  - rewrite !in_app_iff. intuition.
  - rewrite !in_app_iff. intuition.
  - exact IHc.
Qed.

Lemma concurrent_primitive_mod_in_fv p x :
  In x (Concurrent.primitive_mod p) -> In x (Concurrent.primitive_fv p).
Proof.
  destruct p; simpl; try contradiction. apply sequential_primitive_mod_in_fv.
Qed.

Theorem concurrent_mod_in_fv c x :
  In x (Concurrent.modifies c) -> In x (Concurrent.fv c).
Proof.
  induction c; simpl.
  - intros H. apply in_or_app. left. apply concurrent_primitive_mod_in_fv, H.
  - rewrite !in_app_iff. intuition.
  - rewrite !in_app_iff. intuition.
  - exact IHc.
  - rewrite !in_app_iff. intuition.
Qed.

Theorem embedding_preserves_modifies c processor :
  Concurrent.modifies (Concurrent.of_sequential processor c) = Sequential.modifies c.
Proof. induction c; simpl; congruence. Qed.

Theorem embedding_fv c processor x :
  In x (Concurrent.fv (Concurrent.of_sequential processor c)) <->
  In x (Sequential.fv c) \/ In x (expr_fv processor).
Proof.
  induction c; simpl; rewrite ?in_app_iff; tauto.
Qed.
