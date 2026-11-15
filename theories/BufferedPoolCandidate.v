From Stdlib Require Import List ZArith.
From WMLR Require Import Expressions Languages Machine BufferRelations Separation
  RepairedSeparation GeneralizedFlushing OperationalSemantics ProgramSteps Assertions
  AssertionSemantics PersistentAssertions PersistentRules Specifications Safety TemporalSafety
  InvariantFragment OwnedSafety AssertionSubstitution.
Import ListNotations.

(** Approved buffered-pool definitions and rule statements. The corresponding
    proofs and inductive calculus are in BufferedPool*.v. The Owned development is unchanged.
    Pools remain spatially separate and may own pending writes. *)
Inductive buffered_invariant_fragment : A.assertion -> Prop :=
| BufferedEmp : buffered_invariant_fragment A.Emp
| BufferedCell address value : buffered_invariant_fragment (writer_points_to address value)
| BufferedHistory address old actor value : buffered_invariant_fragment
    (A.Temporal (writer_points_to address old) (A.LeadsTo address actor value))
| BufferedSpatial p q : buffered_invariant_fragment p -> buffered_invariant_fragment q ->
    buffered_invariant_fragment (A.Spatial p q)
| BufferedOr p q : buffered_invariant_fragment p -> buffered_invariant_fragment q ->
    buffered_invariant_fragment (A.Or p q)
| BufferedExists x p : buffered_invariant_fragment p -> buffered_invariant_fragment (A.Exists x p)
| BufferedGuard b p : buffered_invariant_fragment p -> buffered_invariant_fragment (A.And (A.Pure b) p).

Fixpoint buffered_lock_free command : Prop :=
  match command with
  | C.Prim (C.Common _) _ => True
  | C.Prim _ _ => False
  | C.Seq c1 c2 | C.Choice c1 c2 | C.Parallel c1 c2 =>
      buffered_lock_free c1 /\ buffered_lock_free c2
  | C.Loop body => buffered_lock_free body
  end.

(** Marks are not erased or re-marked arbitrarily. Every pool model is
    interpreted at full completeness, before and after every step/flush.
    The fragment is NOT assumed insensitive to marks. *)
Record buffered_environment active mode invariant s (local : resource active)
    pool (frame : resource active) whole : Prop := {
  buffered_pool_wf : memory_well_formed active pool;
  buffered_whole_wf : memory_well_formed active whole;
  buffered_whole_free : lock_free whole;
  buffered_pool_models : persistent_full_satisfies active s pool invariant;
  buffered_composition : exists combined : resource active,
    repaired_spatiotemporal active (proj1_sig frame) (proj1_sig local) (proj1_sig combined) /\
    memory_spatial pool (resource_memory active combined) whole;
  buffered_frame_mode : mode_compatible active mode frame local
}.

Record buffered_update active action (local : resource active) pool
    (local' : resource active) pool' : Prop := {
  buffered_footprint : forall loc,
    memory_domain pool' loc \/ memory_domain (resource_memory active local') loc ->
    memory_domain pool loc \/ memory_domain (resource_memory active local) loc;
  buffered_mark_budget : forall i, complete (proj1_sig local') i ->
    complete (proj1_sig local) i \/ action_earns action i
}.

Definition buffered_component_flush active actor (before after : resource active) : Prop :=
  flush_at active actor (resource_memory active before) (resource_memory active after) /\
  (forall i, complete (proj1_sig after) i <-> complete (proj1_sig before) i \/ i = actor).

Definition buffered_flush_update active actor (local frame : resource active) pool
    (local' frame' : resource active) pool' : Prop :=
  (local' = local /\ frame' = frame /\ flush_at active actor pool pool') \/
  (pool' = pool /\ frame' = frame /\ buffered_component_flush active actor local local') \/
  (pool' = pool /\ local' = local /\ buffered_component_flush active actor frame frame').

Fixpoint buffered_safe active mode invariant n command s (local : resource active) post : Prop :=
  match n with
  | O => True
  | S remaining => forall later, resource_future active local later ->
      (terminal command -> persistent_models active s later post) /\
      forall pool frame whole, buffered_environment active mode invariant s later pool frame whole ->
        ~ abort active command (State s whole) /\
        (forall action next t whole',
          program_step active action command (State s whole) next (State t whole') ->
          exists local' pool',
            buffered_environment active mode invariant t local' pool' frame whole' /\
            buffered_update active action later pool local' pool' /\
            buffered_safe active mode invariant remaining next t local' post) /\
        (forall actor whole', flush_at active actor whole whole' ->
          exists local' frame' pool',
            buffered_flush_update active actor later frame pool local' frame' pool' /\
            buffered_environment active mode invariant s local' pool' frame' whole' /\
            buffered_safe active mode invariant remaining command s local' post)
  end.

Definition buffered_valid_mode active mode invariant pre command post : Prop :=
  buffered_lock_free command /\ forall s local, persistent_models active s local pre ->
    forall n, buffered_safe active mode invariant n command s local post.

(** Intended judgment: DJ, since every atomic step may transfer ownership.
    OV is retained as a diagnostic comparison, not a proposed frame rule. *)
Definition buffered_valid active invariant pre command post : Prop :=
  buffered_valid_mode active DisjointMode invariant pre command post.

Definition buffered_atomic_primitive primitive : Prop :=
  match primitive with S.Skip => False | _ => True end.

(** Frameless one-step premise. Local marks are checked against the ORIGINAL
    local resource, never against the full marks of pool * local. No
    ordinary-step or store requirement keeps the pool fixed. *)
Definition buffered_atomic_premise active invariant pre primitive annotation post : Prop :=
  buffered_atomic_primitive primitive /\
  forall s (local : resource active) pool whole,
    persistent_models active s local pre ->
    persistent_full_satisfies active s pool invariant ->
    memory_spatial pool (resource_memory active local) whole ->
    lock_free whole ->
    ~ abort active (C.Prim (C.Common primitive) annotation) (State s whole) /\
    forall action next t whole',
      program_step active action (C.Prim (C.Common primitive) annotation)
        (State s whole) next (State t whole') ->
      exists local' pool',
        memory_spatial pool' (resource_memory active local') whole' /\
        lock_free whole' /\ persistent_full_satisfies active t pool' invariant /\
        persistent_models active t local' post /\
        buffered_update active action local pool local' pool'.

Definition buffered_atomic_rule active invariant pre primitive annotation post : Prop :=
  buffered_invariant_fragment invariant ->
  buffered_atomic_premise active invariant pre primitive annotation post ->
  buffered_valid active invariant pre (C.Prim (C.Common primitive) annotation) post.

Definition buffered_skip_rule active invariant pre annotation : Prop :=
  buffered_invariant_fragment invariant -> buffered_valid active invariant pre (C.skip annotation) pre.
Definition buffered_sequence_rule active invariant pre middle post first second : Prop :=
  buffered_valid active invariant pre first middle -> buffered_valid active invariant middle second post ->
  buffered_valid active invariant pre (C.Seq first second) post.
Definition buffered_consequence_rule active invariant pre pre' command post' post : Prop :=
  persistent_entails active pre pre' -> buffered_valid active invariant pre' command post' ->
  persistent_entails active post' post -> buffered_valid active invariant pre command post.
Definition buffered_disjunction_rule active invariant pre pre' command post : Prop :=
  buffered_valid active invariant pre command post -> buffered_valid active invariant pre' command post ->
  buffered_valid active invariant (A.Or pre pre') command post.
Definition buffered_choice_rule active invariant pre left right post : Prop :=
  buffered_valid active invariant pre left post -> buffered_valid active invariant pre right post ->
  buffered_valid active invariant pre (C.Choice left right) post.
Definition buffered_loop_rule active invariant pre body : Prop :=
  buffered_valid active invariant pre body pre -> buffered_valid active invariant pre (C.Loop body) pre.
Definition buffered_exists_rule active invariant pre command post x : Prop :=
  ~ In x (A.fv invariant) -> ~ In x (C.fv command) -> ~ In x (A.fv post) ->
  buffered_valid active invariant pre command post ->
  buffered_valid active invariant (A.Exists x pre) command post.
Definition buffered_frame_rule active invariant pre command post frame : Prop :=
  buffered_valid active invariant pre command post -> frame_variable_condition command frame ->
  buffered_valid active invariant (A.Spatial frame pre) command (A.Spatial frame post).
Definition buffered_parallel_rule active invariant left_pre left left_post right_pre right right_post : Prop :=
  buffered_valid active invariant left_pre left left_post -> buffered_valid active invariant right_pre right right_post ->
  parallel_variable_condition (Build_concurrent_specification invariant left_pre left left_post)
    (Build_concurrent_specification invariant right_pre right right_post) ->
  frame_variable_condition left invariant -> frame_variable_condition right invariant ->
  buffered_valid active invariant (A.Spatial left_pre right_pre)
    (C.Parallel left right) (A.Spatial left_post right_post).

Definition buffered_private_store_rule active invariant address old value annotation : Prop :=
  buffered_invariant_fragment invariant ->
  buffered_valid active invariant (writer_points_to address old)
    (C.Prim (C.Common (S.Store address value)) annotation)
    (A.Temporal (writer_points_to address old) (A.LeadsTo address annotation value)).
Definition buffered_private_load_rule active invariant address value annotation x : Prop :=
  buffered_invariant_fragment invariant -> ~ In x (A.fv invariant) ->
  ~ In x (expr_fv address ++ expr_fv value) ->
  buffered_valid active invariant (writer_points_to address value)
    (C.Prim (C.Common (S.Load x address)) annotation)
    (A.And (writer_points_to address value) (A.Pure (BEq (EVar x) value))).
Definition buffered_private_fence_rule active invariant annotation : Prop :=
  buffered_invariant_fragment invariant ->
  buffered_valid active invariant A.Emp (C.Prim (C.Common S.Fence) annotation) (A.Barrier annotation).
Definition buffered_assignment_rule active invariant post x rhs annotation : Prop :=
  buffered_invariant_fragment invariant -> ~ In x (A.fv invariant) ->
  buffered_valid active invariant (assertion_subst x rhs post)
    (C.Prim (C.Common (S.Assign x rhs)) annotation) post.
Definition buffered_assume_rule active invariant pre condition annotation : Prop :=
  buffered_invariant_fragment invariant ->
  buffered_valid active invariant (A.Or (A.Pure (BNot condition)) pre)
    (C.Prim (C.Common (S.Assume condition)) annotation) pre.
Definition buffered_assert_rule active invariant pre condition annotation : Prop :=
  buffered_invariant_fragment invariant ->
  buffered_valid active invariant (A.And (A.Pure condition) pre)
    (C.Prim (C.Common (S.Assert condition)) annotation) pre.

(** Empty-frame adequacy; no ambient-frame or mode obligation remains.
    Unlike locking adequacy this statement needs no two-processor assumption. *)
Definition buffered_adequacy_statement active invariant pre command post : Prop :=
  buffered_invariant_fragment invariant -> buffered_valid active invariant pre command post ->
  forall n s whole last t final local pool,
    persistent_models active s local pre -> persistent_full_satisfies active s pool invariant ->
    memory_spatial pool (resource_memory active local) whole -> lock_free whole ->
    execution active n command s whole last t final ->
    ~ abort active last (State t final) /\
    (terminal last -> exists local' pool', memory_spatial pool' (resource_memory active local') final /\
      lock_free final /\ persistent_full_satisfies active t pool' invariant /\
      persistent_models active t local' post).

(** Exact six premise questions enumerated by search_buffered_pool.py.
    The script's actors 0/1 correspond to positive processors 1/2 here.
    Ghost addresses/values agree with the script; these are definitions,
    not Rocq proofs of the six obligations. *)
Module BufferedDekker.
Definition active (actor : processor) := actor = 1%positive \/ actor = 2%positive.
Definition e (n : positive) := EVal (Z.pos n).
Definition ghost (address : positive) := writer_points_to (e address) (EVal 0%Z).
Definition flag (address : positive) value := writer_points_to (e address) (EVal value).
Definition triple x y z := A.Spatial x (A.Spatial y z).
Definition finished (address a t : positive) := triple (ghost a) (ghost t) (flag address 1%Z).
Definition stages (actor address a b q t : positive) :=
  A.Or (triple (ghost b) (ghost q) (flag address 0%Z))
    (A.Or (triple (ghost a) (ghost q)
      (A.Temporal (flag address 0%Z) (A.LeadsTo (e address) (e actor) (EVal 1%Z))))
      (finished address a t)).
Definition g0 := stages 1%positive 1%positive 4%positive 5%positive 6%positive 7%positive.
Definition g1 := stages 2%positive 2%positive 9%positive 10%positive 11%positive 12%positive.
Definition f0 := finished 1%positive 4%positive 7%positive.
Definition f1 := finished 2%positive 9%positive 12%positive.
Definition invariant := A.Or (triple (ghost 3%positive) g0 g1)
  (A.Or (triple (ghost 8%positive) f0 g1) (triple (ghost 13%positive) f1 g0)).
Definition start0 := triple (ghost 4%positive) (ghost 7%positive) (ghost 8%positive).
Definition start1 := triple (ghost 9%positive) (ghost 12%positive) (ghost 13%positive).
Definition stored0 := triple (ghost 5%positive) (ghost 7%positive) (ghost 8%positive).
Definition stored1 := triple (ghost 10%positive) (ghost 12%positive) (ghost 13%positive).
Definition fenced0 := triple (ghost 5%positive) (ghost 6%positive) (ghost 8%positive).
Definition fenced1 := triple (ghost 10%positive) (ghost 11%positive) (ghost 13%positive).
Definition loaded (target : ident) (b q p : positive) :=
  A.Or (A.And (A.Pure (BEq (EVar target) (EVal 1%Z))) (triple (ghost b) (ghost q) (ghost p)))
    (A.And (A.Pure (BEq (EVar target) (EVal 0%Z))) (triple (ghost b) (ghost q) (ghost 3%positive))).
Definition loaded0 := loaded 0 5%positive 6%positive 8%positive.
Definition loaded1 := loaded 1 10%positive 11%positive 13%positive.
Definition store0_premise := buffered_atomic_premise active invariant start0
  (S.Store (e 1%positive) (EVal 1%Z)) (e 1%positive) stored0.
Definition store1_premise := buffered_atomic_premise active invariant start1
  (S.Store (e 2%positive) (EVal 1%Z)) (e 2%positive) stored1.
Definition fence0_premise := buffered_atomic_premise active invariant stored0 S.Fence (e 1%positive) fenced0.
Definition fence1_premise := buffered_atomic_premise active invariant stored1 S.Fence (e 2%positive) fenced1.
Definition load0_premise := buffered_atomic_premise active invariant fenced0
  (S.Load 0 (e 2%positive)) (e 1%positive) loaded0.
Definition load1_premise := buffered_atomic_premise active invariant fenced1
  (S.Load 1 (e 1%positive)) (e 2%positive) loaded1.
Definition thread0 := C.Seq (C.Prim (C.Common (S.Store (e 1%positive) (EVal 1%Z))) (e 1%positive))
  (C.Seq (C.Prim (C.Common S.Fence) (e 1%positive)) (C.Prim (C.Common (S.Load 0 (e 2%positive))) (e 1%positive))).
Definition thread1 := C.Seq (C.Prim (C.Common (S.Store (e 2%positive) (EVal 1%Z))) (e 2%positive))
  (C.Seq (C.Prim (C.Common S.Fence) (e 2%positive)) (C.Prim (C.Common (S.Load 1 (e 1%positive))) (e 2%positive))).
Definition program := C.Parallel thread0 thread1.
End BufferedDekker.
