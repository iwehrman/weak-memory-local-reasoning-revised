From Stdlib Require Import List ZArith.
From WMLR Require Import Expressions Languages Machine Separation StableCompatibility
  RepairedSeparation GeneralizedFlushing OperationalSemantics ProgramSteps Assertions
  AssertionSemantics PersistentAssertions PersistentRules Specifications Safety TemporalSafety
  InvariantFragment OwnedSafety.
Import ListNotations.

(** Stage 2 STATEMENT ONLY. None of the rule propositions below is claimed
    or proved. This candidate is independent of the active calculus. *)
Fixpoint daring_lock_free command : Prop :=
  match command with
  | C.Prim (C.Common _) _ => True
  | C.Prim _ _ => False
  | C.Seq c1 c2 | C.Choice c1 c2 | C.Parallel c1 c2 =>
      daring_lock_free c1 /\ daring_lock_free c2
  | C.Loop body => daring_lock_free body
  end.

Record daring_environment active invariant s (local : resource active)
    pool (frame : resource active) whole : Prop := {
  daring_pool_wf : memory_well_formed active pool;
  daring_whole_wf : memory_well_formed active whole;
  daring_pool_empty_buffers : forall i, buffers pool i = [];
  daring_pool_free : lock_free pool;
  daring_whole_free : lock_free whole;
  daring_pool_invariant : persistent_full_satisfies active s pool invariant;
  daring_composition : exists combined : resource active,
    repaired_spatiotemporal active (proj1_sig frame) (proj1_sig local) (proj1_sig combined) /\
    memory_temporal active pool (resource_memory active combined) whole
}.

(** Stores keep the exact pool. Other program steps may repartition the
    pool and local heap, but retain the exact external frame, the footprint
    bound and the old action-specific mark budget. *)
Record daring_program_update active action (local : resource active) pool whole
    (local' : resource active) pool' whole' : Prop := {
  daring_update_footprint : forall loc,
    memory_domain pool' loc \/ memory_domain (resource_memory active local') loc ->
    memory_domain pool loc \/ memory_domain (resource_memory active local) loc;
  daring_update_marks : forall i, complete (proj1_sig local') i ->
    complete (proj1_sig local) i \/ action_earns action i;
  daring_store_keeps_pool : forall actor loc value,
    whole' = enqueue whole actor loc value -> pool' = pool
}.

(** A physical flush updates the pool exactly when it writes a pool cell.
    The flushed component also takes its usual generalized flush; the other
    component is fixed. This is deliberately the existing resource future,
    not a new interpretation of the write atom. *)
Definition daring_pool_flush pool loc value :=
  match shared_heap pool loc with
  | None => pool
  | Some _ => Memory (heap_update (shared_heap pool) loc value) (buffers pool) (blocked pool)
  end.

Definition daring_component_flush active actor (before after : resource active) : Prop :=
  flush_at active actor (resource_memory active before) (resource_memory active after) /\
  (forall i, complete (proj1_sig after) i <-> complete (proj1_sig before) i \/ i = actor).

Definition daring_flush_update active actor loc value (local frame : resource active) pool
    (local' frame' : resource active) pool' : Prop :=
  pool' = daring_pool_flush pool loc value /\
  ((frame' = frame /\ daring_component_flush active actor local local') \/
   (local' = local /\ daring_component_flush active actor frame frame')).

Fixpoint daring_safe active invariant n command s (local : resource active) post : Prop :=
  match n with
  | O => True
  | S remaining => forall future_local, resource_future active local future_local ->
      (terminal command -> persistent_models active s future_local post) /\
      forall pool frame whole, daring_environment active invariant s future_local pool frame whole ->
        ~ abort active command (State s whole) /\
        (forall action next t whole',
          program_step active action command (State s whole) next (State t whole') ->
          exists local' pool',
            daring_environment active invariant t local' pool' frame whole' /\
            daring_program_update active action future_local pool whole local' pool' whole' /\
            daring_safe active invariant remaining next t local' post) /\
        (forall actor loc value rest, active actor -> ~ blocked whole actor ->
          buffers whole actor = (loc,value) :: rest ->
          exists local' frame' pool',
            daring_flush_update active actor loc value future_local frame pool local' frame' pool' /\
            daring_environment active invariant s local' pool' frame'
              (flush_write whole actor loc value rest) /\
            daring_safe active invariant remaining command s local' post)
  end.

Definition daring_valid active invariant pre command post : Prop :=
  daring_lock_free command /\ forall s local, persistent_models active s local pre ->
    forall n, daring_safe active invariant n command s local post.

Definition daring_nonstore primitive : Prop :=
  match primitive with S.Store _ _ => False | _ => True end.

Definition daring_access_rule active invariant pre post primitive annotation : Prop :=
  invariant_fragment invariant -> daring_nonstore primitive ->
  owned_valid active OverlapMode A.Emp (A.Temporal invariant pre)
    (C.Prim (C.Common primitive) annotation) (A.Temporal invariant post) ->
  daring_valid active invariant pre (C.Prim (C.Common primitive) annotation) post.

(** The stability premise is universal over stacks and models. It changes
    the heap value only, not the footprint, buffers, or ghost ownership. *)
Definition daring_store_stable active invariant address value : Prop :=
  forall s pool, persistent_full_satisfies active s pool invariant ->
    exists loc old, eval_expr s address = Z.pos loc /\ shared_heap pool loc = Some old /\
      persistent_full_satisfies active s
        (Memory (heap_update (shared_heap pool) loc (eval_expr s value)) (buffers pool) (blocked pool)) invariant.

Definition daring_store_rule active invariant pre address value annotation : Prop :=
  invariant_fragment invariant -> daring_store_stable active invariant address value ->
  daring_valid active invariant pre (C.Prim (C.Common (S.Store address value)) annotation)
    (A.Temporal pre (A.LeadsTo address annotation value)).

Definition daring_skip_rule active invariant pre annotation : Prop :=
  invariant_fragment invariant -> daring_valid active invariant pre (C.skip annotation) pre.
Definition daring_sequence_rule active invariant pre middle post first second : Prop :=
  daring_valid active invariant pre first middle -> daring_valid active invariant middle second post ->
  daring_valid active invariant pre (C.Seq first second) post.
Definition daring_consequence_rule active invariant pre pre' command post' post : Prop :=
  persistent_entails active pre pre' -> daring_valid active invariant pre' command post' ->
  persistent_entails active post' post -> daring_valid active invariant pre command post.
Definition daring_disjunction_rule active invariant pre pre' command post : Prop :=
  daring_valid active invariant pre command post -> daring_valid active invariant pre' command post ->
  daring_valid active invariant (A.Or pre pre') command post.
Definition daring_choice_rule active invariant pre left right post : Prop :=
  daring_valid active invariant pre left post -> daring_valid active invariant pre right post ->
  daring_valid active invariant pre (C.Choice left right) post.
Definition daring_loop_rule active invariant pre body : Prop :=
  daring_valid active invariant pre body pre -> daring_valid active invariant pre (C.Loop body) pre.
Definition daring_exists_rule active invariant pre command post x : Prop :=
  ~ In x (A.fv invariant) -> ~ In x (C.fv command) -> ~ In x (A.fv post) ->
  daring_valid active invariant pre command post ->
  daring_valid active invariant (A.Exists x pre) command post.
Definition daring_frame_rule active invariant pre command post frame : Prop :=
  daring_valid active invariant pre command post -> frame_variable_condition command frame ->
  daring_valid active invariant (A.Spatial frame pre) command (A.Spatial frame post).
Definition daring_parallel_rule active invariant left_pre left left_post right_pre right right_post : Prop :=
  daring_valid active invariant left_pre left left_post -> daring_valid active invariant right_pre right right_post ->
  parallel_variable_condition (Build_concurrent_specification invariant left_pre left left_post)
    (Build_concurrent_specification invariant right_pre right right_post) ->
  frame_variable_condition left invariant -> frame_variable_condition right invariant ->
  daring_valid active invariant (A.Spatial left_pre right_pre)
    (C.Parallel left right) (A.Spatial left_post right_post).

Definition daring_adequacy_statement active invariant pre command post : Prop :=
  invariant_fragment invariant -> two_active_processors active ->
  daring_valid active invariant pre command post ->
  forall n s whole last t final local pool,
    persistent_models active s local pre ->
    daring_environment active invariant s local pool (empty_resource_value active) whole ->
    execution active n command s whole last t final ->
    ~ abort active last (State t final) /\
    (terminal last -> exists local' pool',
      daring_environment active invariant t local' pool' (empty_resource_value active) final /\
      persistent_models active t local' post).
