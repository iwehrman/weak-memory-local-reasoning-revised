From Stdlib Require Import List ZArith.
From WMLR Require Import Expressions Languages Machine BufferRelations OrderedBuffers
  Separation RepairedSeparation RepairedFlushing GeneralizedFlushing FrameDecomposition
  OperationalSemantics ProgramSteps Assertions AssertionSemantics PersistentAssertions
  HeapRules OwnedHeapResources OwnershipProtocol PrivateOwnership SpatialExchange TemporalSafety
  InvariantFragment OwnedSafety ResidualUniqueness BufferedPoolCandidate BufferedPoolResources.
Import ListNotations.

Lemma buffered_spatial_read frame joint whole actor address v :
  memory_spatial frame joint whole -> local_read joint actor address = Some v ->
  local_read whole actor address = Some v.
Proof.
  intros Hsp Hread. destruct address; try discriminate.
  eapply spatial_read_right; eassumption.
Qed.

Lemma buffered_primitive_abort_frame active p actor s frame joint whole :
  memory_spatial frame joint whole -> lock_free joint ->
  ~ primitive_abort active (C.Common p) actor (State s joint) ->
  ~ primitive_abort active (C.Common p) actor (State s whole).
Proof.
  intros Hsp Hfree Hsafe Hbad; inversion Hbad; subst.
  - apply Hsafe; constructor; assumption.
  - destruct (local_read joint actor (eval_expr s address)) eqn:E.
    + pose proof (buffered_spatial_read _ _ _ _ _ _ Hsp E); congruence.
    + apply Hsafe; constructor; auto.
  - destruct (local_read joint actor (eval_expr s address)) eqn:E.
    + pose proof (buffered_spatial_read _ _ _ _ _ _ Hsp E); congruence.
    + apply Hsafe; constructor; auto.
Qed.

(** Project an enabled machine action to the pool/local union. For fences
    the implication is only from an enabled framed fence to a frameless one. *)
Lemma buffered_primitive_project active p actor s frame joint whole t whole' :
  memory_spatial frame joint whole -> lock_free joint ->
  ~ primitive_abort active (C.Common p) actor (State s joint) ->
  primitive_step active (C.Common p) actor (State s whole) (State t whole') ->
  exists joint', primitive_step active (C.Common p) actor (State s joint) (State t joint') /\
    memory_spatial frame joint' whole'.
Proof.
  intros Hsp Hfree Hsafe Hstep; inversion Hstep; subst.
  - exists joint; split; [constructor; assumption |exact Hsp].
  - exists joint; split; [constructor; assumption |exact Hsp].
  - exists joint; split; [constructor; assumption |exact Hsp].
  - destruct (local_read joint actor (eval_expr s address)) as [w|] eqn:E.
    + pose proof (buffered_spatial_read _ _ _ _ _ _ Hsp E) as Ewhole.
      assert (w = v) by congruence; subst w.
      exists joint; split; [constructor; auto |exact Hsp].
    + exfalso; apply Hsafe; constructor; auto.
  - destruct (local_read joint actor (Z.pos loc)) as [w|] eqn:E.
    + exists (enqueue joint actor loc (eval_expr t rhs)); split.
      * econstructor; eassumption.
      * apply spatial_enqueue_right; [exact Hsp |]. eapply local_read_domain; eassumption.
    + exfalso; apply Hsafe. apply AbortStore; [assumption |]. congruence.
  - exists joint; split; [|exact Hsp]. constructor; [assumption |].
    eapply spatial_empty_buffer_parts in Hsp; [exact (proj2 Hsp) |eassumption].
Qed.

Theorem buffered_atomic_extension active J P p annotation Q s local pool frame whole :
  buffered_atomic_premise active J P p annotation Q ->
  persistent_models active s local P ->
  buffered_environment active DisjointMode J s local pool frame whole ->
  ~ abort active (C.Prim (C.Common p) annotation) (State s whole) /\
  forall action next t whole',
    program_step active action (C.Prim (C.Common p) annotation) (State s whole) next (State t whole') ->
    exists local' pool',
      buffered_environment active DisjointMode J t local' pool' frame whole' /\
      buffered_update active action local pool local' pool' /\
      persistent_models active t local' Q.
Proof.
  intros [_ Hpremise] HP Henv.
  destruct (buffered_environment_joint _ _ _ _ _ _ _ Henv) as (joint & Hjoint & Hframe).
  pose proof (proj2 (spatial_free_parts _ _ _ Hframe
    (buffered_whole_free _ _ _ _ _ _ _ _ Henv))) as Hfree.
  destruct (Hpremise s local pool joint HP (buffered_pool_models _ _ _ _ _ _ _ _ Henv)
    Hjoint Hfree) as [Hsafe Hnext].
  assert (Hprimitive : forall actor, eval_expr s annotation = Z.pos actor ->
    ~ primitive_abort active (C.Common p) actor (State s joint)).
  { intros actor E Hbad; apply Hsafe; econstructor; eassumption. }
  split.
  - intros Hbad; inversion Hbad; subst.
    eapply buffered_primitive_abort_frame; [exact Hframe |exact Hfree |apply Hprimitive; eassumption |eassumption].
  - intros action next t whole' Hstep; inversion Hstep; subst.
    destruct (buffered_primitive_project _ _ _ _ _ _ _ _ _ Hframe Hfree
      (Hprimitive _ ltac:(eassumption)) ltac:(eassumption)) as (joint' & Hproject & Hframe').
    destruct (Hnext _ _ _ _ (ProgramPrimitive _ _ _ _ _ _ _ ltac:(eassumption) Hproject))
      as (local' & pool' & Hjoint' & Hfree' & HJ' & HQ & Hupdate).
    destruct (spatial_exchange _ _ _ _ _ (memory_spatial_comm _ _ _ Hjoint') Hframe') as (combined & Hcombined & Houter).
    exists local', pool'; split.
    + eapply buffered_environment_intro; [exact HJ' | |apply memory_spatial_comm, Hcombined |exact Houter].
      eapply spatial_free_union; [exact Hframe' | |exact Hfree'].
      exact (proj1 (spatial_free_parts _ _ _ Hframe (buffered_whole_free _ _ _ _ _ _ _ _ Henv))).
    + auto.
Qed.
