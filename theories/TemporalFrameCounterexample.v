From Stdlib Require Import List ZArith.
From WMLR Require Import Expressions Languages Machine BufferRelations Separation StableCompatibility
  RepairedSeparation OperationalSemantics ExecutionExamples Assertions AssertionSemantics ConcreteAssertions
  RepairedAssertions PersistentAssertions Safety Specifications OwnershipProtocol PrivateOwnership FlushingCounterexample.
Import ListNotations.

(** Full-resource validity forgets which component supplied completeness.
    This is harmless for spatial promotion but obstructs temporal framing. *)
Lemma full_emp_implies_active_barrier active s m i : active i ->
  persistent_full_satisfies active s m A.Emp ->
  persistent_full_satisfies active s m (A.Barrier (EVal (Z.pos i))).
Proof.
  intros Hi [r [Er Hempty]]. exists r; split; [exact Er |].
  split; [exact Hempty |]. right. rewrite Er; exact Hi.
Qed.

Theorem private_skip_full_barrier_valid active owner invariant i : active i ->
  private_valid active owner invariant Closed A.Emp (Concurrent.skip (EVal (Z.pos owner)))
    Closed (A.Barrier (EVal (Z.pos i))).
Proof.
  intros Hi s local region Hr Hp n. apply private_skip_safe; [exact Hr |].
  eapply full_emp_implies_active_barrier; eassumption.
Qed.

Definition pending_prefix := A.LeadsTo (EVal 1%Z) (EVal 1%Z) (EVal 7%Z).
Definition unmarked_empty_resource : resource two_processors :=
  exist _ empty_generalized (empty_generalized_well_formed two_processors).

Lemma pending_prefix_model s : persistent_models two_processors s wand_pending_resource pending_prefix.
Proof.
  split; [left; reflexivity |]. left.
  split; [intros; reflexivity |]. split; [intros; reflexivity |intros j H; contradiction].
Qed.

Lemma pending_prefix_before_emp s : persistent_full_satisfies two_processors s wand_pending_memory
  (A.Temporal pending_prefix A.Emp).
Proof.
  exists wand_pending_resource; split; [reflexivity |].
  exists wand_pending_resource, unmarked_empty_resource. split.
  - split.
    + split; [intros j H; contradiction |]. split.
      * intros i _ loc _ [v H]; discriminate.
      * intros i j _ _ _ loc _ [v H]; contradiction.
    + split.
      * split.
        -- split; [intros j H; contradiction |]. split.
           ++ intros i _ loc _ [v H]; discriminate.
           ++ intros i j _ _ _ loc _ [v H]; contradiction.
        -- split; [intros; reflexivity |]. split.
           ++ intros i; simpl; rewrite app_nil_r; reflexivity.
           ++ intros i; simpl; unfold no_blocked; tauto.
      * split; [intros i H; contradiction |intros i; simpl; unfold no_blocked; tauto].
  - split; [apply pending_prefix_model |].
    split; [intros; reflexivity |]. split; [intros; reflexivity |intros i H; contradiction].
Qed.

Lemma temporal_barrier_requires_empty_buffer active s whole past i : active i ->
  persistent_full_satisfies active s whole (A.Temporal past (A.Barrier (EVal (Z.pos i)))) ->
  buffers whole i = [].
Proof.
  intros Hi [r [Er [a [b [[_ [[_ [_ [Hb _]]] [Hbefore _]]] [_ [Hempty Hmark]]]]]]].
  destruct Hmark as [Hnot |Hmark]; [contradiction |].
  specialize (Hb i); rewrite Er in Hb; simpl in Hb.
  rewrite Hb, (Hbefore i Hmark), (proj1 (proj2 Hempty) i); reflexivity.
Qed.

Lemma pending_prefix_not_before_barrier s :
  ~ persistent_full_satisfies two_processors s wand_pending_memory
    (A.Temporal pending_prefix (A.Barrier (EVal 1%Z))).
Proof.
  intros H. pose proof (temporal_barrier_requires_empty_buffer _ _ _ _ 1%positive (or_introl eq_refl) H) as E.
  change (buffer_update empty_buffers 1%positive [(1%positive, 7%Z)] 1%positive = []) in E.
  rewrite buffer_update_same in E; discriminate.
Qed.

Lemma pending_prefix_private_region s : private_region two_processors 1%positive A.Emp
  Closed s wand_pending_memory wand_pending_memory.
Proof.
  split; [exact (proj1 wand_pending_valid) |]. split; [exact (proj1 wand_pending_valid) |].
  split; [intros i H; contradiction |]. exists empty_memory; split; [apply protocol_empty_satisfies |].
  exact (proj1 (spatial_empty_left (Generalized wand_pending_memory two_processors))).
Qed.

Theorem private_temporal_frame_counterexample :
  private_valid two_processors 1%positive A.Emp Closed A.Emp (Concurrent.skip (EVal 1%Z))
    Closed (A.Barrier (EVal 1%Z)) /\
  frame_variable_condition (Concurrent.skip (EVal 1%Z)) pending_prefix /\
  ~ private_valid two_processors 1%positive A.Emp Closed (A.Temporal pending_prefix A.Emp)
    (Concurrent.skip (EVal 1%Z)) Closed (A.Temporal pending_prefix (A.Barrier (EVal 1%Z))).
Proof.
  split; [apply private_skip_full_barrier_valid; left; reflexivity |].
  split; [intros x H; contradiction |].
  intros H. specialize (H (fun _ => 0%Z) _ _ (pending_prefix_private_region _) (pending_prefix_before_emp _) 1).
  destruct H as [_ [Hdone _]]. apply (pending_prefix_not_before_barrier (fun _ => 0%Z)).
  exact (proj2 (Hdone (ex_intro _ (EVal 1%Z) eq_refl))).
Qed.
