From Stdlib Require Import List ZArith.
From WMLR Require Import Expressions Machine BufferRelations Separation StableCompatibility
  RepairedSeparation Assertions AssertionSemantics ConcreteAssertions PersistentAssertions
  PersistentRules TemporalSafety TemporalFence RegionalResources TransferredCells InvariantFragment
  AssertionResourceEquivalence AssertionAlgebra AssertionBarrierAlgebra.
Import ListNotations.

Lemma assertion_write_barrier_shape active s r address annotation value :
  persistent_models active s r (A.Temporal (A.LeadsTo address annotation value) (A.Barrier annotation)) ->
  exists loc owner, eval_expr s address = Z.pos loc /\ eval_expr s annotation = Z.pos owner /\
    active owner /\ flushed_atom owner loc (eval_expr s value) (proj1_sig r).
Proof.
  intros (a & b & Htm & HW & HB).
  change (write_atom active (eval_expr s address) (eval_expr s annotation) (eval_expr s value) (proj1_sig a)) in HW.
  change (barrier_atom active (eval_expr s annotation) (proj1_sig b)) in HB.
  destruct (eval_expr s address) as [|loc|neg]; try contradiction;
    destruct (eval_expr s annotation) as [|owner|negowner]; try contradiction.
  pose proof (proj1 HW) as Hi; exists loc,owner; repeat split; try reflexivity; try exact Hi.
  all: pose proof (processor_cell_shape active owner s r loc (eval_expr s value) Hi
    (ex_intro _ a (ex_intro _ b (conj Htm (conj HW HB))))) as Hshape;
    exact (proj1 Hshape) || exact (proj1 (proj2 Hshape)) || exact (proj1 (proj2 (proj2 Hshape)))
      || exact (proj2 (proj2 (proj2 Hshape))).
Qed.

Lemma assertion_write_barrier_from_shape active s r address annotation value loc owner :
  eval_expr s address = Z.pos loc -> eval_expr s annotation = Z.pos owner -> active owner ->
  flushed_atom owner loc (eval_expr s value) (proj1_sig r) ->
  persistent_models active s r (A.Temporal (A.LeadsTo address annotation value) (A.Barrier annotation)).
Proof.
  intros Eaddr Eowner Hi Hshape.
  destruct Hshape as [Hheap [Hbuffers [Hfree Hmark]]].
  pose proof (processor_cell_from_shape active owner s r loc (eval_expr s value) Hi
    Hheap Hbuffers Hfree Hmark) as (a & b & Htm & HW & HB).
  exists a,b; split; [exact Htm |]. split.
  - change (write_atom active (eval_expr s address) (eval_expr s annotation) (eval_expr s value) (proj1_sig a)).
    rewrite Eaddr,Eowner; exact HW.
  - change (barrier_atom active (eval_expr s annotation) (proj1_sig b)); rewrite Eowner; exact HB.
Qed.

Definition assertion_revalue_cell active (r : resource active) (loc : location) (value : value) (owner : processor)
    (Hmark : complete (proj1_sig r) owner) : resource active.
Proof.
  refine (exist _ (Generalized (Memory (heap_update empty_heap loc value) empty_buffers no_blocked)
    (complete (proj1_sig r))) _).
  split; [split; [intros i H; contradiction |intros; reflexivity] |].
  split; [exact (proj1 (proj2 (proj2_sig r))) |].
  intros Hnone address; exfalso; exact (Hnone owner Hmark).
Defined.

(** E12: the printed successive-write collapse, for arbitrary expressions.
    No active-processor premise is needed: invalid annotations make both
    sides false. Old and new values may differ. *)
Theorem assertion_successive_writes_collapse active address annotation old next s r :
  persistent_models active s r
    (A.Temporal (A.Temporal (A.LeadsTo address annotation old) (A.LeadsTo address annotation next))
      (A.Barrier annotation)) <->
  persistent_models active s r (A.Temporal (A.LeadsTo address annotation next) (A.Barrier annotation)).
Proof.
  rewrite assertion_barrier_distributes_temporal; split.
  - intros (a & b & [_ [[_ [Hheap [Hbuffers Hblocks]]] [_ Hmarks]]] & HA & HB).
    apply assertion_write_barrier_shape in HA; destruct HA as (loc & owner & Eaddr & Eowner & Hi & Hah & Hab & Hak & Ham).
    apply assertion_write_barrier_shape in HB; destruct HB as (loc' & owner' & Eaddr' & Eowner' & Hi' & Hbh & Hbb & Hbk & Hbm).
    assert (loc' = loc) by congruence; assert (owner' = owner) by congruence; subst loc' owner'.
    eapply assertion_write_barrier_from_shape; [exact Eaddr |exact Eowner |exact Hi |].
    split.
    + intros l; rewrite Hheap; unfold heap_override; rewrite Hah,Hbh.
      unfold heap_update,empty_heap; destruct (Pos.eq_dec l loc); reflexivity.
    + split; [intros i; rewrite Hbuffers,Hab,Hbb; reflexivity |]. split.
      * intros i H; apply Hblocks in H; destruct H; [exact (Hak i H) |exact (Hbk i H)].
      * apply Hmarks; right; exact Hbm.
  - intros HB; pose proof (assertion_write_barrier_shape _ _ _ _ _ _ HB)
      as (loc & owner & Eaddr & Eowner & Hi & Hh & Hb & Hk & Hm).
    pose (a := assertion_revalue_cell active r loc (eval_expr s old) owner Hm).
    assert (HA : persistent_models active s a (A.Temporal (A.LeadsTo address annotation old) (A.Barrier annotation))).
    { eapply assertion_write_barrier_from_shape; [exact Eaddr |exact Eowner |exact Hi |].
      split; [intros; reflexivity |]. split; [intros; reflexivity |]. split; [intros i H; exact H |exact Hm]. }
    exists a,r; split; [|auto].
    assert (Hstable : stable_compatible active (resource_memory active a) (resource_memory active r)).
    { split; [intros i H; contradiction |]. split;
        [intros i _ l [v H]; contradiction |intros i j _ _ _ l [v H]; contradiction]. }
    split; [exact Hstable |]. split.
    + split; [apply stable_implies_printed_compatible,Hstable |]. split.
      * intros l; change (shared_heap (resource_memory active r) l =
          heap_override (heap_update empty_heap loc (eval_expr s old)) (shared_heap (resource_memory active r)) l).
        unfold resource_memory,heap_override; rewrite Hh; unfold heap_update,empty_heap.
        destruct (Pos.eq_dec l loc); reflexivity.
      * split; [intros; reflexivity |intros i; cbn; unfold no_blocked; tauto].
    + split; [intros; reflexivity |intros i; cbn; tauto].
Qed.

(** T4's valid form for the printed all-processor cell. *)
Theorem assertion_points_to_write_active active address value annotation :
  (forall s, exists owner, eval_expr s annotation = Z.pos owner /\ active owner) ->
  persistent_entails active (A.points_to address value) (A.LeadsTo address annotation value).
Proof.
  intros Hannotation s r HP.
  pose proof (assertion_wand_free_in_printed active (A.points_to address value) ltac:(cbn [A.points_to wand_free]; tauto) s r HP) as Hprinted.
  destruct (points_to_requires_flushed _ _ _ _ _ Hprinted) as
    (loc & writer & Eaddr & Hwriter & [Hheap [Hbuffers [Hfree HwriterMark]]] & Hall).
  destruct (Hannotation s) as (owner & Eowner & Hi).
  change (write_atom active (eval_expr s address) (eval_expr s annotation) (eval_expr s value) (proj1_sig r)).
  rewrite Eaddr,Eowner; split; [exact Hi |right].
  split; [exact Hheap |]. split; [exact Hbuffers |]. split; [exact Hfree |apply Hall,Hi].
Qed.

(** The weaker cell implies a named write exactly when that processor's
    mark is present. Active-processor membership alone is insufficient. *)
Theorem assertion_writer_cell_named_write active address value annotation s r :
  persistent_models active s r (writer_points_to address value) ->
  (persistent_models active s r (A.LeadsTo address annotation value) <->
    exists owner, eval_expr s annotation = Z.pos owner /\ complete (proj1_sig r) owner).
Proof.
  intros HC; destruct (writer_points_to_shape _ _ _ _ _ HC)
    as (loc & writer & Eaddr & Hwriter & Hheap & Hbuffers & Hfree & HwriterMark).
  split.
  - intros HW; change (write_atom active (eval_expr s address) (eval_expr s annotation)
      (eval_expr s value) (proj1_sig r)) in HW; rewrite Eaddr in HW.
    destruct (eval_expr s annotation) as [|owner|neg]; try contradiction.
    destruct HW as [_ [[_ [Hb _]] |[_ [_ [_ Hmark]]]]].
    + specialize (Hb owner); change (buffers (resource_memory active r) owner =
        buffer_update empty_buffers owner [(loc,eval_expr s value)] owner) in Hb.
      rewrite Hbuffers,buffer_update_same in Hb; discriminate.
    + exists owner; auto.
  - intros (owner & Eowner & Hmark).
    change (write_atom active (eval_expr s address) (eval_expr s annotation) (eval_expr s value) (proj1_sig r)).
    rewrite Eaddr,Eowner; split; [exact (proj1 (proj2 (proj2_sig r)) owner Hmark) |right].
    split; [exact Hheap |]. split; [exact Hbuffers |]. split; assumption.
Qed.
