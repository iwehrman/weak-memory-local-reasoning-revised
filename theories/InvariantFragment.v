From Stdlib Require Import List ZArith.
From WMLR Require Import Expressions Machine BufferRelations Separation
  RepairedSeparation Assertions AssertionSemantics ConcreteAssertions
  RepairedAssertions PersistentAssertions HeapRules TemporalSafety TemporalFence
  RegionalResources TransferredCells.
Import ListNotations.

(** Checkpoint 2: an assertion-fragment result in the existing interpretation.
    No new assertion atom, Hoare judgment, safety predicate or operational rule
    is defined here. The old all-processor [A.points_to] remains unchanged. *)
Definition writer_points_to (address contents : expr) : A.assertion :=
  let name := fresh (expr_fv address ++ expr_fv contents) in
  A.Exists name (A.Temporal (A.LeadsTo address (EVar name) contents)
    (A.Barrier (EVar name))).

Lemma writer_points_to_shape active s (r : resource active) address contents :
  persistent_models active s r (writer_points_to address contents) ->
  exists loc owner, eval_expr s address = Z.pos loc /\ active owner /\
    (forall l, shared_heap (resource_memory active r) l =
      heap_update empty_heap loc (eval_expr s contents) l) /\
    (forall i, buffers (resource_memory active r) i = []) /\
    lock_free (resource_memory active r) /\ complete (proj1_sig r) owner.
Proof.
  pose proof (A.points_to_binder_fresh address contents) as [Haddress Hcontents].
  intros [owner_value H].
  change (exists a b : resource active,
    repaired_temporal active (proj1_sig a) (proj1_sig b) (proj1_sig r) /\
    write_atom active
      (eval_expr (update s (fresh (expr_fv address ++ expr_fv contents)) owner_value) address)
      (update s (fresh (expr_fv address ++ expr_fv contents)) owner_value
        (fresh (expr_fv address ++ expr_fv contents)))
      (eval_expr (update s (fresh (expr_fv address ++ expr_fv contents)) owner_value) contents)
      (proj1_sig a) /\
    barrier_atom active
      (update s (fresh (expr_fv address ++ expr_fv contents)) owner_value
        (fresh (expr_fv address ++ expr_fv contents))) (proj1_sig b)) in H.
  rewrite !update_same, !eval_expr_update_irrelevant in H by assumption.
  destruct (eval_expr s address) as [|loc|negative] eqn:Eaddress;
    destruct owner_value as [|owner|negative_owner];
    try solve [destruct H as (a & b & _ & H & _); contradiction].
  change (persistent_models active s r
    (processor_cell owner loc (eval_expr s contents))) in H.
  pose proof (processor_cell_active _ _ _ _ _ _ H) as Hactive.
  exists loc, owner; split; [reflexivity |]. split; [exact Hactive |].
  exact (processor_cell_shape _ _ _ _ _ _ Hactive H).
Qed.

Lemma writer_points_to_from_shape active s (r : resource active) address contents loc owner :
  eval_expr s address = Z.pos loc -> active owner ->
  (forall l, shared_heap (resource_memory active r) l =
    heap_update empty_heap loc (eval_expr s contents) l) ->
  (forall i, buffers (resource_memory active r) i = []) ->
  lock_free (resource_memory active r) -> complete (proj1_sig r) owner ->
  persistent_models active s r (writer_points_to address contents).
Proof.
  intros Eaddress Hactive Hheap Hbuffers Hfree Hmark.
  pose proof (A.points_to_binder_fresh address contents) as [Haddress Hcontents].
  exists (Z.pos owner).
  change (exists a b : resource active,
    repaired_temporal active (proj1_sig a) (proj1_sig b) (proj1_sig r) /\
    write_atom active
      (eval_expr (update s (fresh (expr_fv address ++ expr_fv contents)) (Z.pos owner)) address)
      (update s (fresh (expr_fv address ++ expr_fv contents)) (Z.pos owner)
        (fresh (expr_fv address ++ expr_fv contents)))
      (eval_expr (update s (fresh (expr_fv address ++ expr_fv contents)) (Z.pos owner)) contents)
      (proj1_sig a) /\
    barrier_atom active
      (update s (fresh (expr_fv address ++ expr_fv contents)) (Z.pos owner)
        (fresh (expr_fv address ++ expr_fv contents))) (proj1_sig b)).
  rewrite !update_same, !eval_expr_update_irrelevant by assumption.
  rewrite Eaddress.
  exact (processor_cell_from_shape active owner s r loc (eval_expr s contents)
    Hactive Hheap Hbuffers Hfree Hmark).
Qed.

(** Pure assertions are allowed only with a heap-accounting conjunct.
    This is a syntactic classification of existing assertions, not a new
    semantic validity condition. Guards may occur at any depth. *)
Inductive invariant_fragment : A.assertion -> Prop :=
| InvariantEmp : invariant_fragment A.Emp
| InvariantCell address contents : invariant_fragment (writer_points_to address contents)
| InvariantSpatial p q : invariant_fragment p -> invariant_fragment q ->
    invariant_fragment (A.Spatial p q)
| InvariantOr p q : invariant_fragment p -> invariant_fragment q ->
    invariant_fragment (A.Or p q)
| InvariantExists x p : invariant_fragment p -> invariant_fragment (A.Exists x p)
| InvariantGuard b p : invariant_fragment p -> invariant_fragment (A.And (A.Pure b) p).

Theorem invariant_fragment_shape p : invariant_fragment p ->
  forall active s (r : resource active), persistent_models active s r p ->
  (forall i, buffers (resource_memory active r) i = []) /\
  lock_free (resource_memory active r).
Proof.
  induction 1; intros active s r Hmodel.
  - exact (proj2 Hmodel).
  - destruct (writer_points_to_shape _ _ _ _ _ Hmodel)
      as (loc & owner & _ & _ & _ & Hb & Hfree & _); auto.
  - destruct Hmodel as (a & b & [[Hcompatible [Hheap [Hbuffers Hblocked]]] Hmarks] & Ha & Hb).
    destruct (IHinvariant_fragment1 _ _ _ Ha) as [Hab Hak].
    destruct (IHinvariant_fragment2 _ _ _ Hb) as [Hbb Hbk].
    split.
    + intros i. specialize (Hbuffers i).
      change (interleaves (buffers (resource_memory active a) i)
        (buffers (resource_memory active b) i) (buffers (resource_memory active r) i)) in Hbuffers.
      rewrite Hab, Hbb in Hbuffers; apply interleaves_nil_left, Hbuffers.
    + intros i Hi. apply Hblocked in Hi; destruct Hi; [apply (Hak i) |apply (Hbk i)]; assumption.
  - destruct Hmodel; [eapply IHinvariant_fragment1 |eapply IHinvariant_fragment2]; eassumption.
  - destruct Hmodel as [v Hmodel]; eapply IHinvariant_fragment; exact Hmodel.
  - eapply IHinvariant_fragment; exact (proj2 Hmodel).
Qed.

(** Re-mark the same memory. A nonempty subset of the active processors is
    enough for well-formedness; neither finiteness nor full completeness is
    needed. This is not asserted to be a flushing transition. *)
Definition remark_resource active (r : resource active) marks
    (Hactive : forall i, marks i -> active i) (Hnonempty : exists i, marks i) : resource active.
Proof.
  refine (exist _ (Generalized (resource_memory active r) marks) _).
  split; [exact (proj1 (proj2_sig r)) |]. split; [exact Hactive |].
  intros Hnone loc; destruct Hnonempty as [i Hi]; exfalso; exact (Hnone i Hi).
Defined.

Theorem invariant_fragment_remark p : invariant_fragment p ->
  forall active s (r target : resource active),
  resource_memory active r = resource_memory active target ->
  (exists i, complete (proj1_sig target) i) ->
  persistent_models active s r p -> persistent_models active s target p.
Proof.
  induction 1; intros active s r target Ememory Hnonempty Hmodel.
  - change (empty_atom (proj1_sig target)).
    change ((forall loc, shared_heap (resource_memory active target) loc = None) /\
      (forall i, buffers (resource_memory active target) i = []) /\
      lock_free (resource_memory active target)).
    rewrite <- Ememory; exact Hmodel.
  - destruct (writer_points_to_shape _ _ _ _ _ Hmodel)
      as (loc & oldowner & Eaddress & _ & Hheap & Hbuffers & Hfree & _).
    destruct Hnonempty as [owner Howner].
    eapply writer_points_to_from_shape with (loc := loc) (owner := owner).
    + exact Eaddress.
    + exact (proj1 (proj2 (proj2_sig target)) owner Howner).
    + rewrite <- Ememory; exact Hheap.
    + rewrite <- Ememory; exact Hbuffers.
    + rewrite <- Ememory; exact Hfree.
    + exact Howner.
  - destruct Hmodel as (a & b & [Hsp Hmarks] & Ha & Hb).
    pose (a' := remark_resource active a (complete (proj1_sig target))
      (proj1 (proj2 (proj2_sig target))) Hnonempty).
    pose (b' := remark_resource active b (complete (proj1_sig target))
      (proj1 (proj2 (proj2_sig target))) Hnonempty).
    exists a', b'; split.
    + split.
      * change (memory_spatial (resource_memory active a) (resource_memory active b)
          (resource_memory active target)).
        rewrite <- Ememory; exact Hsp.
      * intros i; change (complete (proj1_sig target) i <->
          complete (proj1_sig target) i \/ complete (proj1_sig target) i); tauto.
    + split.
      * exact (IHinvariant_fragment1 active s a a' eq_refl Hnonempty Ha).
      * exact (IHinvariant_fragment2 active s b b' eq_refl Hnonempty Hb).
  - destruct Hmodel; [left; eapply IHinvariant_fragment1 |right; eapply IHinvariant_fragment2]; eassumption.
  - destruct Hmodel as [v Hmodel]; exists v; eapply IHinvariant_fragment; eassumption.
  - split; [exact (proj1 Hmodel) |]. eapply IHinvariant_fragment; [exact Ememory |exact Hnonempty |exact (proj2 Hmodel)].
Qed.

Corollary invariant_singleton_remark active owner s m p :
  active owner -> invariant_fragment p -> persistent_full_satisfies active s m p ->
  exists r : resource active, resource_memory active r = m /\
    (forall i, complete (proj1_sig r) i <-> i = owner) /\
    persistent_models active s r p /\
    (forall i, buffers (resource_memory active r) i = []) /\
    lock_free (resource_memory active r).
Proof.
  intros Howner Hfragment [original [Eoriginal Hmodel]].
  assert (Hactive : forall i, i = owner -> active i) by (intros i ->; exact Howner).
  assert (Hnonempty : exists i, i = owner) by (exists owner; reflexivity).
  pose (target := remark_resource active original (fun i => i = owner) Hactive Hnonempty).
  assert (Htarget : persistent_models active s target p).
  { exact (invariant_fragment_remark p Hfragment active s original target eq_refl Hnonempty Hmodel). }
  exists target; split.
  - change (underlying (proj1_sig original) = m); rewrite Eoriginal; reflexivity.
  - split; [intros i; reflexivity |]. split; [exact Htarget |].
    exact (invariant_fragment_shape p Hfragment active s target Htarget).
Qed.

Corollary invariant_return_full_completeness active owner s (r : resource active) p :
  active owner -> invariant_fragment p -> persistent_models active s r p ->
  persistent_full_satisfies active s (resource_memory active r) p.
Proof.
  intros Howner Hfragment Hmodel.
  pose (target := remark_resource active r active (fun i H => H) (ex_intro _ owner Howner)).
  exists target; split; [reflexivity |].
  exact (invariant_fragment_remark p Hfragment active s r target eq_refl
    (ex_intro _ owner Howner) Hmodel).
Qed.

(** Release-side obligation: a spatial split into invariant and retained
    resource puts every buffered write, with its order and multiplicity,
    in the retained resource. No buffered address belongs to the invariant. *)
Theorem invariant_spatial_pending_retained active s (pool retained whole : resource active) p :
  invariant_fragment p -> persistent_models active s pool p ->
  spatial (proj1_sig pool) (proj1_sig retained) (proj1_sig whole) ->
  (forall i, buffers (resource_memory active retained) i =
    buffers (resource_memory active whole) i) /\
  (forall i loc v, In (loc, v) (buffers (resource_memory active whole) i) ->
    ~ memory_domain (resource_memory active pool) loc).
Proof.
  intros Hfragment Hmodel [[[Hdomain Hblocked] [Hheap [Hbuffers Hblocks]]] Hmarks].
  destruct (invariant_fragment_shape p Hfragment active s pool Hmodel) as [Hempty Hfree].
  assert (Hretained : forall i, buffers (resource_memory active retained) i =
    buffers (resource_memory active whole) i).
  { intros i; specialize (Hbuffers i).
    change (interleaves (buffers (resource_memory active pool) i)
      (buffers (resource_memory active retained) i) (buffers (resource_memory active whole) i)) in Hbuffers.
    rewrite Hempty in Hbuffers; symmetry; apply interleaves_nil_left, Hbuffers. }
  split; [exact Hretained |]. intros i loc v Hin Hpool.
  apply (Hdomain loc Hpool); right; exists i, v; rewrite Hretained; exact Hin.
Qed.

(** This checks the proposed UNLOCK entailment, not a Hoare/safety rule.
    [pre ; bar(owner)] is evaluated at the resource immediately before
    ownership is returned. A foreign write may remain in [post], never in
    the invariant or at an address donated to it. *)
Corollary invariant_unlock_premise_pending_retained active owner pre invariant post :
  invariant_fragment invariant ->
  (forall s (r : resource active),
    persistent_models active s r (A.Temporal pre (A.Barrier (EVal (Z.pos owner)))) ->
    persistent_models active s r (A.Spatial invariant post)) ->
  forall s r,
    persistent_models active s r (A.Temporal pre (A.Barrier (EVal (Z.pos owner)))) ->
    exists pool retained : resource active,
      spatial (proj1_sig pool) (proj1_sig retained) (proj1_sig r) /\
      persistent_models active s pool invariant /\ persistent_models active s retained post /\
      (forall i, buffers (resource_memory active retained) i = buffers (resource_memory active r) i) /\
      (forall i loc v, In (loc, v) (buffers (resource_memory active r) i) ->
        ~ memory_domain (resource_memory active pool) loc).
Proof.
  intros Hfragment Hentails s r Hpre.
  destruct (Hentails s r Hpre) as (pool & retained & Hsp & Hinv & Hpost).
  exists pool, retained; split; [exact Hsp |]. split; [exact Hinv |].
  split; [exact Hpost |].
  exact (invariant_spatial_pending_retained active s pool retained r invariant Hfragment Hinv Hsp).
Qed.

Corollary invariant_cannot_absorb_pending active s (r : resource active) p i :
  invariant_fragment p -> buffers (resource_memory active r) i <> [] ->
  ~ persistent_models active s r (A.Spatial p A.Emp).
Proof.
  intros Hfragment Hpending (pool & retained & Hsp & Hinv & Hemp).
  destruct (invariant_spatial_pending_retained _ _ _ _ _ _ Hfragment Hinv Hsp) as [Hbuffers _].
  apply Hpending; rewrite <- Hbuffers; exact (proj1 (proj2 Hemp) i).
Qed.

(** Without the guard, the proposed release entailment can indeed assign
    the entire resource, including pending foreign writes, to [Pure true]. *)
Theorem bare_pure_unlock_premise active pre owner :
  forall s (r : resource active),
  persistent_models active s r (A.Temporal pre (A.Barrier (EVal (Z.pos owner)))) ->
  persistent_models active s r (A.Spatial (A.Pure BTrue) A.Emp).
Proof.
  intros s r _; exists r, (bare_resource active); split; [apply spatial_empty_right |].
  split; [reflexivity |apply bare_resource_models].
Qed.
