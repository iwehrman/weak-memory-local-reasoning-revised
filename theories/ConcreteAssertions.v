From Stdlib Require Import List ZArith.
From WMLR Require Import Expressions Machine BufferRelations Separation
  Assertions AssertionSemantics.
Import ListNotations.

(** The auxiliary predicates of Figure 4.4, p. 115. Completeness is
    unrestricted by emp, lock, and pending, subject to Definition 5. *)
Definition empty_atom (g : generalized_memory) : Prop :=
  (forall loc, shared_heap (underlying g) loc = None) /\
  (forall i, buffers (underlying g) i = []) /\ lock_free (underlying g).

Definition barrier_atom active (processor_value : value) g : Prop :=
  empty_atom g /\
  match processor_value with
  | Z.pos i => ~ active i \/ complete g i
  | _ => True
  end.

Definition lock_atom active (processor_value : value) g : Prop :=
  match processor_value with
  | Z.pos i =>
      (forall loc, shared_heap (underlying g) loc = None) /\
      (forall j, buffers (underlying g) j = []) /\ lock_held active (underlying g) i
  | _ => False
  end.

Definition pending_atom i loc v g : Prop :=
  (forall address, shared_heap (underlying g) address = None) /\
  (forall j, buffers (underlying g) j = buffer_update empty_buffers i [(loc, v)] j) /\
  (forall j, blocked (underlying g) j -> j = i).

Definition flushed_atom i loc v g : Prop :=
  (forall address, shared_heap (underlying g) address = heap_update empty_heap loc v address) /\
  (forall j, buffers (underlying g) j = []) /\
  lock_free (underlying g) /\ complete g i.

Definition write_atom active (address processor_value contents : value) g : Prop :=
  match address, processor_value with
  | Z.pos loc, Z.pos i => active i /\
      (pending_atom i loc contents g \/ flushed_atom i loc contents g)
  | _, _ => False
  end.

(** Restrict the resource universe itself, including wand quantification, to
    well-formed generalized memories. No separation law is assumed. *)
Definition concrete_interpretation active : interpretation (resource active) := {|
  empty_resource := fun r => empty_atom (proj1_sig r);
  barrier_resource := fun i r => barrier_atom active i (proj1_sig r);
  lock_resource := fun i r => lock_atom active i (proj1_sig r);
  write_resource := fun loc i v r => write_atom active loc i v (proj1_sig r);
  spatial_composition := fun a b c => spatial (proj1_sig a) (proj1_sig b) (proj1_sig c);
  temporal_composition := fun a b c => temporal active (proj1_sig a) (proj1_sig b) (proj1_sig c)
|}.

Definition models active s (r : resource active) p : Prop :=
  satisfies (concrete_interpretation active) s r p.

Theorem concrete_satisfies_agrees active p s t r :
  agrees (ConcurrentAssertion.fv p) s t ->
  (models active s r p <-> models active t r p).
Proof. intros H. exact (satisfies_agrees (concrete_interpretation active) p s t H r). Qed.

Theorem concrete_spatial_comm active s r p q :
  models active s r (ConcurrentAssertion.Spatial p q) <->
  models active s r (ConcurrentAssertion.Spatial q p).
Proof.
  split; intros [a [b [Hsep [Ha Hb]]]]; exists b, a;
    split; [apply spatial_comm, Hsep | split; assumption |
            apply spatial_comm, Hsep | split; assumption].
Qed.

Lemma barrier_invalid active i g : ~ active i ->
  (barrier_atom active (Z.pos i) g <-> empty_atom g).
Proof. intros Hi; unfold barrier_atom; tauto. Qed.

Lemma barrier_nonpositive active g : barrier_atom active 0%Z g <-> empty_atom g.
Proof. unfold barrier_atom; tauto. Qed.

Lemma all_barriers_complete active s r name :
  models active s r (ConcurrentAssertion.Forall name
    (ConcurrentAssertion.Barrier (EVar name))) ->
  empty_atom (proj1_sig r) /\
  forall i, active i -> complete (proj1_sig r) i.
Proof.
  intros H. change (forall v, barrier_atom active (update s name v name) (proj1_sig r)) in H.
  assert (Hbar : forall v, barrier_atom active v (proj1_sig r)).
  { intros v. specialize (H v). rewrite update_same in H. exact H. }
  split; [exact (proj1 (Hbar 0%Z)) |].
  intros i Hi. destruct (proj2 (Hbar (Z.pos i))); [contradiction | assumption].
Qed.

Lemma temporal_write_all_barriers active a b c i loc v :
  temporal active a b c -> active i ->
  (pending_atom i loc v a \/ flushed_atom i loc v a) ->
  empty_atom b -> (forall j, active j -> complete b j) ->
  flushed_atom i loc v c /\ (forall j, active j -> complete c j).
Proof.
  intros [[_ [Hh [Hb Hk]]] [Hbefore Hg]] Hi Hwrite [Hbh [Hbb Hbk]] Hcomplete.
  assert (Hafter : forall j, active j -> complete c j).
  { intros j Hj. apply (Hg j). right. apply Hcomplete, Hj. }
  split; [|exact Hafter].
  destruct Hwrite as [[_ [Hpending _]] | [Hah [Hab [Hak Hac]]]].
  - specialize (Hbefore i (Hcomplete i Hi)).
    rewrite Hpending, buffer_update_same in Hbefore. discriminate.
  - split.
    + intros address. rewrite Hh. unfold heap_override. rewrite Hbh. apply Hah.
    + split; [intros j; rewrite Hb, Hab, Hbb; reflexivity |].
      split; [|apply Hafter, Hi].
      intros j Hj. apply Hk in Hj. destruct Hj; [apply (Hak j) | apply (Hbk j)]; assumption.
Qed.

(** The fresh-binder points-to abbreviation really excludes pending writes:
    it describes one flushed cell and makes every active buffer complete. *)
Theorem points_to_requires_flushed active s r address contents :
  models active s r (ConcurrentAssertion.points_to address contents) ->
  exists loc i, eval_expr s address = Z.pos loc /\ active i /\
    flushed_atom i loc (eval_expr s contents) (proj1_sig r) /\
    (forall j, active j -> complete (proj1_sig r) j).
Proof.
  pose proof (ConcurrentAssertion.points_to_binder_fresh address contents) as [Haddr Hval].
  unfold ConcurrentAssertion.points_to. intros [a [b [Hsep [Hleft Hright]]]].
  destruct Hleft as [processor_value Hwrite].
  change (write_atom active
    (eval_expr (update s (fresh (expr_fv address ++ expr_fv contents)) processor_value) address)
    (update s (fresh (expr_fv address ++ expr_fv contents)) processor_value
      (fresh (expr_fv address ++ expr_fv contents)))
    (eval_expr (update s (fresh (expr_fv address ++ expr_fv contents)) processor_value) contents)
    (proj1_sig a)) in Hwrite.
  rewrite update_same, !eval_expr_update_irrelevant in Hwrite by assumption.
  destruct (all_barriers_complete active s b _ Hright) as [Hempty Hcomplete].
  unfold write_atom in Hwrite.
  destruct (eval_expr s address) as [|loc|negative] eqn:Haddress; try contradiction;
    destruct processor_value as [|i|negative_processor]; try contradiction.
  destruct Hwrite as [Hi Hwrite]. exists loc, i. split; [reflexivity |].
  split; [exact Hi |].
  exact (temporal_write_all_barriers active (proj1_sig a) (proj1_sig b)
    (proj1_sig r) i loc (eval_expr s contents) Hsep Hi Hwrite Hempty Hcomplete).
Qed.

Corollary points_to_has_no_pending_writes active s r address contents :
  models active s r (ConcurrentAssertion.points_to address contents) ->
  forall i, buffers (underlying (proj1_sig r)) i = [].
Proof.
  intros H. destruct (points_to_requires_flushed _ _ _ _ _ H)
    as [loc [owner [_ [_ [[_ [Hb _]] _]]]]]. exact Hb.
Qed.
