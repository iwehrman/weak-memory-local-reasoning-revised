From Stdlib Require Import List ZArith.
From WMLR Require Import Expressions Languages Machine BufferRelations Separation RepairedSeparation
  GeneralizedFlushing OperationalSemantics Assertions AssertionSemantics ConcreteAssertions
  RepairedAssertions PersistentAssertions Safety RepairedSafety Specifications PrivateOwnership TemporalSafety.
Import ListNotations.

Definition mark_processor active (r : resource active) i (Hi : active i) : resource active.
Proof.
  refine (exist _ (Generalized (resource_memory active r) (fun j => complete (proj1_sig r) j \/ j = i)) _).
  apply (generalized_step_well_formed active (proj1_sig r)); [|exact (proj2_sig r)].
  destruct r as [[m marks] [Hwf [Hactive Hheap]]]; simpl.
  apply GeneralizedMark; [auto |]. intros j [Hj | ->]; auto.
Defined.

Lemma temporal_mark_right active (frame local combined : resource active) i (Hi : active i) :
  repaired_temporal active (proj1_sig frame) (proj1_sig local) (proj1_sig combined) ->
  buffers (resource_memory active combined) i = [] ->
  repaired_temporal active (proj1_sig frame) (proj1_sig (mark_processor active local i Hi))
    (proj1_sig (mark_processor active combined i Hi)).
Proof.
  intros [Hstable [Hmemory [Hbefore Hmarks]]] Hempty.
  assert (Hframeempty : buffers (resource_memory active frame) i = []).
  { unfold resource_memory in Hempty. rewrite (proj1 (proj2 (proj2 Hmemory)) i) in Hempty.
    apply app_eq_nil in Hempty; tauto. }
  split; [exact Hstable |]. split; [exact Hmemory |]. split.
  - intros j [Hj | ->]; [apply Hbefore, Hj |exact Hframeempty].
  - intros j; change ((complete (proj1_sig combined) j \/ j = i) <->
      complete (proj1_sig frame) j \/ complete (proj1_sig local) j \/ j = i).
    rewrite (Hmarks j); tauto.
Qed.

Lemma prefix_environment_fence active invariant s local shared frame whole i (Hi : active i) :
  prefix_environment active invariant s local shared frame whole -> buffers whole i = [] ->
  prefix_environment active invariant s (mark_processor active local i Hi) shared frame whole.
Proof.
  intros [Hs Hw [combined [Htm Hsp]] Hlock Hinv] Hempty. constructor; try assumption.
  exists (mark_processor active combined i Hi). split; [|exact Hsp].
  apply temporal_mark_right; [exact Htm |].
  exact (proj2 (spatial_empty_buffer_parts _ _ _ _ Hsp Hempty)).
Qed.

Lemma marked_emp_barrier active s (local : resource active) i (Hi : active i) :
  persistent_models active s local A.Emp ->
  persistent_models active s (mark_processor active local i Hi) (A.Barrier (EVal (Z.pos i))).
Proof. intros H; split; [exact H |right; right; reflexivity]. Qed.

Theorem prefix_fence_valid active invariant i :
  prefix_valid active invariant A.Emp
    (Concurrent.Prim (Concurrent.Common Sequential.Fence) (EVal (Z.pos i)))
    (A.Barrier (EVal (Z.pos i))).
Proof.
  intros s local HP n. revert s local HP.
  assert (Hclosed : flush_closed active (fun s m => persistent_full_satisfies active s m invariant)).
  { intros t a b Hfuture HJ; eapply persistent_full_flushing_closed; eassumption. }
  induction n; intros s local HP; [exact I |]. split.
  - intros [ann E]; discriminate.
  - split.
    + intros shared frame whole Henv Hfault. inversion Hfault; subst.
      match goal with H : primitive_abort _ _ _ _ |- _ => inversion H end.
    + intros shared frame whole next t whole' Henv Hstep. inversion Hstep; subst.
      * match goal with H : primitive_step _ _ _ _ _ |- _ => inversion H; subst end.
        match goal with E : eval_expr _ (EVal (Z.pos _)) = Z.pos _ |- _ => simpl in E; inversion E; subst end.
        match goal with Hi : active ?owner |- _ =>
          exists (mark_processor active local owner Hi), shared, frame end.
        split; [eapply prefix_environment_fence; eassumption |].
        split; [constructor |]. split; [apply ownership_preserved_refl |].
        apply prefix_skip_safe; [exact Hclosed |apply marked_emp_barrier, HP].
      * match goal with H : flush _ _ _ |- _ =>
          destruct (prefix_environment_flush _ _ _ _ _ _ _ _ Hclosed Henv H)
            as (local' & shared' & frame' & Henv' & Hlf & Hff & Howned) end.
        exists local', shared', frame'. split; [exact Henv' |]. split; [exact Hff |].
        split; [exact Howned |]. apply IHn; eapply persistent_assertion_flushing_closed; eassumption.
Qed.

(** Pending writes in the past are allowed. The operational fence, not an
    assertion restriction, forces their flush before the barrier is earned. *)
Theorem prefix_framed_fence_valid active invariant past i :
  prefix_valid active invariant (A.Temporal past A.Emp)
    (Concurrent.Prim (Concurrent.Common Sequential.Fence) (EVal (Z.pos i)))
    (A.Temporal past (A.Barrier (EVal (Z.pos i)))).
Proof.
  apply prefix_temporal_frame_valid; [apply prefix_fence_valid |]. intros x H; contradiction.
Qed.
