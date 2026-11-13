From Stdlib Require Import List ZArith.
From WMLR Require Import Expressions Languages Machine BufferRelations OrderedBuffers Separation
  StableCompatibility RepairedSeparation FrameDecomposition OperationalSemantics
  Assertions AssertionSemantics ConcreteAssertions RepairedAssertions PersistentAssertions
  Safety RepairedSafety PersistentRules.
Import ListNotations.

Definition cell_assertion loc v := A.points_to (EVal (Z.pos loc)) (EVal v).

Lemma cell_assertion_wand_free loc v : wand_free (cell_assertion loc v).
Proof. unfold cell_assertion, A.points_to; simpl; tauto. Qed.

Lemma cell_assertion_fresh loc v x : ~ In x (A.fv (cell_assertion loc v)).
Proof.
  intros H. apply A.points_to_fv in H. simpl in H; tauto.
Qed.

Lemma persistent_cell_shape active s local loc v : persistent_full_satisfies active s local (cell_assertion loc v) ->
  shared_heap local loc = Some v /\ (forall i, buffers local i = []) /\ lock_free local.
Proof.
  intros [r [Hr Hp]]. apply (proj1 (persistent_wand_free_unchanged active _ _ _ (cell_assertion_wand_free loc v))) in Hp.
  destruct (repaired_points_to_requires_flushed _ _ _ _ _ Hp) as
    [address [owner [Haddress [Howner [[Hheap [Hbuffers [Hfree Hcomplete]]] HcompleteAll]]]]].
  simpl in Haddress; inversion Haddress; subst address. rewrite Hr in Hheap, Hbuffers, Hfree.
  split; [rewrite Hheap; apply heap_update_same |]. split; assumption.
Qed.

Lemma framed_cell_read active shared frame local whole i loc v :
  active i -> repaired_framed active shared frame local whole ->
  shared_heap local loc = Some v -> buffers local i = [] -> local_read whole i (Z.pos loc) = Some v.
Proof.
  intros Hi [combined [[Hstable [Hch [Hcb Hck]]] [[Hdisjoint Hblocked] [Hwh [Hwb Hwk]]]]] Hcell Hempty.
  assert (HcombinedHeap : shared_heap combined loc = Some v).
  { rewrite Hch; unfold heap_override; rewrite Hcell; reflexivity. }
  assert (Hframe : buffer_lookup (buffers frame i) loc = None).
  { apply buffer_lookup_none. intros Hdom.
    apply (proj1 (proj2 Hstable) i Hi loc Hdom); exists v; exact Hcell. }
  assert (Hcombined : buffer_lookup (buffers combined i) loc = None).
  { rewrite (proj2 (ordered_is_override _ _ _ (Hcb i)) loc), Hempty.
    cbn [buffer_lookup heap_override]; exact Hframe. }
  assert (Hwhole : buffer_lookup (buffers whole i) loc = None).
  { apply buffer_lookup_none. intros [w Hw].
    apply (interleaves_in _ _ _ _ (Hwb i)) in Hw. destruct Hw as [Hs |Hc].
    - apply (Hdisjoint loc); [right; exists i, w; exact Hs |left; exists v; exact HcombinedHeap].
    - apply (proj1 (buffer_lookup_none _ _) Hcombined). exists w; exact Hc. }
  unfold local_read; rewrite Hwhole, Hwh; unfold heap_override; rewrite HcombinedHeap; reflexivity.
Qed.

Theorem persistent_load_cell_valid active invariant loc v x annotation :
  ~ In x (A.fv invariant) ->
  persistent_valid active invariant (cell_assertion loc v)
    (Concurrent.Prim (Concurrent.Common (Sequential.Load x (EVal (Z.pos loc)))) annotation)
    (A.And (cell_assertion loc v) (A.Pure (BEq (EVar x) (EVal v)))).
Proof.
  intros Hfresh. apply persistent_primitive_rule; [discriminate | |].
  - intros s local Hp shared frame whole Henv i Hi Habort.
    destruct (persistent_cell_shape _ _ _ _ _ Hp) as [Hheap [Hbuffers Hfree]].
    inversion Habort; subst.
    pose proof (framed_cell_read active shared frame local whole i loc v ltac:(assumption)
      (repaired_environment_framed _ _ _ _ _ _ _ Henv) Hheap (Hbuffers i)) as Hread.
    cbn [eval_expr] in *; congruence.
  - intros s local Hp shared frame whole Henv i t whole' Hi Hstep.
    destruct (persistent_cell_shape _ _ _ _ _ Hp) as [Hheap [Hbuffers Hfree]].
    inversion Hstep; subst.
    pose proof (framed_cell_read active shared frame local whole' i loc v ltac:(assumption)
      (repaired_environment_framed _ _ _ _ _ _ _ Henv) Hheap (Hbuffers i)) as Hread.
    assert (Heq : v0 = v) by (cbn [eval_expr] in *; congruence); subst v0.
    exists local, shared, frame. split; [apply persistent_update_environment; assumption |].
    split; [constructor |]. split; [apply ownership_preserved_refl |].
    assert (Hp' : persistent_full_satisfies active (update s x v) local (cell_assertion loc v)).
    { eapply persistent_full_agrees; [apply agrees_update_irrelevant, cell_assertion_fresh |exact Hp]. }
    destruct Hp' as [r [Hr Hp']]. exists r; split; [exact Hr |]. split; [exact Hp' |].
    change (Z.eqb (update s x v x) v = true). rewrite update_same; apply Z.eqb_refl.
Qed.

Lemma ordered_append_future a b out w : ordered_overrides a b out ->
  ordered_overrides a (b ++ [w]) (out ++ [w]).
Proof.
  induction 1; simpl.
  - apply OrderedRight; [intros [v H]; contradiction |constructor].
  - constructor; exact IHordered_overrides.
  - apply OrderedRight; assumption.
Qed.

Lemma interleaves_append_right {T} (a b out : list T) w : interleaves a b out ->
  interleaves a (b ++ [w]) (out ++ [w]).
Proof. induction 1; simpl; constructor; assumption || constructor. Qed.

Lemma repaired_enqueue_right active frame local whole i loc v old :
  memory_repaired active frame local whole -> shared_heap local loc = Some old ->
  memory_repaired active frame (enqueue local i loc v) (enqueue whole i loc v).
Proof.
  intros [Hcompat [Hh [Hb Hk]]] Hcell. split.
  - destruct Hcompat as [Hblocked [Hheap Hbuffers]]. split; [exact Hblocked |]. split; [exact Hheap |].
    intros j k Hj Hk' Hneq address Hframe [w Hw]. cbn [enqueue buffers] in Hw.
    unfold buffer_update in Hw. destruct (Pos.eq_dec k i) as [-> |Hother].
    + apply in_app_iff in Hw; destruct Hw as [Hw |[Heq |Hfalse]]; [| |contradiction].
      * apply (Hbuffers j i Hj Hk' Hneq address Hframe). exists w; exact Hw.
      * inversion Heq; subst address w. apply (Hheap j Hj loc Hframe). exists old; exact Hcell.
    + apply (Hbuffers j k Hj Hk' Hneq address Hframe). exists w; exact Hw.
  - split; [exact Hh |]. split; [|exact Hk]. intros j; cbn [enqueue buffers]; unfold buffer_update.
    destruct (Pos.eq_dec j i) as [-> |Hneq]; [apply ordered_append_future, Hb |apply Hb].
Qed.

Lemma spatial_enqueue_right a b whole i loc v :
  memory_spatial a b whole -> memory_domain b loc ->
  memory_spatial a (enqueue b i loc v) (enqueue whole i loc v).
Proof.
  intros [[Hd Hk] [Hh [Hb Hblocks]]] Hloc. split.
  - split; [|exact Hk]. intros address Ha Hb'. apply (Hd address Ha).
    apply (enqueue_domain_subset b i loc v Hloc), Hb'.
  - split; [exact Hh |]. split; [|exact Hblocks]. intros j; cbn [enqueue buffers]; unfold buffer_update.
    destruct (Pos.eq_dec j i) as [-> |Hneq]; [apply interleaves_append_right, Hb |apply Hb].
Qed.

Lemma framed_enqueue_cell active shared frame local whole i loc v old :
  repaired_framed active shared frame local whole -> shared_heap local loc = Some old ->
  repaired_framed active shared frame (enqueue local i loc v) (enqueue whole i loc v).
Proof.
  intros [combined [Hinner Houter]] Hcell. exists (enqueue combined i loc v). split.
  - eapply repaired_enqueue_right; eassumption.
  - apply spatial_enqueue_right; [exact Houter |]. left; exists old.
    rewrite (proj1 (proj2 Hinner)); unfold heap_override; rewrite Hcell; reflexivity.
Qed.

Lemma full_memory_valid_with_processor active i m : active i -> memory_well_formed active m ->
  generalized_well_formed active (Generalized m active).
Proof.
  intros Hi Hwf. split; [exact Hwf |]. split; [intros j Hj; exact Hj |].
  intros Hnone loc; exfalso; apply (Hnone i Hi).
Qed.

Definition pending_write_memory i loc v := Memory empty_heap
  (buffer_update empty_buffers i [(loc, v)]) no_blocked.

Lemma pending_write_valid active i loc v : active i ->
  generalized_well_formed active (Generalized (pending_write_memory i loc v) no_blocked).
Proof.
  intros Hi. split.
  - split; [intros j H; contradiction |]. intros j Hj.
    cbn [pending_write_memory underlying buffers]; rewrite buffer_update_other; [reflexivity |].
    intros ->; contradiction.
  - split; [intros j H; contradiction |intros; reflexivity].
Qed.

Definition pending_write_resource active i loc v (Hi : active i) : resource active :=
  exist _ (Generalized (pending_write_memory i loc v) no_blocked) (pending_write_valid active i loc v Hi).

Lemma cell_store_post active s local loc old i v : active i ->
  persistent_full_satisfies active s local (cell_assertion loc old) ->
  persistent_full_satisfies active s (enqueue local i loc v)
    (A.Temporal (cell_assertion loc old) (A.LeadsTo (EVal (Z.pos loc)) (EVal (Z.pos i)) (EVal v))).
Proof.
  intros Hi Hp. pose proof (persistent_full_well_formed _ _ _ _ Hp) as [Hwf _].
  destruct (persistent_cell_shape _ _ _ _ _ Hp) as [Hheap [Hbuffers Hfree]].
  destruct Hp as [r [Hr Hp]].
  assert (Hnew : generalized_well_formed active (Generalized (enqueue local i loc v) active)).
  { apply (full_memory_valid_with_processor active i); [exact Hi |].
    apply update_buffers_well_formed; assumption. }
  exists (exist _ _ Hnew). split; [reflexivity |].
  exists r, (pending_write_resource active i loc v Hi). split.
  - change (repaired_temporal active (proj1_sig r)
      (Generalized (pending_write_memory i loc v) no_blocked)
      (Generalized (enqueue local i loc v) active)).
    rewrite Hr. split.
    + split; [intros j Hj Hfalse; contradiction |]. split.
      * intros j _ address [w Hw]; rewrite Hbuffers in Hw; contradiction.
      * intros j k _ _ _ address [w Hw]; rewrite Hbuffers in Hw; contradiction.
    + split.
      * split.
        -- apply stable_implies_original_compatible. split; [intros j Hj Hfalse; contradiction |]. split.
           ++ intros j _ address [w Hw]; rewrite Hbuffers in Hw; contradiction.
           ++ intros j k _ _ _ address [w Hw]; rewrite Hbuffers in Hw; contradiction.
        -- split; [intros address; reflexivity |]. split.
           ++ intros j. cbn [underlying pending_write_resource proj1_sig pending_write_memory enqueue buffers].
              unfold buffer_update. destruct (Pos.eq_dec j i) as [-> |Hneq]; [reflexivity |rewrite app_nil_r; reflexivity].
           ++ intros j; simpl; unfold no_blocked; tauto.
      * split; [intros j H; contradiction |]. intros j; simpl; unfold no_blocked; tauto.
  - split; [exact Hp |]. split; [exact Hi |left].
    split; [intros; reflexivity |]. split; [intros; reflexivity |intros j H; contradiction].
Qed.

Theorem persistent_store_cell_valid active invariant loc old i v :
  persistent_valid active invariant (cell_assertion loc old)
    (Concurrent.Prim (Concurrent.Common (Sequential.Store (EVal (Z.pos loc)) (EVal v))) (EVal (Z.pos i)))
    (A.Temporal (cell_assertion loc old) (A.LeadsTo (EVal (Z.pos loc)) (EVal (Z.pos i)) (EVal v))).
Proof.
  apply persistent_primitive_rule; [discriminate | |].
  - intros s local Hp shared frame whole Henv j Heval Habort. simpl in Heval; inversion Heval; subst j.
    destruct (persistent_cell_shape _ _ _ _ _ Hp) as [Hheap [Hbuffers Hfree]].
    inversion Habort; subst.
    pose proof (framed_cell_read active shared frame local whole i loc old ltac:(assumption)
      (repaired_environment_framed _ _ _ _ _ _ _ Henv) Hheap (Hbuffers i)) as Hread.
    cbn [eval_expr] in *; congruence.
  - intros s local Hp shared frame whole Henv j t whole' Heval Hstep.
    simpl in Heval; inversion Heval; subst j. inversion Hstep; subst.
    match goal with H : eval_expr _ _ = Z.pos ?address |- _ =>
      cbn [eval_expr] in H; injection H as Haddress; subst address end.
    destruct (persistent_cell_shape _ _ _ _ _ Hp) as [Hheap [Hbuffers Hfree]].
    exists (enqueue local i loc v), shared, frame. split.
    + destruct Henv as [Hl Hs Hf Hw Hsep Hlock Hinv]. constructor.
      * apply update_buffers_well_formed; assumption.
      * exact Hs.
      * exact Hf.
      * apply update_buffers_well_formed; assumption.
      * eapply framed_enqueue_cell; eassumption.
      * exact Hlock.
      * exact Hinv.
    + split; [constructor |]. split.
      * split; intros address Hdom; [left |right; exact Hdom].
        apply (enqueue_domain_subset local i loc v); [left; exists old; exact Hheap |exact Hdom].
      * apply cell_store_post; assumption.
Qed.
