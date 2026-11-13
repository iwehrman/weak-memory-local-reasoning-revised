From Stdlib Require Import List ZArith.
From WMLR Require Import Expressions Languages Machine BufferRelations Separation StableCompatibility
  RepairedSeparation OperationalSemantics Assertions AssertionSemantics ConcreteAssertions
  PersistentAssertions Safety RepairedSafety PersistentRules HeapRules.
Import ListNotations.

Definition reblock m blocks := Memory (shared_heap m) (buffers m) blocks.

Lemma framed_blocked_union active shared frame local whole :
  repaired_framed active shared frame local whole ->
  forall i, blocked whole i <-> blocked shared i \/ blocked frame i \/ blocked local i.
Proof.
  intros [combined [[_ [_ [_ Hinner]]] [_ [_ [_ Houter]]]]] i.
  rewrite Houter, Hinner; tauto.
Qed.

Lemma framed_free_externals active shared frame local whole :
  repaired_framed active shared frame local whole -> lock_free whole -> lock_free shared /\ lock_free frame.
Proof.
  intros Hsep Hfree. split; intros i Hi; apply (Hfree i), (framed_blocked_union _ _ _ _ _ Hsep i);
    [left |right; left]; exact Hi.
Qed.

Lemma framed_owned_lock_externals active shared frame local whole i :
  repaired_framed active shared frame local whole ->
  lock_held active local i -> lock_held active whole i -> lock_free shared /\ lock_free frame.
Proof.
  intros [combined [[Hcompat [_ [_ Hinner]]] [[Hdomains Hblocks] [_ [_ Houter]]]]]
    [Hi Hlocal] [_ Hwhole]. split.
  - intros j Hj. assert (Hglobal : blocked whole j) by (apply Houter; left; exact Hj).
    apply Hwhole in Hglobal. apply (Hblocks j Hj), Hinner; right; apply Hlocal, Hglobal.
  - intros j Hj. assert (Hglobal : blocked whole j).
    { apply Houter; right; apply Hinner; left; exact Hj. }
    apply Hwhole in Hglobal. apply (proj1 Hcompat j Hj), Hlocal, Hglobal.
Qed.

Lemma framed_reblock active shared frame local whole blocks :
  repaired_framed active shared frame local whole -> lock_free shared -> lock_free frame ->
  repaired_framed active shared frame (reblock local blocks) (reblock whole blocks).
Proof.
  intros [combined [[Hcompat [Hih [Hib Hik]]] [[Hdomains Hblocks] [Hoh [Hob Hok]]]]] Hshared Hframe.
  exists (reblock combined blocks). split.
  - split.
    + destruct Hcompat as [_ [Hh Hb]]. split; [intros i H _; apply (Hframe i H) |]. split; assumption.
    + split; [exact Hih |]. split; [exact Hib |].
      intros i; cbn [reblock blocked]; split; [intros H; right; exact H |intros [H |H]; [exfalso; apply (Hframe i H) |exact H]].
  - split.
    + split; [exact Hdomains |intros i H _; apply (Hshared i H)].
    + split; [exact Hoh |]. split; [exact Hob |].
      intros i; cbn [reblock blocked]; split; [intros H; right; exact H |intros [H |H]; [exfalso; apply (Hshared i H) |exact H]].
Qed.

Lemma persistent_full_emp active s local : persistent_full_satisfies active s local A.Emp ->
  (forall loc, shared_heap local loc = None) /\ (forall i, buffers local i = []) /\ lock_free local.
Proof. intros [r [Hr Hp]]. change (empty_atom (proj1_sig r)) in Hp; rewrite Hr in Hp; exact Hp. Qed.

Lemma persistent_full_lock active s local i : persistent_full_satisfies active s local (A.Lock (EVal (Z.pos i))) ->
  (forall loc, shared_heap local loc = None) /\ (forall j, buffers local j = []) /\ lock_held active local i.
Proof. intros [r [Hr Hp]]. change (lock_atom active (Z.pos i) (proj1_sig r)) in Hp; rewrite Hr in Hp; exact Hp. Qed.

Theorem persistent_fence_valid active invariant i : persistent_valid active invariant A.Emp
  (Concurrent.Prim (Concurrent.Common Sequential.Fence) (EVal (Z.pos i))) (A.Barrier (EVal (Z.pos i))).
Proof.
  apply persistent_primitive_rule; [discriminate | |].
  - intros s local Hp shared frame whole Henv j Heval Hfault; inversion Hfault.
  - intros s local Hp shared frame whole Henv j t whole' Heval Hstep.
    simpl in Heval; inversion Heval; subst j. inversion Hstep; subst.
    exists local, shared, frame. split; [exact Henv |]. split; [constructor |].
    split; [apply ownership_preserved_refl |]. destruct Hp as [r [Hr Hp]].
    exists r; split; [exact Hr |]. split; [exact Hp |]. right; rewrite Hr; assumption.
Qed.

Theorem persistent_lock_valid active invariant i : persistent_valid active invariant A.Emp
  (Concurrent.Prim Concurrent.Lock (EVal (Z.pos i))) (A.Lock (EVal (Z.pos i))).
Proof.
  apply persistent_primitive_rule; [discriminate | |].
  - intros s local Hp shared frame whole Henv j Heval Hfault; inversion Hfault.
  - intros s local Hp shared frame whole Henv j t whole' Heval Hstep.
    simpl in Heval; inversion Heval; subst j. inversion Hstep; subst.
    destruct (persistent_full_emp _ _ _ Hp) as [Hheap [Hbuffers Hfree]].
    destruct Henv as [Hl Hs Hf Hw Hsep Hlock Hinv].
    assert (Hi : active i) by assumption.
    assert (HglobalFree : lock_free whole) by assumption.
    destruct (framed_free_externals _ _ _ _ _ Hsep HglobalFree) as [Hshared Hframe].
    assert (Hheld : lock_held active (acquire active whole i) i).
    { split; [exact Hi |intros k; reflexivity]. }
    exists (acquire active local i), shared, frame. split.
    + constructor.
      * apply acquire_well_formed, Hl.
      * exact Hs.
      * exact Hf.
      * apply acquire_well_formed, Hw.
      * apply framed_reblock; assumption.
      * right; exists i; exact Hheld.
      * right; exists i; exact Hheld.
    + split; [constructor |]. split.
      * split; intros address Hdom; [left |right]; exact Hdom.
      * exists (exist _ (Generalized (acquire active local i) active)
          (full_memory_valid_with_processor active i _ Hi (acquire_well_formed active local i Hl))).
        split; [reflexivity |]. split; [exact Hheap |]. split; [exact Hbuffers |].
        split; [exact Hi |intros k; reflexivity].
Qed.

(** The original arbitrary-invariant unlock rule is invalid (see the checked
    counterexample). For a pure invariant, explicitly requiring its truth in
    the precondition suffices to restore it at release. *)
Theorem persistent_unlock_pure_valid active invariant i :
  persistent_valid active (A.Pure invariant) (A.And (A.Lock (EVal (Z.pos i))) (A.Pure invariant))
    (Concurrent.Prim Concurrent.Unlock (EVal (Z.pos i))) A.Emp.
Proof.
  apply persistent_primitive_rule; [discriminate | |].
  - intros s local Hp shared frame whole Henv j Heval Hfault; inversion Hfault.
  - intros s local Hp shared frame whole Henv j t whole' Heval Hstep.
    simpl in Heval; inversion Heval; subst j. inversion Hstep; subst.
    destruct Hp as [r [Hr [Hlock Hpure]]].
    assert (HpreLock : persistent_full_satisfies active t local (A.Lock (EVal (Z.pos i)))).
    { exists r; split; assumption. }
    destruct (persistent_full_lock _ _ _ _ HpreLock) as [Hheap [Hbuffers HlocalHeld]].
    destruct Henv as [Hl Hs Hf Hw Hsep Hcomplete Hinv].
    assert (HglobalHeld : lock_held active whole i) by assumption.
    destruct (framed_owned_lock_externals _ _ _ _ _ _ Hsep HlocalHeld HglobalHeld) as [Hshared Hframe].
    exists (release local), shared, frame. split.
    + constructor.
      * apply release_well_formed, Hl.
      * exact Hs.
      * exact Hf.
      * apply release_well_formed, Hw.
      * apply framed_reblock; assumption.
      * left; intros j H; contradiction.
      * left. exists (exist _ (Generalized shared active)
          (full_memory_valid_with_processor active i _ (proj1 HlocalHeld) Hs)).
        split; [reflexivity |exact Hpure].
    + split; [constructor |]. split.
      * split; intros address Hdom; [left |right]; exact Hdom.
      * exists (exist _ (Generalized (release local) active)
          (full_memory_valid_with_processor active i _ (proj1 HlocalHeld) (release_well_formed active local Hl))).
        split; [reflexivity |]. split; [exact Hheap |]. split; [exact Hbuffers |intros j H; contradiction].
Qed.
