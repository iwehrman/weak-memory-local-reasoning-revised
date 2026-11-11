From Stdlib Require Import List ZArith.
From WMLR Require Import Expressions Languages Machine BufferRelations Separation RepairedSeparation
  RepairedFlushing FrameDecomposition OperationalSemantics Assertions AssertionSemantics ConcreteAssertions
  RepairedAssertions PersistentAssertions Safety RepairedSafety HeapRules LockRules
  OwnershipProtocol OwnershipRules.
Import ListNotations.

Definition owned_assertion owner p := A.Spatial (A.Lock (EVal (Z.pos owner))) p.
Definition buffered_cell owner loc old v :=
  A.Temporal (cell_assertion loc old) (A.LeadsTo (EVal (Z.pos loc)) (EVal (Z.pos owner)) (EVal v)).

Lemma protocol_as_repaired_frame active frame region whole :
  memory_spatial frame region whole -> repaired_framed active empty_memory frame region whole.
Proof.
  intros H. exists whole. split; [apply memory_spatial_in_repaired, H |].
  exact (proj1 (spatial_empty_left (Generalized whole active))).
Qed.

Lemma region_reacquire_equiv active owner region pool :
  lock_held active region owner -> memory_equiv (release region) pool ->
  memory_equiv region (acquire active pool owner).
Proof.
  intros Hheld [Hh [Hb Hk]]. split; [exact Hh |]. split; [exact Hb |exact (proj2 Hheld)].
Qed.

Lemma memory_equiv_domain a b : memory_equiv a b -> forall loc, memory_domain a loc <-> memory_domain b loc.
Proof.
  intros [Hh [Hb Hk]] loc. unfold memory_domain, heap_domain, buffer_domain.
  rewrite Hh. setoid_rewrite Hb. reflexivity.
Qed.

Lemma memory_equiv_enqueue a b owner loc v : memory_equiv a b ->
  memory_equiv (enqueue a owner loc v) (enqueue b owner loc v).
Proof.
  intros [Hh [Hb Hk]]. split; [exact Hh |]. split; [|exact Hk].
  intros i; cbn [enqueue buffers]; unfold buffer_update.
  destruct (Pos.eq_dec i owner); rewrite Hb; reflexivity.
Qed.

Theorem protocol_store_cell_valid active owner invariant loc old v :
  protocol_valid active owner invariant Open (owned_assertion owner (cell_assertion loc old))
    (Concurrent.Prim (Concurrent.Common (Sequential.Store (EVal (Z.pos loc)) (EVal v))) (EVal (Z.pos owner)))
    Open (owned_assertion owner (buffered_cell owner loc old v)).
Proof.
  apply protocol_primitive_rule; [discriminate | |].
  - intros s region frame whole Henv Hp i Heval Hfault.
    simpl in Heval; inversion Heval; subst i.
    destruct (protocol_region_ok _ _ _ _ _ _ _ _ Henv) as [Hwf Hheld].
    destruct (release_returns_invariant _ _ _ _ _ Hheld Hp) as [pool [Hcell [Hfree [Eh [Eb Ek]]]]].
    destruct (persistent_cell_shape _ _ _ _ _ Hcell) as [Hheap [Hbuffers Hpoolfree]].
    assert (Hrheap : shared_heap region loc = Some old) by (rewrite <- Eh in Hheap; exact Hheap).
    assert (Hrbuffer : buffers region owner = []).
    { transitivity (buffers pool owner); [exact (Eb owner) |apply Hbuffers]. }
    inversion Hfault; subst.
    pose proof (framed_cell_read active empty_memory frame region whole owner loc old (proj1 Hheld)
      (protocol_as_repaired_frame _ _ _ _ (protocol_separation _ _ _ _ _ _ _ _ Henv)) Hrheap Hrbuffer).
    cbn [eval_expr] in *; congruence.
  - intros s region frame whole [Hr Hf Hw Hframefree Hsep] Hp i t whole' Heval Hstep.
    simpl in Heval; inversion Heval; subst i. inversion Hstep; subst.
    cbn [eval_expr] in *.
    match goal with H : Z.pos loc = Z.pos ?other |- _ => inversion H; subst other end.
    destruct Hr as [Hwf Hheld].
    destruct (release_returns_invariant _ _ _ _ _ Hheld Hp) as [pool [Hcell [Hfree Heq]]].
    destruct (persistent_cell_shape _ _ _ _ _ Hcell) as [Hheap [Hbuffers Hpoolfree]].
    assert (Hrheap : shared_heap region loc = Some old) by (rewrite <- (proj1 Heq) in Hheap; exact Hheap).
    assert (Hpost : persistent_full_satisfies active t (enqueue pool owner loc v) (buffered_cell owner loc old v)).
    { apply cell_store_post; [exact (proj1 Hheld) |exact Hcell]. }
    assert (Hnewfree : lock_free (enqueue pool owner loc v)) by exact Hfree.
    assert (Hnewwf : memory_well_formed active (enqueue pool owner loc v)).
    { exact (proj1 (persistent_full_well_formed _ _ _ _ Hpost)). }
    assert (Enew : memory_equiv (enqueue region owner loc v) (acquire active (enqueue pool owner loc v) owner)).
    { pose proof (memory_equiv_enqueue _ _ owner loc v Heq) as E.
      destruct E as [Eh [Eb Ek]]. split; [exact Eh |]. split; [exact Eb |exact (proj2 Hheld)]. }
    exists (acquire active (enqueue pool owner loc v) owner), frame. split.
    + constructor; try assumption.
      * split; [apply acquire_well_formed, Hnewwf |]. split; [exact (proj1 Hheld) |intros j; reflexivity].
      * apply update_buffers_well_formed; [exact (proj1 Hheld) |exact Hw].
      * eapply protocol_spatial_equiv_right; [exact Enew |].
        apply spatial_enqueue_right; [exact Hsep |left; exists old; exact Hrheap].
    + split; [constructor |]. split.
      * intros address Hdom. apply (memory_equiv_domain _ _ Enew) in Hdom.
        apply (enqueue_domain_subset region owner loc v ltac:(left; exists old; exact Hrheap) address Hdom).
      * apply acquire_exposes_invariant; [exact (proj1 Hheld) |exact Hnewfree |exact Hpost].
Qed.

Lemma persistent_cell_domain_cases active s (r : resource active) loc v :
  persistent_models active s r (cell_assertion loc v) -> forall i, ~ active i \/ active i.
Proof.
  intros [a [b [_ [_ Hbar]]]] i.
  change (forall z, barrier_atom active z (proj1_sig b)) in Hbar.
  destruct (proj2 (Hbar (Z.pos i))) as [Hno |Hyes]; [left; exact Hno |].
  right. exact (proj1 (proj2 (proj2_sig b)) i Hyes).
Qed.

Lemma persistent_cell_from_shape active owner s m loc v :
  (forall i, ~ active i \/ active i) -> active owner ->
  (forall address, shared_heap m address = heap_update empty_heap loc v address) ->
  (forall i, buffers m i = []) -> lock_free m -> persistent_full_satisfies active s m (cell_assertion loc v).
Proof.
  intros Hcases Hi Hheap Hbuffers Hfree.
  assert (Hwf : memory_well_formed active m).
  { split; [intros i H; exfalso; apply (Hfree i H) |intros; apply Hbuffers]. }
  pose (r := exist _ (Generalized m active) (full_memory_valid_with_processor active owner m Hi Hwf)).
  assert (Hempty : generalized_well_formed active (Generalized empty_memory active)).
  { split; [exact (proj1 (empty_generalized_well_formed active)) |]. split; [auto |intros; reflexivity]. }
  pose (bar := exist _ (Generalized empty_memory active) Hempty).
  exists r; split; [reflexivity |].
  apply (proj2 (persistent_wand_free_unchanged _ _ _ _ (cell_assertion_wand_free loc v))).
  change (exists a b : resource active,
    repaired_temporal active (proj1_sig a) (proj1_sig b) (proj1_sig r) /\
    (exists i, write_atom active (Z.pos loc) i v (proj1_sig a)) /\
    (forall i, barrier_atom active i (proj1_sig b))).
  exists r, bar. split.
  - split.
    + apply spatial_compatible_stable. exact (proj1 (proj1 (spatial_empty_right (Generalized m active)))).
    + split.
      * exact (proj1 (temporal_empty_right active (Generalized m active))).
      * split; [intros; apply Hbuffers |intros i; simpl; tauto].
  - split.
    + exists (Z.pos owner). split; [exact Hi |]. right. split; [exact Hheap |].
      split; [exact Hbuffers |]. split; [exact Hfree |exact Hi].
    + intros i. split.
      * split; [intros; reflexivity |]. split; [intros; reflexivity |intros j H; exact H].
      * destruct i; simpl; auto.
Qed.

Lemma persistent_cell_resource_shape active s (r : resource active) loc v :
  persistent_models active s r (cell_assertion loc v) ->
  (forall address, shared_heap (underlying (proj1_sig r)) address = heap_update empty_heap loc v address) /\
  (forall i, buffers (underlying (proj1_sig r)) i = []) /\ lock_free (underlying (proj1_sig r)).
Proof.
  intros Hp. apply (proj1 (persistent_wand_free_unchanged _ _ _ _ (cell_assertion_wand_free loc v))) in Hp.
  destruct (repaired_points_to_requires_flushed _ _ _ _ _ Hp) as
    [address [owner [Haddress [Howner [[Hheap [Hbuffers [Hfree Hcomplete]]] HcompleteAll]]]]].
  simpl in Haddress; inversion Haddress; subst address. repeat split; assumption.
Qed.

(** A fence obtains the new points-to assertion only once the issuing
    processor's buffer is empty. Pending stores are not silently erased. *)
Lemma buffered_cell_drained active owner s pool loc old v :
  persistent_full_satisfies active s pool (buffered_cell owner loc old v) ->
  buffers pool owner = [] -> persistent_full_satisfies active s pool (cell_assertion loc v).
Proof.
  intros [r [Hr [past [future [Hsep [Hpast Hwrite]]]]]] Hempty.
  pose proof (persistent_cell_domain_cases _ _ _ _ _ Hpast) as Hcases.
  destruct (persistent_cell_resource_shape _ _ _ _ _ Hpast) as [Hph [Hpb Hpk]].
  change (repaired_temporal active (proj1_sig past) (proj1_sig future) (proj1_sig r)) in Hsep.
  rewrite Hr in Hsep. destruct Hsep as [Hstable [[Hcompat [Hh [Hb Hk]]] [Hcomplete Hmarks]]].
  change (write_atom active (Z.pos loc) (Z.pos owner) v (proj1_sig future)) in Hwrite.
  destruct Hwrite as [Hi [[Hfh [Hfb Hfk]] |[Hfh [Hfb [Hfk Hfc]]]]].
  - specialize (Hb owner). cbn [underlying] in Hb. rewrite Hempty, Hpb, Hfb, buffer_update_same in Hb.
    discriminate.
  - apply (persistent_cell_from_shape active owner); [exact Hcases |exact Hi | | |].
    + intros address; rewrite Hh; unfold heap_override; rewrite Hfh, Hph.
      unfold heap_update; destruct (Pos.eq_dec address loc); reflexivity.
    + intros i; rewrite Hb, Hpb, Hfb; reflexivity.
    + intros i H; apply Hk in H; destruct H; [apply (Hpk i) |apply (Hfk i)]; assumption.
Qed.

Theorem protocol_fence_cell_valid active owner invariant loc old v :
  protocol_valid active owner invariant Open (owned_assertion owner (buffered_cell owner loc old v))
    (Concurrent.Prim (Concurrent.Common Sequential.Fence) (EVal (Z.pos owner)))
    Open (owned_assertion owner (cell_assertion loc v)).
Proof.
  apply protocol_primitive_rule; [discriminate | |].
  - intros s region frame whole Henv Hp i Heval Hfault; inversion Hfault.
  - intros s region frame whole [Hr Hf Hw Hframefree Hsep] Hp i t whole' Heval Hstep.
    simpl in Heval; inversion Heval; subst i. inversion Hstep; subst.
    destruct Hr as [Hwf Hheld].
    destruct (release_returns_invariant _ _ _ _ _ Hheld Hp) as [pool [Hbuffered [Hpoolfree Heq]]].
    assert (Hregionempty : buffers region owner = []).
    { pose proof (proj1 (proj2 (proj2 Hsep)) owner) as Hb.
      match goal with H : buffers whole' owner = [] |- _ => rewrite H in Hb end.
      inversion Hb; reflexivity. }
    assert (Hpoolempty : buffers pool owner = []).
    { rewrite <- (proj1 (proj2 Heq) owner); exact Hregionempty. }
    pose proof (buffered_cell_drained _ _ _ _ _ _ _ Hbuffered Hpoolempty) as Hcell.
    pose proof (region_reacquire_equiv _ _ _ _ Hheld Heq) as Enew.
    exists (acquire active pool owner), frame. split.
    + constructor; try assumption.
      * split.
        -- apply acquire_well_formed. exact (proj1 (persistent_full_well_formed _ _ _ _ Hcell)).
        -- split; [exact (proj1 Hheld) |intros j; reflexivity].
      * eapply protocol_spatial_equiv_right; eassumption.
    + split; [constructor |]. split.
      * intros address Hdom; apply (memory_equiv_domain _ _ Enew), Hdom.
      * apply acquire_exposes_invariant; [exact (proj1 Hheld) |exact Hpoolfree |exact Hcell].
Qed.

(** Release itself waits for an empty issuing buffer. For a single-cell
    invariant this discharges restoration without an extra explicit fence. *)
Theorem protocol_release_buffered_cell_valid active owner loc old v :
  protocol_valid active owner (cell_assertion loc v) Open
    (owned_assertion owner (buffered_cell owner loc old v))
    (Concurrent.Prim Concurrent.Unlock (EVal (Z.pos owner))) Closed A.Emp.
Proof.
  apply protocol_primitive_rule; [discriminate | |].
  - intros s region frame whole Henv Hp i Heval Hfault; inversion Hfault.
  - intros s region frame whole [Hr Hf Hw Hframefree Hsep] Hp i t whole' Heval Hstep.
    simpl in Heval; inversion Heval; subst i. inversion Hstep; subst.
    destruct Hr as [Hwf Hheld].
    destruct (release_returns_invariant _ _ _ _ _ Hheld Hp) as [pool [Hbuffered [Hpoolfree Heq]]].
    assert (Hregionempty : buffers region owner = []).
    { pose proof (proj1 (proj2 (proj2 Hsep)) owner) as Hb.
      match goal with H : buffers whole owner = [] |- _ => rewrite H in Hb end.
      inversion Hb; reflexivity. }
    assert (Hpoolempty : buffers pool owner = []).
    { rewrite <- (proj1 (proj2 Heq) owner); exact Hregionempty. }
    pose proof (buffered_cell_drained _ _ _ _ _ _ _ Hbuffered Hpoolempty) as Hcell.
    exists pool, frame. split.
    + constructor; try assumption.
      * split; [exact (proj1 (persistent_full_well_formed _ _ _ _ Hcell)) |auto].
      * apply release_well_formed, Hw.
      * eapply protocol_spatial_equiv_right; [exact Heq |]. apply protocol_spatial_reblock; assumption.
    + split; [constructor |]. split.
      * intros address Hdom; apply (memory_equiv_domain _ _ Heq), Hdom.
      * apply protocol_empty_satisfies.
Qed.
