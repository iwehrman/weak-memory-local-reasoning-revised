From Stdlib Require Import List ZArith.
From WMLR Require Import Expressions Languages Machine BufferRelations Separation FrameDecomposition
  OperationalSemantics Assertions AssertionSemantics PersistentAssertions Safety HeapRules
  OwnershipProtocol OwnershipRules OwnershipHeap PrivateOwnership PrivateRules.
Import ListNotations.

Lemma spatial_heap_lookup a b whole i loc v : memory_spatial a b whole ->
  shared_heap b loc = Some v -> buffer_lookup (buffers b i) loc = None ->
  shared_heap whole loc = Some v /\ buffer_lookup (buffers whole i) loc = None.
Proof.
  intros [[Hd Hk] [Hh [Hb Hblocks]]] Hcell Hnone. split.
  - rewrite Hh; unfold heap_override; rewrite Hcell; reflexivity.
  - apply buffer_lookup_none. intros [w Hw]. apply (interleaves_in _ _ _ _ (Hb i)) in Hw.
    destruct Hw as [Ha |Hb'].
    + apply (Hd loc); [right; exists i, w; exact Ha |left; exists v; exact Hcell].
    + apply (proj1 (buffer_lookup_none _ _) Hnone); exists w; exact Hb'.
Qed.

Lemma private_closed_cell_read active owner invariant s local region frame whole loc v p :
  private_environment active owner invariant Closed s local region frame whole ->
  persistent_full_satisfies active s local (cell_assertion loc v) ->
  local_read whole p (Z.pos loc) = Some v.
Proof.
  intros [[Hl [Hr [Hfree [pool [HJ Hinner]]]]] Hf Hw Hff Houter] Hcell.
  destruct (persistent_cell_shape _ _ _ _ _ Hcell) as [Hheap [Hbuffers Hlfree]].
  assert (Hnone : buffer_lookup (buffers local p) loc = None) by (rewrite Hbuffers; reflexivity).
  destruct (spatial_heap_lookup _ _ _ _ _ _ Hinner Hheap Hnone) as [Hrh Hrb].
  destruct (spatial_heap_lookup _ _ _ _ _ _ Houter Hrh Hrb) as [Hwh Hwb].
  unfold local_read; rewrite Hwb; exact Hwh.
Qed.

Theorem private_closed_load_valid active owner invariant loc v x : ~ In x (A.fv invariant) ->
  private_valid active owner invariant Closed (cell_assertion loc v)
    (Concurrent.Prim (Concurrent.Common (Sequential.Load x (EVal (Z.pos loc)))) (EVal (Z.pos owner)))
    Closed (A.And (cell_assertion loc v) (A.Pure (BEq (EVar x) (EVal v)))).
Proof.
  intros Hfresh. apply private_primitive_rule; [discriminate | |].
  - intros s local region frame whole Henv Hp i Heval Hfault.
    simpl in Heval; inversion Heval; subst i.
    pose proof (private_closed_cell_read _ _ _ _ _ _ _ _ _ _ owner Henv Hp) as Hread.
    inversion Hfault; subst; cbn [eval_expr] in *; congruence.
  - intros s local region frame whole Henv Hp i t whole' Heval Hstep.
    simpl in Heval; inversion Heval; subst i. inversion Hstep; subst.
    pose proof (private_closed_cell_read _ _ _ _ _ _ _ _ _ _ owner Henv Hp) as Hread.
    assert (E : v0 = v) by (cbn [eval_expr] in *; congruence); subst v0.
    destruct Henv as [[Hl [Hr [Hfree [pool [HJ Hinner]]]]] Hf Hw Hff Houter].
    exists local, region, frame. split.
    + constructor; try assumption. split; [exact Hl |]. split; [exact Hr |].
      split; [exact Hfree |]. exists pool; split; [|exact Hinner].
      eapply persistent_full_agrees; [apply agrees_update_irrelevant, Hfresh |exact HJ].
    + split; [constructor |]. split; [intros address H; exact H |].
      assert (Hp' : persistent_full_satisfies active (update s x v) local (cell_assertion loc v)).
      { eapply persistent_full_agrees; [apply agrees_update_irrelevant, cell_assertion_fresh |exact Hp]. }
      destruct Hp' as [r [Er Hp']]. exists r; split; [exact Er |]. split; [exact Hp' |].
      change (Z.eqb (update s x v x) v = true); rewrite update_same; apply Z.eqb_refl.
Qed.

Lemma owned_framed_cell_read active owner s region frame whole loc old p :
  lock_held active region owner -> memory_spatial frame region whole ->
  persistent_full_satisfies active s region (owned_assertion owner (A.Spatial (cell_assertion loc old) p)) ->
  shared_heap region loc = Some old /\ local_read whole owner (Z.pos loc) = Some old.
Proof.
  intros Hheld Hsep Hp.
  destruct (release_returns_invariant _ _ _ _ _ Hheld Hp) as [payload [Hboth [Hfree [Eh [Eb Ek]]]]].
  destruct (full_spatial_elim _ _ _ _ _ Hboth) as [cell [private [Hinner [Hcell HP]]]].
  destruct (persistent_cell_shape _ _ _ _ _ Hcell) as [Hheap [Hbuffers Hcellfree]].
  assert (Hnone : buffer_lookup (buffers cell owner) loc = None) by (rewrite Hbuffers; reflexivity).
  destruct (spatial_heap_lookup _ _ _ owner _ _ (memory_spatial_comm _ _ _ Hinner) Hheap Hnone) as [Hph Hpb].
  assert (Hrh : shared_heap region loc = Some old) by (rewrite <- Eh in Hph; exact Hph).
  assert (Hrb : buffer_lookup (buffers region owner) loc = None).
  { change (buffer_lookup (buffers (release region) owner) loc = None); rewrite Eb; exact Hpb. }
  split; [exact Hrh |]. destruct (spatial_heap_lookup _ _ _ _ _ _ Hsep Hrh Hrb) as [Hwh Hwb].
  unfold local_read; rewrite Hwb; exact Hwh.
Qed.

Lemma framed_cell_store_post active owner s payload loc old v p : active owner ->
  persistent_full_satisfies active s payload (A.Spatial (cell_assertion loc old) p) ->
  persistent_full_satisfies active s (enqueue payload owner loc v) (A.Spatial (buffered_cell owner loc old v) p).
Proof.
  intros Hi Hboth. destruct (full_spatial_elim _ _ _ _ _ Hboth) as [cell [private [Hsep [Hcell HP]]]].
  eapply full_spatial_intro with (a := enqueue cell owner loc v) (b := private).
  - apply memory_spatial_comm, spatial_enqueue_right; [apply memory_spatial_comm, Hsep |].
    destruct (persistent_cell_shape _ _ _ _ _ Hcell) as [Hheap _]. left; exists old; exact Hheap.
  - apply cell_store_post; assumption.
  - exact HP.
Qed.

Lemma framed_cell_drained active owner s payload loc old v p :
  persistent_full_satisfies active s payload (A.Spatial (buffered_cell owner loc old v) p) ->
  buffers payload owner = [] -> persistent_full_satisfies active s payload (A.Spatial (cell_assertion loc v) p).
Proof.
  intros Hboth Hempty. destruct (full_spatial_elim _ _ _ _ _ Hboth) as [cell [private [Hsep [Hcell HP]]]].
  eapply full_spatial_intro; [exact Hsep | |exact HP]. eapply buffered_cell_drained; [exact Hcell |].
  exact (proj1 (spatial_empty_buffer_parts _ _ _ _ Hsep Hempty)).
Qed.

Theorem protocol_store_framed_cell_valid active owner invariant loc old v p :
  protocol_valid active owner invariant Open (owned_assertion owner (A.Spatial (cell_assertion loc old) p))
    (Concurrent.Prim (Concurrent.Common (Sequential.Store (EVal (Z.pos loc)) (EVal v))) (EVal (Z.pos owner)))
    Open (owned_assertion owner (A.Spatial (buffered_cell owner loc old v) p)).
Proof.
  apply protocol_primitive_rule; [discriminate | |].
  - intros s region frame whole Henv Hp i Heval Hfault.
    simpl in Heval; inversion Heval; subst i.
    destruct (protocol_region_ok _ _ _ _ _ _ _ _ Henv) as [Hwf Hheld].
    pose proof (proj2 (owned_framed_cell_read _ _ _ _ _ _ _ _ _ Hheld
      (protocol_separation _ _ _ _ _ _ _ _ Henv) Hp)) as Hread.
    inversion Hfault; subst; cbn [eval_expr] in *; congruence.
  - intros s region frame whole [Hr Hf Hw Hframefree Hsep] Hp i t whole' Heval Hstep.
    simpl in Heval; inversion Heval; subst i. inversion Hstep; subst. cbn [eval_expr] in *.
    match goal with H : Z.pos loc = Z.pos ?other |- _ => inversion H; subst other end.
    destruct Hr as [Hwf Hheld].
    pose proof (proj1 (owned_framed_cell_read _ _ _ _ _ _ _ _ _ Hheld Hsep Hp)) as Hrheap.
    destruct (release_returns_invariant _ _ _ _ _ Hheld Hp) as [payload [Hboth [Hfree Heq]]].
    pose proof (framed_cell_store_post active owner t payload loc old v p (proj1 Hheld) Hboth) as Hpost.
    assert (Enew : memory_equiv (enqueue region owner loc v) (acquire active (enqueue payload owner loc v) owner)).
    { pose proof (memory_equiv_enqueue _ _ owner loc v Heq) as [Eh [Eb Ek]].
      split; [exact Eh |]. split; [exact Eb |exact (proj2 Hheld)]. }
    exists (acquire active (enqueue payload owner loc v) owner), frame. split.
    + constructor; try assumption.
      * split.
        -- apply acquire_well_formed. exact (proj1 (persistent_full_well_formed _ _ _ _ Hpost)).
        -- split; [exact (proj1 Hheld) |intros j; reflexivity].
      * apply update_buffers_well_formed; [exact (proj1 Hheld) |exact Hw].
      * eapply protocol_spatial_equiv_right; [exact Enew |].
        apply spatial_enqueue_right; [exact Hsep |left; exists old; exact Hrheap].
    + split; [constructor |]. split.
      * intros address Hdom. apply (memory_equiv_domain _ _ Enew) in Hdom.
        apply (enqueue_domain_subset region owner loc v ltac:(left; exists old; exact Hrheap) address Hdom).
      * apply acquire_exposes_invariant; [exact (proj1 Hheld) |exact Hfree |exact Hpost].
Qed.

Theorem protocol_fence_framed_cell_valid active owner invariant loc old v p :
  protocol_valid active owner invariant Open (owned_assertion owner (A.Spatial (buffered_cell owner loc old v) p))
    (Concurrent.Prim (Concurrent.Common Sequential.Fence) (EVal (Z.pos owner)))
    Open (owned_assertion owner (A.Spatial (cell_assertion loc v) p)).
Proof.
  apply protocol_primitive_rule; [discriminate | |].
  - intros s region frame whole Henv Hp i Heval Hfault; inversion Hfault.
  - intros s region frame whole [Hr Hf Hw Hframefree Hsep] Hp i t whole' Heval Hstep.
    simpl in Heval; inversion Heval; subst i. inversion Hstep; subst.
    destruct Hr as [Hwf Hheld].
    destruct (release_returns_invariant _ _ _ _ _ Hheld Hp) as [payload [Hboth [Hfree Heq]]].
    assert (Hempty : buffers region owner = []) by (eapply (proj2 (spatial_empty_buffer_parts _ _ _ _ Hsep ltac:(eassumption)))).
    assert (Hpayloadempty : buffers payload owner = []) by (rewrite <- (proj1 (proj2 Heq) owner); exact Hempty).
    pose proof (framed_cell_drained _ _ _ _ _ _ _ _ Hboth Hpayloadempty) as Hpost.
    pose proof (region_reacquire_equiv _ _ _ _ Hheld Heq) as Enew.
    exists (acquire active payload owner), frame. split.
    + constructor; try assumption.
      * split.
        -- apply acquire_well_formed. exact (proj1 (persistent_full_well_formed _ _ _ _ Hpost)).
        -- split; [exact (proj1 Hheld) |intros j; reflexivity].
      * eapply protocol_spatial_equiv_right; eassumption.
    + split; [constructor |]. split.
      * intros address Hdom; apply (memory_equiv_domain _ _ Enew), Hdom.
      * apply acquire_exposes_invariant; [exact (proj1 Hheld) |exact Hfree |exact Hpost].
Qed.

Theorem private_store_cell_valid active owner invariant loc old v p :
  private_valid active owner invariant Open (owned_assertion owner (A.Spatial (cell_assertion loc old) p))
    (Concurrent.Prim (Concurrent.Common (Sequential.Store (EVal (Z.pos loc)) (EVal v))) (EVal (Z.pos owner)))
    Open (owned_assertion owner (A.Spatial (buffered_cell owner loc old v) p)).
Proof. apply private_lift_open_primitive; [discriminate |apply protocol_store_framed_cell_valid]. Qed.

Theorem private_fence_cell_valid active owner invariant loc old v p :
  private_valid active owner invariant Open (owned_assertion owner (A.Spatial (buffered_cell owner loc old v) p))
    (Concurrent.Prim (Concurrent.Common Sequential.Fence) (EVal (Z.pos owner)))
    Open (owned_assertion owner (A.Spatial (cell_assertion loc v) p)).
Proof. apply private_lift_open_primitive; [discriminate |apply protocol_fence_framed_cell_valid]. Qed.

Theorem private_release_buffered_cell_valid active owner loc old v p :
  private_valid active owner (cell_assertion loc v) Open
    (owned_assertion owner (A.Spatial (buffered_cell owner loc old v) p))
    (Concurrent.Prim Concurrent.Unlock (EVal (Z.pos owner))) Closed p.
Proof.
  apply private_primitive_rule; [discriminate | |].
  - intros s local region frame whole Henv Hp i Heval Hfault; inversion Hfault.
  - intros s local region frame whole [Hr Hf Hw Hframefree Hsep] Hp i t whole' Heval Hstep.
    simpl in Heval; inversion Heval; subst i. inversion Hstep; subst.
    destruct Hr as [Hl [Hr [-> Hheld]]].
    destruct (release_returns_invariant _ _ _ _ _ Hheld Hp) as [payload [Hboth [Hfree Heq]]].
    assert (Hempty : buffers region owner = []) by (eapply (proj2 (spatial_empty_buffer_parts _ _ _ _ Hsep ltac:(eassumption)))).
    assert (Hpayloadempty : buffers payload owner = []) by (rewrite <- (proj1 (proj2 Heq) owner); exact Hempty).
    pose proof (framed_cell_drained _ _ _ _ _ _ _ _ Hboth Hpayloadempty) as Hpost.
    destruct (full_spatial_elim _ _ _ _ _ Hpost) as [pool [private [Hinner [HJ HQ]]]].
    exists private, payload, frame. split.
    + constructor; try assumption.
      * split; [exact (proj1 (persistent_full_well_formed _ _ _ _ HQ)) |].
        split; [exact (proj1 (persistent_full_well_formed _ _ _ _ Hpost)) |].
        split; [exact Hfree |exists pool; auto].
      * apply release_well_formed, Hw.
      * eapply protocol_spatial_equiv_right; [exact Heq |]. apply protocol_spatial_reblock; assumption.
    + split; [constructor |]. split; [|exact HQ].
      intros address Hdom; apply (memory_equiv_domain _ _ Heq), Hdom.
Qed.
