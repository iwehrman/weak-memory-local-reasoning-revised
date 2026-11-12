From Stdlib Require Import List Arith ZArith.
From WMLR Require Import Expressions Languages Machine BufferRelations Separation RepairedSeparation FrameDecomposition
  OperationalSemantics ProgramSteps Assertions AssertionSemantics ConcreteAssertions PersistentAssertions
  Safety TemporalSafety RegionalResources InvariantFragment OwnedSafety OwnedResources OwnedInterference OwnedParallel
  OwnedPrimitives OwnedHeapResources.
Import ListNotations.

Lemma writer_points_to_fv address contents x :
  In x (A.fv (writer_points_to address contents)) <->
  In x (expr_fv address) \/ In x (expr_fv contents).
Proof.
  unfold writer_points_to; cbn [A.fv expr_fv].
  set (name := fresh (expr_fv address ++ expr_fv contents)).
  assert (Hfresh : ~ In name (expr_fv address ++ expr_fv contents)) by apply fresh_not_in.
  split.
  - intros H; apply in_remove in H; destruct H as [H Hne].
    repeat rewrite in_app_iff in H; cbn in H; intuition congruence.
  - intros H; apply in_in_remove.
    + intros E; subst x; apply Hfresh; apply in_app_iff; exact H.
    + repeat rewrite in_app_iff; cbn; tauto.
Qed.

Lemma spatial_write_access active s local address annotation value tail actor :
  persistent_models active s local (A.Spatial (A.LeadsTo address annotation value) tail) ->
  eval_expr s annotation = Z.pos actor ->
  exists loc, eval_expr s address = Z.pos loc /\
    local_read (resource_memory active local) actor (Z.pos loc) = Some (eval_expr s value) /\
    (forall other, other <> actor -> ~ buffer_domain (buffers (resource_memory active local) other) loc).
Proof.
  intros (write & retained & Hsp & HW & HP) Eactor.
  change (write_atom active (eval_expr s address) (eval_expr s annotation) (eval_expr s value) (proj1_sig write)) in HW.
  rewrite Eactor in HW; destruct (eval_expr s address) as [|loc|negative] eqn:E; try contradiction.
  pose proof (write_atom_read _ _ _ _ _ HW) as Hread.
  exists loc; split; [reflexivity |]. split.
  - eapply spatial_read_right; [exact (proj1 (spatial_comm _ _ _ Hsp)) |exact Hread].
  - eapply spatial_foreign_empty; [exact (proj1 Hsp) | |].
    + eapply local_read_some_domain; exact Hread.
    + exact (write_atom_foreign_empty _ _ _ _ _ HW).
Qed.

Lemma spatial_cell_access active s local address value tail actor :
  persistent_models active s local (A.Spatial (writer_points_to address value) tail) ->
  exists loc, eval_expr s address = Z.pos loc /\
    local_read (resource_memory active local) actor (Z.pos loc) = Some (eval_expr s value) /\
    (forall other, other <> actor -> ~ buffer_domain (buffers (resource_memory active local) other) loc).
Proof.
  intros (cell & retained & Hsp & HC & HP).
  destruct (writer_points_to_shape _ _ _ _ _ HC) as (loc & writer & E & Hi & Hheap & Hbuffers & Hfree & Hmark).
  assert (Hread : local_read (resource_memory active cell) actor (Z.pos loc) = Some (eval_expr s value)).
  { unfold local_read; rewrite Hbuffers, Hheap; apply heap_update_same. }
  exists loc; split; [exact E |]. split.
  - eapply spatial_read_right; [exact (proj1 (spatial_comm _ _ _ Hsp)) |exact Hread].
  - eapply spatial_foreign_empty; [exact (proj1 Hsp) | |].
    + eapply local_read_some_domain; exact Hread.
    + intros other Hne [w Hw]; rewrite Hbuffers in Hw; contradiction.
Qed.

(** These two proof helpers expose the access obligation, rather than
    presupposing validity. The four rules below discharge it from a spatial
    conjunct, without identifying the two witnesses of strong temporal. *)
Lemma owned_load_from_read active mode invariant pre address value annotation x :
  ~ In x (A.fv invariant) -> ~ In x (A.fv pre) -> ~ In x (expr_fv value) ->
  (forall s local, persistent_models active s local pre -> forall actor,
    eval_expr s annotation = Z.pos actor ->
    exists loc, eval_expr s address = Z.pos loc /\
      local_read (resource_memory active local) actor (Z.pos loc) = Some (eval_expr s value)) ->
  owned_valid active mode invariant pre (C.Prim (C.Common (S.Load x address)) annotation)
    (A.And pre (A.Pure (BEq (EVar x) value))).
Proof.
  intros HJ HPfresh HV Haccess; apply owned_primitive_rule; [discriminate | |].
  - intros s local HP pool frame whole phase Henv actor Eactor Hfault.
    destruct (Haccess _ _ HP _ Eactor) as (loc & Eaddress & Hread).
    inversion Hfault; subst.
    match goal with Hi : active actor |- _ =>
      pose proof (owned_read_preserved _ _ _ _ _ _ _ _ _ _ _ _ Hi Henv Hread) as Hwhole end.
    rewrite <- Eaddress in Hwhole; congruence.
  - intros s local HP pool frame whole phase Henv actor t whole' Eactor Hstep.
    destruct (Haccess _ _ HP _ Eactor) as (loc & Eaddress & Hread).
    inversion Hstep; subst.
    match goal with Hi : active actor |- _ =>
      pose proof (owned_read_preserved _ _ _ _ _ _ _ _ _ _ _ _ Hi Henv Hread) as Hwhole end.
    rewrite <- Eaddress in Hwhole.
    match goal with H : primitive_step _ (C.Common (S.Load x address)) _ _ (State (update s x ?loaded) _) |- _ =>
      assert (Ev : loaded = eval_expr s value) by congruence end.
    subst.
    exists local, pool, phase; split; [apply owned_environment_update_stack; assumption |].
    split; [apply owned_update_identity |]. split.
    + apply (proj1 (future_satisfies_agrees _ _ pre s _ (agrees_update_irrelevant _ _ _ _ HPfresh) local)), HP.
    + change (Z.eqb (update s x (eval_expr s value) x) (eval_expr (update s x (eval_expr s value)) value) = true).
      rewrite update_same, eval_expr_update_irrelevant by exact HV; apply Z.eqb_refl.
Qed.

Lemma owned_store_from_access active mode invariant pre address old value annotation :
  (forall s local, persistent_models active s local pre -> forall actor,
    eval_expr s annotation = Z.pos actor ->
    exists loc, eval_expr s address = Z.pos loc /\
      local_read (resource_memory active local) actor (Z.pos loc) = Some (eval_expr s old) /\
      (forall other, other <> actor -> ~ buffer_domain (buffers (resource_memory active local) other) loc)) ->
  owned_valid active mode invariant pre (C.Prim (C.Common (S.Store address value)) annotation)
    (A.Temporal pre (A.LeadsTo address annotation value)).
Proof.
  intros Haccess; apply owned_primitive_rule; [discriminate | |].
  - intros s local HP pool frame whole phase Henv actor Eactor Hfault.
    destruct (Haccess _ _ HP _ Eactor) as (loc & Eaddress & Hread & Hforeign).
    inversion Hfault; subst.
    match goal with Hi : active actor |- _ =>
      pose proof (owned_read_preserved _ _ _ _ _ _ _ _ _ _ _ _ Hi Henv Hread) as Hwhole end.
    rewrite <- Eaddress in Hwhole; congruence.
  - intros s local HP pool frame whole phase Henv actor t whole' Eactor Hstep.
    destruct (Haccess _ _ HP _ Eactor) as (loc & Eaddress & Hread & Hforeign).
    inversion Hstep; subst.
    match goal with H : primitive_step _ _ _ _ (State _ (enqueue _ _ ?other _)) |- _ =>
      assert (Eloc : other = loc) by congruence; subst other end.
    match goal with Hi : active actor |- _ =>
      exists (owned_enqueue_resource active local actor loc (eval_expr t value) Hi), pool, phase;
      pose proof (owned_enqueue_temporal_post active t local pre actor loc (eval_expr t value) Hi HP Hforeign) as Hpost end.
    split; [eapply owned_environment_enqueue_read; eassumption |].
    split; [eapply owned_enqueue_read_update; exact Hread |].
    destruct Hpost as (a & b & Htm & Ha & Hb); exists a, b; split; [exact Htm |]. split; [exact Ha |].
    change (write_atom active (eval_expr t address) (eval_expr t annotation) (eval_expr t value) (proj1_sig b)).
    rewrite Eaddress, Eactor; exact Hb.
Qed.

Theorem owned_load_valid active mode invariant address value annotation tail x :
  ~ In x (A.fv invariant) ->
  ~ In x (expr_fv address ++ expr_fv annotation ++ expr_fv value ++ A.fv tail) ->
  owned_valid active mode invariant (A.strong_temporal (A.LeadsTo address annotation value) tail)
    (C.Prim (C.Common (S.Load x address)) annotation)
    (A.And (A.strong_temporal (A.LeadsTo address annotation value) tail) (A.Pure (BEq (EVar x) value))).
Proof.
  intros HJ Hfresh; repeat rewrite in_app_iff in Hfresh.
  apply owned_load_from_read; [exact HJ | |tauto |].
  - cbn [A.fv A.strong_temporal]; repeat rewrite in_app_iff; tauto.
  - intros s local [Hsp Htm] actor E.
    destruct (spatial_write_access _ _ _ _ _ _ _ _ Hsp E) as (loc & Ea & Hread & _).
    exists loc; auto.
Qed.

Theorem owned_store_valid active mode invariant address old value annotation tail :
  owned_valid active mode invariant (A.strong_temporal (A.LeadsTo address annotation old) tail)
    (C.Prim (C.Common (S.Store address value)) annotation)
    (A.Temporal (A.strong_temporal (A.LeadsTo address annotation old) tail) (A.LeadsTo address annotation value)).
Proof.
  apply owned_store_from_access with (old := old).
  intros s local [Hsp Htm] actor E; exact (spatial_write_access _ _ _ _ _ _ _ _ Hsp E).
Qed.

(** Explicit additions to the printed schemas: a buffer-free cell can be
    read or written by any processor, without adding completeness marks. *)
Theorem owned_load_any_writer_valid active mode invariant address value annotation tail x :
  ~ In x (A.fv invariant) -> ~ In x (expr_fv address ++ expr_fv value ++ A.fv tail) ->
  owned_valid active mode invariant (A.strong_temporal (writer_points_to address value) tail)
    (C.Prim (C.Common (S.Load x address)) annotation)
    (A.And (A.strong_temporal (writer_points_to address value) tail) (A.Pure (BEq (EVar x) value))).
Proof.
  intros HJ Hfresh; repeat rewrite in_app_iff in Hfresh.
  apply owned_load_from_read; [exact HJ | |tauto |].
  - change (~ In x ((A.fv (writer_points_to address value) ++ A.fv tail) ++
      (A.fv (writer_points_to address value) ++ A.fv tail))).
    repeat rewrite in_app_iff; rewrite writer_points_to_fv; tauto.
  - intros s local [Hsp Htm] actor E.
    destruct (spatial_cell_access _ _ _ _ _ _ actor Hsp) as (loc & Ea & Hread & _); exists loc; auto.
Qed.

Theorem owned_store_any_writer_valid active mode invariant address old value annotation tail :
  owned_valid active mode invariant (A.strong_temporal (writer_points_to address old) tail)
    (C.Prim (C.Common (S.Store address value)) annotation)
    (A.Temporal (A.strong_temporal (writer_points_to address old) tail) (A.LeadsTo address annotation value)).
Proof.
  apply owned_store_from_access with (old := old).
  intros s local [Hsp Htm] actor E; exact (spatial_cell_access _ _ _ _ _ _ actor Hsp).
Qed.

Lemma persistent_spatial_emp_right active s local pre :
  persistent_models active s local pre -> persistent_models active s local (A.Spatial pre A.Emp).
Proof.
  intros HP; exists local, (bare_resource active); split; [apply spatial_empty_right |].
  split; [exact HP |apply bare_resource_models].
Qed.

Lemma persistent_strong_emp_right active s local pre :
  persistent_models active s local pre -> persistent_models active s local (A.strong_temporal pre A.Emp).
Proof. intros HP; split; [apply persistent_spatial_emp_right, HP |apply temporal_emp_right_intro, HP]. Qed.

Theorem owned_load_cell_valid active mode invariant address value annotation x :
  ~ In x (A.fv invariant) -> ~ In x (expr_fv address ++ expr_fv value) ->
  owned_valid active mode invariant (writer_points_to address value)
    (C.Prim (C.Common (S.Load x address)) annotation)
    (A.And (writer_points_to address value) (A.Pure (BEq (EVar x) value))).
Proof.
  intros HJ Hfresh; rewrite in_app_iff in Hfresh.
  apply owned_load_from_read; [exact HJ |rewrite writer_points_to_fv; exact Hfresh |tauto |].
  intros s local HP actor E.
  destruct (spatial_cell_access _ _ _ _ _ _ actor (persistent_spatial_emp_right _ _ _ _ HP))
    as (loc & Ea & Hread & Hforeign); exists loc; auto.
Qed.

Theorem owned_store_cell_valid active mode invariant address old value annotation :
  owned_valid active mode invariant (writer_points_to address old)
    (C.Prim (C.Common (S.Store address value)) annotation)
    (A.Temporal (writer_points_to address old) (A.LeadsTo address annotation value)).
Proof.
  apply owned_store_from_access with (old := old); intros s local HP actor E.
  exact (spatial_cell_access _ _ _ _ _ _ actor (persistent_spatial_emp_right _ _ _ _ HP)).
Qed.
