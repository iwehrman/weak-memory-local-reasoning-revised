From Stdlib Require Import List ZArith Bool.
From WMLR Require Import Expressions Languages Machine BufferRelations Separation RepairedSeparation
  GeneralizedFlushing FrameDecomposition OperationalSemantics ProgramSteps Assertions AssertionSemantics
  ConcreteAssertions PersistentAssertions AssertionSubstitution Safety PrivateOwnership HeapRules
  TemporalSafety TemporalFence InvariantFragment OwnedSafety OwnedResources OwnedHeapResources OwnedHeap
  BufferedPoolCandidate BufferedPoolResources BufferedPoolRules.
Import ListNotations.

(** Direct primitive obligations for the approved frameless premise. *)
Lemma buffered_primitive_premise active J P p annotation Q : buffered_atomic_primitive p ->
  (forall s local, persistent_models active s local P -> forall pool whole,
    persistent_full_satisfies active s pool J -> memory_spatial pool (resource_memory active local) whole ->
    lock_free whole -> forall actor, eval_expr s annotation = Z.pos actor ->
    ~ primitive_abort active (C.Common p) actor (State s whole)) ->
  (forall s local, persistent_models active s local P -> forall pool whole,
    persistent_full_satisfies active s pool J -> memory_spatial pool (resource_memory active local) whole ->
    lock_free whole -> forall actor t whole', eval_expr s annotation = Z.pos actor ->
    primitive_step active (C.Common p) actor (State s whole) (State t whole') ->
    exists local' pool', memory_spatial pool' (resource_memory active local') whole' /\
      lock_free whole' /\ persistent_full_satisfies active t pool' J /\ persistent_models active t local' Q /\
      buffered_update active (primitive_action (C.Common p) actor) local pool local' pool') ->
  buffered_atomic_premise active J P p annotation Q.
Proof.
  intros Hnot Hbad Hstep; split; [exact Hnot |]. intros s local HP pool whole HJ Hsp Hfree; split.
  - intros H; inversion H; subst; eapply Hbad; eassumption.
  - intros action next t whole' H; inversion H; subst; eapply Hstep; eassumption.
Qed.

Theorem buffered_assignment_premise active J Q x rhs annotation : ~ In x (A.fv J) ->
  buffered_atomic_premise active J (assertion_subst x rhs Q) (S.Assign x rhs) annotation Q.
Proof.
  intros Hfresh; apply buffered_primitive_premise; [exact I | |].
  - intros s local HP pool whole HJ Hsp Hfree actor E Hbad; inversion Hbad.
  - intros s local HP pool whole HJ Hsp Hfree actor t whole' E Hstep; inversion Hstep; subst.
    exists local,pool; split; [exact Hsp |]. split; [exact Hfree |]. split.
    + eapply persistent_full_agrees; [apply agrees_update_irrelevant,Hfresh |exact HJ].
    + split; [apply (proj1 (persistent_assertion_subst _ _ _ _ _ _)),HP |apply buffered_update_identity].
Qed.
Theorem buffered_assignment_valid active J Q x rhs annotation : buffered_assignment_rule active J Q x rhs annotation.
Proof. intros Hfragment Hfresh; apply buffered_atomic_valid; [exact Hfragment |apply buffered_assignment_premise,Hfresh]. Qed.

Theorem buffered_assume_premise active J P condition annotation :
  buffered_atomic_premise active J (A.Or (A.Pure (BNot condition)) P) (S.Assume condition) annotation P.
Proof.
  apply buffered_primitive_premise; [exact I | |].
  - intros s local HP pool whole HJ Hsp Hfree actor E Hbad; inversion Hbad.
  - intros s local HP pool whole HJ Hsp Hfree actor t whole' E Hstep; inversion Hstep; subst.
    exists local,pool; split; [exact Hsp |]. split; [exact Hfree |]. split; [exact HJ |].
    split; [|apply buffered_update_identity]. destruct HP as [Hb |HP]; [|exact HP].
    change (negb (eval_bexpr t condition) = true) in Hb.
    match goal with H : eval_bexpr t condition = true |- _ => rewrite H in Hb; discriminate end.
Qed.
Theorem buffered_assume_valid active J P condition annotation : buffered_assume_rule active J P condition annotation.
Proof. intros H; apply buffered_atomic_valid; [exact H |apply buffered_assume_premise]. Qed.

Theorem buffered_assert_premise active J P condition annotation :
  buffered_atomic_premise active J (A.And (A.Pure condition) P) (S.Assert condition) annotation P.
Proof.
  apply buffered_primitive_premise; [exact I | |].
  - intros s local [Hb HP] pool whole HJ Hsp Hfree actor E Hbad; inversion Hbad; subst.
    change (eval_bexpr s condition = true) in Hb; congruence.
  - intros s local [Hb HP] pool whole HJ Hsp Hfree actor t whole' E Hstep; inversion Hstep; subst.
    exists local,pool; split; [exact Hsp |]. split; [exact Hfree |]. split; [exact HJ |].
    split; [exact HP |apply buffered_update_identity].
Qed.
Theorem buffered_assert_valid active J P condition annotation : buffered_assert_rule active J P condition annotation.
Proof. intros H; apply buffered_atomic_valid; [exact H |apply buffered_assert_premise]. Qed.

Theorem buffered_private_fence_premise active J annotation :
  buffered_atomic_premise active J A.Emp S.Fence annotation (A.Barrier annotation).
Proof.
  apply buffered_primitive_premise; [exact I | |].
  - intros s local HP pool whole HJ Hsp Hfree actor E Hbad; inversion Hbad.
  - intros s local HP pool whole HJ Hsp Hfree actor t whole' E Hstep; inversion Hstep; subst.
    match goal with Hi : active actor |- _ => exists (mark_processor active local actor Hi),pool end.
    split; [exact Hsp |]. split; [exact Hfree |]. split; [exact HJ |]. split.
    + match goal with Hi : active actor |- _ =>
        change (barrier_atom active (eval_expr t annotation) (proj1_sig (mark_processor active local actor Hi))) end.
      rewrite E; eapply marked_emp_barrier; exact HP.
    + constructor; [intros; assumption |intros i [Hi |Hi]; [left |right]; exact Hi].
Qed.
Theorem buffered_private_fence_valid active J annotation : buffered_private_fence_rule active J annotation.
Proof. intros H; apply buffered_atomic_valid; [exact H |apply buffered_private_fence_premise]. Qed.

Lemma buffered_cell_read active s local address value actor :
  persistent_models active s local (writer_points_to address value) ->
  exists loc, eval_expr s address = Z.pos loc /\
    local_read (resource_memory active local) actor (Z.pos loc) = Some (eval_expr s value) /\
    (forall other, other <> actor -> ~ buffer_domain (buffers (resource_memory active local) other) loc).
Proof.
  intros HP; eapply spatial_cell_access; eapply persistent_spatial_emp_right; exact HP.
Qed.

Theorem buffered_private_load_premise active J address value annotation x :
  ~ In x (A.fv J) -> ~ In x (expr_fv address ++ expr_fv value) ->
  buffered_atomic_premise active J (writer_points_to address value) (S.Load x address) annotation
    (A.And (writer_points_to address value) (A.Pure (BEq (EVar x) value))).
Proof.
  intros HJfresh Hfresh.
  assert (HPfresh : ~ In x (A.fv (writer_points_to address value))).
  { intros H; apply Hfresh,in_app_iff,writer_points_to_fv,H. }
  assert (HV : ~ In x (expr_fv value)) by (intros H; apply Hfresh,in_or_app; auto).
  apply buffered_primitive_premise; [exact I | |].
  - intros s local HP pool whole HJ Hsp Hfree actor E Hbad.
    destruct (buffered_cell_read _ _ _ _ _ actor HP) as (loc & Eaddress & Hread & _).
    pose proof (spatial_read_right _ _ _ _ _ _ Hsp Hread) as Hwhole.
    inversion Hbad; subst; rewrite <- Eaddress in Hwhole; congruence.
  - intros s local HP pool whole HJ Hsp Hfree actor t whole' E Hstep.
    destruct (buffered_cell_read _ _ _ _ _ actor HP) as (loc & Eaddress & Hread & _).
    pose proof (spatial_read_right _ _ _ _ _ _ Hsp Hread) as Hwhole.
    inversion Hstep; subst; rewrite <- Eaddress in Hwhole.
    match goal with H : primitive_step _ _ _ _ (State (update s x ?loaded) _) |- _ =>
      assert (Ev : loaded = eval_expr s value) by congruence; subst loaded end.
    exists local,pool; split; [exact Hsp |]. split; [exact Hfree |]. split.
    + eapply persistent_full_agrees; [apply agrees_update_irrelevant,HJfresh |exact HJ].
    + split; [|apply buffered_update_identity]. split.
      * apply (proj1 (future_satisfies_agrees _ _ _ _ _ (agrees_update_irrelevant _ _ _ _ HPfresh) local)),HP.
      * change (Z.eqb (update s x (eval_expr s value) x) (eval_expr (update s x (eval_expr s value)) value) = true).
        rewrite update_same,eval_expr_update_irrelevant by exact HV; apply Z.eqb_refl.
Qed.
Theorem buffered_private_load_valid active J address value annotation x : buffered_private_load_rule active J address value annotation x.
Proof. intros H HJ HV; apply buffered_atomic_valid; [exact H |apply buffered_private_load_premise; assumption]. Qed.

Theorem buffered_private_store_premise active J address old value annotation :
  buffered_atomic_premise active J (writer_points_to address old) (S.Store address value) annotation
    (A.Temporal (writer_points_to address old) (A.LeadsTo address annotation value)).
Proof.
  apply buffered_primitive_premise; [exact I | |].
  - intros s local HP pool whole HJ Hsp Hfree actor E Hbad.
    destruct (buffered_cell_read _ _ _ _ _ actor HP) as (loc & Eaddress & Hread & _).
    pose proof (spatial_read_right _ _ _ _ _ _ Hsp Hread) as Hwhole.
    inversion Hbad; subst; rewrite <- Eaddress in Hwhole; congruence.
  - intros s local HP pool whole HJ Hsp Hfree actor t whole' E Hstep.
    destruct (buffered_cell_read _ _ _ _ _ actor HP) as (loc & Eaddress & Hread & Hforeign).
    inversion Hstep; subst.
    match goal with H : primitive_step _ _ _ _ (State _ (enqueue _ _ ?other _)) |- _ =>
      assert (Eloc : other = loc) by congruence; subst other end.
    match goal with Hi : active actor |- _ =>
      exists (owned_enqueue_resource active local actor loc (eval_expr t value) Hi),pool;
      pose proof (owned_enqueue_temporal_post active t local _ actor loc (eval_expr t value) Hi HP Hforeign) as Hpost end.
    split.
    + apply spatial_enqueue_right; [exact Hsp |eapply local_read_some_domain; exact Hread].
    + split; [exact Hfree |]. split; [exact HJ |]. split.
      * destruct Hpost as (a & b & Htm & Ha & Hb); exists a,b; split; [exact Htm |]. split; [exact Ha |].
        change (write_atom active (eval_expr t address) (eval_expr t annotation) (eval_expr t value) (proj1_sig b)).
        rewrite Eaddress,E; exact Hb.
      * constructor.
        -- intros address' [HJdom |HLdom]; [left; exact HJdom |right].
           eapply enqueue_domain_subset; [eapply local_read_some_domain; exact Hread |exact HLdom].
        -- intros i H; left; exact H.
Qed.
Theorem buffered_private_store_valid active J address old value annotation : buffered_private_store_rule active J address old value annotation.
Proof. intros H; apply buffered_atomic_valid; [exact H |apply buffered_private_store_premise]. Qed.
