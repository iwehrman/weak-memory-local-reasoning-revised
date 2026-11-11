From Stdlib Require Import List ZArith.
From WMLR Require Import Expressions Languages Machine BufferRelations Separation RepairedSeparation
  GeneralizedFlushing FrameDecomposition OperationalSemantics Assertions AssertionSemantics PersistentAssertions
  Safety RepairedSafety HeapRules OwnershipProtocol OwnershipHeap PrivateOwnership TemporalSafety
  SeparatedSafety SeparatedRules.
Import ListNotations.

Lemma separated_cell_read active owner invariant phase s local protected history whole loc v i : active i ->
  separated_environment active owner invariant phase s local protected history whole ->
  persistent_models active s local (cell_assertion loc v) -> local_read whole i (Z.pos loc) = Some v.
Proof.
  intros Hi [_ _ _ [combined [Htm Hsp]]] HP.
  destruct (persistent_cell_resource_shape _ _ _ _ _ HP) as [Hheap [Hbuffers Hfree]].
  eapply framed_cell_read; [exact Hi | | |exact (Hbuffers i)].
  - exists (resource_memory active combined); split.
    + exact (proj1 (repaired_temporal_in_spatiotemporal _ _ _ _ Htm)).
    + apply memory_spatial_comm, Hsp.
  - rewrite Hheap; apply heap_update_same.
Qed.

Lemma protocol_region_update active owner invariant phase s protected x v :
  ~ In x (A.fv invariant) -> protocol_region active owner invariant phase s protected ->
  protocol_region active owner invariant phase (update s x v) protected.
Proof.
  intros Hfresh [Hwf Hp]; split; [exact Hwf |]. destruct phase; [|exact Hp].
  destruct Hp as [Hfree HJ]; split; [exact Hfree |].
  eapply persistent_full_agrees; [apply agrees_update_irrelevant, Hfresh |exact HJ].
Qed.

(** A private load may change a register. Freshness for the invariant and the
    separate protected assertion replaces any blanket ban on register writes. *)
Theorem separated_load_cell_valid active owner invariant phase protected_assertion loc v x :
  ~ In x (A.fv invariant) -> ~ In x (A.fv protected_assertion) ->
  separated_valid active owner invariant phase protected_assertion (cell_assertion loc v)
    (Concurrent.Prim (Concurrent.Common (Sequential.Load x (EVal (Z.pos loc)))) (EVal (Z.pos owner)))
    phase protected_assertion (A.And (cell_assertion loc v) (A.Pure (BEq (EVar x) (EVal v)))).
Proof.
  intros Hinvfresh Hprotectedfresh s local protected Hr Hl HS HP n.
  revert s local protected Hr Hl HS HP; induction n; intros s local protected Hr Hl HS HP; [exact I |].
  split; [exact Hr |]. split; [exact Hl |]. split; [intros [ann E]; discriminate |]. split.
  - intros history whole Henv Hfault; inversion Hfault; subst.
    match goal with E : eval_expr _ (EVal (Z.pos _)) = Z.pos _ |- _ => simpl in E; inversion E; subst end.
    match goal with H : primitive_abort _ _ _ _ |- _ => inversion H; subst end.
    match goal with Hi : active ?j |- _ =>
      pose proof (separated_cell_read _ _ _ _ _ _ _ _ _ _ _ j Hi Henv HP) as Hread end.
    cbn [eval_expr] in *; congruence.
  - intros history whole next t whole' Henv Hstep; inversion Hstep; subst.
    + match goal with H : primitive_step _ _ _ _ _ |- _ => inversion H; subst end.
      match goal with E : eval_expr _ (EVal (Z.pos _)) = Z.pos _ |- _ => simpl in E; inversion E; subst end.
      match goal with Hi : active ?j |- _ =>
        pose proof (separated_cell_read _ _ _ _ _ _ _ _ _ _ _ j Hi Henv HP) as Hread end.
      assert (Evalue : v0 = v) by (cbn [eval_expr] in *; congruence); subst v0.
      pose proof (protocol_region_update _ _ _ _ _ _ x v Hinvfresh Hr) as Hr'.
      exists phase, local, protected, history; split.
      * destruct Henv as [_ _ Hhf Hcomp]; constructor; assumption.
      * split; [constructor |]. split; [intros loc0 H; exact H |]. split; [intros loc0 H; exact H |].
        apply separated_skip_safe; try assumption.
        -- eapply persistent_full_agrees; [apply agrees_update_irrelevant, Hprotectedfresh |exact HS].
        -- split.
           ++ apply (proj1 (future_satisfies_agrees _ _ _ _ _
                (agrees_update_irrelevant (A.fv (cell_assertion loc v)) s x v (cell_assertion_fresh loc v x)) local)), HP.
           ++ change (Z.eqb (update s x v x) v = true); rewrite update_same; apply Z.eqb_refl.
    + match goal with H : flush _ _ _ |- _ =>
        destruct (separated_environment_flush _ _ _ _ _ _ _ _ _ _ Henv H)
          as (local' & protected' & history' & Henv' & Hlf & Hpf & Hhf & Hld & Hpd) end.
      exists phase, local', protected', history'; split; [exact Henv' |]. split; [exact Hhf |].
      split; [exact Hld |]. split; [exact Hpd |]. apply IHn.
      * exact (separated_protected_ok _ _ _ _ _ _ _ _ _ Henv').
      * exact (separated_local_free _ _ _ _ _ _ _ _ _ Henv').
      * eapply protocol_assertion_flush; eassumption.
      * eapply persistent_assertion_flushing_closed; eassumption.
Qed.
