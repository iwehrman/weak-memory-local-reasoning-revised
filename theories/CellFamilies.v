From Stdlib Require Import List ZArith.
From WMLR Require Import Expressions Machine BufferRelations Separation Assertions AssertionSemantics
  PersistentAssertions TemporalSafety InvariantFragment AssertionDerivation AssertionDerivedRules
  AssertionRearrangements AssertionClientRules AssertionCellSubstitution.
Import ListNotations.

(** Finite Rocq families of existing cell assertions, not recursive predicates
    in the assertion grammar. Useful for concrete states and region clients. *)
Definition concrete_cell loc value := writer_points_to (EVal (Z.pos loc)) (EVal value).
Fixpoint cell_family (items : list (location * Z)) : A.assertion :=
  match items with [] => A.Emp |(loc,value)::rest => A.Spatial (concrete_cell loc value) (cell_family rest) end.
Fixpoint cell_heap (items : list (location * Z)) : heap :=
  match items with [] => empty_heap |(loc,value)::rest => heap_override (heap_update empty_heap loc value) (cell_heap rest) end.
Definition cell_memory items := Memory (cell_heap items) empty_buffers no_blocked.

Definition cell_resource active owner (Hactive : active owner) (items : list (location * Z)) : resource active.
Proof.
  refine (exist _ (Generalized (cell_memory items) active) _).
  split; [split; [intros i H; contradiction |intros; reflexivity] |].
  split; [intros i H; exact H |intros Hnone loc; exfalso; exact (Hnone owner Hactive)].
Defined.

Lemma cell_heap_domain items loc : heap_domain (cell_heap items) loc <-> In loc (map fst items).
Proof.
  induction items as [|[address value] rest IH]; cbn [cell_heap map fst In].
  - split; [intros [v H]; discriminate |contradiction].
  - unfold heap_domain,heap_override; destruct (cell_heap rest loc) eqn:ER.
    + split; [intros H; right; apply IH; exists v; exact ER |intros H; exists v; reflexivity].
    + unfold heap_update; destruct (Pos.eq_dec loc address) as [-> |Hne].
      * split; [intros H; left; reflexivity |intros H; exists value; reflexivity].
      * split; [intros [v H]; discriminate |intros [E |H]; [congruence |]].
        apply IH in H; destruct H as [v H]; rewrite ER in H; discriminate.
Qed.

Lemma cell_memory_domain items loc : memory_domain (cell_memory items) loc <-> In loc (map fst items).
Proof.
  split.
  - intros [H |[i [v H]]]; [apply cell_heap_domain,H |contradiction].
  - intros H; left; apply cell_heap_domain,H.
Qed.

Lemma cell_memory_split loc value rest : ~ In loc (map fst rest) ->
  memory_spatial (Memory (heap_update empty_heap loc value) empty_buffers no_blocked)
    (cell_memory rest) (cell_memory ((loc,value)::rest)).
Proof.
  intros HF; split.
  - split; [|intros i H _; exact H]. intros l [[v Hh] |[i [v Hb]]] HR; [|contradiction].
    change (heap_update empty_heap loc value l = Some v) in Hh.
    unfold heap_update in Hh; destruct (Pos.eq_dec l loc) as [-> |Hne]; [apply HF,cell_memory_domain,HR |discriminate].
  - split; [intros; reflexivity |split; [intros; constructor |intros i; cbn; unfold no_blocked; tauto]].
Qed.

Lemma cell_resource_single active owner Hactive s loc value :
  persistent_models active s (cell_resource active owner Hactive [(loc,value)]) (concrete_cell loc value).
Proof.
  eapply writer_points_to_from_shape with (loc := loc) (owner := owner);
    [reflexivity |exact Hactive |intros; reflexivity |intros; reflexivity |intros i H; exact H |exact Hactive].
Qed.

Theorem cell_family_models active owner Hactive s items : NoDup (map fst items) ->
  persistent_models active s (cell_resource active owner Hactive items) (cell_family items).
Proof.
  induction items as [|[loc value] rest IH]; intros Hnd.
  - split; [intros; reflexivity |split; [intros; reflexivity |intros i H; exact H]].
  - inversion Hnd; subst; exists (cell_resource active owner Hactive [(loc,value)]), (cell_resource active owner Hactive rest).
    split.
    + split; [apply cell_memory_split; assumption |intros i; cbn; tauto].
    + split; [apply cell_resource_single |apply IH; assumption].
Qed.

Lemma cell_family_fv items : A.fv (cell_family items) = [].
Proof.
  induction items as [|[loc value] rest IH]; [reflexivity |].
  cbn [cell_family A.fv]; unfold concrete_cell; rewrite assertion_writer_cell_fv,IH; reflexivity.
Qed.

Lemma cell_family_fragment items : invariant_fragment (cell_family items).
Proof. induction items as [|[loc value] rest IH]; [constructor |constructor; [constructor |exact IH]]. Qed.

Theorem cell_family_exclusive active loc value rest :
  assertion_derivation active (A.Spatial (cell_family ((loc,value)::rest)) (cell_family ((loc,value)::rest))) (A.Pure BFalse).
Proof.
  cbn [cell_family]; eapply AssertTrans; [apply (AssertAssociative active SepSpatial Forward) |].
  eapply AssertTrans; [apply (AssertSeparateMono active SepSpatial); [apply AssertRefl |apply assert_derive_spatial_rotate] |].
  eapply AssertTrans; [apply (AssertAssociative active SepSpatial Backward) |].
  eapply AssertTrans with (q := A.Spatial (A.Pure BFalse) (A.Spatial (cell_family rest) (cell_family rest))).
  - apply (AssertSeparateMono active SepSpatial); [apply assert_derive_cells_exclusive |apply AssertRefl].
  - apply (assert_derive_separate_pure_left active SepSpatial).
Qed.
