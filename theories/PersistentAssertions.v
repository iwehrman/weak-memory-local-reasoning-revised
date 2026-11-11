From Stdlib Require Import List ZArith.
From WMLR Require Import Expressions Assertions AssertionSemantics Machine Separation
  GeneralizedFlushing ConcreteAssertions RepairedAssertions AssertionFlushing.
Import ListNotations.

(** Only wands change: they must hold at every reachable future resource.
    Atoms, quantifiers, and conjunctions keep their pointwise definitions. *)
Fixpoint future_satisfies {R} (model : interpretation R) (future : R -> R -> Prop)
    (s : stack) (r : R) (p : ConcurrentAssertion.assertion) : Prop :=
  match p with
  | A.Pure b => eval_bexpr s b = true
  | A.Or p q => future_satisfies model future s r p \/ future_satisfies model future s r q
  | A.And p q => future_satisfies model future s r p /\ future_satisfies model future s r q
  | A.Exists x p => exists v, future_satisfies model future (update s x v) r p
  | A.Forall x p => forall v, future_satisfies model future (update s x v) r p
  | A.Emp => empty_resource model r
  | A.Barrier i => barrier_resource model (eval_expr s i) r
  | A.Lock i => lock_resource model (eval_expr s i) r
  | A.LeadsTo e i v => write_resource model (eval_expr s e) (eval_expr s i) (eval_expr s v) r
  | A.Spatial p q => exists a b, spatial_composition model a b r /\
      future_satisfies model future s a p /\ future_satisfies model future s b q
  | A.Temporal p q => exists a b, temporal_composition model a b r /\
      future_satisfies model future s a p /\ future_satisfies model future s b q
  | A.SpatialWand p q => forall later, future r later -> forall a out,
      future_satisfies model future s a p -> spatial_composition model a later out ->
      future_satisfies model future s out q
  | A.TemporalWandLeft p q => forall later, future r later -> forall a out,
      future_satisfies model future s a p -> temporal_composition model a later out ->
      future_satisfies model future s out q
  | A.TemporalWandRight q p => forall later, future r later -> forall a out,
      future_satisfies model future s a p -> temporal_composition model later a out ->
      future_satisfies model future s out q
  end.

Record future_model_laws {R} (model : interpretation R) (future : R -> R -> Prop) : Prop := {
  future_reflexive : forall a, future a a;
  future_transitive : forall a b c, future a b -> future b c -> future a c;
  future_empty : forall a b, future a b -> empty_resource model a -> empty_resource model b;
  future_barrier : forall i a b, future a b -> barrier_resource model i a -> barrier_resource model i b;
  future_lock : forall i a b, future a b -> lock_resource model i a -> lock_resource model i b;
  future_write : forall e i v a b, future a b -> write_resource model e i v a -> write_resource model e i v b;
  future_spatial : forall out out' a b, future out out' -> spatial_composition model a b out ->
    exists a' b', future a a' /\ future b b' /\ spatial_composition model a' b' out';
  future_temporal : forall out out' a b, future out out' -> temporal_composition model a b out ->
    exists a' b', future a a' /\ future b b' /\ temporal_composition model a' b' out'
}.

Theorem future_satisfies_closed {R} (model : interpretation R) future :
  future_model_laws model future -> forall p s a b,
  future a b -> future_satisfies model future s a p -> future_satisfies model future s b p.
Proof.
  intros [Hrefl Htrans Hemp Hbar Hlock Hwrite Hsp Htm] p.
  induction p; intros s r r' Hfuture Hp; cbn [future_satisfies] in *.
  - exact Hp.
  - destruct Hp; [left; eapply IHp1 |right; eapply IHp2]; eassumption.
  - destruct Hp; split; [eapply IHp1 |eapply IHp2]; eassumption.
  - destruct Hp as [v Hp]; exists v; eapply IHp; eassumption.
  - intros v; eapply IHp; [exact Hfuture |apply Hp].
  - eapply Hemp; eassumption.
  - eapply Hbar; eassumption.
  - eapply Hlock; eassumption.
  - eapply Hwrite; eassumption.
  - destruct Hp as [a [b [Hsep [Ha Hb]]]].
    destruct (Hsp _ _ _ _ Hfuture Hsep) as [a' [b' [Ha' [Hb' Hsep']]]].
    exists a', b'. split; [exact Hsep' |]. split; [eapply IHp1 |eapply IHp2]; eassumption.
  - destruct Hp as [a [b [Hsep [Ha Hb]]]].
    destruct (Htm _ _ _ _ Hfuture Hsep) as [a' [b' [Ha' [Hb' Hsep']]]].
    exists a', b'. split; [exact Hsep' |]. split; [eapply IHp1 |eapply IHp2]; eassumption.
  - intros later Hlater a out Ha Hsep. eapply Hp; [eapply Htrans; eassumption |exact Ha |exact Hsep].
  - intros later Hlater a out Ha Hsep. eapply Hp; [eapply Htrans; eassumption |exact Ha |exact Hsep].
  - intros later Hlater a out Ha Hsep. eapply Hp; [eapply Htrans; eassumption |exact Ha |exact Hsep].
Qed.

Theorem repaired_future_model_laws active :
  future_model_laws (repaired_interpretation active) (resource_future active).
Proof.
  constructor.
  - intros a; constructor.
  - intros a b c Hab Hbc; eapply generalized_future_trans; eassumption.
  - intros a b Hfuture Hp; eapply empty_atom_future; eassumption.
  - intros i a b Hfuture Hp; eapply barrier_atom_future; eassumption.
  - intros i a b Hfuture Hp; eapply lock_atom_future; eassumption.
  - intros e i v a b Hfuture Hp; eapply write_atom_future; eassumption.
  - exact (resource_spatial_future_split active).
  - exact (resource_temporal_future_split active).
Qed.

Definition persistent_models active s (r : resource active) p : Prop :=
  future_satisfies (repaired_interpretation active) (resource_future active) s r p.

Definition persistent_full_satisfies active s m p : Prop :=
  exists r : resource active, proj1_sig r = Generalized m active /\ persistent_models active s r p.

Lemma persistent_full_well_formed active s m p : persistent_full_satisfies active s m p ->
  generalized_well_formed active (Generalized m active).
Proof. intros [r [Hr Hp]]; rewrite <- Hr; apply (proj2_sig r). Qed.

Theorem persistent_assertion_flushing_closed active p s a b :
  resource_future active a b -> persistent_models active s a p -> persistent_models active s b p.
Proof. apply future_satisfies_closed, repaired_future_model_laws. Qed.

Theorem persistent_full_flushing_closed active p s m m' :
  memory_flushes active m m' -> persistent_full_satisfies active s m p -> persistent_full_satisfies active s m' p.
Proof.
  intros Hflushes. induction Hflushes as [m |m middle final Hstep Htail IH]; intros Hp; [exact Hp |].
  apply IH. destruct Hp as [r [Hr Hp]].
  destruct (flush_at_exists _ _ _ Hstep) as [i Hi].
  assert (Hfuture : generalized_future active (proj1_sig r) (Generalized middle active)).
  { rewrite Hr. apply generalized_future_one. eapply GeneralizedFlush;
      [exact Hi |intros j Hj; exact Hj |intros j Hj; exact Hj |].
    destruct Hi; assumption. }
  exists (exist _ (Generalized middle active)
    (generalized_future_well_formed _ _ _ Hfuture (proj2_sig r))).
  split; [reflexivity |]. eapply persistent_assertion_flushing_closed; [exact Hfuture |exact Hp].
Qed.

Fixpoint wand_free (p : A.assertion) : Prop :=
  match p with
  | A.Or p q | A.And p q | A.Spatial p q | A.Temporal p q => wand_free p /\ wand_free q
  | A.Exists _ p | A.Forall _ p => wand_free p
  | A.SpatialWand _ _ | A.TemporalWandLeft _ _ | A.TemporalWandRight _ _ => False
  | _ => True
  end.

Theorem future_satisfies_wand_free {R} (model : interpretation R) future p :
  wand_free p -> forall s r, future_satisfies model future s r p <-> satisfies model s r p.
Proof.
  induction p; intros Hfree s r; cbn [wand_free] in Hfree;
    cbn [future_satisfies satisfies]; try reflexivity; try contradiction.
  - destruct Hfree as [H1 H2]. rewrite (IHp1 H1 s r), (IHp2 H2 s r); reflexivity.
  - destruct Hfree as [H1 H2]. rewrite (IHp1 H1 s r), (IHp2 H2 s r); reflexivity.
  - split; intros [v Hv]; exists v; [apply (proj1 (IHp Hfree _ _)) |apply (proj2 (IHp Hfree _ _))]; exact Hv.
  - split; intros H v; [apply (proj1 (IHp Hfree _ _)) |apply (proj2 (IHp Hfree _ _))]; apply H.
  - destruct Hfree as [H1 H2]. split; intros [a [b [Hsep [Ha Hb]]]]; exists a, b;
      split; [exact Hsep | |exact Hsep |]; split.
    + apply (proj1 (IHp1 H1 _ _)), Ha.
    + apply (proj1 (IHp2 H2 _ _)), Hb.
    + apply (proj2 (IHp1 H1 _ _)), Ha.
    + apply (proj2 (IHp2 H2 _ _)), Hb.
  - destruct Hfree as [H1 H2]. split; intros [a [b [Hsep [Ha Hb]]]]; exists a, b;
      split; [exact Hsep | |exact Hsep |]; split.
    + apply (proj1 (IHp1 H1 _ _)), Ha.
    + apply (proj1 (IHp2 H2 _ _)), Hb.
    + apply (proj2 (IHp1 H1 _ _)), Ha.
    + apply (proj2 (IHp2 H2 _ _)), Hb.
Qed.

Corollary persistent_wand_free_unchanged active p s r : wand_free p ->
  (persistent_models active s r p <-> repaired_models active s r p).
Proof. intros H; apply future_satisfies_wand_free, H. Qed.

Theorem future_satisfies_agrees {R} (model : interpretation R) future p s t :
  agrees (A.fv p) s t -> forall r,
  future_satisfies model future s r p <-> future_satisfies model future t r p.
Proof.
  revert s t. induction p; intros s t H r; cbn [future_satisfies A.fv] in *.
  - rewrite (eval_bexpr_agrees _ _ _ H); reflexivity.
  - rewrite (IHp1 s t (agrees_app_left _ _ _ _ H) r),
      (IHp2 s t (agrees_app_right _ _ _ _ H) r); reflexivity.
  - rewrite (IHp1 s t (agrees_app_left _ _ _ _ H) r),
      (IHp2 s t (agrees_app_right _ _ _ _ H) r); reflexivity.
  - split; intros [v Hv]; exists v;
      [apply (proj1 (IHp _ _ (agrees_under_binder _ _ _ _ _ H) r)) |
       apply (proj2 (IHp _ _ (agrees_under_binder _ _ _ _ _ H) r))]; exact Hv.
  - split; intros Hv v;
      [apply (proj1 (IHp _ _ (agrees_under_binder _ _ _ _ _ H) r)) |
       apply (proj2 (IHp _ _ (agrees_under_binder _ _ _ _ _ H) r))]; apply Hv.
  - reflexivity.
  - rewrite (eval_expr_agrees _ _ _ H); reflexivity.
  - rewrite (eval_expr_agrees _ _ _ H); reflexivity.
  - pose proof (agrees_app_left _ _ _ _ H) as Ha.
    pose proof (agrees_app_right _ _ _ _ H) as Hr.
    rewrite (eval_expr_agrees _ _ _ Ha), (eval_expr_agrees _ _ _ (agrees_app_left _ _ _ _ Hr)),
      (eval_expr_agrees _ _ _ (agrees_app_right _ _ _ _ Hr)); reflexivity.
  - split; intros [a [b [Hsep [Ha Hb]]]]; exists a, b; split;
      [exact Hsep | |exact Hsep |]; split.
    + apply (proj1 (IHp1 _ _ (agrees_app_left _ _ _ _ H) a)), Ha.
    + apply (proj1 (IHp2 _ _ (agrees_app_right _ _ _ _ H) b)), Hb.
    + apply (proj2 (IHp1 _ _ (agrees_app_left _ _ _ _ H) a)), Ha.
    + apply (proj2 (IHp2 _ _ (agrees_app_right _ _ _ _ H) b)), Hb.
  - split; intros [a [b [Hsep [Ha Hb]]]]; exists a, b; split;
      [exact Hsep | |exact Hsep |]; split.
    + apply (proj1 (IHp1 _ _ (agrees_app_left _ _ _ _ H) a)), Ha.
    + apply (proj1 (IHp2 _ _ (agrees_app_right _ _ _ _ H) b)), Hb.
    + apply (proj2 (IHp1 _ _ (agrees_app_left _ _ _ _ H) a)), Ha.
    + apply (proj2 (IHp2 _ _ (agrees_app_right _ _ _ _ H) b)), Hb.
  - split; intros Hw later Hlater a out Hp Hsep.
    + apply (proj1 (IHp2 _ _ (agrees_app_right _ _ _ _ H) out)).
      eapply Hw; [exact Hlater | |exact Hsep].
      apply (proj2 (IHp1 _ _ (agrees_app_left _ _ _ _ H) a)), Hp.
    + apply (proj2 (IHp2 _ _ (agrees_app_right _ _ _ _ H) out)).
      eapply Hw; [exact Hlater | |exact Hsep].
      apply (proj1 (IHp1 _ _ (agrees_app_left _ _ _ _ H) a)), Hp.
  - split; intros Hw later Hlater a out Hp Hsep.
    + apply (proj1 (IHp2 _ _ (agrees_app_right _ _ _ _ H) out)).
      eapply Hw; [exact Hlater | |exact Hsep].
      apply (proj2 (IHp1 _ _ (agrees_app_left _ _ _ _ H) a)), Hp.
    + apply (proj2 (IHp2 _ _ (agrees_app_right _ _ _ _ H) out)).
      eapply Hw; [exact Hlater | |exact Hsep].
      apply (proj1 (IHp1 _ _ (agrees_app_left _ _ _ _ H) a)), Hp.
  - split; intros Hw later Hlater a out Hp Hsep.
    + apply (proj1 (IHp1 _ _ (agrees_app_left _ _ _ _ H) out)).
      eapply Hw; [exact Hlater | |exact Hsep].
      apply (proj2 (IHp2 _ _ (agrees_app_right _ _ _ _ H) a)), Hp.
    + apply (proj2 (IHp1 _ _ (agrees_app_left _ _ _ _ H) out)).
      eapply Hw; [exact Hlater | |exact Hsep].
      apply (proj1 (IHp2 _ _ (agrees_app_right _ _ _ _ H) a)), Hp.
Qed.

Lemma persistent_full_agrees active p s t m : agrees (A.fv p) s t ->
  persistent_full_satisfies active s m p -> persistent_full_satisfies active t m p.
Proof.
  intros H [r [Hr Hp]]. exists r; split; [exact Hr |].
  apply (proj1 (future_satisfies_agrees _ _ _ _ _ H r)), Hp.
Qed.
