From Stdlib Require Import List ZArith.
From WMLR Require Import Expressions Languages Machine Separation OperationalSemantics
  GeneralizedFlushing Assertions AssertionSemantics PersistentAssertions Safety RepairedSafety RepairedRules.
Import ListNotations.

Definition persistent_valid active invariant pre c post : Prop :=
  forall s local, persistent_full_satisfies active s local pre -> forall n,
    repaired_safe active n c s local
      (fun s m => persistent_full_satisfies active s m invariant)
      (fun s m => persistent_full_satisfies active s m post).

Lemma persistent_predicate_closed active p :
  flush_closed active (fun s m => persistent_full_satisfies active s m p).
Proof. intros s m m' Hfuture Hp; eapply persistent_full_flushing_closed; eassumption. Qed.

Theorem persistent_skip_valid active invariant p annotation :
  persistent_valid active invariant p (Concurrent.skip annotation) p.
Proof.
  intros s local Hp n. apply repaired_skip_safe; [apply persistent_predicate_closed |apply persistent_predicate_closed |exact Hp].
Qed.

Lemma persistent_update_environment active invariant s local shared frame whole x v :
  ~ In x (A.fv invariant) ->
  repaired_environment active (fun s m => persistent_full_satisfies active s m invariant)
    s local shared frame whole ->
  repaired_environment active (fun s m => persistent_full_satisfies active s m invariant)
    (update s x v) local shared frame whole.
Proof.
  intros Hfresh [Hl Hs Hf Hw Hsep Hlock Hinv]. constructor; try assumption.
  destruct Hinv as [Hinv |Hheld]; [left |right; exact Hheld].
  eapply persistent_full_agrees; [apply agrees_update_irrelevant, Hfresh |exact Hinv].
Qed.

(** A proof tool for primitive rules, not a derivation constructor. Its
    action and non-abort premises must be discharged for each actual rule. *)
Lemma persistent_primitive_rule active invariant pre primitive annotation post :
  primitive <> Concurrent.Common Sequential.Skip ->
  (forall s local, persistent_full_satisfies active s local pre -> forall shared frame whole,
    repaired_environment active (fun s m => persistent_full_satisfies active s m invariant)
      s local shared frame whole -> forall i,
    eval_expr s annotation = Z.pos i -> ~ primitive_abort active primitive i (State s whole)) ->
  (forall s local, persistent_full_satisfies active s local pre -> forall shared frame whole,
    repaired_environment active (fun s m => persistent_full_satisfies active s m invariant)
      s local shared frame whole -> forall i t whole',
    eval_expr s annotation = Z.pos i -> primitive_step active primitive i (State s whole) (State t whole') ->
    exists local' shared' frame',
      repaired_environment active (fun s m => persistent_full_satisfies active s m invariant)
        t local' shared' frame' whole' /\ memory_flushes active frame frame' /\
      ownership_preserved local shared local' shared' /\ persistent_full_satisfies active t local' post) ->
  persistent_valid active invariant pre (Concurrent.Prim primitive annotation) post.
Proof.
  intros HnotSkip Hnoabort Haction s local Hp n. revert s local Hp.
  induction n; intros s local Hp; [exact I |]. split.
  - intros [ann Heq]. inversion Heq; contradiction.
  - split.
    + intros shared frame whole Henv Habort. inversion Habort; subst.
      eapply Hnoabort; eassumption.
    + intros shared frame whole next t whole' Henv Hstep. inversion Hstep; subst.
      * match goal with H : primitive_step _ _ _ _ _ |- _ =>
          destruct (Haction _ _ Hp _ _ _ Henv _ _ _ ltac:(eassumption) H)
            as [local' [shared' [frame' [Henv' [Hflush [Howned Hpost]]]]]] end.
        exists local', shared', frame'. split; [exact Henv' |]. split; [exact Hflush |].
        split; [exact Howned |]. apply repaired_skip_safe;
          [apply persistent_predicate_closed |apply persistent_predicate_closed |exact Hpost].
      * match goal with H : flush _ _ _ |- _ =>
          destruct (repaired_environment_flush _ _ _ _ _ _ _ _
            (persistent_predicate_closed active invariant) Henv H)
            as [local' [shared' [frame' [Henv' [Hlocal [Hframe Howned]]]]]] end.
        exists local', shared', frame'. split; [exact Henv' |]. split; [exact Hframe |].
        split; [exact Howned |]. apply IHn; eapply persistent_full_flushing_closed; eassumption.
Qed.

Theorem persistent_assignment_valid active invariant b x rhs annotation :
  ~ In x (A.fv invariant) -> persistent_valid active invariant (A.Pure (subst_bexpr x rhs b))
    (Concurrent.Prim (Concurrent.Common (Sequential.Assign x rhs)) annotation) (A.Pure b).
Proof.
  intros Hfresh. apply persistent_primitive_rule; [discriminate | |].
  - intros s local Hp shared frame whole Henv i Hi Habort; inversion Habort.
  - intros s local Hp shared frame whole Henv i t whole' Hi Hstep; inversion Hstep; subst.
    exists local, shared, frame. split; [apply persistent_update_environment; assumption |].
    split; [constructor |]. split; [apply ownership_preserved_refl |].
    destruct Hp as [r [Hr Hp]]. exists r; split; [exact Hr |].
    change (eval_bexpr s (subst_bexpr x rhs b) = true) in Hp.
    rewrite eval_subst_bexpr in Hp; exact Hp.
Qed.

Theorem persistent_assume_valid active invariant p b annotation :
  persistent_valid active invariant (A.Or (A.Pure (BNot b)) p)
    (Concurrent.Prim (Concurrent.Common (Sequential.Assume b)) annotation) p.
Proof.
  apply persistent_primitive_rule; [discriminate | |].
  - intros s local Hp shared frame whole Henv i Hi Habort; inversion Habort.
  - intros s local Hp shared frame whole Henv i t whole' Hi Hstep; inversion Hstep; subst.
    exists local, shared, frame. split; [exact Henv |]. split; [constructor |].
    split; [apply ownership_preserved_refl |]. destruct Hp as [r [Hr [Hfalse |Hp]]].
    + change (negb (eval_bexpr t b) = true) in Hfalse.
      match goal with H : eval_bexpr _ _ = true |- _ => rewrite H in Hfalse end; discriminate.
    + exists r; split; assumption.
Qed.

Theorem persistent_assert_valid active invariant p b annotation :
  persistent_valid active invariant (A.And (A.Pure b) p)
    (Concurrent.Prim (Concurrent.Common (Sequential.Assert b)) annotation) p.
Proof.
  apply persistent_primitive_rule; [discriminate | |].
  - intros s local [r [Hr [Hb Hp]]] shared frame whole Henv i Hi Habort; inversion Habort; subst.
    change (eval_bexpr s b = true) in Hb; congruence.
  - intros s local [r [Hr [Hb Hp]]] shared frame whole Henv i t whole' Hi Hstep; inversion Hstep; subst.
    exists local, shared, frame. split; [exact Henv |]. split; [constructor |].
    split; [apply ownership_preserved_refl |]. exists r; split; assumption.
Qed.

Theorem persistent_sequence_valid active invariant pre middle post first second :
  persistent_valid active invariant pre first middle -> persistent_valid active invariant middle second post ->
  persistent_valid active invariant pre (Concurrent.Seq first second) post.
Proof.
  intros Hfirst Hsecond s local Hp n. eapply repaired_safe_sequence;
    [apply Hfirst, Hp |intros k t m Hmiddle; apply Hsecond, Hmiddle].
Qed.

Definition persistent_entails active p q :=
  forall s (r : resource active), persistent_models active s r p -> persistent_models active s r q.

Theorem persistent_consequence_valid active invariant pre pre' c post' post :
  persistent_entails active pre pre' -> persistent_valid active invariant pre' c post' ->
  persistent_entails active post' post -> persistent_valid active invariant pre c post.
Proof.
  intros Hpre Hvalid Hpost s local [r [Hr Hp]] n.
  eapply repaired_safe_post_mono with (post := fun t m => persistent_full_satisfies active t m post').
  - intros t m [r' [Hr' Hq]]. exists r'; split; [exact Hr' |apply Hpost, Hq].
  - apply Hvalid. exists r; split; [exact Hr |apply Hpre, Hp].
Qed.

(** The future-aware wands retain the usual adjunctions on persistent
    assertions. Introduction uses flushing closure of the antecedent. *)
Theorem persistent_spatial_wand_adjoint active p q r :
  persistent_entails active (A.Spatial p q) r <-> persistent_entails active q (A.SpatialWand p r).
Proof.
  split.
  - intros H s current Hq later Hfuture past out Hp Hsep.
    apply H. exists past, later. split; [exact Hsep |]. split; [exact Hp |].
    eapply persistent_assertion_flushing_closed; eassumption.
  - intros H s out [past [current [Hsep [Hp Hq]]]].
    exact (H s current Hq current (GeneralizedRefl active (proj1_sig current)) past out Hp Hsep).
Qed.

Theorem persistent_temporal_wand_left_adjoint active p q r :
  persistent_entails active (A.Temporal p q) r <-> persistent_entails active q (A.TemporalWandLeft p r).
Proof.
  split.
  - intros H s current Hq later Hfuture past out Hp Hsep.
    apply H. exists past, later. split; [exact Hsep |]. split; [exact Hp |].
    eapply persistent_assertion_flushing_closed; eassumption.
  - intros H s out [past [current [Hsep [Hp Hq]]]].
    exact (H s current Hq current (GeneralizedRefl active (proj1_sig current)) past out Hp Hsep).
Qed.

Theorem persistent_temporal_wand_right_adjoint active p q r :
  persistent_entails active (A.Temporal q p) r <-> persistent_entails active q (A.TemporalWandRight r p).
Proof.
  split.
  - intros H s current Hq later Hfuture future out Hp Hsep.
    apply H. exists later, future. split; [exact Hsep |]. split; [|exact Hp].
    eapply persistent_assertion_flushing_closed; eassumption.
  - intros H s out [current [future [Hsep [Hq Hp]]]].
    exact (H s current Hq current (GeneralizedRefl active (proj1_sig current)) future out Hp Hsep).
Qed.

Theorem persistent_disjunction_valid active invariant pre pre' c post :
  persistent_valid active invariant pre c post -> persistent_valid active invariant pre' c post ->
  persistent_valid active invariant (A.Or pre pre') c post.
Proof.
  intros Hleft Hright s local [r [Hr [Hp |Hp]]] n;
    [apply Hleft |apply Hright]; exists r; split; assumption.
Qed.
