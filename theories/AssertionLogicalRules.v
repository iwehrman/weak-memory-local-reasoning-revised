From Stdlib Require Import List ZArith Bool.
From WMLR Require Import Expressions Machine Separation Assertions AssertionSemantics
  PersistentAssertions PersistentRules AssertionSubstitution AssertionDerivation.
Import ListNotations.

(** Semantic lemmas for the logical part of the assertion calculus.
    These apply to the entire grammar, including future-aware wands. *)
Lemma assertion_models_update_irrelevant active p s r x v : ~ In x (A.fv p) ->
  (persistent_models active (update s x v) r p <-> persistent_models active s r p).
Proof. intros H; symmetry; apply future_satisfies_agrees,agrees_update_irrelevant,H. Qed.

Lemma assertion_rule_refl active p : persistent_entails active p p.
Proof. intros s r H; exact H. Qed.

Lemma assertion_rule_trans active p q r :
  persistent_entails active p q -> persistent_entails active q r -> persistent_entails active p r.
Proof. intros HP HQ s a H; apply HQ,HP,H. Qed.

Lemma assertion_rule_true active p : persistent_entails active p (A.Pure BTrue).
Proof. intros s r H; reflexivity. Qed.

Lemma assertion_rule_false active p : persistent_entails active (A.Pure BFalse) p.
Proof. intros s r H; discriminate. Qed.

Lemma assertion_rule_and_intro active p q r :
  persistent_entails active p q -> persistent_entails active p r -> persistent_entails active p (A.And q r).
Proof. intros HQ HR s a H; split; [apply HQ |apply HR]; exact H. Qed.

Lemma assertion_rule_and_left active p q : persistent_entails active (A.And p q) p.
Proof. intros s r [HP HQ]; exact HP. Qed.

Lemma assertion_rule_and_right active p q : persistent_entails active (A.And p q) q.
Proof. intros s r [HP HQ]; exact HQ. Qed.

Lemma assertion_rule_or_left active p q : persistent_entails active p (A.Or p q).
Proof. intros s r HP; left; exact HP. Qed.

Lemma assertion_rule_or_right active p q : persistent_entails active q (A.Or p q).
Proof. intros s r HQ; right; exact HQ. Qed.

Lemma assertion_rule_or_cases active context p q result :
  persistent_entails active (A.And context p) result ->
  persistent_entails active (A.And context q) result ->
  persistent_entails active (A.And context (A.Or p q)) result.
Proof. intros HP HQ s r [HC [H |H]]; [apply HP |apply HQ]; split; assumption. Qed.

Lemma assertion_rule_exists_intro active x p expression :
  persistent_entails active (assertion_subst x expression p) (A.Exists x p).
Proof. intros s r H; exists (eval_expr s expression); apply persistent_assertion_subst,H. Qed.

Lemma assertion_rule_exists_elim active context x p result :
  ~ In x (A.fv context ++ A.fv result) ->
  persistent_entails active (A.And context p) result ->
  persistent_entails active (A.And context (A.Exists x p)) result.
Proof.
  intros Hfresh H s r [HC [v HP]]; rewrite in_app_iff in Hfresh.
  apply (proj1 (assertion_models_update_irrelevant active result s r x v ltac:(tauto))).
  apply H; split; [|exact HP].
  apply (proj2 (assertion_models_update_irrelevant active context s r x v ltac:(tauto))),HC.
Qed.

Lemma assertion_rule_forall_intro active p x q :
  ~ In x (A.fv p) -> persistent_entails active p q -> persistent_entails active p (A.Forall x q).
Proof.
  intros Hfresh H s r HP v; apply H.
  apply (proj2 (assertion_models_update_irrelevant active p s r x v Hfresh)),HP.
Qed.

Lemma assertion_rule_forall_elim active x p expression :
  persistent_entails active (A.Forall x p) (assertion_subst x expression p).
Proof. intros s r H; apply persistent_assertion_subst,H. Qed.

Lemma assertion_rule_substitute active x expression p q :
  persistent_entails active p q ->
  persistent_entails active (assertion_subst x expression p) (assertion_subst x expression q).
Proof. intros H s r HP; apply persistent_assertion_subst,H; apply persistent_assertion_subst,HP. Qed.

Lemma assertion_pure_assumptions active conditions s r :
  persistent_models active s r (pure_assumptions conditions) <->
  (forall b, In b conditions -> eval_bexpr s b = true).
Proof.
  induction conditions as [|b rest IH]; cbn [pure_assumptions].
  - split; [intros _ b H; contradiction |intros; reflexivity].
  - change ((eval_bexpr s b = true /\ persistent_models active s r (pure_assumptions rest)) <->
      (forall c, In c (b :: rest) -> eval_bexpr s c = true)).
    rewrite IH; cbn; split; [intros [Hb Hr] c [<- |H]; auto |intros H; split; [apply H; auto |intros; apply H; auto]].
Qed.

Lemma assertion_rule_pure active conditions conclusion :
  (forall s, (forall b, In b conditions -> eval_bexpr s b = true) -> eval_bexpr s conclusion = true) ->
  persistent_entails active (pure_assumptions conditions) (A.Pure conclusion).
Proof. intros H s r HP; apply H; apply (proj1 (assertion_pure_assumptions active conditions s r)),HP. Qed.

Lemma assertion_rule_pure_cases active p b q :
  persistent_entails active (A.And p (A.Pure b)) q ->
  persistent_entails active (A.And p (A.Pure (BNot b))) q -> persistent_entails active p q.
Proof.
  intros Hyes Hno s r HP; destruct (eval_bexpr s b) eqn:E.
  - apply Hyes; split; assumption.
  - apply Hno; split; [exact HP |change (negb (eval_bexpr s b) = true); rewrite E; reflexivity].
Qed.

Lemma assertion_rule_equality active x expression replacement p :
  persistent_entails active
    (A.And (A.Pure (BEq expression replacement)) (assertion_subst x expression p))
    (assertion_subst x replacement p).
Proof.
  intros s r [Heq HP]; change (Z.eqb (eval_expr s expression) (eval_expr s replacement) = true) in Heq.
  apply Z.eqb_eq in Heq; apply persistent_assertion_subst.
  apply persistent_assertion_subst in HP; rewrite Heq in HP; exact HP.
Qed.

Lemma assertion_rule_or_separate_left kind active p q r s a :
  persistent_models active s a (separate kind (A.Or p q) r) <->
  persistent_models active s a (A.Or (separate kind p r) (separate kind q r)).
Proof.
  destruct kind; cbn [separate]; split.
  all: try (intros (b & c & Hsep & [HP |HQ] & HR);
    [left |right]; (exists b,c; split; [exact Hsep |split; assumption])).
  all: intros [(b & c & Hsep & HP & HR) |(b & c & Hsep & HQ & HR)];
    exists b,c; split; [exact Hsep | |exact Hsep |]; split;
    [left; exact HP |exact HR |right; exact HQ |exact HR].
Qed.

Lemma assertion_rule_or_separate_right kind active p q r s a :
  persistent_models active s a (separate kind p (A.Or q r)) <->
  persistent_models active s a (A.Or (separate kind p q) (separate kind p r)).
Proof.
  destruct kind; cbn [separate]; split.
  all: try (intros (b & c & Hsep & HP & [HQ |HR]);
    [left |right]; (exists b,c; split; [exact Hsep |split; assumption])).
  all: intros [(b & c & Hsep & HP & HQ) |(b & c & Hsep & HP & HR)];
    exists b,c; split; [exact Hsep | |exact Hsep |]; split;
    [exact HP |left; exact HQ |exact HP |right; exact HR].
Qed.

Lemma assertion_rule_exists_separate_left kind active x p q : ~ In x (A.fv q) ->
  forall s a, persistent_models active s a (separate kind (A.Exists x p) q) <->
  persistent_models active s a (A.Exists x (separate kind p q)).
Proof.
  intros Hfresh s a; destruct kind; cbn [separate]; split.
  all: try (intros (b & c & Hsep & (v & HP) & HQ); exists v,b,c; split; [exact Hsep |];
    split; [exact HP |apply (proj2 (assertion_models_update_irrelevant active q s c x v Hfresh)),HQ]).
  all: intros (v & b & c & Hsep & HP & HQ); exists b,c; split; [exact Hsep |];
    split; [exists v; exact HP |apply (proj1 (assertion_models_update_irrelevant active q s c x v Hfresh)),HQ].
Qed.

Lemma assertion_rule_exists_separate_right kind active x p q : ~ In x (A.fv p) ->
  forall s a, persistent_models active s a (separate kind p (A.Exists x q)) <->
  persistent_models active s a (A.Exists x (separate kind p q)).
Proof.
  intros Hfresh s a; destruct kind; cbn [separate]; split.
  all: try (intros (b & c & Hsep & HP & (v & HQ)); exists v,b,c; split; [exact Hsep |];
    split; [apply (proj2 (assertion_models_update_irrelevant active p s b x v Hfresh)),HP |exact HQ]).
  all: intros (v & b & c & Hsep & HP & HQ); exists b,c; split; [exact Hsep |];
    split; [apply (proj1 (assertion_models_update_irrelevant active p s b x v Hfresh)),HP |exists v; exact HQ].
Qed.

Lemma assertion_rule_pure_separate_left kind active b p q s a :
  persistent_models active s a (separate kind (A.And (A.Pure b) p) q) <->
  persistent_models active s a (A.And (A.Pure b) (separate kind p q)).
Proof.
  destruct kind; cbn [separate]; split.
  all: try (intros (l & r & Hsep & [Hb HP] & HQ); split;
    [exact Hb |exists l,r; split; [exact Hsep |]; split; assumption]).
  all: intros [Hb (l & r & Hsep & HP & HQ)]; exists l,r; split;
    [exact Hsep |]; split; [split; assumption |exact HQ].
Qed.

Lemma assertion_rule_pure_separate_right kind active b p q s a :
  persistent_models active s a (separate kind p (A.And q (A.Pure b))) <->
  persistent_models active s a (A.And (separate kind p q) (A.Pure b)).
Proof.
  destruct kind; cbn [separate]; split.
  all: try (intros (l & r & Hsep & HP & [HQ Hb]); split;
    [exists l,r; split; [exact Hsep |]; split; assumption |exact Hb]).
  all: intros [(l & r & Hsep & HP & HQ) Hb]; exists l,r; split;
    [exact Hsep |]; split; [exact HP |split; assumption].
Qed.
