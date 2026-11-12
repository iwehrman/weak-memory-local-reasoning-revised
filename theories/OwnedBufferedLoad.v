From Stdlib Require Import List ZArith.
From WMLR Require Import Expressions Languages OperationalSemantics Assertions AssertionSemantics
  PersistentAssertions PersistentRules Specifications OwnedSafety OwnedHeap OwnedCalculus OwnedDerivedRules
  OwnedContainerEntailments InvariantFragment.
Import ListNotations.

(** Priority 5.1 target: the existing LOAD axiom and FRAME-TM suffice.
    No new constructor or semantic-validity premise is introduced. *)
Lemma owned_derive_load_write active invariant mode address annotation value x :
  ~ In x (A.fv invariant) ->
  ~ In x (expr_fv address ++ expr_fv annotation ++ expr_fv value) ->
  owned_derivation active invariant mode (A.LeadsTo address annotation value)
    (C.Prim (C.Common (S.Load x address)) annotation)
    (A.And (A.LeadsTo address annotation value) (A.Pure (BEq (EVar x) value))).
Proof.
  intros HJ Hfresh; eapply OwnedConsequence.
  - intros s r H; apply persistent_strong_emp_right, H.
  - apply OwnedLoad; [exact HJ |cbn [A.fv]; rewrite app_nil_r; exact Hfresh].
  - intros s r [[Hsp Htm] Hb]; split; [|exact Hb].
    eapply container_spatial_emp_elim; [exact I |exact Hsp].
Qed.

Lemma buffered_load_pure_temporal active past current b :
  persistent_entails active (A.Temporal past (A.And current (A.Pure b)))
    (A.And (A.Temporal past current) (A.Pure b)).
Proof.
  intros s r (a & c & Htm & HP & HQ & Hb); split; [exists a,c; auto |exact Hb].
Qed.

Theorem owned_derive_load_after_history_overlap active invariant past address annotation value x :
  ~ In x (A.fv invariant) -> ~ In x (A.fv past) ->
  ~ In x (expr_fv address ++ expr_fv annotation ++ expr_fv value) ->
  owned_derivation active invariant OverlapMode
    (A.Temporal past (A.LeadsTo address annotation value))
    (C.Prim (C.Common (S.Load x address)) annotation)
    (A.And (A.Temporal past (A.LeadsTo address annotation value)) (A.Pure (BEq (EVar x) value))).
Proof.
  intros HJ HP Hfresh; eapply OwnedConsequence; [intros s r H; exact H | |apply buffered_load_pure_temporal].
  apply OwnedFrameTM; [apply owned_derive_load_write; assumption |].
  intros y Hy; cbn [C.modifies C.primitive_mod S.primitive_mod] in Hy.
  destruct Hy as [E |H]; [subst y; exact HP |contradiction].
Qed.

Theorem owned_derive_load_after_history active invariant mode past address annotation value x :
  ~ In x (A.fv invariant) -> ~ In x (A.fv past) ->
  ~ In x (expr_fv address ++ expr_fv annotation ++ expr_fv value) ->
  owned_derivation active invariant mode
    (A.Temporal past (A.LeadsTo address annotation value))
    (C.Prim (C.Common (S.Load x address)) annotation)
    (A.And (A.Temporal past (A.LeadsTo address annotation value)) (A.Pure (BEq (EVar x) value))).
Proof.
  intros HJ HP Hfresh; destruct mode; [|apply OwnedWeaken];
    apply owned_derive_load_after_history_overlap; assumption.
Qed.

Theorem owned_derive_load_after_history_spatial active invariant mode past tail address annotation value x :
  ~ In x (A.fv invariant) -> ~ In x (A.fv past) -> ~ In x (A.fv tail) ->
  ~ In x (expr_fv address ++ expr_fv annotation ++ expr_fv value) ->
  owned_derivation active invariant mode
    (A.Spatial (A.Temporal past (A.LeadsTo address annotation value)) tail)
    (C.Prim (C.Common (S.Load x address)) annotation)
    (A.And (A.Spatial (A.Temporal past (A.LeadsTo address annotation value)) tail)
      (A.Pure (BEq (EVar x) value))).
Proof.
  intros HJ HP HT Hfresh; eapply OwnedConsequence; [apply container_spatial_comm | |].
  - apply OwnedFrameSP; [apply owned_derive_load_after_history; assumption |].
    intros y Hy; cbn [C.modifies C.primitive_mod S.primitive_mod] in Hy.
    destruct Hy as [E |H]; [subst y; exact HT |contradiction].
  - intros s r (a & b & Hsp & HR & HH & Hb); split; [apply container_spatial_comm; exists a,b; auto |exact Hb].
Qed.

(** The queue's particular history, using an explicit existential binder.
    Its freshness is stated through the formula's free variables, so bound
    occurrences do not impose a spurious freshness requirement. *)
Corollary owned_derive_load_own_buffered_write active invariant mode address value annotation old x tail :
  ~ In x (A.fv invariant) ->
  ~ In x (A.fv (A.Exists old (writer_points_to address (EVar old)))) ->
  ~ In x (A.fv tail) ->
  ~ In x (expr_fv address ++ expr_fv annotation ++ expr_fv value) ->
  owned_derivation active invariant mode
    (A.Spatial (A.Temporal (A.Exists old (writer_points_to address (EVar old)))
      (A.LeadsTo address annotation value)) tail)
    (C.Prim (C.Common (S.Load x address)) annotation)
    (A.And (A.Spatial (A.Temporal (A.Exists old (writer_points_to address (EVar old)))
      (A.LeadsTo address annotation value)) tail) (A.Pure (BEq (EVar x) value))).
Proof. apply owned_derive_load_after_history_spatial. Qed.
