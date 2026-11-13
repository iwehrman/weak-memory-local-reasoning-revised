From Stdlib Require Import List ZArith.
From WMLR Require Import Expressions Machine BufferRelations Separation
  RepairedSeparation Assertions AssertionSemantics ConcreteAssertions.
Import ListNotations.

(** Candidate assertion semantics: retain the atoms and spatial separator;
    use the stable temporal separator. This is separate from the original
    interpretation, including for the universally quantified wands. *)
Definition repaired_interpretation active : interpretation (resource active) := {|
  empty_resource := fun r => empty_atom (proj1_sig r);
  barrier_resource := fun i r => barrier_atom active i (proj1_sig r);
  lock_resource := fun i r => lock_atom active i (proj1_sig r);
  write_resource := fun loc i v r => write_atom active loc i v (proj1_sig r);
  spatial_composition := fun a b c => spatial (proj1_sig a) (proj1_sig b) (proj1_sig c);
  temporal_composition := fun a b c => repaired_temporal active (proj1_sig a) (proj1_sig b) (proj1_sig c)
|}.

Definition repaired_models active s (r : resource active) p : Prop :=
  satisfies (repaired_interpretation active) s r p.

Definition repaired_full_satisfies active s m p : Prop :=
  exists r : resource active,
    proj1_sig r = Generalized m active /\ repaired_models active s r p.

Theorem repaired_satisfies_agrees active p s t r :
  agrees (ConcurrentAssertion.fv p) s t ->
  (repaired_models active s r p <-> repaired_models active t r p).
Proof. intros H; exact (satisfies_agrees (repaired_interpretation active) p s t H r). Qed.

Lemma repaired_full_agrees active p s t m :
  agrees (ConcurrentAssertion.fv p) s t ->
  repaired_full_satisfies active s m p -> repaired_full_satisfies active t m p.
Proof.
  intros H [r [Hr Hp]]. exists r; split; [exact Hr |].
  apply (proj1 (repaired_satisfies_agrees _ _ _ _ _ H)), Hp.
Qed.

Lemma repaired_full_well_formed active s m p :
  repaired_full_satisfies active s m p -> generalized_well_formed active (Generalized m active).
Proof. intros [r [Hr _]]. rewrite <- Hr; apply (proj2_sig r). Qed.

Lemma full_generalized_flush_well_formed active m m' :
  generalized_well_formed active (Generalized m active) -> flush active m m' ->
  generalized_well_formed active (Generalized m' active).
Proof.
  intros [Hwf [Hactive Hempty]] Hflush. split.
  - eapply flush_preserves_well_formed; eassumption.
  - split; [exact Hactive |]. intros Hnone loc.
    destruct Hflush as [m i loc' v rest Hi Hlive Hhead]. exfalso; apply (Hnone i Hi).
Qed.

Theorem repaired_full_pure_flushes active s m m' b :
  memory_flushes active m m' ->
  repaired_full_satisfies active s m (ConcurrentAssertion.Pure b) ->
  repaired_full_satisfies active s m' (ConcurrentAssertion.Pure b).
Proof.
  intros Hflushes. induction Hflushes as [m | m middle final Hstep Hrest IH]; intros Hp; [exact Hp |].
  apply IH. pose proof (repaired_full_well_formed _ _ _ _ Hp) as Hwf.
  destruct Hp as [r [Hr Hp]].
  exists (exist _ (Generalized middle active) (full_generalized_flush_well_formed _ _ _ Hwf Hstep)).
  split; [reflexivity | exact Hp].
Qed.

Theorem repaired_temporal_assertion_associative active s r p q t :
  repaired_models active s r (ConcurrentAssertion.Temporal p (ConcurrentAssertion.Temporal q t)) <->
  repaired_models active s r (ConcurrentAssertion.Temporal (ConcurrentAssertion.Temporal p q) t).
Proof.
  split.
  - intros [a [bc [Hout [Hp [b [c [Hbc [Hq Ht]]]]]]]].
    destruct (proj1 (repaired_temporal_resource_associative active a b c r)
      (ex_intro _ bc (conj Hbc Hout))) as [ab [Hab Habc]].
    exists ab, c. split; [exact Habc |]. split; [|exact Ht].
    exists a, b. split; [exact Hab |]. split; assumption.
  - intros [ab [c [Hout [[a [b [Hab [Hp Hq]]]] Ht]]]].
    destruct (proj2 (repaired_temporal_resource_associative active a b c r)
      (ex_intro _ ab (conj Hab Hout))) as [bc [Hbc Habc]].
    exists a, bc. split; [exact Habc |]. split; [exact Hp |].
    exists b, c. split; [exact Hbc |]. split; assumption.
Qed.

Theorem repaired_points_to_requires_flushed active s r address contents :
  repaired_models active s r (ConcurrentAssertion.points_to address contents) ->
  exists loc i, eval_expr s address = Z.pos loc /\ active i /\
    flushed_atom i loc (eval_expr s contents) (proj1_sig r) /\
    (forall j, active j -> complete (proj1_sig r) j).
Proof.
  intros [a [b [[Hstable Hsep] [Ha Hb]]]].
  apply points_to_requires_flushed. exists a, b. split; [exact Hsep |]. split; assumption.
Qed.
