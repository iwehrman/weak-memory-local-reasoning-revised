From Stdlib Require Import List ZArith.
From WMLR Require Import Expressions Machine BufferRelations Separation StableCompatibility
  RepairedSeparation GeneralizedFlushing Assertions AssertionSemantics ConcreteAssertions
  RepairedAssertions PersistentAssertions.
Import ListNotations.

(** Extensional transport for the existing resource semantics, including
    future-aware wands. No functional extensionality or new future relation. *)
Lemma assertion_memory_equiv_refl m : memory_equiv m m.
Proof. split; [intros; reflexivity |]. split; intros; reflexivity. Qed.

Lemma assertion_memory_equiv_sym a b : memory_equiv a b -> memory_equiv b a.
Proof. intros [Hh [Hb Hk]]; split; [intros; symmetry; apply Hh |].
  split; [intros; symmetry; apply Hb |intros; symmetry; apply Hk]. Qed.

Lemma assertion_generalized_equiv_refl a : generalized_equiv a a.
Proof. split; [apply assertion_memory_equiv_refl |intros; reflexivity]. Qed.

Lemma assertion_generalized_equiv_sym a b : generalized_equiv a b -> generalized_equiv b a.
Proof. intros [Hm Hg]; split; [apply assertion_memory_equiv_sym, Hm |intros; symmetry; apply Hg]. Qed.

Lemma assertion_domain_equiv a b : memory_equiv a b -> forall loc, memory_domain a loc <-> memory_domain b loc.
Proof.
  intros [Hh [Hb Hk]] loc; unfold memory_domain, heap_domain, buffer_domain.
  rewrite Hh; setoid_rewrite Hb; reflexivity.
Qed.

Lemma assertion_merge_equiv R a a' b b' c c' :
  memory_equiv a a' -> memory_equiv b b' -> memory_equiv c c' ->
  memory_merge R a b c -> memory_merge R a' b' c'.
Proof.
  intros [Ha [Ba Ka]] [Hb [Bb Kb]] [Hc [Bc Kc]] [Hh [Hbuf Hk]].
  split.
  - intros loc; rewrite <- Hc, Hh; unfold heap_override; rewrite Ha,Hb; reflexivity.
  - split; [intros i; rewrite <- Ba, <- Bb, <- Bc; apply Hbuf
    |intros i; rewrite <- Ka, <- Kb, <- Kc; apply Hk].
Qed.

Lemma assertion_stable_equiv active a a' b b' :
  memory_equiv a a' -> memory_equiv b b' -> stable_compatible active a b -> stable_compatible active a' b'.
Proof.
  intros [Ha [Ba Ka]] [Hb [Bb Kb]] [Hk [Hh Hbuf]]; split.
  - intros i H1 H2; apply (Hk i); [apply Ka,H1 |apply Kb,H2].
  - split.
    + intros i Hi loc H1 H2; apply (Hh i Hi loc).
      * unfold buffer_domain in *; rewrite Ba; exact H1.
      * unfold heap_domain in *; rewrite Hb; exact H2.
    + intros i j Hi Hj Hne loc H1 H2; apply (Hbuf i j Hi Hj Hne loc).
      * unfold buffer_domain in *; rewrite Ba; exact H1.
      * unfold buffer_domain in *; rewrite Bb; exact H2.
Qed.

Lemma assertion_spatial_equiv a a' b b' c c' :
  generalized_equiv a a' -> generalized_equiv b b' -> generalized_equiv c c' ->
  spatial a b c -> spatial a' b' c'.
Proof.
  intros [Ha Ga] [Hb Gb] [Hc Gc] [[[Hd Hk] Hmerge] Gout]; split.
  - split.
    + split.
      * intros loc H1 H2; apply (Hd loc); [apply (assertion_domain_equiv _ _ Ha loc),H1
          |apply (assertion_domain_equiv _ _ Hb loc),H2].
      * intros i H1 H2; apply (Hk i); [apply (proj2 (proj2 Ha) i),H1 |apply (proj2 (proj2 Hb) i),H2].
    + eapply assertion_merge_equiv; eassumption.
  - intros i; rewrite <- Ga, <- Gb, <- Gc; apply Gout.
Qed.

Lemma assertion_temporal_equiv active a a' b b' c c' :
  generalized_equiv a a' -> generalized_equiv b b' -> generalized_equiv c c' ->
  repaired_temporal active a b c -> repaired_temporal active a' b' c'.
Proof.
  intros [Ha Ga] [Hb Gb] [Hc Gc] [Hst [[Hcompat Hmerge] [Hbefore Gout]]].
  assert (Hst' : stable_compatible active (underlying a') (underlying b'))
    by (eapply assertion_stable_equiv; eassumption).
  split; [exact Hst' |]. split.
  - split; [apply stable_implies_printed_compatible,Hst' |eapply assertion_merge_equiv; eassumption].
  - split.
    + intros i Hi; rewrite <- (proj1 (proj2 Ha) i); apply Hbefore, Gb, Hi.
    + intros i; rewrite <- Ga, <- Gb, <- Gc; apply Gout.
Qed.

Lemma assertion_flush_equiv a b i loc value rest :
  memory_equiv a b -> memory_equiv (flush_write a i loc value rest) (flush_write b i loc value rest).
Proof.
  intros [Hh [Hb Hk]]; split.
  - intros address; cbn; unfold heap_update; destruct (Pos.eq_dec address loc); [reflexivity |apply Hh].
  - split; [intros j; cbn; unfold buffer_update; destruct (Pos.eq_dec j i); [reflexivity |apply Hb] |exact Hk].
Qed.

Lemma assertion_generalized_step_equiv active a b b' :
  generalized_equiv a b -> generalized_step active b b' ->
  exists a', generalized_step active a a' /\ generalized_equiv a' b'.
Proof.
  intros Hequiv Hstep; destruct a as [m marks].
  destruct Hstep as [mem before after Hinc Hactive |mem mem' before after i Hflush Hinc Hactive Hi];
    destruct Hequiv as [Hm Hg]; cbn in Hm,Hg.
  - exists (Generalized m after); split.
    + apply GeneralizedMark; [intros j Hj; apply Hinc,Hg,Hj |exact Hactive].
    + split; [exact Hm |intros; reflexivity].
  - destruct Hflush as [mem loc value rest Hactor Hlive Hhead].
    exists (Generalized (flush_write m i loc value rest) after); split.
    + eapply GeneralizedFlush with (i := i).
      * constructor; [exact Hactor |intros H; apply Hlive,(proj2 (proj2 Hm) i),H
          |rewrite (proj1 (proj2 Hm) i); exact Hhead].
      * intros j Hj; apply Hinc,Hg,Hj.
      * exact Hactive.
      * exact Hi.
    + split; [apply assertion_flush_equiv,Hm |intros; reflexivity].
Qed.

Lemma assertion_generalized_future_equiv active b b' : generalized_future active b b' ->
  forall a, generalized_equiv a b -> exists a', generalized_future active a a' /\ generalized_equiv a' b'.
Proof.
  induction 1; intros original Heq.
  - exists original; split; [constructor |exact Heq].
  - destruct (assertion_generalized_step_equiv _ _ _ _ Heq H) as (middle & Hstep & Hmiddle).
    destruct (IHgeneralized_future _ Hmiddle) as (last & Hfuture & Hlast).
    exists last; split; [econstructor; eassumption |exact Hlast].
Qed.

Lemma assertion_resource_future_equiv active (a b b' : resource active) :
  generalized_equiv (proj1_sig a) (proj1_sig b) -> resource_future active b b' ->
  exists a' : resource active, resource_future active a a' /\ generalized_equiv (proj1_sig a') (proj1_sig b').
Proof.
  intros Heq Hfuture.
  destruct (assertion_generalized_future_equiv _ _ _ Hfuture _ Heq) as (g & Hf & Hg).
  exists (exist _ g (generalized_future_well_formed _ _ _ Hf (proj2_sig a))); auto.
Qed.

Theorem persistent_models_resource_equiv active p s (a b : resource active) :
  generalized_equiv (proj1_sig a) (proj1_sig b) -> persistent_models active s a p -> persistent_models active s b p.
Proof.
  revert s a b; induction p; intros s a b Hequiv Hp;
    pose proof Hequiv as [[Hh [Hb Hk]] Hmarks];
    cbn [persistent_models future_satisfies repaired_interpretation] in *.
  - exact Hp.
  - destruct Hp; [left; eapply IHp1 |right; eapply IHp2]; eauto.
  - destruct Hp; split; [eapply IHp1 |eapply IHp2]; eauto.
  - destruct Hp as [v Hv]; exists v; eapply IHp; eassumption.
  - intros v; eapply IHp; [exact Hequiv |apply Hp].
  - destruct Hp as [Hheap [Hbuffers Hfree]]; split.
    + intros loc; rewrite <- Hh; apply Hheap.
    + split; [intros i; rewrite <- Hb; apply Hbuffers |intros i H; apply (Hfree i),Hk,H].
  - destruct Hp as [[Hheap [Hbuffers Hfree]] Hmark]; split.
    + split; [intros loc; rewrite <- Hh; apply Hheap |].
      split; [intros i; rewrite <- Hb; apply Hbuffers |intros i H; apply (Hfree i),Hk,H].
    + destruct (eval_expr s processor); try exact I.
      destruct Hmark; [left; assumption |right; apply Hmarks; assumption].
  - destruct (eval_expr s processor); try contradiction.
    destruct Hp as [Hheap [Hbuffers [Hi Hheld]]]; split.
    + intros loc; rewrite <- Hh; apply Hheap.
    + split; [intros i; rewrite <- Hb; apply Hbuffers |].
      split; [exact Hi |intros i; rewrite <- Hk; apply Hheld].
  - destruct (eval_expr s address); try contradiction;
      destruct (eval_expr s processor); try contradiction.
    destruct Hp as [Hi [Hpending |Hflushed]]; split; [exact Hi | |exact Hi |].
    + left; destruct Hpending as [Hheap [Hbuffers Hblocks]]; split.
      * intros loc; rewrite <- Hh; apply Hheap.
      * split; [intros i; rewrite <- Hb; apply Hbuffers |intros i H; apply Hblocks,Hk,H].
    + right; destruct Hflushed as [Hheap [Hbuffers [Hfree Hmark]]]; split.
      * intros loc; rewrite <- Hh; apply Hheap.
      * split; [intros i; rewrite <- Hb; apply Hbuffers |].
        split; [intros i H; apply (Hfree i),Hk,H |apply Hmarks,Hmark].
  - destruct Hp as (left & right & Hsp & HP & HQ); exists left,right; split; [|auto].
    eapply assertion_spatial_equiv; [apply assertion_generalized_equiv_refl
      |apply assertion_generalized_equiv_refl |exact Hequiv |exact Hsp].
  - destruct Hp as (left & right & Htm & HP & HQ); exists left,right; split; [|auto].
    eapply assertion_temporal_equiv; [apply assertion_generalized_equiv_refl
      |apply assertion_generalized_equiv_refl |exact Hequiv |exact Htm].
  - intros later Hfuture extension out HP Hsp.
    destruct (assertion_resource_future_equiv _ _ _ _ Hequiv Hfuture) as (earlier & HF & HE).
    apply (Hp earlier HF extension out HP).
    eapply assertion_spatial_equiv; [apply assertion_generalized_equiv_refl
      |apply assertion_generalized_equiv_sym,HE |apply assertion_generalized_equiv_refl |exact Hsp].
  - intros later Hfuture extension out HP Htm.
    destruct (assertion_resource_future_equiv _ _ _ _ Hequiv Hfuture) as (earlier & HF & HE).
    apply (Hp earlier HF extension out HP).
    eapply assertion_temporal_equiv; [apply assertion_generalized_equiv_refl
      |apply assertion_generalized_equiv_sym,HE |apply assertion_generalized_equiv_refl |exact Htm].
  - intros later Hfuture extension out HP Htm.
    destruct (assertion_resource_future_equiv _ _ _ _ Hequiv Hfuture) as (earlier & HF & HE).
    apply (Hp earlier HF extension out HP).
    eapply assertion_temporal_equiv; [apply assertion_generalized_equiv_sym,HE
      |apply assertion_generalized_equiv_refl |apply assertion_generalized_equiv_refl |exact Htm].
Qed.

Theorem persistent_models_mark_extension active p s (a b : resource active) :
  memory_equiv (underlying (proj1_sig a)) (underlying (proj1_sig b)) ->
  (forall i, complete (proj1_sig a) i -> complete (proj1_sig b) i) ->
  persistent_models active s a p -> persistent_models active s b p.
Proof.
  intros Hequiv Hmarks HP.
  assert (Hfuture : generalized_future active (proj1_sig a)
    (Generalized (underlying (proj1_sig a)) (complete (proj1_sig b)))).
  { destruct a as [[m marks] Ha]; cbn in *; apply generalized_future_one,GeneralizedMark;
      [exact Hmarks |exact (proj1 (proj2 (proj2_sig b)))]. }
  pose (marked := exist _ _ (generalized_future_well_formed _ _ _ Hfuture (proj2_sig a)) : resource active).
  apply (persistent_models_resource_equiv active p s marked b).
  - split; [exact Hequiv |intros i; reflexivity].
  - eapply persistent_assertion_flushing_closed; [exact Hfuture |exact HP].
Qed.
