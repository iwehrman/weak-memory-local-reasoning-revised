From Stdlib Require Import List ZArith.
From WMLR Require Import Expressions Languages Machine BufferRelations Separation
  RepairedSeparation FrameDecomposition RepairedFlushing GeneralizedFlushing
  OperationalSemantics Assertions AssertionSemantics ConcreteAssertions
  PersistentAssertions Safety RepairedSafety PersistentRules HeapRules LockRules.
Import ListNotations.

(** A first ownership protocol, with spatial external frames and no private
    payload carried across the closed boundary. The assertion grammar AND its
    interpretation are unchanged. The phase is an index of specifications.
    In Closed the region is the shared pool; in Open it is owned by [owner].
    There is no second, unconstrained shared fragment in the Open case. *)
Inductive ownership_phase := Closed | Open.

Definition protocol_region active owner invariant phase s region : Prop :=
  memory_well_formed active region /\
  match phase with
  | Closed => lock_free region /\ persistent_full_satisfies active s region invariant
  | Open => lock_held active region owner
  end.

Definition visible_memory phase region :=
  match phase with Closed => empty_memory | Open => region end.

Definition protocol_assertion active phase s region p :=
  persistent_full_satisfies active s (visible_memory phase region) p.

Record protocol_environment active owner invariant phase s region frame whole : Prop := {
  protocol_region_ok : protocol_region active owner invariant phase s region;
  protocol_frame_wf : memory_well_formed active frame;
  protocol_whole_wf : memory_well_formed active whole;
  protocol_frame_free : lock_free frame;
  protocol_separation : memory_spatial frame region whole
}.

Lemma protocol_empty_satisfies active s : persistent_full_satisfies active s empty_memory A.Emp.
Proof.
  assert (Hwf : generalized_well_formed active (Generalized empty_memory active)).
  { split; [exact (proj1 (empty_generalized_well_formed active)) |].
    split; [auto |intros; reflexivity]. }
  exists (exist _ _ Hwf). split; [reflexivity |].
  split; [intros; reflexivity |]. split; [intros; reflexivity |intros i H; exact H].
Qed.

Lemma persistent_promote_full active s (r : resource active) p :
  persistent_models active s r p ->
  persistent_full_satisfies active s (underlying (proj1_sig r)) p.
Proof.
  intros Hp. assert (Hfuture : generalized_future active (proj1_sig r)
    (Generalized (underlying (proj1_sig r)) active)).
  { destruct r as [[m marks] [Hwf [Hactive Hheap]]]; simpl.
    apply generalized_future_one, GeneralizedMark; assumption || auto. }
  exists (exist _ _ (generalized_future_well_formed _ _ _ Hfuture (proj2_sig r))).
  split; [reflexivity |]. eapply persistent_assertion_flushing_closed; eassumption.
Qed.

Lemma protocol_spatial_reblock frame region whole blocks :
  lock_free frame -> memory_spatial frame region whole ->
  memory_spatial frame (reblock region blocks) (reblock whole blocks).
Proof.
  intros Hfree [[Hd Hk] [Hh [Hb Hblocks]]]. split.
  - split; [exact Hd |intros i H _; apply (Hfree i H)].
  - split; [exact Hh |]. split; [exact Hb |].
    intros i; cbn [reblock blocked]; split; [auto |intros [H |H]; [exfalso; apply (Hfree i H) |exact H]].
Qed.

Lemma protocol_spatial_equiv_right frame a b whole :
  memory_equiv a b -> memory_spatial frame a whole -> memory_spatial frame b whole.
Proof.
  intros [Eh [Eb Ek]] [[Hd Hk] [Hh [Hb Hblocks]]]. split.
  - split.
    + intros loc Hf [Hb' |[i Hb']]; apply (Hd loc Hf).
      * left. unfold heap_domain in *; rewrite Eh; exact Hb'.
      * right; exists i. rewrite Eb; exact Hb'.
    + intros i Hf Hb'. apply (Hk i Hf), Ek, Hb'.
  - split.
    + intros loc; rewrite Hh; unfold heap_override; rewrite Eh; reflexivity.
    + split; [intros i; rewrite <- Eb; apply Hb |intros i; rewrite Hblocks, Ek; reflexivity].
Qed.

Lemma protocol_spatial_domain_right frame region whole loc :
  memory_spatial frame region whole -> memory_domain region loc -> memory_domain whole loc.
Proof.
  intros [[Hd Hk] [Hh [Hb Hblocks]]] [[v Hv] |[i [v Hv]]].
  - left; exists v; rewrite Hh; unfold heap_override; rewrite Hv; reflexivity.
  - right; exists i, v. apply (proj2 (interleaves_in _ _ _ _ (Hb i))); right; exact Hv.
Qed.

Lemma protocol_region_flush active owner invariant phase s region region' :
  protocol_region active owner invariant phase s region -> memory_flushes active region region' ->
  protocol_region active owner invariant phase s region'.
Proof.
  intros Hr Hflush. revert Hr. induction Hflush; intros Hr; [exact Hr |].
  apply IHHflush. destruct Hr as [Hwf Hphase]. split.
  - eapply flush_preserves_well_formed; eassumption.
  - destruct phase; simpl in *.
    + destruct Hphase as [Hfree Hinv]. split.
      * inversion H; exact Hfree.
      * eapply persistent_full_flushing_closed; [econstructor; [exact H |constructor] |exact Hinv].
    + inversion H; exact Hphase.
Qed.

Lemma protocol_assertion_flush active phase s region region' p :
  memory_flushes active region region' -> protocol_assertion active phase s region p ->
  protocol_assertion active phase s region' p.
Proof.
  destruct phase; [intros _ H; exact H |].
  apply persistent_full_flushing_closed.
Qed.

Theorem protocol_environment_flush active owner invariant phase s region frame whole whole' :
  protocol_environment active owner invariant phase s region frame whole -> flush active whole whole' ->
  exists region' frame', protocol_environment active owner invariant phase s region' frame' whole' /\
    memory_flushes active region region' /\ memory_flushes active frame frame' /\ domain_included region' region.
Proof.
  intros [Hr Hf Hw Hfree Hsep] Hflush.
  destruct (spatial_flush_split _ _ _ _ _ Hsep Hflush) as [[frame' [Hf' Hsep']] |[region' [Hr' Hsep']]].
  - exists region, frame'. split.
    + constructor; try assumption.
      * eapply flush_preserves_well_formed; eassumption.
      * eapply flush_preserves_well_formed; eassumption.
      * inversion Hf'; exact Hfree.
    + split; [constructor |]. split; [econstructor; [exact Hf' |constructor] |intros loc H; exact H].
  - exists region', frame. split.
    + constructor; try assumption.
      * eapply protocol_region_flush; [exact Hr |econstructor; [exact Hr' |constructor]].
      * eapply flush_preserves_well_formed; eassumption.
    + split; [econstructor; [exact Hr' |constructor] |].
      split; [constructor |apply (flush_domain_subset _ _ _ Hr')].
Qed.

(** Safety quantifies over actual machine steps, including ALL flushes.
    Phase transitions are proof witnesses, not guards added to execution. *)
Fixpoint protocol_safe active owner invariant n command s phase region finish post : Prop :=
  match n with
  | O => True
  | S remaining =>
    protocol_region active owner invariant phase s region /\
    (terminal command -> phase = finish /\ protocol_assertion active phase s region post) /\
    (forall frame whole, protocol_environment active owner invariant phase s region frame whole ->
      ~ abort active command (State s whole)) /\
    (forall frame whole next t whole',
      protocol_environment active owner invariant phase s region frame whole ->
      step active command (State s whole) next (State t whole') ->
      exists phase' region' frame',
        protocol_environment active owner invariant phase' t region' frame' whole' /\
        memory_flushes active frame frame' /\ domain_included region' region /\
        protocol_safe active owner invariant remaining next t phase' region' finish post)
  end.

Definition protocol_valid active owner invariant start pre command finish post :=
  forall s region, protocol_region active owner invariant start s region ->
    protocol_assertion active start s region pre -> forall n,
    protocol_safe active owner invariant n command s start region finish post.

Lemma protocol_skip_safe active owner invariant n annotation s phase region post :
  protocol_region active owner invariant phase s region -> protocol_assertion active phase s region post ->
  protocol_safe active owner invariant n (Concurrent.skip annotation) s phase region phase post.
Proof.
  revert s region. induction n; intros s region Hr Hp; [exact I |].
  split; [exact Hr |]. split; [intros _; auto |]. split.
  - intros frame whole Henv Habort; inversion Habort; subst;
      match goal with H : primitive_abort _ _ _ _ |- _ => inversion H end.
  - intros frame whole next t whole' Henv Hstep. inversion Hstep; subst.
    + match goal with H : primitive_step _ _ _ _ _ |- _ => inversion H end.
    + match goal with H : flush _ _ _ |- _ =>
        destruct (protocol_environment_flush _ _ _ _ _ _ _ _ _ Henv H)
          as [region' [frame' [Henv' [Hregion [Hframe Hdom]]]]] end.
      exists phase, region', frame'. split; [exact Henv' |]. split; [exact Hframe |].
      split; [exact Hdom |]. apply IHn.
      * exact (protocol_region_ok _ _ _ _ _ _ _ _ Henv').
      * eapply protocol_assertion_flush; eassumption.
Qed.

Lemma protocol_primitive_rule active owner invariant start pre primitive annotation finish post :
  primitive <> Concurrent.Common Sequential.Skip ->
  (forall s region frame whole,
    protocol_environment active owner invariant start s region frame whole ->
    protocol_assertion active start s region pre -> forall i,
    eval_expr s annotation = Z.pos i -> ~ primitive_abort active primitive i (State s whole)) ->
  (forall s region frame whole,
    protocol_environment active owner invariant start s region frame whole ->
    protocol_assertion active start s region pre -> forall i t whole',
    eval_expr s annotation = Z.pos i -> primitive_step active primitive i (State s whole) (State t whole') ->
    exists region' frame', protocol_environment active owner invariant finish t region' frame' whole' /\
      memory_flushes active frame frame' /\ domain_included region' region /\
      protocol_assertion active finish t region' post) ->
  protocol_valid active owner invariant start pre (Concurrent.Prim primitive annotation) finish post.
Proof.
  intros Hnot Hfault Haction s region Hr Hp n. revert s region Hr Hp.
  induction n; intros s region Hr Hp; [exact I |]. split; [exact Hr |].
  split; [intros [ann H]; inversion H; contradiction |]. split.
  - intros frame whole Henv Habort; inversion Habort; subst; eapply Hfault; eassumption.
  - intros frame whole next t whole' Henv Hstep; inversion Hstep; subst.
    + match goal with H : primitive_step _ _ _ _ _ |- _ =>
        destruct (Haction _ _ _ _ Henv Hp _ _ _ ltac:(eassumption) H)
          as [region' [frame' [Henv' [Hframe [Hdom Hpost]]]]] end.
      exists finish, region', frame'. split; [exact Henv' |]. split; [exact Hframe |].
      split; [exact Hdom |]. apply protocol_skip_safe;
        [exact (protocol_region_ok _ _ _ _ _ _ _ _ Henv') |exact Hpost].
    + match goal with H : flush _ _ _ |- _ =>
        destruct (protocol_environment_flush _ _ _ _ _ _ _ _ _ Henv H)
          as [region' [frame' [Henv' [Hregion [Hframe Hdom]]]]] end.
      exists start, region', frame'. split; [exact Henv' |]. split; [exact Hframe |].
      split; [exact Hdom |]. apply IHn;
        [exact (protocol_region_ok _ _ _ _ _ _ _ _ Henv') |eapply protocol_assertion_flush; eassumption].
Qed.
