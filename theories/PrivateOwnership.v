From Stdlib Require Import List ZArith.
From WMLR Require Import Expressions Languages Machine BufferRelations Separation RepairedFlushing
  FrameDecomposition OperationalSemantics Assertions AssertionSemantics PersistentAssertions Safety
  OwnershipProtocol OwnershipRules OwnershipHeap.
Import ListNotations.

Lemma memory_spatial_comm a b out : memory_spatial a b out -> memory_spatial b a out.
Proof.
  intros H. assert (Hsp : spatial (Generalized a no_blocked) (Generalized b no_blocked)
    (Generalized out no_blocked)).
  { split; [exact H |intros i; simpl; unfold no_blocked; tauto]. }
  exact (proj1 (spatial_comm _ _ _ Hsp)).
Qed.

Lemma full_spatial_intro active s a b out p q : memory_spatial a b out ->
  persistent_full_satisfies active s a p -> persistent_full_satisfies active s b q ->
  persistent_full_satisfies active s out (A.Spatial p q).
Proof.
  intros Hsep [ra [Ea Ha]] [rb [Eb Hb]].
  assert (Hsp : spatial (proj1_sig ra) (proj1_sig rb) (Generalized out active)).
  { rewrite Ea, Eb. split; [exact Hsep |intros i; simpl; tauto]. }
  exists (exist _ _ (spatial_well_formed _ _ _ _ (proj2_sig ra) (proj2_sig rb) Hsp)).
  split; [reflexivity |]. exists ra, rb. split; [exact Hsp |auto].
Qed.

Lemma full_spatial_elim active s out p q : persistent_full_satisfies active s out (A.Spatial p q) ->
  exists a b, memory_spatial a b out /\ persistent_full_satisfies active s a p /\
    persistent_full_satisfies active s b q.
Proof.
  intros [r [Er [ra [rb [Hsep [Ha Hb]]]]]].
  exists (underlying (proj1_sig ra)), (underlying (proj1_sig rb)).
  change (spatial (proj1_sig ra) (proj1_sig rb) (proj1_sig r)) in Hsep.
  rewrite Er in Hsep. split; [exact (proj1 Hsep) |].
  split; apply persistent_promote_full; assumption.
Qed.

Lemma spatial_free_parts a b out : memory_spatial a b out -> lock_free out -> lock_free a /\ lock_free b.
Proof.
  intros [_ [_ [_ Hk]]] Hfree. split; intros i Hi; apply (Hfree i), Hk; auto.
Qed.

Lemma spatial_empty_buffer_parts a b out i : memory_spatial a b out -> buffers out i = [] ->
  buffers a i = [] /\ buffers b i = [].
Proof.
  intros [_ [_ [Hb _]]] Hempty. specialize (Hb i). rewrite Hempty in Hb; inversion Hb; auto.
Qed.

(** The region is the combined private/protected footprint. Closed retains
    a genuine private local component; Open gives the owner the whole region.
    Assertion grammar and interpretation remain exactly persistent_models. *)
Definition private_region active owner invariant phase s local region : Prop :=
  memory_well_formed active local /\ memory_well_formed active region /\
  match phase with
  | Closed => lock_free region /\ exists pool,
      persistent_full_satisfies active s pool invariant /\ memory_spatial pool local region
  | Open => local = region /\ lock_held active region owner
  end.

Record private_environment active owner invariant phase s local region frame whole : Prop := {
  private_region_ok : private_region active owner invariant phase s local region;
  private_frame_wf : memory_well_formed active frame;
  private_whole_wf : memory_well_formed active whole;
  private_frame_free : lock_free frame;
  private_separation : memory_spatial frame region whole
}.

Lemma private_region_flush active owner invariant phase s local region region' :
  private_region active owner invariant phase s local region -> flush active region region' ->
  exists local', private_region active owner invariant phase s local' region' /\ memory_flushes active local local'.
Proof.
  intros [Hl [Hr Hphase]] Hflush. assert (Hr' : memory_well_formed active region').
  { eapply flush_preserves_well_formed; eassumption. }
  destruct phase.
  - destruct Hphase as [Hfree [pool [Hinv Hsep]]].
    assert (Hfree' : lock_free region') by (inversion Hflush; exact Hfree).
    destruct (spatial_flush_split _ _ _ _ _ Hsep Hflush) as [[pool' [Hp' Hsep']] |[local' [Hl' Hsep']]].
    + exists local. split; [|constructor]. split; [exact Hl |]. split; [exact Hr' |].
      split; [exact Hfree' |]. exists pool'; split; [|exact Hsep'].
      eapply persistent_full_flushing_closed; [econstructor; [exact Hp' |constructor] |exact Hinv].
    + exists local'. split; [|econstructor; [exact Hl' |constructor]].
      split; [eapply flush_preserves_well_formed; eassumption |].
      split; [exact Hr' |]. split; [exact Hfree' |]. exists pool; auto.
  - destruct Hphase as [-> Hheld]. exists region'. split; [|econstructor; [exact Hflush |constructor]].
    split; [exact Hr' |]. split; [exact Hr' |]. split; [reflexivity |inversion Hflush; exact Hheld].
Qed.

Theorem private_environment_flush active owner invariant phase s local region frame whole whole' :
  private_environment active owner invariant phase s local region frame whole -> flush active whole whole' ->
  exists local' region' frame', private_environment active owner invariant phase s local' region' frame' whole' /\
    memory_flushes active local local' /\ memory_flushes active frame frame' /\ domain_included region' region.
Proof.
  intros [Hr Hf Hw Hfree Hsep] Hflush.
  destruct (spatial_flush_split _ _ _ _ _ Hsep Hflush) as [[frame' [Hf' Hsep']] |[region' [Hr' Hsep']]].
  - exists local, region, frame'. split.
    + constructor; try assumption; [eapply flush_preserves_well_formed; eassumption
        |eapply flush_preserves_well_formed; eassumption |inversion Hf'; exact Hfree].
    + split; [constructor |]. split; [econstructor; [exact Hf' |constructor] |intros loc H; exact H].
  - destruct (private_region_flush _ _ _ _ _ _ _ _ Hr Hr') as [local' [Hlocal Hflushlocal]].
    exists local', region', frame. split.
    + constructor; try assumption; eapply flush_preserves_well_formed; eassumption.
    + split; [exact Hflushlocal |]. split; [constructor |exact (flush_domain_subset _ _ _ Hr')].
Qed.

Fixpoint private_safe active owner invariant n command s phase local region finish post : Prop :=
  match n with
  | O => True
  | S remaining =>
    private_region active owner invariant phase s local region /\
    (terminal command -> phase = finish /\ persistent_full_satisfies active s local post) /\
    (forall frame whole, private_environment active owner invariant phase s local region frame whole ->
      ~ abort active command (State s whole)) /\
    (forall frame whole next t whole',
      private_environment active owner invariant phase s local region frame whole ->
      step active command (State s whole) next (State t whole') ->
      exists phase' local' region' frame',
        private_environment active owner invariant phase' t local' region' frame' whole' /\
        memory_flushes active frame frame' /\ domain_included region' region /\
        private_safe active owner invariant remaining next t phase' local' region' finish post)
  end.

Definition private_valid active owner invariant start pre command finish post :=
  forall s local region, private_region active owner invariant start s local region ->
    persistent_full_satisfies active s local pre -> forall n,
    private_safe active owner invariant n command s start local region finish post.

Lemma private_skip_safe active owner invariant n annotation s phase local region post :
  private_region active owner invariant phase s local region -> persistent_full_satisfies active s local post ->
  private_safe active owner invariant n (Concurrent.skip annotation) s phase local region phase post.
Proof.
  revert s local region. induction n; intros s local region Hr Hp; [exact I |].
  split; [exact Hr |]. split; [intros _; auto |]. split.
  - intros frame whole Henv Habort; inversion Habort; subst;
      match goal with H : primitive_abort _ _ _ _ |- _ => inversion H end.
  - intros frame whole next t whole' Henv Hstep; inversion Hstep; subst.
    + match goal with H : primitive_step _ _ _ _ _ |- _ => inversion H end.
    + match goal with H : flush _ _ _ |- _ =>
        destruct (private_environment_flush _ _ _ _ _ _ _ _ _ _ Henv H)
          as [local' [region' [frame' [Henv' [Hlocal [Hframe Hdom]]]]]] end.
      exists phase, local', region', frame'. split; [exact Henv' |]. split; [exact Hframe |].
      split; [exact Hdom |]. apply IHn;
        [exact (private_region_ok _ _ _ _ _ _ _ _ _ Henv') |eapply persistent_full_flushing_closed; eassumption].
Qed.

Lemma private_primitive_rule active owner invariant start pre primitive annotation finish post :
  primitive <> Concurrent.Common Sequential.Skip ->
  (forall s local region frame whole,
    private_environment active owner invariant start s local region frame whole ->
    persistent_full_satisfies active s local pre -> forall i,
    eval_expr s annotation = Z.pos i -> ~ primitive_abort active primitive i (State s whole)) ->
  (forall s local region frame whole,
    private_environment active owner invariant start s local region frame whole ->
    persistent_full_satisfies active s local pre -> forall i t whole',
    eval_expr s annotation = Z.pos i -> primitive_step active primitive i (State s whole) (State t whole') ->
    exists local' region' frame', private_environment active owner invariant finish t local' region' frame' whole' /\
      memory_flushes active frame frame' /\ domain_included region' region /\
      persistent_full_satisfies active t local' post) ->
  private_valid active owner invariant start pre (Concurrent.Prim primitive annotation) finish post.
Proof.
  intros Hnot Hfault Haction s local region Hr Hp n. revert s local region Hr Hp.
  induction n; intros s local region Hr Hp; [exact I |]. split; [exact Hr |].
  split; [intros [ann H]; inversion H; contradiction |]. split.
  - intros frame whole Henv Habort; inversion Habort; subst; eapply Hfault; eassumption.
  - intros frame whole next t whole' Henv Hstep; inversion Hstep; subst.
    + match goal with H : primitive_step _ _ _ _ _ |- _ =>
        destruct (Haction _ _ _ _ _ Henv Hp _ _ _ ltac:(eassumption) H)
          as [local' [region' [frame' [Henv' [Hframe [Hdom Hpost]]]]]] end.
      exists finish, local', region', frame'. split; [exact Henv' |]. split; [exact Hframe |].
      split; [exact Hdom |]. apply private_skip_safe;
        [exact (private_region_ok _ _ _ _ _ _ _ _ _ Henv') |exact Hpost].
    + match goal with H : flush _ _ _ |- _ =>
        destruct (private_environment_flush _ _ _ _ _ _ _ _ _ _ Henv H)
          as [local' [region' [frame' [Henv' [Hlocal [Hframe Hdom]]]]]] end.
      exists start, local', region', frame'. split; [exact Henv' |]. split; [exact Hframe |].
      split; [exact Hdom |]. apply IHn;
        [exact (private_region_ok _ _ _ _ _ _ _ _ _ Henv') |eapply persistent_full_flushing_closed; eassumption].
Qed.
