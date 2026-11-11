From Stdlib Require Import List ZArith.
From WMLR Require Import Expressions Languages Machine BufferRelations Separation
  OperationalSemantics.
Import ListNotations.

Definition domain_included (new old : memory) : Prop :=
  forall loc, memory_domain new loc -> memory_domain old loc.

Lemma buffer_lookup_some_domain b loc v :
  buffer_lookup b loc = Some v -> buffer_domain b loc.
Proof.
  induction b as [|[address contents] rest IH]; simpl; [discriminate |].
  destruct (buffer_lookup rest loc) eqn:Hrest.
  - intros H. destruct (IH H) as [w Hw]. exists w; right; exact Hw.
  - destruct (Pos.eq_dec loc address) as [Heq | Hneq]; [|discriminate].
    subst. intros H; inversion H; subst. exists v; left; reflexivity.
Qed.

Lemma local_read_domain m i loc v :
  local_read m i (Z.pos loc) = Some v -> memory_domain m loc.
Proof.
  unfold local_read. destruct (buffer_lookup (buffers m i) loc) eqn:Hbuffer.
  - intros H. right; exists i. eapply buffer_lookup_some_domain; exact Hbuffer.
  - intros H. left; exists v; exact H.
Qed.

Lemma enqueue_domain_subset m i address contents :
  memory_domain m address -> domain_included (enqueue m i address contents) m.
Proof.
  intros Haddress loc [[v Hheap] | [j [v Hbuffer]]].
  - left; exists v; exact Hheap.
  - cbn [enqueue buffers] in Hbuffer. unfold buffer_update in Hbuffer.
    destruct (Pos.eq_dec j i) as [Heq | Hneq].
    + subst j. apply in_app_iff in Hbuffer. destruct Hbuffer as [Hbuffer | Hbuffer].
      * right; exists i, v; exact Hbuffer.
      * simpl in Hbuffer. destruct Hbuffer as [Hbuffer | Hbuffer]; [|contradiction].
        inversion Hbuffer; subst; exact Haddress.
    + right; exists j, v; exact Hbuffer.
Qed.

Theorem flush_domain_subset active m m' :
  flush active m m' -> domain_included m' m.
Proof.
  intros Hflush. destruct Hflush as [m i address contents rest Hi Hunblocked Hbuffer].
  intros loc [[v Hheap] | [j [v Hrest]]].
  - cbn [flush_write shared_heap] in Hheap. unfold heap_update in Hheap.
    destruct (Pos.eq_dec loc address) as [Heq | Hneq].
    + subst loc. right; exists i, contents. rewrite Hbuffer; left; reflexivity.
    + left; exists v; exact Hheap.
  - cbn [flush_write buffers] in Hrest. unfold buffer_update in Hrest.
    destruct (Pos.eq_dec j i) as [Heq | Hneq].
    + subst j. right; exists i, v. rewrite Hbuffer; right; exact Hrest.
    + right; exists j, v; exact Hrest.
Qed.

Theorem flushes_domain_subset active m m' :
  memory_flushes active m m' -> domain_included m' m.
Proof.
  induction 1; [intros loc Hloc; exact Hloc |].
  intros loc Hloc. apply (flush_domain_subset _ _ _ H), IHmemory_flushes, Hloc.
Qed.

Theorem primitive_domain_subset active p i initial final :
  primitive_step active p i initial final ->
  domain_included (memory_state final) (memory_state initial).
Proof.
  intros Hstep; destruct Hstep; simpl;
    try (intros loc Hloc; exact Hloc).
  apply enqueue_domain_subset. eapply local_read_domain; eassumption.
Qed.

Theorem step_domain_subset active c initial next final :
  step active c initial next final ->
  domain_included (memory_state final) (memory_state initial).
Proof.
  intros Hstep; induction Hstep; simpl; try assumption;
    try (intros loc Hloc; exact Hloc).
  - exact (primitive_domain_subset _ _ _ _ _ H0).
  - exact (flush_domain_subset _ _ _ H).
Qed.

Theorem steps_domain_subset active c initial next final :
  steps active c initial next final ->
  domain_included (memory_state final) (memory_state initial).
Proof.
  induction 1; [intros loc Hloc; exact Hloc |].
  intros loc Hloc. apply (step_domain_subset _ _ _ _ _ H), IHsteps, Hloc.
Qed.

(** A replacement for the invalid arbitrary-redecomposition claim in
    Conjecture 1. Residual footprints must stay within their original owners.
    This hypothesis concerns provenance of locations, not their values. *)
Theorem spatial_frame_recombination active frame local whole frame' local' whole' :
  memory_spatial frame local whole ->
  domain_included frame' frame -> domain_included local' local ->
  memory_spatiotemporal active frame' local' whole' ->
  memory_spatial frame' local' whole'.
Proof.
  intros [[Hdomains _] _] Hframe Hlocal [[Hblocked _] [Hheap [Hbuffers Hblocks]]].
  split; [split |].
  - intros loc Hf Hl. apply (Hdomains loc); [apply Hframe | apply Hlocal]; assumption.
  - exact Hblocked.
  - split; [exact Hheap |]. split; [intros i; exact (proj1 (Hbuffers i)) | exact Hblocks].
Qed.

(** The footprint hypotheses follow from actual execution: this language has
    no allocation, and a store must address a cell in its local view. This
    proves a useful operational form without assuming Conjecture 1. It does
    not yet handle transfer of ownership from a shared invariant. *)
Theorem spatial_frame_recombination_steps active frame local whole frame' local'
    whole' command next s s' :
  memory_spatial frame local whole -> memory_flushes active frame frame' ->
  steps active command (State s local) next (State s' local') ->
  memory_spatiotemporal active frame' local' whole' ->
  memory_spatial frame' local' whole'.
Proof.
  intros Hsep Hflush Hsteps Hpost.
  eapply spatial_frame_recombination; [exact Hsep | | | exact Hpost].
  - exact (flushes_domain_subset _ _ _ Hflush).
  - exact (steps_domain_subset _ _ _ _ _ Hsteps).
Qed.

Lemma memory_spatial_in_spatiotemporal active a b c :
  memory_spatial a b c -> memory_spatiotemporal active a b c.
Proof.
  intros H.
  assert (Hsp : spatial (Generalized a no_blocked) (Generalized b no_blocked)
    (Generalized c no_blocked)).
  { split; [exact H | intros i; simpl; unfold no_blocked; tauto]. }
  exact (proj1 (spatial_in_spatiotemporal active _ _ _ Hsp)).
Qed.

(** Equality of result sets, matching the conclusion needed by the printed
    argument, now with an operational justification for residual ownership. *)
Theorem spatial_frame_recombination_sets active frame local whole frame' local'
    command next s s' :
  memory_spatial frame local whole -> memory_flushes active frame frame' ->
  steps active command (State s local) next (State s' local') ->
  forall out, memory_spatiotemporal active frame' local' out <->
    memory_spatial frame' local' out.
Proof.
  intros Hsep Hflush Hsteps out. split.
  - eapply spatial_frame_recombination_steps; eassumption.
  - apply memory_spatial_in_spatiotemporal.
Qed.

(** A local ownership region may include shared state. If execution of that
    region supplies a residual subresource, the same argument still applies;
    it need not remain within the original private footprint. The remaining
    soundness obligation is to produce this region execution and subresource
    from the global safety step, including lock-mediated ownership transfers. *)
Theorem spatial_frame_recombination_region active frame region whole frame' region'
    local' command next s s' :
  memory_spatial frame region whole -> memory_flushes active frame frame' ->
  steps active command (State s region) next (State s' region') ->
  domain_included local' region' ->
  forall out, memory_spatiotemporal active frame' local' out <->
    memory_spatial frame' local' out.
Proof.
  intros Hsep Hflush Hsteps Hlocal out. split; [intros Hpost | apply memory_spatial_in_spatiotemporal].
  eapply spatial_frame_recombination; [exact Hsep | | | exact Hpost].
  - exact (flushes_domain_subset _ _ _ Hflush).
  - intros loc Hloc. apply (steps_domain_subset _ _ _ _ _ Hsteps), Hlocal, Hloc.
Qed.
