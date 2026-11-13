From Stdlib Require Import List ZArith.
From WMLR Require Import Expressions Languages Machine BufferRelations OrderedBuffers Separation
  StableCompatibility RepairedSeparation GeneralizedFlushing FrameDecomposition
  OperationalSemantics ProgramSteps Assertions AssertionSemantics ConcreteAssertions
  PersistentAssertions Safety RepairedSafety HeapRules TemporalSafety InvariantFragment
  OwnedSafety OwnedResources.
Import ListNotations.

Lemma buffer_lookup_some_domain buffer loc v :
  buffer_lookup buffer loc = Some v -> buffer_domain buffer loc.
Proof.
  revert v; induction buffer as [|[a w] rest IH]; intros v H; [discriminate |].
  cbn in H; destruct (buffer_lookup rest loc) eqn:E.
  - destruct (IH _ eq_refl) as [u Hu]; exists u; right; exact Hu.
  - destruct (Pos.eq_dec loc a); [subst; exists w; left; reflexivity |discriminate].
Qed.

Lemma local_read_some_domain m actor loc v :
  local_read m actor (Z.pos loc) = Some v -> memory_domain m loc.
Proof.
  unfold local_read; destruct (buffer_lookup (buffers m actor) loc) eqn:E; intros H.
  - right; exists actor; eapply buffer_lookup_some_domain; exact E.
  - left; exists v; exact H.
Qed.

Lemma spatial_read_right a b whole actor loc v :
  memory_spatial a b whole -> local_read b actor (Z.pos loc) = Some v ->
  local_read whole actor (Z.pos loc) = Some v.
Proof.
  intros [[Hd Hk] [Hh [Hb Hblocks]]] Hread.
  assert (Hlookup : buffer_lookup (buffers whole actor) loc =
    heap_override (buffer_lookup (buffers a actor)) (buffer_lookup (buffers b actor)) loc).
  { apply interleaves_lookup_disjoint; [apply Hb |].
    intros l Ha Hb'; apply (Hd l); [right; exists actor; exact Ha |right; exists actor; exact Hb']. }
  unfold local_read in *; rewrite Hlookup; unfold heap_override.
  destruct (buffer_lookup (buffers b actor) loc) eqn:E; [exact Hread |].
  assert (Ha : buffer_lookup (buffers a actor) loc = None).
  { apply buffer_lookup_none; intros H; apply (Hd loc); [right; exists actor; exact H |left; exists v; exact Hread]. }
  rewrite Ha, Hh; unfold heap_override; rewrite Hread; reflexivity.
Qed.

Lemma repaired_read_right active a b whole actor loc v :
  active actor -> memory_repaired active a b whole -> local_read b actor (Z.pos loc) = Some v ->
  local_read whole actor (Z.pos loc) = Some v.
Proof.
  intros Hi [Hstable [Hh [Hb Hk]]] Hread.
  unfold local_read in *; rewrite (proj2 (ordered_is_override _ _ _ (Hb actor)) loc).
  unfold heap_override; destruct (buffer_lookup (buffers b actor) loc) eqn:E; [exact Hread |].
  assert (Ha : buffer_lookup (buffers a actor) loc = None).
  { apply buffer_lookup_none; intros H; apply (proj1 (proj2 Hstable) actor Hi loc H); exists v; exact Hread. }
  rewrite Ha, Hh; unfold heap_override; rewrite Hread; reflexivity.
Qed.

Lemma owned_read_preserved active mode invariant s local pool frame whole phase actor loc v :
  active actor -> owned_environment active mode invariant s local pool frame whole phase ->
  local_read (resource_memory active local) actor (Z.pos loc) = Some v ->
  local_read whole actor (Z.pos loc) = Some v.
Proof.
  intros Hi Henv Hread.
  destruct (owned_composition _ _ _ _ _ _ _ _ _ Henv) as (combined & [Hinner _] & Houter).
  eapply spatial_read_right; [exact Houter |]. eapply repaired_read_right; eassumption.
Qed.

Lemma write_atom_read active actor loc v g :
  write_atom active (Z.pos loc) (Z.pos actor) v g ->
  local_read (underlying g) actor (Z.pos loc) = Some v.
Proof.
  intros [Hi [[Hh [Hb Hk]] |[Hh [Hb [Hk Hmark]]]]]; unfold local_read.
  - rewrite Hb, buffer_update_same; cbn [buffer_lookup]; destruct (Pos.eq_dec loc loc); congruence.
  - rewrite Hb, Hh; apply heap_update_same.
Qed.

Lemma write_atom_foreign_empty active actor loc v g :
  write_atom active (Z.pos loc) (Z.pos actor) v g ->
  forall other, other <> actor -> ~ buffer_domain (buffers (underlying g) other) loc.
Proof.
  intros [Hi [[Hh [Hb Hk]] |[Hh [Hb [Hk Hmark]]]]] other Hne [w Hw]; rewrite Hb in Hw.
  - rewrite buffer_update_other in Hw by exact Hne; contradiction.
  - contradiction.
Qed.

Lemma spatial_foreign_empty a b whole actor loc :
  memory_spatial a b whole -> memory_domain a loc ->
  (forall other, other <> actor -> ~ buffer_domain (buffers a other) loc) ->
  forall other, other <> actor -> ~ buffer_domain (buffers whole other) loc.
Proof.
  intros [[Hd Hk] [Hh [Hb Hblocks]]] Ha Hforeign other Hne [w Hw].
  apply (interleaves_in _ _ _ _ (Hb other)) in Hw; destruct Hw as [Hw |Hw].
  - apply (Hforeign other Hne); exists w; exact Hw.
  - apply (Hd loc Ha); right; exists other, w; exact Hw.
Qed.

(** Enqueue is local even when allocation is witnessed only by a pending
    write in the issuing buffer, rather than by a heap cell. *)
Lemma repaired_enqueue_read_right active frame local whole actor loc old v :
  active actor -> memory_repaired active frame local whole ->
  local_read local actor (Z.pos loc) = Some old ->
  memory_repaired active frame (enqueue local actor loc v) (enqueue whole actor loc v).
Proof.
  intros Hi [Hstable [Hh [Hb Hk]]] Hread.
  assert (Hforeign : forall other, active other -> other <> actor ->
    ~ buffer_domain (buffers frame other) loc).
  { intros other Ho Hne HF; unfold local_read in Hread.
    destruct (buffer_lookup (buffers local actor) loc) eqn:E.
    - apply (proj2 (proj2 Hstable) other actor Ho Hi Hne loc HF).
      eapply buffer_lookup_some_domain; exact E.
    - apply (proj1 (proj2 Hstable) other Ho loc HF); exists old; exact Hread. }
  split.
  - destruct Hstable as [Hblocks [Hheap Hbuffers]]. split; [exact Hblocks |]. split; [exact Hheap |].
    intros i j Hia Hja Hne address HF [w Hw]; cbn [enqueue buffers] in Hw.
    unfold buffer_update in Hw; destruct (Pos.eq_dec j actor) as [-> |Hother].
    + apply in_app_iff in Hw; destruct Hw as [Hw |[E |Hfalse]]; [| |contradiction].
      * apply (Hbuffers i actor Hia Hja Hne address HF); exists w; exact Hw.
      * inversion E; subst; exact (Hforeign i Hia Hne HF).
    + apply (Hbuffers i j Hia Hja Hne address HF); exists w; exact Hw.
  - split; [exact Hh |]. split; [|exact Hk]. intros i; cbn [enqueue buffers]; unfold buffer_update.
    destruct (Pos.eq_dec i actor) as [-> |Hne]; [apply ordered_append_future, Hb |apply Hb].
Qed.

Lemma owned_environment_enqueue_read active mode invariant s local pool frame whole phase actor loc old v
    (Hi : active actor) :
  owned_environment active mode invariant s local pool frame whole phase ->
  local_read (resource_memory active local) actor (Z.pos loc) = Some old ->
  owned_environment active mode invariant s (owned_enqueue_resource active local actor loc v Hi)
    pool frame (enqueue whole actor loc v) phase.
Proof.
  intros [Hp Hw [combined [[Hinner Hmarks] Houter]] Hmode Hstatus] Hread.
  pose proof (local_read_some_domain _ _ _ _ Hread) as Hdomain.
  constructor; [exact Hp |apply update_buffers_well_formed; assumption | | |exact Hstatus].
  - exists (owned_enqueue_resource active combined actor loc v Hi); split.
    + split; [eapply repaired_enqueue_read_right; eassumption |exact Hmarks].
    + apply spatial_enqueue_right; [exact Houter |].
      exact (local_read_some_domain _ _ _ _ (repaired_read_right _ _ _ _ _ _ _ Hi Hinner Hread)).
  - destruct mode; [exact I |]. intros address HF HL; apply (Hmode address HF).
    exact (enqueue_domain_subset (resource_memory active local) actor loc v Hdomain address HL).
Qed.

Lemma owned_enqueue_read_update active phase local pool actor loc old v (Hi : active actor) :
  local_read (resource_memory active local) actor (Z.pos loc) = Some old ->
  owned_update active OrdinaryAction phase phase local pool
    (owned_enqueue_resource active local actor loc v Hi) pool.
Proof.
  intros Hread; constructor.
  - split; [reflexivity |]. split; [reflexivity |intros; reflexivity].
  - intros address [HP |HL]; [left; exact HP |right].
    eapply enqueue_domain_subset; [eapply local_read_some_domain; exact Hread |exact HL].
  - intros i H; left; exact H.
Qed.

Lemma owned_enqueue_temporal_post active s local pre actor loc v (Hi : active actor) :
  persistent_models active s local pre ->
  (forall other, other <> actor -> ~ buffer_domain (buffers (resource_memory active local) other) loc) ->
  persistent_models active s (owned_enqueue_resource active local actor loc v Hi)
    (A.Temporal pre (A.LeadsTo (EVal (Z.pos loc)) (EVal (Z.pos actor)) (EVal v))).
Proof.
  intros HP Hforeign; exists local, (pending_write_resource active actor loc v Hi); split.
  - assert (Hstable : stable_compatible active (resource_memory active local) (pending_write_memory actor loc v)).
    { split; [intros i _ H; exact H |]. split.
      - intros i _ address _ [w H]; discriminate.
      - intros i j Hia Hja Hne address HL [w Hw].
        change (In (address,w) (buffer_update empty_buffers actor [(loc,v)] j)) in Hw.
        unfold buffer_update in Hw; destruct (Pos.eq_dec j actor) as [-> |Hother]; [|contradiction].
        destruct Hw as [E |Hfalse]; [inversion E; subst; exact (Hforeign i Hne HL) |contradiction]. }
    split; [exact Hstable |]. split.
    + split; [apply stable_implies_original_compatible, Hstable |].
      split; [intros; reflexivity |]. split.
      * intros i; cbn [owned_enqueue_resource pending_write_resource proj1_sig underlying enqueue buffers pending_write_memory].
        unfold buffer_update; destruct (Pos.eq_dec i actor) as [-> |Hne]; [reflexivity |rewrite app_nil_r; reflexivity].
      * intros i; cbn; unfold no_blocked; tauto.
    + split; [intros i H; contradiction |]. intros i; cbn; unfold no_blocked; tauto.
  - split; [exact HP |]. split; [exact Hi |left].
    split; [intros; reflexivity |]. split; [intros; reflexivity |intros i H; contradiction].
Qed.
