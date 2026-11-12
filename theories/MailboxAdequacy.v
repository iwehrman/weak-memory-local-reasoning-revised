From Stdlib Require Import List ZArith.
From WMLR Require Import Expressions Languages Machine BufferRelations Separation OperationalSemantics
  Assertions AssertionSemantics ConcreteAssertions PersistentAssertions Safety TemporalSafety
  InvariantFragment OwnedSafety OwnedCalculus AssertionDerivation AssertionSoundness OwnedAssertionRules
  CellFamilies RegionRules NamedLockSyntax MailboxSyntax MailboxDerivation.
Import ListNotations.

Definition mailbox_active (i : processor) := i = 1%positive \/ i = 2%positive \/ i = 3%positive.
Definition mailbox_foreign loc := A.LeadsTo (EVal (Z.pos loc)) (EVal 3%Z) (EVal 17%Z).
Definition mailbox_foreign_buffers loc := buffer_update empty_buffers 3%positive [(loc,17%Z)].
Definition mailbox_pool_memory := cell_memory [(1%positive,0%Z);(2%positive,0%Z)].
Definition mailbox_local_memory items foreign := Memory (cell_heap (zero_items items))
  (mailbox_foreign_buffers foreign) no_blocked.
Definition mailbox_initial items foreign := Memory
  (heap_override (shared_heap mailbox_pool_memory) (cell_heap (zero_items items)))
  (mailbox_foreign_buffers foreign) no_blocked.

Lemma mailbox_two_active : two_active_processors mailbox_active.
Proof. exists 1%positive,2%positive; split; [left; reflexivity |split; [right; left; reflexivity |discriminate]]. Qed.

Lemma zero_items_addresses items : map fst (zero_items items) = map fst items.
Proof.
  induction items as [|[loc value] rest IH]; [reflexivity |].
  change (loc :: map fst (zero_items rest) = loc :: map fst rest); rewrite IH; reflexivity.
Qed.

Definition mailbox_local_resource (items : list (location * Z)) (foreign : location) : resource mailbox_active.
Proof.
  refine (exist _ (Generalized (mailbox_local_memory items foreign) mailbox_active) _).
  split.
  - split; [intros i H; contradiction |intros i Hi].
    change (buffer_update empty_buffers 3%positive [(foreign,17%Z)] i = []); unfold buffer_update.
    destruct (Pos.eq_dec i 3%positive); [subst i; exfalso; apply Hi; right; right; reflexivity |reflexivity].
  - split; [intros i H; exact H |intros Hnone loc; exfalso; apply (Hnone 1%positive); left; reflexivity].
Defined.

Definition mailbox_pending_resource (foreign : location) : resource mailbox_active.
Proof.
  refine (exist _ (Generalized (Memory empty_heap (mailbox_foreign_buffers foreign) no_blocked) no_blocked) _).
  split.
  - split; [intros i H; contradiction |intros i Hi].
    change (buffer_update empty_buffers 3%positive [(foreign,17%Z)] i = []); unfold buffer_update.
    destruct (Pos.eq_dec i 3%positive); [subst i; exfalso; apply Hi; right; right; reflexivity |reflexivity].
  - split; [intros i H; contradiction |intros; reflexivity].
Defined.

Lemma mailbox_pending_domain foreign loc : memory_domain (resource_memory mailbox_active (mailbox_pending_resource foreign)) loc -> loc = foreign.
Proof.
  intros [[v H] |[i [v H]]]; [discriminate |].
  change (In (loc,v) (buffer_update empty_buffers 3%positive [(foreign,17%Z)] i)) in H.
  unfold buffer_update in H; destruct (Pos.eq_dec i 3%positive); [|contradiction].
  destruct H as [H |H]; [inversion H; reflexivity |contradiction].
Qed.

Lemma mailbox_local_models s items foreign : NoDup (map fst items) -> ~ In foreign (map fst items) ->
  persistent_models mailbox_active s (mailbox_local_resource items foreign)
    (A.Spatial (mailbox_foreign foreign) (cell_family (zero_items items))).
Proof.
  intros Hnd HF; exists (mailbox_pending_resource foreign),
    (cell_resource mailbox_active 1%positive (or_introl eq_refl) (zero_items items)); split.
  - split.
    + split.
      * split; [|intros i H _; exact H]. intros loc HP HC; apply mailbox_pending_domain in HP; subst loc.
        apply cell_memory_domain in HC; rewrite zero_items_addresses in HC; contradiction.
      * split.
        -- intros loc; change (cell_heap (zero_items items) loc = heap_override empty_heap (cell_heap (zero_items items)) loc).
           unfold heap_override; destruct (cell_heap (zero_items items) loc); reflexivity.
        -- split.
           ++ intros i; change (interleaves (mailbox_foreign_buffers foreign i) [] (mailbox_foreign_buffers foreign i)).
              unfold mailbox_foreign_buffers,buffer_update; destruct (Pos.eq_dec i 3%positive); repeat constructor.
           ++ intros i; cbn; unfold no_blocked; tauto.
    + intros i; cbn; unfold no_blocked; tauto.
  - split.
    + split; [right; right; reflexivity |left].
      split; [intros; reflexivity |split; [intros; reflexivity |intros i H; contradiction]].
    + apply cell_family_models; rewrite zero_items_addresses; exact Hnd.
Qed.

Lemma mailbox_pool_initial_assertion active items : assertion_derivation active
  (cell_family [(1%positive,0%Z);(2%positive,0%Z)]) (nl_pool (mailbox_locks items)).
Proof.
  eapply AssertTrans; [apply (AssertAssociative active SepSpatial Backward) |].
  apply (AssertSeparateMono active SepSpatial); [|apply AssertRefl].
  eapply AssertTrans; [apply (AssertSeparateMono active SepSpatial); [apply AssertRefl |apply AssertOrLeft] |apply AssertOrLeft].
Qed.

Lemma mailbox_pool_initial_models s items :
  persistent_full_satisfies mailbox_active s mailbox_pool_memory (nl_pool (mailbox_locks items)).
Proof.
  exists (cell_resource mailbox_active 1%positive (or_introl eq_refl) [(1%positive,0%Z);(2%positive,0%Z)]).
  split; [reflexivity |].
  apply (assertion_derivation_sound _ _ _ (mailbox_pool_initial_assertion mailbox_active items)).
  apply cell_family_models; repeat constructor; cbn; intuition discriminate.
Qed.

Lemma mailbox_initial_split items foreign :
  ~ In 1%positive (map fst items) -> ~ In 2%positive (map fst items) ->
  foreign <> 1%positive -> foreign <> 2%positive ->
  memory_spatial mailbox_pool_memory (mailbox_local_memory items foreign) (mailbox_initial items foreign).
Proof.
  intros H1 H2 HF1 HF2; split.
  - split; [|intros i H _; exact H]. intros loc HP HL; apply cell_memory_domain in HP.
    cbn in HP; destruct HP as [<- |[<- |H]]; [| |contradiction];
      destruct HL as [[v HH] |[i [v HB]]].
    + apply H1; rewrite <- zero_items_addresses; apply cell_heap_domain; exists v; exact HH.
    + assert (E : 1%positive = foreign).
      { apply mailbox_pending_domain; right; exists i,v; exact HB. } congruence.
    + apply H2; rewrite <- zero_items_addresses; apply cell_heap_domain; exists v; exact HH.
    + assert (E : 2%positive = foreign).
      { apply mailbox_pending_domain; right; exists i,v; exact HB. } congruence.
  - split; [intros; reflexivity |split; [intros i; apply interleaves_app |intros i; cbn; unfold no_blocked; tauto]].
Qed.

Theorem mailbox_framed_derived items foreign : owned_derivation mailbox_active (nl_pool (mailbox_locks items)) DisjointMode
  (A.Spatial (mailbox_foreign foreign) (cell_family (zero_items items))) (mailbox_program items)
  (A.Spatial (mailbox_foreign foreign) (cell_family items)).
Proof. apply OwnedFrameSP; [apply mailbox_parallel_derived |intros x HM HF; exact HF]. Qed.

(** The physical initial heap has the two flags and the zero-filled region.
    The third processor's unrelated write is already buffered. The list
    parameter is arbitrary, including the empty region. *)
Theorem mailbox_all_runs items foreign s n last t final :
  NoDup (1%positive :: 2%positive :: foreign :: map fst items) ->
  execution mailbox_active n (mailbox_program items) s (mailbox_initial items foreign) last t final ->
  ~ abort mailbox_active last (State t final) /\
  (terminal last -> exists local pool,
    memory_spatial pool (resource_memory mailbox_active local) final /\
    persistent_models mailbox_active t local (A.Spatial (mailbox_foreign foreign) (cell_family items)) /\
    lock_free final /\ persistent_full_satisfies mailbox_active t pool (nl_pool (mailbox_locks items))).
Proof.
  intros Hnd HR; inversion Hnd as [|a aa H1 Hnd1]; subst.
  inversion Hnd1 as [|b bb H2 Hnd2]; subst; inversion Hnd2 as [|f ff HF Hitems]; subst.
  assert (HS : memory_spatial mailbox_pool_memory (mailbox_local_memory items foreign) (mailbox_initial items foreign)).
  { apply mailbox_initial_split; cbn in H1,H2; intuition congruence. }
  assert (Hfree : lock_free (mailbox_initial items foreign)) by (intros i H; exact H).
  destruct (owned_derivation_adequacy mailbox_active (nl_pool (mailbox_locks items))
    (mailbox_pool_fragment items) mailbox_two_active DisjointMode _ _ _ (mailbox_framed_derived items foreign)
    n s _ last t final (mailbox_local_resource items foreign) mailbox_pool_memory
    (mailbox_local_models s items foreign Hitems HF) (mailbox_pool_initial_models s items) Hfree HS HR)
    as [Hsafe Hdone].
  split; [exact Hsafe |intros HT].
  destruct (Hdone HT) as (local & pool & Hsplit & HQ & [[HK HJ] |[owner [[Hi Hheld] Ep]]]).
  - exists local,pool; auto.
  - exfalso; assert (Honly : forall i, blocked (resource_memory mailbox_active local) i -> i = 3%positive).
    { destruct HQ as (fr & cells & [[HD [Hh [Hb Hk]]] HM] & HW & HC).
      destruct (invariant_fragment_shape _ (cell_family_fragment items) _ _ _ HC) as [Hbuf Hfreecells].
      intros i HB; apply Hk in HB; destruct HB as [HB |HB]; [|exfalso; exact (Hfreecells i HB)].
      destruct HW as [Hactive [[Hheap [Hbuffers Hblocked]] |[Hheap [Hbuffers [Hfreeforeign Hmarks]]]]].
      - apply Hblocked,HB.
      - exfalso; exact (Hfreeforeign i HB). }
    destruct Hi as [-> |[-> | ->]].
    + assert (E : 2%positive = 3%positive) by (apply Honly,Hheld; split; [right; left; reflexivity |discriminate]); discriminate.
    + assert (E : 1%positive = 3%positive) by (apply Honly,Hheld; split; [left; reflexivity |discriminate]); discriminate.
    + assert (E : 1%positive = 3%positive) by (apply Honly,Hheld; split; [left; reflexivity |discriminate]); discriminate.
Qed.
