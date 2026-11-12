From Stdlib Require Import List ZArith Lia.
From WMLR Require Import Expressions Languages Machine BufferRelations Separation OperationalSemantics
  ExecutionExamples Assertions AssertionSemantics PersistentAssertions Safety TemporalSafety
  InvariantFragment PrivateOwnership LockRepresentation OwnedSafety OwnedCalculus OwnedAcceptance
  ExecutionDomain HeapExtension OwnedPointsToRules MessagePassingSyntax MessagePassingResources
  MessagePassingDerivation.
Import ListNotations.

Lemma mp_received_free s local loc r value : s 1 = Z.pos loc ->
  persistent_models two_processors s local (mp_received r value) ->
  lock_free (resource_memory two_processors local).
Proof.
  intros E H; destruct (mp_received_shape _ _ _ _ _ E H) as [[_ Hshape] |[_ Hshape]];
    eapply mp_shape_free; eassumption.
Qed.

Lemma mp_outcome_from_shape s final loc h value : s 0 = value ->
  (value = 0%Z \/ value = 1%Z) -> h loc = Some (value + 1)%Z ->
  memory_equiv final (mp_plain h) ->
  (s 0 = 0%Z \/ s 0 = 1%Z) /\ shared_heap final loc = Some (s 0%nat + 1)%Z /\
  (forall i, buffers final i = []) /\ lock_free final.
Proof.
  intros E HV HH HS; destruct HS as [Hh [Hb Hk]].
  rewrite E; split; [exact HV |split; [rewrite Hh; exact HH |]].
  split; [exact Hb |intros i Hi; apply Hk in Hi; exact Hi].
Qed.

Lemma mp_terminal_extract s local pool final loc t r :
  loc <> t -> loc <> r -> t <> r -> s 1 = Z.pos loc ->
  memory_spatial pool (resource_memory two_processors local) final ->
  persistent_full_satisfies two_processors s pool (mp_invariant t r) ->
  persistent_models two_processors s local (mp_received r 2%Z) ->
  memory_domain final t ->
  (s 0 = 0%Z \/ s 0 = 1%Z) /\ shared_heap final loc = Some (s 0%nat + 1)%Z /\
  (forall i, buffers final i = []) /\ lock_free final.
Proof.
  intros Ht Hr Htr E HS HJ HQ Hdomain.
  destruct (mp_received_shape _ _ _ _ _ E HQ) as [[EV HL] |[EV HL]];
    destruct (mp_invariant_shape _ _ _ _ _ E HJ) as [HP |[HP |HP]].
  - pose proof (mp_spatial_shape _ _ _ _ _ HS HP HL) as HO.
    apply (mp_shape_domain _ _ _ HO) in Hdomain; destruct Hdomain as [v HV].
    unfold heap_override,mp_single,heap_update,empty_heap in HV.
    destruct (Pos.eq_dec t r), (Pos.eq_dec t loc); congruence.
  - eapply mp_outcome_from_shape with (h := heap_override
      (heap_override (mp_single loc 1%Z) (mp_single t 0%Z)) (mp_single r 0%Z));
      [exact EV |left; reflexivity | |eapply mp_spatial_shape; eassumption].
    unfold heap_override,mp_single,heap_update,empty_heap;
      destruct (Pos.eq_dec loc loc), (Pos.eq_dec loc t), (Pos.eq_dec loc r); congruence || reflexivity.
  - exfalso; apply (mp_shapes_disjoint _ _ _ _ _ HS HP HL r).
    + exists 0%Z; unfold mp_tokens,heap_override,mp_single; rewrite heap_update_same; reflexivity.
    + apply mp_single_domain; reflexivity.
  - exfalso; apply (mp_shapes_disjoint _ _ _ _ _ HS HP HL loc); apply mp_single_domain; reflexivity.
  - exfalso; apply (mp_shapes_disjoint _ _ _ _ _ HS HP HL loc).
    + exists 1%Z; unfold heap_override,mp_single; rewrite heap_update_other by exact Ht.
      cbn [empty_heap]; apply heap_update_same.
    + apply mp_single_domain; reflexivity.
  - eapply mp_outcome_from_shape with (h := heap_override (mp_tokens t r) (mp_single loc 2%Z));
      [exact EV |right; reflexivity | |eapply mp_spatial_shape; eassumption].
    unfold heap_override,mp_single; rewrite heap_update_same; reflexivity.
Qed.

Theorem mp_augmented_all_runs s n last u final loc t r :
  loc <> t -> loc <> r -> t <> r -> s 1 = Z.pos loc ->
  execution two_processors n mp_program s (mp_augmented loc t r) last u final ->
  ~ abort two_processors last (State u final) /\
  (terminal last -> (u 0 = 0%Z \/ u 0 = 1%Z) /\
    shared_heap final loc = Some (u 0%nat + 1)%Z /\
    (forall i, buffers final i = []) /\ lock_free final).
Proof.
  intros Ht Hr Htr E HR.
  assert (HP : persistent_models two_processors s (mp_full (mp_tokens t r))
    (A.Spatial (mp_token t) (mp_token r))) by (apply mp_tokens_models,Htr).
  assert (HJ : persistent_full_satisfies two_processors s (mp_initial loc) (mp_invariant t r)).
  { exists (mp_full (mp_single loc 0%Z)); split; [reflexivity |left; apply mp_full_cell,E]. }
  assert (Hfree : lock_free (mp_augmented loc t r)) by (intros i H; exact H).
  destruct (owned_derivation_adequacy two_processors (mp_invariant t r)
    (mp_invariant_fragment t r) acceptance_two_active DisjointMode _ _ _
    (mp_parallel_derived two_processors t r) n s _ last u final
    (mp_full (mp_tokens t r)) (mp_initial loc) HP HJ Hfree
    (mp_augmented_split loc t r Ht Hr) HR) as [Hsafe Hdone].
  split; [exact Hsafe |intros HT].
  assert (Eu : u 1 = Z.pos loc).
  { rewrite <- (execution_preserves_unmodified _ _ _ _ _ _ _ _ HR 1); [exact E |cbn; intuition discriminate]. }
  destruct (Hdone HT) as (local & pool & HS & HQ & [[HK Hpool] |[owner [HK Ep]]]).
  - eapply mp_terminal_extract; [exact Ht |exact Hr |exact Htr |exact Eu |exact HS |exact Hpool |exact HQ |].
    apply (proj2 (execution_preserves_domain _ _ _ _ _ _ _ _ HR t)).
    left; exists 0%Z; unfold mp_augmented,mp_plain,mp_tokens,mp_single,heap_override; cbn [shared_heap].
    rewrite heap_update_other by exact Htr; cbn [empty_heap]; rewrite heap_update_same; reflexivity.
  - exfalso; eapply two_processors_separate_free_held;
      [exact (or_introl eq_refl : two_processors 1%positive)
      |exact (or_intror eq_refl : two_processors 2%positive) |discriminate
      |eapply mp_received_free; [exact Eu |exact HQ] |exact HK].
Qed.

Lemma mp_program_accesses : accesses_only mp_address mp_program.
Proof. repeat split; reflexivity. Qed.

Lemma mp_tokens_fresh loc t r : loc <> t -> loc <> r -> mp_tokens t r loc = None.
Proof.
  intros Ht Hr; unfold mp_tokens,heap_override,mp_single.
  rewrite !heap_update_other by assumption; reflexivity.
Qed.

(** No tokens, auxiliary assignment, altered command or initial result-register
    hypothesis occurs in this theorem. The proof chooses two untouched cells,
    applies the derivation, and erases them from every original execution. *)
Theorem message_passing_all_runs s n last u final loc : s 1 = Z.pos loc ->
  execution two_processors n mp_program s (mp_initial loc) last u final ->
  ~ abort two_processors last (State u final) /\
  (terminal last -> (u 0 = 0%Z \/ u 0 = 1%Z) /\
    (forall address, shared_heap final address = mp_single loc (u 0%nat + 1)%Z address) /\
    (forall i, buffers final i = []) /\ lock_free final).
Proof.
  intros E HR.
  set (t := Pos.succ loc); set (r := Pos.succ t).
  assert (Ht : loc <> t) by (unfold t; lia).
  assert (Hr : loc <> r) by (unfold r,t; lia).
  assert (Htr : t <> r) by (unfold r; lia).
  destruct (execution_heap_extension _ _ _ _ _ _ _ _ HR (mp_tokens t r)
    (mp_augmented loc t r) (mp_augmented_extension loc t r Ht Hr)) as [out [HX HE]].
  destruct (mp_augmented_all_runs _ _ _ _ _ _ _ _ Ht Hr Htr E HX) as [Hsafe Hdone].
  assert (Eu : u 1 = Z.pos loc).
  { rewrite <- (execution_preserves_unmodified _ _ _ _ _ _ _ _ HR 1); [exact E |cbn; intuition discriminate]. }
  split.
  - intros HA; apply Hsafe; eapply (abort_heap_extension two_processors last (State u final)
      HA mp_address (mp_tokens t r) out);
      [eapply execution_accesses_only; [exact HR |exact mp_program_accesses] |exact HE |].
    intros address EA; change (u 1 = Z.pos address) in EA; rewrite Eu in EA; inversion EA; subst.
    apply mp_tokens_fresh; assumption.
  - intros HT; destruct (Hdone HT) as [HV [HH [HB HK]]].
    destruct HE as [EH [EB EK]]; split; [exact HV |].
    split.
    + intros address; destruct (Pos.eq_dec address loc) as [-> |Hne].
      * unfold mp_single; rewrite heap_update_same.
        rewrite EH in HH; unfold heap_override in HH.
        destruct (shared_heap final loc) eqn:HF; [exact HH |].
        rewrite mp_tokens_fresh in HH by assumption; discriminate.
      * unfold mp_single; rewrite heap_update_other by exact Hne.
        destruct (shared_heap final address) eqn:HF; [|reflexivity].
        exfalso; assert (HD : memory_domain final address) by (left; eexists; exact HF).
        apply (execution_preserves_domain _ _ _ _ _ _ _ _ HR address) in HD.
        apply mp_plain_domain,mp_single_domain in HD; contradiction.
    + split; [intros i; rewrite <- EB; apply HB |intros i HI; apply (HK i),(EK i),HI].
Qed.

Corollary message_passing_points_to s n last u final loc : s 1 = Z.pos loc ->
  execution two_processors n mp_program s (mp_initial loc) last u final -> terminal last ->
  persistent_full_satisfies two_processors u final
    (A.And (A.points_to mp_address (EAdd (EVar 0) (EVal 1%Z)))
      (A.Or (A.Pure (mp_guard 0%Z)) (A.Pure (mp_guard 1%Z)))).
Proof.
  intros E HR HT.
  destruct (proj2 (message_passing_all_runs _ _ _ _ _ _ E HR) HT) as [HV [HH [HB HK]]].
  assert (Eu : u 1 = Z.pos loc).
  { rewrite <- (execution_preserves_unmodified _ _ _ _ _ _ _ _ HR 1); [exact E |cbn; intuition discriminate]. }
  assert (Hwf : generalized_well_formed two_processors (Generalized final two_processors)).
  { split; [split; [intros i Hi; exfalso; exact (HK i Hi) |intros; apply HB] |].
    split; [intros i Hi; exact Hi |intros Hnone address; exfalso; exact (Hnone 1%positive (or_introl eq_refl))]. }
  exists (exist _ (Generalized final two_processors) Hwf); split; [reflexivity |split].
  - apply alternative_writer_complete_points_to.
    + eapply writer_points_to_from_shape with (loc := loc) (owner := 1%positive);
        [exact Eu |left; reflexivity |exact HH |exact HB |exact HK |left; reflexivity].
    + intros i; cbn [proj1_sig complete]; unfold two_processors;
        destruct (Pos.eq_dec i 1%positive), (Pos.eq_dec i 2%positive); tauto.
  - destruct HV as [H |H].
    + left; change (Z.eqb (u 0) 0%Z = true); apply Z.eqb_eq,H.
    + right; change (Z.eqb (u 0) 1%Z = true); apply Z.eqb_eq,H.
Qed.
