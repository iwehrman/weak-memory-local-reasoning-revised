From Stdlib Require Import List ZArith.
From WMLR Require Import Expressions Languages Machine BufferRelations OrderedBuffers Separation
  RepairedSeparation GeneralizedFlushing OperationalSemantics ProgramSteps ExecutionExamples
  Assertions AssertionSemantics ConcreteAssertions PersistentAssertions PersistentRules Specifications
  Safety TemporalSafety RegionalResources InvariantFragment InvariantFragmentExamples LockRepresentation
  OwnedSafety OwnedAdequacy OwnedHeap OwnedResources OwnedRules OwnedAcceptance OwnedCalculus OwnedDerivedRules
  OwnedAssertionRules OwnedClientRules OwnedContainerEntailments OwnedContainerTrace
  StrongTemporalCounterexample AssertionDerivation AssertionSoundness AssertionDerivedRules AssertionRearrangements
  AssertionCellAlgebra AssertionClientRules OwnershipProtocol DaringExtension.
Import ListNotations.

Definition daring_cell := writer_points_to (EVal 2%Z) (EVal 0%Z).
Definition daring_other := writer_points_to (EVal 3%Z) (EVal 0%Z).
Definition daring_history := A.Temporal daring_cell (A.LeadsTo (EVal 2%Z) (EVal 1%Z) (EVal 5%Z)).
Definition daring_token := A.Lock (EVal 1%Z).
Definition daring_held := A.Spatial daring_token daring_history.
Definition daring_zero := A.Pure (BEq (EVar 0) (EVal 0%Z)).
Definition daring_load := load_command 1%positive 2%positive 0.
Definition daring_store := store_command 1%positive 2%positive 5%Z.
Definition daring_program := C.Seq (C.Seq acceptance_acquire daring_store) daring_load.

Lemma daring_cell_closed x : ~ In x (A.fv daring_cell).
Proof. cbn [daring_cell writer_points_to A.fv expr_fv fresh]; tauto. Qed.

Lemma daring_cell_domain s r : persistent_models two_processors s r daring_cell ->
  memory_domain (resource_memory two_processors r) 2%positive.
Proof.
  intros H; destruct (writer_points_to_shape _ _ _ _ _ H)
    as (loc & owner & E & Hi & Hheap & Hrest).
  inversion E; subst loc; left; exists 0%Z; rewrite Hheap; reflexivity.
Qed.

Lemma daring_history_domain s r : persistent_models two_processors s r daring_history ->
  memory_domain (resource_memory two_processors r) 2%positive.
Proof.
  intros (a & b & Htm & HC & HW).
  apply (temporal_memory_domain _ _ _ _ Htm); left.
  eapply daring_cell_domain; exact HC.
Qed.

Lemma daring_held_domain s r : persistent_models two_processors s r daring_held ->
  memory_domain (resource_memory two_processors r) 2%positive.
Proof.
  intros (a & b & Hsp & HL & HH).
  eapply protocol_spatial_domain_right; [exact (proj1 Hsp) |eapply daring_history_domain; exact HH].
Qed.

Lemma daring_duplicate_false :
  persistent_entails two_processors (A.Spatial daring_cell daring_held) (A.Pure BFalse).
Proof.
  intros s r (a & b & [[[Hdis _] _] _] & HC & HH); exfalso.
  apply (Hdis 2%positive); [eapply daring_cell_domain; exact HC
    |eapply daring_held_domain; exact HH].
Qed.

Lemma daring_load_false_pre mode post :
  owned_derivation two_processors A.Emp mode (A.Pure BFalse) daring_load post.
Proof.
  eapply OwnedConsequence with
    (pre' := A.Spatial (A.Pure BFalse) daring_cell)
    (post' := A.Spatial (A.Pure BFalse) (A.And daring_cell daring_zero)).
  - intros s r H; discriminate H.
  - apply OwnedFrameSP.
    + apply owned_derive_load_cell; cbn; tauto.
    + intros x H; cbn; tauto.
  - intros s r (a & b & Hsp & Hfalse & Hpost); discriminate Hfalse.
Qed.

Lemma daring_acquire_store_derivation mode :
  owned_derivation two_processors daring_cell mode A.Emp
    (C.Seq acceptance_acquire daring_store) daring_held.
Proof.
  eapply OwnedSequence with (middle := A.Spatial daring_token daring_cell).
  - eapply OwnedConsequence; [intros s r H; exact H |apply OwnedLock |].
    intros s r H; eapply stm_wand_free_barrier_elim;
      [cbn [daring_token daring_cell writer_points_to wand_free]; tauto |exact H].
  - apply OwnedFrameSP; [apply owned_derive_store_cell |intros x H; contradiction].
Qed.

Theorem daring_load_extended_bad_derivation mode :
  daring_load_extension two_processors daring_cell mode A.Emp daring_program daring_zero.
Proof.
  eapply DaringConsequence with (post' := A.And daring_held daring_zero);
    [intros s r H; exact H | |intros s r [_ HQ]; exact HQ].
  eapply DaringSequence.
  - apply daring_load_embeds_owned, daring_acquire_store_derivation.
  - apply DaringLoadRule, daring_load_embeds_owned.
    eapply OwnedConsequence; [apply daring_duplicate_false |apply daring_load_false_pre |intros s r H; exact H].
Qed.

Definition daring_pool := resource_memory two_processors
  (acceptance_cell 2%positive 0%Z 1%positive (or_introl eq_refl)).
Definition daring_acquired := acquire two_processors daring_pool 1%positive.
Definition daring_pending := enqueue daring_acquired 1%positive 2%positive 5%Z.
Definition daring_final_stack := update initial_registers 0 5%Z.

Lemma daring_pool_models s : persistent_full_satisfies two_processors s daring_pool daring_cell.
Proof. eapply invariant_return_full_completeness with (owner := 1%positive); [left; reflexivity |constructor |apply acceptance_cell_models]. Qed.

Theorem daring_load_extended_trace :
  execution two_processors 5 daring_program initial_registers daring_pool
    halt daring_final_stack daring_pending.
Proof.
  unfold daring_program.
  eapply container_execution_sequence with (n := 3) (m := 1).
  - eapply container_execution_sequence with (n := 1) (m := 1).
    + eapply ExecuteNext; [eapply StepPrimitive; [reflexivity |]
        |apply ExecuteRefl].
      apply PrimitiveLock; [left; reflexivity |reflexivity |intros i H; exact H].
    + eapply ExecuteNext; [eapply StepPrimitive; [reflexivity |]
        |apply ExecuteRefl].
      eapply PrimitiveStore with (previous := 0%Z); [left; reflexivity |reflexivity |reflexivity].
  - eapply ExecuteNext; [eapply StepPrimitive; [reflexivity |] |apply ExecuteRefl].
    apply PrimitiveLoad; [left; reflexivity |change (~ (two_processors 1%positive /\ 1%positive <> 1%positive)); tauto |reflexivity].
Qed.

Theorem daring_load_extension_breaks_adequacy mode :
  invariant_fragment daring_cell /\ two_active_processors two_processors /\
  daring_load_extension two_processors daring_cell mode A.Emp daring_program daring_zero /\
  persistent_models two_processors initial_registers (bare_resource two_processors) A.Emp /\
  persistent_full_satisfies two_processors initial_registers daring_pool daring_cell /\
  lock_free daring_pool /\
  memory_spatial daring_pool (resource_memory two_processors (bare_resource two_processors)) daring_pool /\
  execution two_processors 5 daring_program initial_registers daring_pool halt daring_final_stack daring_pending /\
  terminal halt /\ daring_final_stack 0 = 5%Z /\
  (forall local, ~ persistent_models two_processors daring_final_stack local daring_zero).
Proof.
  split; [constructor |]. split; [apply acceptance_two_active |].
  split; [apply daring_load_extended_bad_derivation |].
  split; [split; [intros; reflexivity |]; split; [intros; reflexivity |intros i H; exact H] |].
  split; [apply daring_pool_models |]. split; [intros i H; exact H |].
  split; [exact (proj1 (spatial_empty_right (proj1_sig
    (acceptance_cell 2%positive 0%Z 1%positive (or_introl eq_refl))))) |].
  split; [apply daring_load_extended_trace |]. split; [eexists; reflexivity |].
  split; [reflexivity |intros local H; discriminate H].
Qed.

(** N2: the premise is an inhabited, ordinary LOAD-ANY derivation.
    Its postcondition is exactly J * Q, as required by DARING-LOAD. *)
Lemma daring_load_honest_premise_derivation mode :
  owned_derivation two_processors A.Emp mode (A.Spatial daring_cell A.Emp)
    daring_load (A.Spatial daring_cell daring_zero).
Proof.
  eapply OwnedConsequence with (pre' := daring_cell) (post' := A.And daring_cell daring_zero).
  - apply container_spatial_emp_elim; cbn [daring_cell writer_points_to wand_free]; tauto.
  - apply owned_derive_load_cell; cbn; tauto.
  - intros s r [HC HQ]; exists r,(bare_resource two_processors).
    split; [apply spatial_empty_right |auto].
Qed.

Definition daring_frame := owned_enqueue_resource two_processors
  (acquired_resource two_processors
    (acceptance_cell 2%positive 0%Z 1%positive (or_introl eq_refl)) 1%positive)
  1%positive 2%positive 5%Z (or_introl eq_refl).

Lemma daring_load_held_environment mode s :
  owned_environment two_processors mode daring_cell s (bare_resource two_processors)
    empty_memory daring_frame daring_pending (PoolHeld 1%positive).
Proof.
  apply owned_held_spatial_environment.
  - exact (proj1 (spatial_empty_right (proj1_sig daring_frame))).
  - split; [left; reflexivity |intros i; reflexivity].
Qed.

Lemma daring_load_held_step :
  program_step two_processors OrdinaryAction daring_load
    (State initial_registers daring_pending) halt (State daring_final_stack daring_pending).
Proof.
  unfold daring_load, load_command; eapply ProgramPrimitive with (i := 1%positive) (p := C.Common (S.Load 0 (EVal 2%Z))); [reflexivity |]. apply PrimitiveLoad;
    [left; reflexivity |change (~ (two_processors 1%positive /\ 1%positive <> 1%positive)); tauto |reflexivity].
Qed.

Theorem daring_load_honest_conclusion_invalid mode :
  ~ owned_valid two_processors mode daring_cell A.Emp daring_load daring_zero.
Proof.
  intros Hvalid.
  assert (HE : persistent_models two_processors initial_registers (bare_resource two_processors) A.Emp).
  { split; [intros; reflexivity |]. split; [intros; reflexivity |intros i H; exact H]. }
  destruct (owned_safe_program_step _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    (Hvalid _ _ HE 2) (daring_load_held_environment mode initial_registers) daring_load_held_step)
    as (local' & pool' & phase' & Henv & Hupdate & Hsafe).
  pose proof (owned_safe_terminal _ _ _ _ _ _ _ _ Hsafe ltac:(eexists; reflexivity)) as Hzero.
  discriminate Hzero.
Qed.

Theorem daring_load_honest_counterexample mode :
  owned_derivation two_processors A.Emp mode (A.Spatial daring_cell A.Emp)
    daring_load (A.Spatial daring_cell daring_zero) /\
  owned_valid two_processors mode A.Emp (A.Spatial daring_cell A.Emp)
    daring_load (A.Spatial daring_cell daring_zero) /\
  (exists r, persistent_models two_processors initial_registers r (A.Spatial daring_cell A.Emp)) /\
  ~ owned_valid two_processors mode daring_cell A.Emp daring_load daring_zero.
Proof.
  split; [apply daring_load_honest_premise_derivation |]. split.
  - apply owned_calculus_sound; [constructor |apply acceptance_two_active |apply daring_load_honest_premise_derivation].
  - split; [|apply daring_load_honest_conclusion_invalid].
    exists (acceptance_cell 2%positive 0%Z 1%positive (or_introl eq_refl));
    apply persistent_spatial_emp_right, acceptance_cell_models.
Qed.

(** N3: the honest premise exchanges the roles of two allocated cells.
    This obstruction already occurs in a FREE-lock environment. *)
Definition daring_swap_invariant := A.Or daring_cell daring_other.
Definition daring_private := acceptance_cell 3%positive 0%Z 1%positive (or_introl eq_refl).
Definition daring_pair := Memory
  (heap_override (shared_heap daring_pool) (shared_heap (resource_memory two_processors daring_private)))
  empty_buffers no_blocked.
Definition daring_pair_after := enqueue daring_pair 1%positive 2%positive 5%Z.

Lemma daring_swap_pre : persistent_entails two_processors
  (A.Spatial daring_swap_invariant daring_other) (A.Spatial daring_other daring_cell).
Proof.
  intros s r (a & b & Hsp & [HC |HO] & HP).
  - exists b,a; split; [apply spatial_comm, Hsp |auto].
  - exfalso.
    pose proof (assertion_derivation_sound _ _ _ (assert_derive_cells_exclusive two_processors
      (EVal 3%Z) (EVal 0%Z) (EVal 0%Z)) s r (ex_intro _ a (ex_intro _ b (conj Hsp (conj HO HP))))) as Hfalse.
    discriminate Hfalse.
Qed.

Lemma daring_store_honest_premise_derivation mode :
  owned_derivation two_processors A.Emp mode (A.Spatial daring_swap_invariant daring_other)
    daring_store (A.Spatial daring_swap_invariant daring_history).
Proof.
  eapply OwnedConsequence; [apply daring_swap_pre | |].
  - apply OwnedFrameSP; [apply owned_derive_store_cell |intros x H; contradiction].
  - intros s r (a & b & Hsp & HO & HH); exists a,b; split; [exact Hsp |split; [right; exact HO |exact HH]].
Qed.

Lemma daring_pair_spatial :
  memory_spatial daring_pool (resource_memory two_processors daring_private) daring_pair.
Proof.
  split.
  - split; [|intros i H _; exact H]. intros loc HD HE.
    pose proof (acceptance_cell_domain 2%positive 0%Z 1%positive (or_introl eq_refl) loc HD) as ED.
    pose proof (acceptance_cell_domain 3%positive 0%Z 1%positive (or_introl eq_refl) loc HE) as EE; congruence.
  - split; [intros; reflexivity |]. split; [intros; constructor |intros i; cbn; unfold no_blocked; tauto].
Qed.

Lemma daring_store_free_environment mode s :
  owned_environment two_processors mode daring_swap_invariant s daring_private daring_pool
    (empty_resource_value two_processors) daring_pair PoolFree.
Proof.
  apply owned_empty_frame_intro.
  - exact (proj1 (proj2_sig (acceptance_cell 2%positive 0%Z 1%positive (or_introl eq_refl)))).
  - apply daring_pair_spatial.
  - split; [intros i H; exact H |].
    destruct (daring_pool_models s) as (r & Er & HJ); exists r; split; [exact Er |left; exact HJ].
Qed.

Lemma daring_store_free_step :
  program_step two_processors OrdinaryAction daring_store
    (State initial_registers daring_pair) halt (State initial_registers daring_pair_after).
Proof.
  unfold daring_store, store_command; eapply ProgramPrimitive with (i := 1%positive) (p := C.Common (S.Store (EVal 2%Z) (EVal 5%Z))); [reflexivity |].
  eapply PrimitiveStore with (previous := 0%Z); [left; reflexivity |reflexivity |reflexivity].
Qed.

Lemma daring_store_no_successor mode local' pool' phase' :
  owned_update two_processors OrdinaryAction PoolFree phase' daring_private daring_pool local' pool' ->
  ~ owned_environment two_processors mode daring_swap_invariant initial_registers local' pool'
    (empty_resource_value two_processors) daring_pair_after phase'.
Proof.
  intros Hupdate Henv.
  destruct (owned_action_transfer _ _ _ _ _ _ _ _ Hupdate) as [-> [-> Hblocks]].
  destruct (owned_empty_frame_elim _ _ _ _ _ _ _ _ Henv) as [Hsp Hstatus].
  destruct Hsp as [[Hdis _] [_ [Hbuffers _]]].
  specialize (Hbuffers 1%positive).
  change (interleaves [] (buffers (resource_memory two_processors local') 1%positive)
    [(2%positive,5%Z)]) in Hbuffers.
  apply interleaves_nil_left in Hbuffers.
  apply (Hdis 2%positive); [left; exists 0%Z; reflexivity |].
  right; exists 1%positive,5%Z; rewrite <- Hbuffers; left; reflexivity.
Qed.

Theorem daring_store_honest_conclusion_invalid mode :
  ~ owned_valid two_processors mode daring_swap_invariant daring_other daring_store daring_history.
Proof.
  intros Hvalid.
  destruct (owned_safe_program_step _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    (Hvalid _ _ (acceptance_cell_models initial_registers 3%positive 0%Z 1%positive (or_introl eq_refl)) 1)
    (daring_store_free_environment mode initial_registers) daring_store_free_step)
    as (local' & pool' & phase' & Henv & Hupdate & Hsafe).
  exact (daring_store_no_successor mode _ _ _ Hupdate Henv).
Qed.

Theorem daring_store_honest_counterexample mode :
  invariant_fragment daring_swap_invariant /\
  owned_derivation two_processors A.Emp mode (A.Spatial daring_swap_invariant daring_other)
    daring_store (A.Spatial daring_swap_invariant daring_history) /\
  owned_valid two_processors mode A.Emp (A.Spatial daring_swap_invariant daring_other)
    daring_store (A.Spatial daring_swap_invariant daring_history) /\
  (exists r, persistent_models two_processors initial_registers r (A.Spatial daring_swap_invariant daring_other)) /\
  ~ owned_valid two_processors mode daring_swap_invariant daring_other daring_store daring_history.
Proof.
  split; [constructor; constructor |]. split; [apply daring_store_honest_premise_derivation |]. split.
  - apply owned_calculus_sound; [constructor |apply acceptance_two_active |apply daring_store_honest_premise_derivation].
  - split; [|apply daring_store_honest_conclusion_invalid].
    assert (Hsp : spatial (proj1_sig (acceptance_cell 2%positive 0%Z 1%positive (or_introl eq_refl)))
      (proj1_sig daring_private) (Generalized daring_pair (fun i => i = 1%positive))).
    { split; [apply daring_pair_spatial |intros i; cbn; tauto]. }
    exists (exist _ _ (spatial_well_formed _ _ _ _
      (proj2_sig (acceptance_cell 2%positive 0%Z 1%positive (or_introl eq_refl)))
      (proj2_sig daring_private) Hsp)).
    eexists; eexists; split; [exact Hsp |].
    split; [left; apply acceptance_cell_models |apply acceptance_cell_models].
Qed.
