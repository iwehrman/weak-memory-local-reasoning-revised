From Stdlib Require Import List ZArith.
From WMLR Require Import Expressions Languages Machine BufferRelations Separation StableCompatibility
  RepairedSeparation GeneralizedFlushing AssertionFlushing OperationalSemantics ExecutionExamples
  Assertions AssertionSemantics ConcreteAssertions PersistentAssertions Safety HeapRules OwnershipProtocol
  OwnershipRules OwnershipHeap OwnershipExamples UnlockCounterexample TemporalSafety TemporalTransfer.
Import ListNotations.

(** Even after retaining completeness, simply replacing spatial external
    frames by temporal prefixes does not integrate invariant transfer.
    A past heap cell can overlap a current owned cell. Releasing that current
    cell into a spatially separated shared pool then leaves overlapping history.
    The invariant is already restored: this is not the old unlock counterexample. *)
Lemma overlapping_history_composition (past local : resource two_processors) :
  proj1_sig past = Generalized (protocol_cell 7%Z) two_processors ->
  proj1_sig local = Generalized (acquire two_processors (protocol_cell 7%Z) 1%positive) two_processors ->
  repaired_temporal two_processors (proj1_sig past) (proj1_sig local) (proj1_sig local).
Proof.
  intros Ep El; rewrite Ep, El. split.
  - split; [intros i H; contradiction |]. split;
      [intros i _ loc [v H]; contradiction |intros i j _ _ _ loc [v H]; contradiction].
  - split.
    + split.
      * split; [intros i H; contradiction |]. split;
          [intros i _ loc [v H]; contradiction |intros i j _ _ _ loc [v H]; contradiction].
      * split.
        -- intros loc; simpl; unfold heap_override;
             destruct (heap_update empty_heap 1%positive 7%Z loc); reflexivity.
        -- split; [intros; reflexivity |intros i; simpl; unfold no_blocked; tauto].
    + split; [intros; reflexivity |intros i; simpl; tauto].
Qed.

Lemma overlapping_history_environment s (past local : resource two_processors) :
  proj1_sig past = Generalized (protocol_cell 7%Z) two_processors ->
  proj1_sig local = Generalized (acquire two_processors (protocol_cell 7%Z) 1%positive) two_processors ->
  prefix_environment two_processors
    (fun t m => persistent_full_satisfies two_processors t m protected_seven) s
    local empty_memory past (acquire two_processors (protocol_cell 7%Z) 1%positive).
Proof.
  intros Ep El. constructor.
  - exact (proj1 (empty_generalized_well_formed two_processors)).
  - pose proof (proj1 (proj2_sig local)) as H; rewrite El in H; exact H.
  - exists local; split.
    + apply overlapping_history_composition; assumption.
    + unfold resource_memory; rewrite El.
      exact (proj1 (spatial_empty_left (Generalized (acquire two_processors (protocol_cell 7%Z) 1%positive) two_processors))).
  - right; exists 1%positive; split; [left; reflexivity |intros i; reflexivity].
  - right; exists 1%positive; split; [left; reflexivity |intros i; reflexivity].
Qed.

Theorem prefix_ownership_release_invalid :
  ~ prefix_valid two_processors protected_seven (owned_assertion 1%positive protected_seven)
    owner_release A.Emp.
Proof.
  intros Hvalid.
  destruct (protocol_cell_models (fun _ => 0%Z) 7%Z) as (past & Ep & Hpast).
  destruct (acquire_exposes_invariant two_processors 1%positive protected_seven (fun _ => 0%Z)
    (protocol_cell 7%Z) (or_introl eq_refl) ltac:(intros i H; contradiction) (protocol_cell_models _ _))
    as (local & El & HP).
  specialize (Hvalid _ _ HP 2). destruct Hvalid as [_ [_ Hprogress]].
  assert (Hstep : step two_processors owner_release
    (State (fun _ => 0%Z) (acquire two_processors (protocol_cell 7%Z) 1%positive)) halt
    (State (fun _ => 0%Z) (protocol_cell 7%Z))).
  { eapply StepPrimitive; [reflexivity |]. apply PrimitiveUnlock;
      [left; reflexivity |reflexivity |split; [left; reflexivity |intros i; reflexivity]]. }
  destruct (Hprogress _ _ _ _ _ _ (overlapping_history_environment _ _ _ Ep El) Hstep)
    as (local' & shared' & past' & Henv & Hfuture & _ & Hdone & _).
  pose proof (Hdone (ex_intro _ (EVal 1%Z) eq_refl)) as Hempty.
  change (empty_atom (proj1_sig local')) in Hempty.
  assert (Epast : resource_memory two_processors past' = protocol_cell 7%Z).
  { pose proof (future_without_buffers _ _ _ Hfuture ltac:(intros i; rewrite Ep; reflexivity)) as E.
    unfold resource_memory; rewrite E, Ep; reflexivity. }
  destruct Henv as [_ _ [combined [Htm Hsp]] _ [HJ |Hlocked]].
  - pose proof (proj1 (persistent_cell_shape _ _ _ _ _ HJ)) as Hshared.
    destruct Htm as [_ [[_ [Hheap _]] _]].
    assert (Hcombined : shared_heap (resource_memory two_processors combined) 1%positive = Some 7%Z).
    { unfold resource_memory; rewrite Hheap. unfold heap_override; rewrite (proj1 Hempty).
      change (shared_heap (resource_memory two_processors past') 1%positive = Some 7%Z).
      rewrite Epast; reflexivity. }
    apply (proj1 (proj1 Hsp) 1%positive); left; exists 7%Z; assumption.
  - apply two_processor_empty_not_locked; exact Hlocked.
Qed.

(** The same overlapping-history example admits the alternative transfer:
    the restored pool is behind the history, inside its ownership region. *)
Theorem overlapping_history_release_recomposes s : exists past owned pool : resource two_processors,
  proj1_sig past = Generalized (protocol_cell 7%Z) two_processors /\
  proj1_sig owned = Generalized (acquire two_processors (protocol_cell 7%Z) 1%positive) two_processors /\
  step two_processors owner_release (State s (acquire two_processors (protocol_cell 7%Z) 1%positive))
    halt (State s (protocol_cell 7%Z)) /\
  persistent_models two_processors s pool protected_seven /\
  repaired_temporal two_processors (proj1_sig past) (proj1_sig pool)
    (proj1_sig (released_resource two_processors owned)).
Proof.
  destruct (protocol_cell_models s 7%Z) as (past & Ep & Hpast).
  destruct (acquire_exposes_invariant two_processors 1%positive protected_seven s
    (protocol_cell 7%Z) (or_introl eq_refl) ltac:(intros i H; contradiction) (protocol_cell_models _ _))
    as (owned & Eowned & Howned).
  assert (Hfree : lock_free (resource_memory two_processors past)) by
    (unfold resource_memory; rewrite Ep; intros i H; contradiction).
  assert (Hheld : lock_held two_processors (resource_memory two_processors owned) 1%positive).
  { unfold resource_memory; rewrite Eowned; split; [left; reflexivity |intros i; reflexivity]. }
  assert (Hdrained : buffers (resource_memory two_processors owned) 1%positive = []) by
    (unfold resource_memory; rewrite Eowned; reflexivity).
  destruct (temporal_history_release_transfer _ _ _ _ _ _ _ Hfree Hheld Howned
    (overlapping_history_composition _ _ Ep Eowned) Hdrained) as (Hstep & pool & HJ & Hsep).
  exists past, owned, pool; split; [exact Ep |]. split; [exact Eowned |]. split; [|auto].
  unfold resource_memory in Hstep; rewrite Eowned in Hstep; exact Hstep.
Qed.
