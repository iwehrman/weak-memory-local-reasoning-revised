From Stdlib Require Import List ZArith.
From WMLR Require Import Expressions Languages Machine BufferRelations Separation StableCompatibility
  RepairedSeparation GeneralizedFlushing AssertionFlushing FrameDecomposition OperationalSemantics ExecutionExamples
  Assertions AssertionSemantics ConcreteAssertions PersistentAssertions Safety HeapRules OwnershipProtocol OwnershipRules
  OwnershipHeap OwnershipExamples PrivateOwnership TemporalSafety RegionalResources RegionalSafety InvariantCompleteness
  SeparatedSafety SeparatedRules TransferredCells OwnershipTransfer.
Import ListNotations.

Theorem processor_cell_does_not_imply_all_processor_cell :
  ~ regional_entails two_processors (processor_cell 1%positive 1%positive 7%Z) protected_seven.
Proof.
  intros Hentails.
  pose (r := imported_cell_resource two_processors 1%positive (or_introl eq_refl) (bare_resource two_processors)
    (protocol_cell 7%Z) (proj1 (persistent_full_well_formed _ _ _ _ (protocol_cell_models protocol_stack 7%Z)))).
  assert (HP : persistent_models two_processors protocol_stack r (processor_cell 1%positive 1%positive 7%Z)).
  { apply processor_cell_from_shape; [left; reflexivity |intros; reflexivity |intros; reflexivity |
      intros i H; contradiction |right; reflexivity]. }
  pose proof (cell_resource_complete _ _ _ _ _ (Hentails _ _ HP) 2%positive (or_intror eq_refl)) as Hmark.
  destruct Hmark as [H |H]; [exact H |discriminate].
Qed.

(** A spatially separate pool cannot receive a cell whose older heap value
    must remain in the private temporal history. This obstruction is independent
    of buffer draining, footprint bounds, and the particular command. *)
Theorem retained_history_prevents_donation active owner invariant s
    (past history local : resource active) protected whole loc old new :
  (forall i, buffers (resource_memory active past) i = []) ->
  shared_heap (resource_memory active past) loc = Some old -> resource_future active past history ->
  separated_environment active owner invariant Open s local protected history whole ->
  persistent_models active s local A.Emp ->
  protocol_assertion active Open s protected (owned_assertion owner (cell_assertion loc new)) -> False.
Proof.
  intros Hempty Hpast Hfuture [_ _ _ [combined [Htm Hsp]]] HP HS.
  pose proof (future_without_buffers _ _ _ Hfuture Hempty) as Ehistory.
  change (resource_memory active history = resource_memory active past) in Ehistory.
  pose proof (temporal_emp_memory_right _ _ _ _ HP Htm) as Ecombined.
  assert (Hcombined : shared_heap (resource_memory active combined) loc = Some old).
  { rewrite (proj1 Ecombined loc), Ehistory; exact Hpast. }
  destruct (full_spatial_elim _ _ _ _ _ HS) as (token & cell & Howned & Htoken & Hcell).
  destruct (persistent_cell_shape _ _ _ _ _ Hcell) as [Hcellheap _].
  apply (proj1 (proj1 Hsp) loc); [left; exists old; exact Hcombined |].
  eapply protocol_spatial_domain_right; [exact Howned |left; exists new; exact Hcellheap].
Qed.

Definition donation_pool := acquire two_processors empty_memory 1%positive.
Definition donation_whole := acquire two_processors (protocol_cell 7%Z) 1%positive.

Lemma donation_pool_certificate s :
  protocol_region two_processors 1%positive protected_seven Open s donation_pool /\
  protocol_assertion two_processors Open s donation_pool (owned_assertion 1%positive A.Emp).
Proof.
  split.
  - split; [apply acquire_well_formed; exact (proj1 (empty_generalized_well_formed two_processors)) |].
    split; [left; reflexivity |intros i; reflexivity].
  - apply acquire_exposes_invariant; [left; reflexivity |intros i H; contradiction |apply protocol_empty_satisfies].
Qed.

Lemma donation_initial_certificate s : exists past local : resource two_processors,
  resource_memory two_processors past = protocol_cell 5%Z /\
  persistent_models two_processors s local protected_seven /\
  separated_environment two_processors 1%positive protected_seven Open s local donation_pool past donation_whole.
Proof.
  destruct (protocol_cell_models s 5%Z) as (past & Epast & HP).
  destruct (protocol_cell_models s 7%Z) as (local & Elocal & HQ).
  assert (Htm : repaired_temporal two_processors (proj1_sig past) (proj1_sig local) (proj1_sig local)).
  { rewrite Epast, Elocal; split.
    - split; [intros i H; contradiction |]. split;
        [intros i _ loc [v H]; contradiction |intros i j _ _ _ loc [v H]; contradiction].
    - split.
      + split.
        * split; [intros i H; contradiction |]. split;
            [intros i _ loc [v H]; contradiction |intros i j _ _ _ loc [v H]; contradiction].
        * split.
          -- intros loc; simpl; unfold heap_override, heap_update; destruct (Pos.eq_dec loc 1%positive); reflexivity.
          -- split; [intros; reflexivity |intros i; simpl; unfold no_blocked; tauto].
      + split; [intros; reflexivity |intros i; simpl; tauto]. }
  assert (Erawlocal : resource_memory two_processors local = protocol_cell 7%Z) by (unfold resource_memory; rewrite Elocal; reflexivity).
  exists past, local; split; [unfold resource_memory; rewrite Epast; reflexivity |]. split; [exact HQ |].
  constructor.
  - exact (proj1 (donation_pool_certificate s)).
  - rewrite Erawlocal; intros i H; contradiction.
  - unfold resource_memory; rewrite Epast; intros i H; contradiction.
  - exists local; split; [exact Htm |]. rewrite Erawlocal.
    apply protocol_spatial_reblock; [intros i H; contradiction |].
    exact (proj1 (spatial_empty_right (Generalized (protocol_cell 7%Z) two_processors))).
Qed.

Theorem owner_fenced_donation_invalid :
  ~ separated_valid two_processors 1%positive protected_seven Open (owned_assertion 1%positive A.Emp)
    protected_seven owner_fence Open (owned_assertion 1%positive protected_seven) A.Emp.
Proof.
  intros Hvalid; destruct (donation_initial_certificate protocol_stack) as (past & local & Epast & HP & Henv).
  pose proof (Hvalid protocol_stack local donation_pool (proj1 (donation_pool_certificate protocol_stack))
    (separated_local_free _ _ _ _ _ _ _ _ _ Henv) (proj2 (donation_pool_certificate protocol_stack)) HP 2) as Hsafe.
  assert (Hrun : execution two_processors 1 owner_fence protocol_stack donation_whole halt protocol_stack donation_whole).
  { eapply ExecuteNext; [|constructor]; eapply StepPrimitive; [reflexivity |]; apply PrimitiveFence;
      [left; reflexivity |reflexivity]. }
  destruct (separated_execution_post _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hrun Hsafe Henv ltac:(eexists; reflexivity))
    as (local' & protected' & history' & Henv' & Hfuture & HS & HQ).
  eapply retained_history_prevents_donation with (past := past) (loc := 1%positive) (old := 5%Z) (new := 7%Z);
    [intros i; rewrite Epast; reflexivity |rewrite Epast; reflexivity |exact Hfuture |exact Henv' |exact HQ |exact HS].
Qed.

(** The disjoint-history replacement has a concrete nonempty model. *)
Example donation_without_history_recomposes s : exists protected,
  separated_environment two_processors 1%positive protected_seven Open s (bare_resource two_processors)
    protected (bare_resource two_processors) donation_whole /\
  protocol_assertion two_processors Open s protected
    (owned_assertion 1%positive (A.Spatial A.Emp protected_seven)).
Proof.
  destruct (protocol_cell_models s 7%Z) as (local & E & HP).
  assert (Eraw : resource_memory two_processors local = protocol_cell 7%Z) by (unfold resource_memory; rewrite E; reflexivity).
  assert (Henv : separated_environment two_processors 1%positive protected_seven Open s local donation_pool
    (bare_resource two_processors) donation_whole).
  { constructor.
    - exact (proj1 (donation_pool_certificate s)).
    - rewrite Eraw; intros i H; contradiction.
    - intros i H; contradiction.
    - exists local; split; [apply repaired_temporal_bare_left |]. rewrite Eraw.
      apply protocol_spatial_reblock; [intros i H; contradiction |].
      exact (proj1 (spatial_empty_right (Generalized (protocol_cell 7%Z) two_processors))). }
  destruct (history_disjoint_donation_recomposes _ _ _ _ _ _ _ _ _ _ _ Henv
    (proj2 (donation_pool_certificate s)) HP ltac:(intros loc [[v H] |[i [v H]]] _; discriminate || contradiction))
    as (protected & Henv' & HS & Hdom).
  exists protected; auto.
Qed.
