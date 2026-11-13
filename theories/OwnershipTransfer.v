From Stdlib Require Import List ZArith.
From WMLR Require Import Expressions Languages Machine BufferRelations Separation StableCompatibility
  RepairedSeparation GeneralizedFlushing FrameDecomposition OperationalSemantics Assertions AssertionSemantics
  ConcreteAssertions PersistentAssertions Safety Specifications HeapRules OwnershipProtocol OwnershipRules
  OwnershipHeap PrivateOwnership SpatialExchange TemporalSafety RegionalResources SeparatedSafety SeparatedRules
  TransferredCells.
Import ListNotations.

Lemma temporal_emp_memory_right active (history local combined : resource active) :
  empty_atom (proj1_sig local) ->
  repaired_temporal active (proj1_sig history) (proj1_sig local) (proj1_sig combined) ->
  memory_equiv (resource_memory active combined) (resource_memory active history).
Proof.
  intros [Hheap [Hbuffers Hfree]] [_ [[_ [Hh [Hb Hk]]] _]].
  split; [|split].
  - intros address; unfold resource_memory; rewrite Hh; unfold heap_override; rewrite Hheap; reflexivity.
  - intros i; unfold resource_memory; rewrite Hb, Hbuffers, app_nil_r; reflexivity.
  - intros i; rewrite Hk; split; [intros [H |H]; [exact H |exfalso; exact (Hfree i H)] |auto].
Qed.

Lemma spatial_empty_right_is_temporal active (history local : resource active) combined :
  memory_spatial (resource_memory active history) (resource_memory active local) combined ->
  (forall i, buffers (resource_memory active local) i = []) ->
  (forall i, complete (proj1_sig local) i -> buffers (resource_memory active history) i = []) ->
  repaired_temporal active (proj1_sig history) (proj1_sig local)
    (Generalized combined (fun i => complete (proj1_sig history) i \/ complete (proj1_sig local) i)).
Proof.
  intros [Hcompatible [Hheap [Hbuffers Hblocks]]] Hempty Hbefore; split.
  - apply spatial_compatible_stable, Hcompatible.
  - split.
    + split; [apply stable_implies_original_compatible, spatial_compatible_stable, Hcompatible |].
      split; [exact Hheap |]. split; [|exact Hblocks].
      intros i; rewrite Hempty, app_nil_r; specialize (Hbuffers i); rewrite Hempty in Hbuffers.
      apply interleaves_nil_right, Hbuffers.
    + split; [exact Hbefore |intros i; reflexivity].
Qed.

(** The machine fence leaves memory unchanged; its draining guard justifies
    reclassifying a protected cell as private with owner-only completeness. *)
Theorem separated_take_cell_environment active owner invariant s local protected history whole rest loc v :
  separated_environment active owner invariant Open s local protected history whole ->
  protocol_assertion active Open s protected (owned_assertion owner (A.Spatial rest (cell_assertion loc v))) ->
  persistent_models active s local A.Emp -> buffers whole owner = [] ->
  exists local' protected', separated_environment active owner invariant Open s local' protected' history whole /\
    protocol_assertion active Open s protected' (owned_assertion owner rest) /\
    persistent_models active s local' (processor_cell owner loc v) /\
    domain_included (resource_memory active local') protected /\ domain_included protected' protected.
Proof.
  intros [Hregion Hl Hhistory [combined [Htm Hsp]]] HS HP Hdrained.
  destruct Hregion as [Hprotectedwf Hheld].
  destruct (full_spatial_elim _ _ _ _ _ HS) as (token & payload & Htoken & Hlock & Hpayload).
  destruct (full_spatial_elim _ _ _ _ _ Hpayload) as (kept & cell & Hpayloadsplit & Hkept & Hcell).
  destruct (proj1 (memory_spatial_associative token kept cell protected)
    (ex_intro _ payload (conj Hpayloadsplit Htoken))) as (protected' & Hprotected' & Hsplit).
  assert (HS' : persistent_full_satisfies active s protected' (owned_assertion owner rest)).
  { eapply full_spatial_intro; eassumption. }
  assert (Hcellshape : (forall address, shared_heap cell address = heap_update empty_heap loc v address) /\
      (forall i, buffers cell i = []) /\ lock_free cell).
  { destruct Hcell as (r & E & H); pose proof (persistent_cell_resource_shape _ _ _ _ _ H) as Hshape.
    rewrite E in Hshape; exact Hshape. }
  destruct Hcellshape as [Hcellheap [Hcellbuffers Hcellfree]].
  assert (Hheld' : lock_held active protected' owner).
  { split; [exact (proj1 Hheld) |]. intros i; rewrite <- (proj2 Hheld i).
    rewrite (proj2 (proj2 (proj2 Hsplit)) i); split; [auto |intros [H |H]; [exact H |exfalso; exact (Hcellfree i H)]]. }
  pose (local' := imported_cell_resource active owner (proj1 Hheld) local cell
    (proj1 (persistent_full_well_formed _ _ _ _ Hcell))).
  assert (Hlocalpost : persistent_models active s local' (processor_cell owner loc v)).
  { apply processor_cell_from_shape; try assumption; [exact (proj1 Hheld) |right; reflexivity]. }
  destruct (spatial_exchange cell protected' (resource_memory active combined) protected whole
    (memory_spatial_comm _ _ _ Hsplit) Hsp) as (combined' & Hnewcombined & Hnewwhole).
  assert (Hhistorycell : memory_spatial (resource_memory active history) cell combined').
  { apply memory_spatial_comm; eapply protocol_spatial_equiv_right; [|exact Hnewcombined].
    exact (temporal_emp_memory_right active history local combined HP Htm). }
  assert (Hhistoryowner : buffers (resource_memory active history) owner = []).
  { pose proof (proj1 (spatial_empty_buffer_parts _ _ _ _ Hsp Hdrained)) as Hcombinedempty.
    rewrite (proj1 (proj2 (temporal_emp_memory_right _ _ _ _ HP Htm)) owner) in Hcombinedempty; exact Hcombinedempty. }
  assert (Hnewtm : repaired_temporal active (proj1_sig history) (proj1_sig local')
    (Generalized combined' (fun i => complete (proj1_sig history) i \/ complete (proj1_sig local') i))).
  { apply spatial_empty_right_is_temporal; [exact Hhistorycell |exact Hcellbuffers |].
    intros i [Hmark | ->]; [exact (proj1 (proj2 (proj2 Htm)) i Hmark) |exact Hhistoryowner]. }
  pose (combinedr := exist _ _ (temporal_well_formed active _ _ _ (proj2_sig history) (proj2_sig local') (proj2 Hnewtm))).
  exists local', protected'; split.
  - constructor.
    + split; [exact (proj1 (persistent_full_well_formed _ _ _ _ HS')) |exact Hheld'].
    + exact Hcellfree.
    + exact Hhistory.
    + exists combinedr; split; [exact Hnewtm |apply memory_spatial_comm, Hnewwhole].
  - split; [exact HS' |]. split; [exact Hlocalpost |]. split.
    + intros address H; exact (protocol_spatial_domain_right _ _ _ _ Hsplit H).
    + intros address H; exact (protocol_spatial_domain_right _ _ _ _ (memory_spatial_comm _ _ _ Hsplit) H).
Qed.

Theorem separated_take_cell_fence_valid active owner invariant rest loc v :
  separated_valid active owner invariant Open (owned_assertion owner (A.Spatial rest (cell_assertion loc v))) A.Emp
    (Concurrent.Prim (Concurrent.Common Sequential.Fence) (EVal (Z.pos owner)))
    Open (owned_assertion owner rest) (processor_cell owner loc v).
Proof.
  intros s local protected Hr Hl HS HP n; revert s local protected Hr Hl HS HP.
  induction n; intros s local protected Hr Hl HS HP; [exact I |].
  split; [exact Hr |]. split; [exact Hl |]. split; [intros [ann E]; discriminate |]. split.
  - intros history whole Henv Hfault; inversion Hfault; subst.
    match goal with H : primitive_abort _ _ _ _ |- _ => inversion H end.
  - intros history whole next t whole' Henv Hstep; inversion Hstep; subst.
    + match goal with H : primitive_step _ _ _ _ _ |- _ => inversion H; subst end.
      match goal with E : eval_expr _ (EVal (Z.pos _)) = Z.pos _ |- _ => simpl in E; inversion E; subst end.
      destruct (separated_take_cell_environment _ _ _ _ _ _ _ _ _ _ _ Henv HS HP ltac:(assumption))
        as (local' & protected' & Henv' & HS' & HP' & Hld & Hpd).
      exists Open, local', protected', history; split; [exact Henv' |]. split; [constructor |].
      split; [intros loc0 H; right; apply Hld, H |]. split; [intros loc0 H; right; apply Hpd, H |].
      apply separated_skip_safe; [exact (separated_protected_ok _ _ _ _ _ _ _ _ _ Henv') |
        exact (separated_local_free _ _ _ _ _ _ _ _ _ Henv') |exact HS' |exact HP'].
    + match goal with H : flush _ _ _ |- _ =>
        destruct (separated_environment_flush _ _ _ _ _ _ _ _ _ _ Henv H)
          as (local' & protected' & history' & Henv' & Hlf & Hpf & Hhf & Hld & Hpd) end.
      exists Open, local', protected', history'; split; [exact Henv' |]. split; [exact Hhf |].
      split; [intros loc0 H; left; apply Hld, H |]. split; [intros loc0 H; right; apply Hpd, H |]. apply IHn.
      * exact (separated_protected_ok _ _ _ _ _ _ _ _ _ Henv').
      * exact (separated_local_free _ _ _ _ _ _ _ _ _ Henv').
      * eapply protocol_assertion_flush; eassumption.
      * eapply persistent_assertion_flushing_closed; eassumption.
Qed.

(** Withdrawal can use unlock's existing empty-buffer guard. No additional
    machine fence instruction is required at this boundary. *)
Theorem separated_take_cell_release_valid active owner invariant loc v :
  separated_valid active owner invariant Open (owned_assertion owner (A.Spatial invariant (cell_assertion loc v))) A.Emp
    (Concurrent.Prim Concurrent.Unlock (EVal (Z.pos owner))) Closed A.Emp (processor_cell owner loc v).
Proof.
  intros s local protected Hr Hl HS HP n; revert s local protected Hr Hl HS HP.
  induction n; intros s local protected Hr Hl HS HP; [exact I |].
  split; [exact Hr |]. split; [exact Hl |]. split; [intros [ann E]; discriminate |]. split.
  - intros history whole Henv Hfault; inversion Hfault; subst.
    match goal with H : primitive_abort _ _ _ _ |- _ => inversion H end.
  - intros history whole next t whole' Henv Hstep; inversion Hstep; subst.
    + match goal with H : primitive_step _ _ _ _ _ |- _ => inversion H; subst end.
      match goal with E : eval_expr _ (EVal (Z.pos _)) = Z.pos _ |- _ => simpl in E; inversion E; subst end.
      destruct (separated_take_cell_environment _ _ _ _ _ _ _ _ _ _ _ Henv HS HP ltac:(assumption))
        as (moved & kept & Henv0 & HS0 & HP0 & Hmove & Hkeep).
      match goal with Hi : active ?i |- _ =>
        pose proof (separated_release_valid active i invariant (processor_cell i loc v) _ _ _
          (separated_protected_ok _ _ _ _ _ _ _ _ _ Henv0)
          (separated_local_free _ _ _ _ _ _ _ _ _ Henv0) HS0 HP0 2) as Hrelease end.
      destruct Hrelease as [_ [_ [_ [_ Hprogress]]]].
      destruct (Hprogress _ _ _ _ _ Henv0 Hstep)
        as (phase' & local' & protected' & history' & Henv' & Hfuture & Hld & Hpd & _ & _ & Hdone & _).
      destruct (Hdone ltac:(eexists; reflexivity)) as [-> [HS' HP']].
      exists Closed, local', protected', history'; split; [exact Henv' |]. split; [exact Hfuture |]. split.
      * intros address H; right; destruct (Hld address H); [apply Hmove |apply Hkeep]; assumption.
      * split.
        -- intros address H; right; destruct (Hpd address H); [apply Hmove |apply Hkeep]; assumption.
        -- apply separated_skip_safe; [exact (separated_protected_ok _ _ _ _ _ _ _ _ _ Henv') |
             exact (separated_local_free _ _ _ _ _ _ _ _ _ Henv') |exact HS' |exact HP'].
    + match goal with H : flush _ _ _ |- _ =>
        destruct (separated_environment_flush _ _ _ _ _ _ _ _ _ _ Henv H)
          as (local' & protected' & history' & Henv' & Hlf & Hpf & Hhf & Hld & Hpd) end.
      exists Open, local', protected', history'; split; [exact Henv' |]. split; [exact Hhf |].
      split; [intros loc0 H; left; apply Hld, H |]. split; [intros loc0 H; right; apply Hpd, H |]. apply IHn.
      * exact (separated_protected_ok _ _ _ _ _ _ _ _ _ Henv').
      * exact (separated_local_free _ _ _ _ _ _ _ _ _ Henv').
      * eapply protocol_assertion_flush; eassumption.
      * eapply persistent_assertion_flushing_closed; eassumption.
Qed.

(** A positive replacement for the failed unrestricted donation: reassembly
    works when external history is disjoint from the donated private cell.
    This is an environment lemma, NOT a separated_valid rule: that predicate
    quantifies over overlapping histories too. *)
Theorem history_disjoint_donation_recomposes active owner invariant s local protected history whole rest loc v :
  separated_environment active owner invariant Open s local protected history whole ->
  protocol_assertion active Open s protected (owned_assertion owner rest) ->
  persistent_models active s local (cell_assertion loc v) ->
  BufferRelations.disjoint (memory_domain (resource_memory active history)) (memory_domain (resource_memory active local)) ->
  exists protected', separated_environment active owner invariant Open s (bare_resource active) protected' history whole /\
    protocol_assertion active Open s protected' (owned_assertion owner (A.Spatial rest (cell_assertion loc v))) /\
    separated_owned_domain (resource_memory active local) protected protected'.
Proof.
  intros [Hregion Hl Hhistory [combined [Htm Hsp]]] HS HP Hdisjoint.
  assert (Hhistorylocal : memory_spatial (resource_memory active history) (resource_memory active local)
    (resource_memory active combined)).
  { destruct Htm as [_ [[_ [Hheap [Hbuffers Hblocks]]] _]]; split.
    - split; [exact Hdisjoint |intros i H _; exact (Hhistory i H)].
    - split; [exact Hheap |]. split; [|exact Hblocks]. intros i; rewrite Hbuffers; apply interleaves_app. }
  destruct (proj2 (memory_spatial_associative (resource_memory active history) (resource_memory active local) protected whole)
    (ex_intro _ (resource_memory active combined) (conj Hhistorylocal Hsp))) as (protected' & Hnewpool & Hwhole).
  destruct (full_spatial_elim _ _ _ _ _ HS) as (token & payload & Htoken & Hlock & Hpayload).
  destruct (proj2 (memory_spatial_associative token payload (resource_memory active local) protected')
    (ex_intro _ protected (conj Htoken (memory_spatial_comm _ _ _ Hnewpool)))) as (payload' & Hpayload' & Htoken').
  assert (HS' : persistent_full_satisfies active s protected'
    (owned_assertion owner (A.Spatial rest (cell_assertion loc v)))).
  { eapply full_spatial_intro; [exact Htoken' |exact Hlock |].
    eapply full_spatial_intro; [exact Hpayload' |exact Hpayload |apply persistent_promote_full, HP]. }
  assert (Hheld : lock_held active protected' owner).
  { destruct Hregion as [_ [Hi Hheld]]; split; [exact Hi |]. intros i.
    rewrite (proj2 (proj2 (proj2 Hnewpool)) i); split.
    - intros [H |H]; [exfalso; exact (Hl i H) |apply Hheld, H].
    - intros H; right; apply Hheld, H. }
  exists protected'; split.
  - constructor.
    + split; [exact (proj1 (persistent_full_well_formed _ _ _ _ HS')) |exact Hheld].
    + intros i H; contradiction.
    + exact Hhistory.
    + exists history; split; [apply repaired_temporal_bare_right |exact Hwhole].
  - split; [exact HS' |]. intros address H.
    apply (spatial_merge_domain _ _ _ (proj2 Hnewpool) address), H.
Qed.
