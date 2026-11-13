From Stdlib Require Import List ZArith.
From WMLR Require Import Expressions Languages Machine BufferRelations Separation
  OperationalSemantics FrameDecomposition Assertions AssertionSemantics ConcreteAssertions.
Import ListNotations.

Definition all_processors : processor_domain := fun _ => True.
Definition cell_memory loc v := Memory (heap_update empty_heap loc v) empty_buffers no_blocked.
Definition cell_generalized loc v := Generalized (cell_memory loc v) all_processors.
Definition full_barrier := Generalized empty_memory all_processors.
Definition pending_generalized i loc v := Generalized
  (Memory empty_heap (buffer_update empty_buffers i [(loc, v)]) no_blocked) no_blocked.

Lemma cell_valid loc v : generalized_well_formed all_processors (cell_generalized loc v).
Proof.
  split; [split; [intros i H; contradiction | intros i _; reflexivity] |].
  split; [intros; exact I |].
  intros Hempty address. exfalso. apply (Hempty 1%positive). exact I.
Qed.

Lemma full_barrier_valid : generalized_well_formed all_processors full_barrier.
Proof.
  split; [split; [intros i H; contradiction | intros i _; reflexivity] |].
  split; [intros; exact I | intros; reflexivity].
Qed.

Lemma pending_valid i loc v :
  generalized_well_formed all_processors (pending_generalized i loc v).
Proof.
  split; [split | split].
  - intros j H; contradiction.
  - intros j H; exfalso; apply H; exact I.
  - intros j H; contradiction.
  - intros; reflexivity.
Qed.

Definition cell_resource loc v : resource all_processors :=
  exist _ (cell_generalized loc v) (cell_valid loc v).
Definition full_barrier_resource : resource all_processors := exist _ full_barrier full_barrier_valid.
Definition pending_resource i loc v : resource all_processors :=
  exist _ (pending_generalized i loc v) (pending_valid i loc v).

Lemma cell_flushed i loc v : flushed_atom i loc v (cell_generalized loc v).
Proof.
  split; [intros; reflexivity |]. split; [intros; reflexivity |].
  split; [intros j H; contradiction | exact I].
Qed.

Lemma cell_temporal_full_barrier loc v :
  temporal all_processors (cell_generalized loc v) full_barrier (cell_generalized loc v).
Proof.
  split; [split | split].
  - apply spatial_compatible_temporal.
    exact (proj1 (proj1 (spatial_empty_right (cell_generalized loc v)))).
  - split; [intros address; reflexivity |]. split.
    + intros i; reflexivity.
    + intros i; simpl; unfold no_blocked; tauto.
  - intros i _; reflexivity.
  - intros i; simpl; unfold all_processors; tauto.
Qed.

Example concrete_points_to_cell s :
  models all_processors s (cell_resource 1%positive 7%Z)
    (ConcurrentAssertion.points_to (EVal 1%Z) (EVal 7%Z)).
Proof.
  change (exists a b : resource all_processors,
    temporal all_processors (proj1_sig a) (proj1_sig b)
      (cell_generalized 1%positive 7%Z) /\
    (exists i, write_atom all_processors 1%Z i 7%Z (proj1_sig a)) /\
    (forall i, barrier_atom all_processors i (proj1_sig b))).
  exists (cell_resource 1%positive 7%Z), full_barrier_resource.
  split; [apply cell_temporal_full_barrier |]. split.
  - exists 1%Z. split; [exact I | right; apply cell_flushed].
  - intros i. split.
    + split; [intros; reflexivity |]. split; [intros; reflexivity | intros j H; contradiction].
    + destruct i; simpl; [exact I | right; exact I | exact I].
Qed.

Example concrete_pending_leads_to s :
  models all_processors s (pending_resource 1%positive 1%positive 7%Z)
    (ConcurrentAssertion.LeadsTo (EVal 1%Z) (EVal 1%Z) (EVal 7%Z)).
Proof.
  change (all_processors 1%positive /\
    (pending_atom 1%positive 1%positive 7%Z (pending_generalized 1%positive 1%positive 7%Z) \/
     flushed_atom 1%positive 1%positive 7%Z (pending_generalized 1%positive 1%positive 7%Z))).
  split; [exact I | left]. split; [intros; reflexivity |].
  split; [intros; reflexivity | intros j H; contradiction].
Qed.

Example concrete_pending_not_points_to s :
  ~ models all_processors s (pending_resource 1%positive 1%positive 7%Z)
    (ConcurrentAssertion.points_to (EVal 1%Z) (EVal 7%Z)).
Proof.
  intros H. pose proof (points_to_has_no_pending_writes _ _ _ _ _ H 1%positive) as Hb.
  cbn [pending_resource pending_generalized proj1_sig underlying buffers] in Hb.
  rewrite buffer_update_same in Hb. discriminate.
Qed.

Example temporal_rejects_pending_before_complete out :
  ~ temporal all_processors (pending_generalized 1%positive 1%positive 7%Z) full_barrier out.
Proof.
  intros [_ [H _]]. specialize (H 1%positive I).
  cbn [pending_generalized underlying buffers] in H.
  rewrite buffer_update_same in H; discriminate.
Qed.

Example spatiotemporal_permits_pending_before_complete :
  spatiotemporal all_processors (pending_generalized 1%positive 1%positive 7%Z)
    full_barrier (Generalized (underlying (pending_generalized 1%positive 1%positive 7%Z)) all_processors).
Proof.
  apply spatial_in_spatiotemporal. split.
  - exact (proj1 (spatial_empty_right (pending_generalized 1%positive 1%positive 7%Z))).
  - intros i; simpl; unfold all_processors, no_blocked; tauto.
Qed.

Example unmarked_heap_invalid :
  ~ generalized_well_formed all_processors (Generalized (cell_memory 1%positive 7%Z) no_blocked).
Proof.
  intros [_ [_ H]]. specialize (H (fun _ Hfalse => Hfalse) 1%positive).
  change (heap_update empty_heap 1%positive 7%Z 1%positive = None) in H.
  rewrite heap_update_same in H; discriminate.
Qed.

Lemma cell_domain loc v address : memory_domain (cell_memory loc v) address <-> address = loc.
Proof.
  split.
  - intros [[w H] | [i [w H]]]; [|contradiction].
    cbn [cell_memory shared_heap] in H. unfold heap_update, empty_heap in H.
    destruct (Pos.eq_dec address loc); [assumption | discriminate].
  - intros Heq; subst address. left; exists v; apply heap_update_same.
Qed.

Lemma duplicate_cell_spatiotemporal active loc v :
  memory_spatiotemporal active (cell_memory loc v) (cell_memory loc v) (cell_memory loc v).
Proof.
  split.
  - split; [intros i H; contradiction |]. split.
    + intros i _ address [w H]; contradiction.
    + intros i j _ _ _ address [w H]; contradiction.
  - split.
    + intros address. unfold heap_override.
      destruct (shared_heap (cell_memory loc v) address); reflexivity.
    + split; [intros i; apply append_overrides |].
      intros i; simpl; unfold no_blocked; tauto.
Qed.

Lemma duplicate_cell_not_spatial loc v out :
  ~ memory_spatial (cell_memory loc v) (cell_memory loc v) out.
Proof.
  intros [[Hdomain _] _]. apply (Hdomain loc); apply cell_domain; reflexivity.
Qed.

(** The quantified assertion of Conjecture 1, p. 174, on the concrete
    operational model. Flushing is oriented from the original to its residual. *)
Definition original_conjecture1 active : Prop :=
  forall frame local whole frame' local' whole' command next s s',
    memory_spatial frame local whole ->
    step active command (State s whole) next (State s' whole') ->
    memory_flushes active frame frame' ->
    memory_spatiotemporal active frame' local' whole' ->
    forall out, memory_spatiotemporal active frame' local' out <->
      memory_spatial frame' local' out.

Theorem original_conjecture1_false : ~ original_conjecture1 all_processors.
Proof.
  intros Hconjecture.
  set (cell := cell_memory 1%positive 7%Z).
  set (s := (fun _ => 0%Z) : stack).
  set (command := Concurrent.Prim (Concurrent.Common (Sequential.Assume BTrue)) (EVal 1%Z)).
  assert (Hsep : memory_spatial cell empty_memory cell).
  { exact (proj1 (spatial_empty_right (Generalized cell all_processors))). }
  assert (Hstep : step all_processors command (State s cell) halt (State s cell)).
  { eapply StepPrimitive with (i := 1%positive); [reflexivity |].
    apply PrimitiveAssume; [exact I | reflexivity]. }
  pose proof (Hconjecture cell empty_memory cell cell cell cell command halt s s
    Hsep Hstep (MemoryFlushesRefl all_processors cell)
    (duplicate_cell_spatiotemporal all_processors 1%positive 7%Z) cell) as Hresult.
  apply (duplicate_cell_not_spatial 1%positive 7%Z cell).
  apply Hresult, duplicate_cell_spatiotemporal.
Qed.

(** The new operational hypothesis rejects exactly the invented ownership
    in the counterexample: executing empty memory cannot produce a cell. *)
Example empty_execution_cannot_acquire_cell active command next s s' :
  ~ steps active command (State s empty_memory) next (State s' (cell_memory 1%positive 7%Z)).
Proof.
  intros Hsteps. pose proof (steps_domain_subset _ _ _ _ _ Hsteps 1%positive) as Hdomain.
  assert (Hcell : memory_domain (cell_memory 1%positive 7%Z) 1%positive).
  { apply cell_domain; reflexivity. }
  destruct (Hdomain Hcell) as [[v H] | [i [v H]]]; discriminate || contradiction.
Qed.
