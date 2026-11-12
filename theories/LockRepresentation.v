From Stdlib Require Import List ZArith.
From WMLR Require Import Expressions Machine OperationalSemantics Separation ConcreteAssertions.
Import ListNotations.

(** Checkpoint 5 diagnostic only: no new safety predicate or restriction on
    the existing semantics is introduced here. The blocked-set encoding of
    a held lock coincides with a free lock on a singleton processor domain. *)
Theorem free_held_characterization active m owner :
  lock_free m ->
  (lock_held active m owner <->
   active owner /\ forall i, active i -> i = owner).
Proof.
  intros Hfree; split.
  - intros [Howner Hheld]; split; [exact Howner |].
    intros i Hi; destruct (Pos.eq_dec i owner) as [Heq | Hne]; [exact Heq |].
    exfalso; apply (Hfree i), Hheld; auto.
  - intros [Howner Hsingle]; split; [exact Howner |].
    intros i; split.
    + intros Hblocked; exfalso; exact (Hfree i Hblocked).
    + intros [Hi Hne]; exfalso; apply Hne, Hsingle, Hi.
Qed.

(** A second diagnostic: complete physical blocking can be assembled from
    two individually incomplete pieces. A proposed environment must not
    reject every such piece just because neither side owns the whole token. *)
Module SplitLockWitness.

Definition active (i : processor) : Prop := i = 1%positive \/ i = 2%positive \/ i = 3%positive.
Definition part (i : processor) : generalized_memory :=
  Generalized (Memory empty_heap empty_buffers (fun j => j = i)) no_blocked.
Definition whole : memory :=
  Memory empty_heap empty_buffers (fun i => i = 2%positive \/ i = 3%positive).

Theorem fragments_well_formed :
  generalized_well_formed active (part 2%positive) /\
  generalized_well_formed active (part 3%positive).
Proof.
  assert (Hpart : forall i, active i -> generalized_well_formed active (part i)).
  { intros i Hi; split.
    - split; [intros j ->; exact Hi |intros; reflexivity].
    - split; [intros j H; contradiction |intros; reflexivity]. }
  split; apply Hpart; unfold active; auto.
Qed.

Theorem fragments_compose :
  spatial (part 2%positive) (part 3%positive) (Generalized whole no_blocked).
Proof.
  split.
  - split.
    + split.
      * intros loc [[v H] | [i [v H]]] _; discriminate || contradiction.
      * intros i Htwo Hthree; change (i = 2%positive) in Htwo;
          change (i = 3%positive) in Hthree; congruence.
    + split; [intros; reflexivity |]. split; [intros; constructor |intros; reflexivity].
  - intros i; cbn; unfold no_blocked; tauto.
Qed.

Theorem whole_held : lock_held active whole 1%positive.
Proof.
  split; [left; reflexivity |]. intros i; cbn; unfold active.
  split.
  - intros [-> | ->]; split; auto; discriminate.
  - intros [[Heq | Hother] Hne]; [contradiction | exact Hother].
Qed.

Theorem parts_incomplete :
  ~ lock_complete active (underlying (part 2%positive)) /\
  ~ lock_complete active (underlying (part 3%positive)).
Proof.
  split; intros [Hfree | [owner [Hactive Hheld]]].
  - apply (Hfree 2%positive); reflexivity.
  - unfold active in Hactive; destruct Hactive as [-> | [-> | ->]].
    + assert (H : 3%positive = 2%positive).
      { apply Hheld; split; [unfold active; auto |discriminate]. }
      discriminate.
    + destruct (proj1 (Hheld 2%positive) eq_refl) as [_ H]; contradiction.
    + assert (H : 1%positive = 2%positive).
      { apply Hheld; split; [unfold active; auto |discriminate]. }
      discriminate.
  - apply (Hfree 3%positive); reflexivity.
  - unfold active in Hactive; destruct Hactive as [-> | [-> | ->]].
    + assert (H : 2%positive = 3%positive).
      { apply Hheld; split; [unfold active; auto |discriminate]. }
      discriminate.
    + assert (H : 1%positive = 3%positive).
      { apply Hheld; split; [unfold active; auto |discriminate]. }
      discriminate.
    + destruct (proj1 (Hheld 3%positive) eq_refl) as [_ H]; contradiction.
Qed.

Theorem failing_assert_enabled s :
  primitive_abort active (C.Common (S.Assert BFalse)) 1%positive (State s whole).
Proof. apply AbortAssert; [left; reflexivity | reflexivity]. Qed.

End SplitLockWitness.

Theorem singleton_emp_lock_equivalent owner g :
  lock_atom (fun i => i = owner) (Z.pos owner) g <-> empty_atom g.
Proof.
  unfold lock_atom, empty_atom; split.
  - intros [Hheap [Hbuffers [_ Hheld]]]; repeat split; try assumption.
    intros i Hblocked; destruct (proj1 (Hheld i) Hblocked); contradiction.
  - intros [Hheap [Hbuffers Hfree]]; split; [exact Hheap |].
    split; [exact Hbuffers |].
    apply (proj2 (free_held_characterization _ _ _ Hfree)); auto.
Qed.

Theorem singleton_acquire_still_free owner m :
  lock_free (acquire (fun i => i = owner) m owner).
Proof. intros i [Heq Hne]; contradiction. Qed.

Theorem singleton_empty_acquire_enabled owner s :
  primitive_step (fun i => i = owner) C.Lock owner
    (State s (Memory empty_heap empty_buffers no_blocked))
    (State s (acquire (fun i => i = owner)
      (Memory empty_heap empty_buffers no_blocked) owner)).
Proof. apply PrimitiveLock; [reflexivity | reflexivity | intros i H; exact H]. Qed.

(** Two distinct active processors suffice to separate free from held.
    This is a conditional theorem, not a new ambient assumption. *)
Theorem two_processors_separate_free_held active first second m owner :
  active first -> active second -> first <> second ->
  lock_free m -> ~ lock_held active m owner.
Proof.
  intros Hfirst Hsecond Hne Hfree Hheld.
  destruct (proj1 (free_held_characterization _ _ _ Hfree) Hheld) as [_ Hsingle].
  apply Hne; transitivity owner; [apply Hsingle, Hfirst |symmetry; apply Hsingle, Hsecond].
Qed.
