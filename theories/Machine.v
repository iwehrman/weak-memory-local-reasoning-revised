From Stdlib Require Import List ZArith.
From WMLR Require Import Expressions.
Import ListNotations.

(** Definition 4, pp. 90-92. Locations are positive integers. The processor
    domain is an explicit parameter of execution, allowing finite machines.
    Heap functions need not have finite support, matching the dissertation. *)
Definition location := positive.
Definition processor := positive.
Definition processor_domain := processor -> Prop.
Definition heap := location -> option value.
Definition write_buffer := list (location * value).
Definition buffer_array := processor -> write_buffer.
Definition blocked_set := processor -> Prop.

Definition empty_heap : heap := fun _ => None.
Definition empty_buffers : buffer_array := fun _ => [].
Definition no_blocked : blocked_set := fun _ => False.

Definition heap_update (h : heap) (address : location) (v : value) : heap :=
  fun other => if Pos.eq_dec other address then Some v else h other.

Definition buffer_update (buffers : buffer_array) (i : processor)
    (b : write_buffer) : buffer_array :=
  fun other => if Pos.eq_dec other i then b else buffers other.

Record memory := Memory {
  shared_heap : heap;
  buffers : buffer_array;
  blocked : blocked_set
}.

Record state := State {
  registers : stack;
  memory_state : memory
}.

(** The list head is the oldest write. Looking up the tail first implements
    the dissertation's convention that the most recent matching write wins. *)
Fixpoint buffer_lookup (b : write_buffer) (address : location) : option value :=
  match b with
  | [] => None
  | (other, v) :: rest =>
      match buffer_lookup rest address with
      | Some latest => Some latest
      | None => if Pos.eq_dec address other then Some v else None
      end
  end.

Definition local_read (m : memory) (i : processor) (address : value)
    : option value :=
  match address with
  | Z.pos loc =>
      match buffer_lookup (buffers m i) loc with
      | Some v => Some v
      | None => shared_heap m loc
      end
  | _ => None
  end.

Definition enqueue (m : memory) (i : processor) (address : location)
    (v : value) : memory :=
  Memory (shared_heap m)
    (buffer_update (buffers m) i (buffers m i ++ [(address, v)]))
    (blocked m).

Definition flush_write (m : memory) (i : processor) (address : location)
    (v : value) (rest : write_buffer) : memory :=
  Memory (heap_update (shared_heap m) address v)
    (buffer_update (buffers m) i rest) (blocked m).

Definition blocked_except (active : processor_domain) (owner : processor)
    : blocked_set := fun i => active i /\ i <> owner.

Definition acquire (active : processor_domain) (m : memory) (i : processor)
    : memory := Memory (shared_heap m) (buffers m) (blocked_except active i).

Definition release (m : memory) : memory :=
  Memory (shared_heap m) (buffers m) no_blocked.

(** Set equalities are expressed pointwise, avoiding a dependency on
    functional or propositional extensionality. *)
Definition lock_free (m : memory) : Prop := forall i, ~ blocked m i.

Definition lock_held (active : processor_domain) (m : memory) (owner : processor)
    : Prop := active owner /\
      forall i, blocked m i <-> active i /\ i <> owner.

Definition lock_complete (active : processor_domain) (m : memory) : Prop :=
  lock_free m \/ exists owner, lock_held active m owner.

(** States may carry partial lock information. Well-formedness only requires
    that blocked processors and nonempty buffers belong to the domain. *)
Definition memory_well_formed (active : processor_domain) (m : memory) : Prop :=
  (forall i, blocked m i -> active i) /\
  (forall i, ~ active i -> buffers m i = []).

(** Silent transitions, p. 95, remove precisely the oldest write. *)
Inductive flush (active : processor_domain) : memory -> memory -> Prop :=
| FlushWrite m i address v rest :
    active i ->
    ~ blocked m i ->
    buffers m i = (address, v) :: rest ->
    flush active m (flush_write m i address v rest).

Lemma heap_update_same h address v :
  heap_update h address v address = Some v.
Proof. unfold heap_update; destruct (Pos.eq_dec address address); congruence. Qed.

Lemma heap_update_other h address other v :
  other <> address -> heap_update h address v other = h other.
Proof. unfold heap_update; destruct (Pos.eq_dec other address); congruence. Qed.

Lemma buffer_update_same b i rest : buffer_update b i rest i = rest.
Proof. unfold buffer_update; destruct (Pos.eq_dec i i); congruence. Qed.

Lemma buffer_update_other b i j rest :
  j <> i -> buffer_update b i rest j = b j.
Proof. unfold buffer_update; destruct (Pos.eq_dec j i); congruence. Qed.

Lemma buffer_lookup_app b1 b2 address :
  buffer_lookup (b1 ++ b2) address =
  match buffer_lookup b2 address with
  | Some v => Some v
  | None => buffer_lookup b1 address
  end.
Proof.
  induction b1 as [|[other v] rest IH]; simpl.
  - destruct (buffer_lookup b2 address); reflexivity.
  - rewrite IH. destruct (buffer_lookup b2 address); reflexivity.
Qed.

Theorem buffer_lookup_newest b address v :
  buffer_lookup (b ++ [(address, v)]) address = Some v.
Proof.
  rewrite buffer_lookup_app. simpl.
  destruct (Pos.eq_dec address address); congruence.
Qed.

Theorem enqueue_read_own_write m i address v :
  local_read (enqueue m i address v) i (Z.pos address) = Some v.
Proof.
  unfold local_read, enqueue; simpl.
  rewrite buffer_update_same, buffer_lookup_newest. reflexivity.
Qed.

Theorem enqueue_other_processor_read m i j address v query :
  j <> i ->
  local_read (enqueue m i address v) j query = local_read m j query.
Proof.
  intros Hneq. destruct query; simpl; try reflexivity.
  unfold enqueue; simpl. rewrite buffer_update_other by exact Hneq. reflexivity.
Qed.

Lemma update_buffers_well_formed active m i b :
  active i -> memory_well_formed active m ->
  memory_well_formed active
    (Memory (shared_heap m) (buffer_update (buffers m) i b) (blocked m)).
Proof.
  intros Hi [Hblocked Hbuffers]. split; [exact Hblocked |].
  intros j Hj. simpl. rewrite buffer_update_other.
  - apply Hbuffers, Hj.
  - intros Heq. subst j. contradiction.
Qed.

Lemma acquire_well_formed active m i :
  memory_well_formed active m -> memory_well_formed active (acquire active m i).
Proof.
  intros [_ Hbuffers]. split; [intros j [Hj _]; exact Hj | exact Hbuffers].
Qed.

Lemma release_well_formed active m :
  memory_well_formed active m -> memory_well_formed active (release m).
Proof.
  intros [_ Hbuffers]. split; [intros j H; contradiction | exact Hbuffers].
Qed.

Theorem flush_preserves_well_formed active m m' :
  flush active m m' -> memory_well_formed active m -> memory_well_formed active m'.
Proof.
  intros Hflush Hwf. destruct Hflush.
  exact (update_buffers_well_formed _ _ _ _ H Hwf).
Qed.

Theorem flush_preserves_lock_complete active m m' :
  flush active m m' -> lock_complete active m -> lock_complete active m'.
Proof. intros Hflush Hcomplete; destruct Hflush; exact Hcomplete. Qed.
