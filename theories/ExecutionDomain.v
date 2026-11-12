From Stdlib Require Import List ZArith.
From WMLR Require Import Expressions Languages Machine BufferRelations Separation
  OperationalSemantics FrameDecomposition Safety.
Import ListNotations.

(** Independent machine lemma requested for the Section 4.1 example.
    Domain means addresses present in either the heap or any buffer.
    The language has neither allocation nor deallocation. Stores require
    a readable address, and a flush moves a buffered address into the heap.
    No assertion, safety, finiteness or processor-count hypothesis is used. *)
Lemma enqueue_retains_domain m actor address value loc :
  memory_domain m loc -> memory_domain (enqueue m actor address value) loc.
Proof.
  intros [[v Hheap] |[i [v Hbuffer]]]; [left; exists v; exact Hheap |right].
  exists i,v; cbn [enqueue buffers]; unfold buffer_update.
  destruct (Pos.eq_dec i actor) as [-> |Hne]; [apply in_or_app; left; exact Hbuffer |exact Hbuffer].
Qed.

Theorem enqueue_preserves_domain m actor address value : memory_domain m address ->
  forall loc, memory_domain (enqueue m actor address value) loc <-> memory_domain m loc.
Proof.
  intros Haddress loc; split; [apply enqueue_domain_subset,Haddress |apply enqueue_retains_domain].
Qed.

Lemma flush_retains_domain active m final : flush active m final ->
  forall loc, memory_domain m loc -> memory_domain final loc.
Proof.
  intros Hflush loc Hdom; destruct Hflush as [m actor address value rest Hi Hfree Hbuffer].
  destruct Hdom as [[v Hheap] |[i [v Hpending]]].
  - left; destruct (Pos.eq_dec loc address) as [-> |Hne].
    + exists value; apply heap_update_same.
    + exists v; change (heap_update (shared_heap m) address value loc = Some v).
      unfold heap_update; destruct (Pos.eq_dec loc address); [contradiction |exact Hheap].
  - destruct (Pos.eq_dec i actor) as [-> |Hne].
    + rewrite Hbuffer in Hpending; destruct Hpending as [E |Hrest].
      * inversion E; subst; left; exists v; apply heap_update_same.
      * right; exists actor,v; change (In (loc,v) (buffer_update (buffers m) actor rest actor)).
        rewrite buffer_update_same; exact Hrest.
    + right; exists i,v; change (In (loc,v) (buffer_update (buffers m) actor rest i)).
      unfold buffer_update; destruct (Pos.eq_dec i actor); [contradiction |exact Hpending].
Qed.

Theorem flush_preserves_domain active m final : flush active m final ->
  forall loc, memory_domain final loc <-> memory_domain m loc.
Proof.
  intros Hflush loc; split; [apply (flush_domain_subset _ _ _ Hflush)
    |apply (flush_retains_domain _ _ _ Hflush)].
Qed.

Theorem primitive_preserves_domain active primitive actor initial final :
  primitive_step active primitive actor initial final ->
  forall loc, memory_domain (memory_state final) loc <-> memory_domain (memory_state initial) loc.
Proof.
  intros Hstep; destruct Hstep; intros address'; try reflexivity.
  apply enqueue_preserves_domain; eapply local_read_domain; eassumption.
Qed.

Theorem step_preserves_domain active command initial next final :
  step active command initial next final ->
  forall loc, memory_domain (memory_state final) loc <-> memory_domain (memory_state initial) loc.
Proof.
  intros Hstep; induction Hstep; intros loc; try reflexivity; try apply IHHstep.
  - eapply primitive_preserves_domain; eassumption.
  - eapply flush_preserves_domain; eassumption.
Qed.

Theorem steps_preserve_domain active command initial next final :
  steps active command initial next final ->
  forall loc, memory_domain (memory_state final) loc <-> memory_domain (memory_state initial) loc.
Proof.
  intros Hrun; induction Hrun; intros loc; [reflexivity |].
  rewrite IHHrun; eapply step_preserves_domain; eassumption.
Qed.

Theorem execution_preserves_domain active n command s initial next t final :
  execution active n command s initial next t final ->
  forall loc, memory_domain final loc <-> memory_domain initial loc.
Proof.
  intros Hrun; induction Hrun; intros loc; [reflexivity |].
  rewrite IHHrun; exact (step_preserves_domain _ _ _ _ _ H loc).
Qed.
