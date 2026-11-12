From Stdlib Require Import List ZArith.
From WMLR Require Import Expressions Languages Machine BufferRelations Separation OperationalSemantics Safety.
Import ListNotations.

(** A relation between concrete machines, not a safety/validity predicate.
    The original heap overrides the extra cells; buffers and lock bits
    agree. Pointwise equations avoid extensionality axioms. *)
Definition heap_extension (extra : heap) (original extended : memory) : Prop :=
  (forall loc, shared_heap extended loc = heap_override extra (shared_heap original) loc) /\
  (forall i, buffers extended i = buffers original i) /\
  (forall i, blocked extended i <-> blocked original i).

Lemma heap_extension_read_some extra original extended actor address value :
  heap_extension extra original extended -> local_read original actor address = Some value ->
  local_read extended actor address = Some value.
Proof.
  intros [Hh [Hb Hk]] H; destruct address; try discriminate.
  cbn [local_read] in *; rewrite Hb; destruct (buffer_lookup (buffers original actor) p); [exact H |].
  rewrite Hh; unfold heap_override; rewrite H; reflexivity.
Qed.

Lemma heap_extension_read_fresh extra original extended actor address :
  heap_extension extra original extended ->
  (forall loc, address = Z.pos loc -> extra loc = None) ->
  local_read extended actor address = local_read original actor address.
Proof.
  intros [Hh [Hb Hk]] Hfresh; destruct address; try reflexivity.
  cbn [local_read]; rewrite Hb; destruct (buffer_lookup (buffers original actor) p); [reflexivity |].
  rewrite Hh; unfold heap_override; destruct (shared_heap original p); [reflexivity |apply Hfresh; reflexivity].
Qed.

Lemma heap_extension_enqueue extra original extended actor loc value :
  heap_extension extra original extended ->
  heap_extension extra (enqueue original actor loc value) (enqueue extended actor loc value).
Proof.
  intros [Hh [Hb Hk]]; split; [exact Hh |]. split; [|exact Hk].
  intros i; cbn [enqueue buffers]; unfold buffer_update; destruct (Pos.eq_dec i actor); rewrite Hb; reflexivity.
Qed.

Lemma heap_extension_flush_write extra original extended actor loc value rest :
  heap_extension extra original extended ->
  heap_extension extra (flush_write original actor loc value rest) (flush_write extended actor loc value rest).
Proof.
  intros [Hh [Hb Hk]]; split.
  - intros l; cbn [flush_write shared_heap]; unfold heap_update,heap_override.
    destruct (Pos.eq_dec l loc); [reflexivity |apply Hh].
  - split; [|exact Hk]; intros i; cbn [flush_write buffers]; unfold buffer_update.
    destruct (Pos.eq_dec i actor); [reflexivity |apply Hb].
Qed.

Theorem primitive_heap_extension active primitive actor s original t final :
  primitive_step active primitive actor (State s original) (State t final) ->
  forall extra extended, heap_extension extra original extended ->
  exists final_extended, primitive_step active primitive actor (State s extended) (State t final_extended) /\
    heap_extension extra final final_extended.
Proof.
  intros Hstep; inversion Hstep; subst; intros extra extended HE; pose proof HE as [Hh [Hb Hk]].
  - exists extended; split; [apply PrimitiveAssume; assumption |exact HE].
  - exists extended; split; [apply PrimitiveAssert; assumption |exact HE].
  - exists extended; split; [apply PrimitiveAssign; assumption |exact HE].
  - exists extended; split; [|exact HE]; apply PrimitiveLoad; try assumption.
    + intros HB; apply (Hk actor) in HB; contradiction.
    + eapply heap_extension_read_some; eassumption.
  - exists (enqueue extended actor loc (eval_expr t rhs)); split.
    + eapply PrimitiveStore; try eassumption; eapply heap_extension_read_some; eassumption.
    + apply heap_extension_enqueue,HE.
  - exists extended; split; [apply PrimitiveFence; [assumption |rewrite Hb; assumption] |exact HE].
  - exists (acquire active extended actor); split.
    + apply PrimitiveLock; [assumption |rewrite Hb; assumption |].
      intros i Hi; apply (Hk i) in Hi.
      match goal with HF : lock_free _ |- _ => exact (HF i Hi) end.
    + split; [exact Hh |split; [exact Hb |intros; reflexivity]].
  - exists (release extended); split.
    + apply PrimitiveUnlock; [assumption |rewrite Hb; assumption |].
      match goal with H : lock_held _ _ _ |- _ => destruct H as [Hi Hheld]; split; [exact Hi |intros i; rewrite Hk; apply Hheld] end.
    + split; [exact Hh |split; [exact Hb |intros; reflexivity]].
Qed.

Lemma flush_heap_extension active original final : flush active original final ->
  forall extra extended, heap_extension extra original extended ->
  exists final_extended, flush active extended final_extended /\ heap_extension extra final final_extended.
Proof.
  intros Hflush; destruct Hflush as [original actor loc value rest Hi Hfree Hbuffer].
  intros extra extended HE; pose proof HE as [Hh [Hb Hk]].
  exists (flush_write extended actor loc value rest); split; [|apply heap_extension_flush_write,HE].
  apply FlushWrite; [exact Hi |intros H; apply Hfree,(Hk actor),H |rewrite Hb; exact Hbuffer].
Qed.

Theorem step_heap_extension active command initial next final : step active command initial next final ->
  forall extra extended, heap_extension extra (memory_state initial) extended ->
  exists final_extended,
    step active command (State (registers initial) extended) next (State (registers final) final_extended) /\
    heap_extension extra (memory_state final) final_extended.
Proof.
  intros Hstep; induction Hstep; intros extra extended HE; cbn in *.
  - destruct final as [t final]. destruct (primitive_heap_extension _ _ _ _ _ _ _ H0 _ _ HE) as [out [HS HX]].
    exists out; split; [eapply StepPrimitive; eassumption |exact HX].
  - destruct (flush_heap_extension _ _ _ H _ _ HE) as [out [HS HX]].
    exists out; split; [apply StepFlush,HS |exact HX].
  - destruct (IHHstep _ _ HE) as [out [HS HX]]; exists out; split; [apply StepSeq,HS |exact HX].
  - exists extended; split; [apply StepSeqDone |exact HE].
  - exists extended; split; [apply StepChoiceLeft |exact HE].
  - exists extended; split; [apply StepChoiceRight |exact HE].
  - exists extended; split; [apply StepLoop |exact HE].
  - destruct (IHHstep _ _ HE) as [out [HS HX]]; exists out; split; [apply StepParallelLeft,HS |exact HX].
  - destruct (IHHstep _ _ HE) as [out [HS HX]]; exists out; split; [apply StepParallelRight,HS |exact HX].
  - exists extended; split; [apply StepParallelLeftDone |exact HE].
  - exists extended; split; [apply StepParallelRightDone |exact HE].
Qed.

Theorem execution_heap_extension active n command s original last t final :
  execution active n command s original last t final ->
  forall extra extended, heap_extension extra original extended ->
  exists final_extended, execution active n command s extended last t final_extended /\
    heap_extension extra final final_extended.
Proof.
  intros Hrun; induction Hrun; intros extra extended HE.
  - exists extended; split; [constructor |exact HE].
  - destruct (step_heap_extension _ _ _ _ _ H _ _ HE) as [middle' [HS HX]].
    destruct (IHHrun _ _ HX) as [final' [HR HY]].
    exists final'; split; [eapply ExecuteNext; eassumption |exact HY].
Qed.

Fixpoint accesses_only (address : expr) (command : C.command) : Prop :=
  match command with
  | C.Prim (C.Common (S.Load _ e)) _ | C.Prim (C.Common (S.Store e _)) _ => e = address
  | C.Prim _ _ => True
  | C.Seq a b | C.Choice a b | C.Parallel a b => accesses_only address a /\ accesses_only address b
  | C.Loop body => accesses_only address body
  end.

Lemma step_accesses_only active command initial next final : step active command initial next final ->
  forall address, accesses_only address command -> accesses_only address next.
Proof.
  intros H; induction H; intros address HA; cbn [accesses_only halt C.skip] in *; intuition.
Qed.

Theorem execution_accesses_only active n command s initial last t final :
  execution active n command s initial last t final ->
  forall address, accesses_only address command -> accesses_only address last.
Proof. intros H; induction H; intros address HA; [exact HA |apply IHexecution; eapply step_accesses_only; eassumption]. Qed.

Theorem execution_preserves_unmodified active n command s initial last t final :
  execution active n command s initial last t final ->
  forall x, ~ In x (C.modifies command) -> s x = t x.
Proof.
  intros H; induction H; intros x Hfresh; [reflexivity |].
  transitivity (t x); [exact (step_preserves_unmodified _ _ _ _ _ H x Hfresh) |].
  apply IHexecution; intros Hin; apply Hfresh; eapply step_modifies_subset; eassumption.
Qed.

Theorem abort_heap_extension active command initial : abort active command initial ->
  forall address extra extended, accesses_only address command ->
  heap_extension extra (memory_state initial) extended ->
  (forall loc, eval_expr (registers initial) address = Z.pos loc -> extra loc = None) ->
  abort active command (State (registers initial) extended).
Proof.
  intros H; induction H; intros address extra extended HA HE Hfresh.
  - pose proof HE as [Hh [Hb Hk]]; inversion H0; subst; cbn [accesses_only] in HA.
    + eapply CommandAbort; [exact H |apply AbortAssert; assumption].
    + subst address0; eapply CommandAbort; [exact H |].
      apply AbortLoad; [assumption |intros HK; apply (Hk i) in HK; contradiction |].
      rewrite (heap_extension_read_fresh _ _ _ _ _ HE Hfresh); assumption.
    + subst address0; eapply CommandAbort; [exact H |].
      apply AbortStore; [assumption |].
      rewrite (heap_extension_read_fresh _ _ _ _ _ HE Hfresh); assumption.
  - apply SeqAbort; eapply IHabort; [exact (proj1 HA) |exact HE |exact Hfresh].
  - apply ParallelLeftAbort; eapply IHabort; [exact (proj1 HA) |exact HE |exact Hfresh].
  - apply ParallelRightAbort; eapply IHabort; [exact (proj2 HA) |exact HE |exact Hfresh].
Qed.
