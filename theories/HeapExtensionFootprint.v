From Stdlib Require Import List ZArith.
From WMLR Require Import Expressions Languages Machine OperationalSemantics Safety HeapExtension.
Import ListNotations.

(** The existing ghost-heap erasure argument with finitely many address
    expressions. This is a syntactic access bound, not a safety predicate. *)
Fixpoint accesses_within (addresses : list expr) (command : C.command) : Prop :=
  match command with
  |C.Prim (C.Common (S.Load _ e)) _ |C.Prim (C.Common (S.Store e _)) _ => In e addresses
  |C.Prim _ _ => True
  |C.Seq a b |C.Choice a b |C.Parallel a b => accesses_within addresses a /\ accesses_within addresses b
  |C.Loop body => accesses_within addresses body end.

Lemma step_accesses_within active command initial next final : step active command initial next final ->
  forall addresses, accesses_within addresses command -> accesses_within addresses next.
Proof.
  intros H; induction H; intros addresses HA; cbn [accesses_within halt C.skip] in *; intuition.
Qed.
Theorem execution_accesses_within active n command s initial last t final :
  execution active n command s initial last t final ->
  forall addresses, accesses_within addresses command -> accesses_within addresses last.
Proof. intros H; induction H; intros addresses HA; [exact HA |apply IHexecution; eapply step_accesses_within; eassumption]. Qed.

Theorem abort_heap_extension_within active command initial : abort active command initial ->
  forall addresses extra extended, accesses_within addresses command ->
  heap_extension extra (memory_state initial) extended ->
  (forall e, In e addresses -> forall loc, eval_expr (registers initial) e = Z.pos loc -> extra loc = None) ->
  abort active command (State (registers initial) extended).
Proof.
  intros H; induction H; intros addresses extra extended HA HE Hfresh.
  - pose proof HE as [Hh [Hb Hk]]; inversion H0; subst; cbn [accesses_within] in HA.
    + eapply CommandAbort; [exact H |apply AbortAssert; assumption].
    + eapply CommandAbort; [exact H |]. apply AbortLoad; [assumption |intros HK; apply (Hk i) in HK; contradiction |].
      rewrite (heap_extension_read_fresh _ _ _ _ _ HE (Hfresh _ HA)); assumption.
    + eapply CommandAbort; [exact H |]. apply AbortStore; [assumption |].
      rewrite (heap_extension_read_fresh _ _ _ _ _ HE (Hfresh _ HA)); assumption.
  - apply SeqAbort; eapply IHabort; [exact (proj1 HA) |exact HE |exact Hfresh].
  - apply ParallelLeftAbort; eapply IHabort; [exact (proj1 HA) |exact HE |exact Hfresh].
  - apply ParallelRightAbort; eapply IHabort; [exact (proj2 HA) |exact HE |exact Hfresh].
Qed.
