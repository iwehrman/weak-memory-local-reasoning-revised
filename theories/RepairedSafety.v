From Stdlib Require Import List Arith Lia ZArith.
From WMLR Require Import Expressions Languages Machine BufferRelations OrderedBuffers Separation
  RepairedSeparation RepairedFlushing FrameDecomposition OperationalSemantics
  Assertions AssertionSemantics ConcreteAssertions RepairedAssertions Safety.
Import ListNotations.

Definition repaired_framed active shared frame local whole : Prop :=
  exists combined, memory_repaired active frame local combined /\ memory_spatial shared combined whole.

Record repaired_environment active (invariant : state_predicate) s local shared frame whole : Prop := {
  repaired_environment_local_wf : memory_well_formed active local;
  repaired_environment_shared_wf : memory_well_formed active shared;
  repaired_environment_frame_wf : memory_well_formed active frame;
  repaired_environment_whole_wf : memory_well_formed active whole;
  repaired_environment_framed : repaired_framed active shared frame local whole;
  repaired_environment_lock_complete : lock_complete active whole;
  repaired_environment_invariant : invariant s shared \/ locked active whole
}.

(** The language has no allocation. Residual private and shared resources
    must come from their previous combined ownership region. This permits
    transfers through the invariant but excludes inventing overlap with an
    external spatial frame. It is an extra witness obligation, not a theorem
    about arbitrary decompositions admitted by the printed safety predicate. *)
Definition ownership_preserved local shared local' shared' : Prop :=
  (forall loc, memory_domain local' loc -> memory_domain local loc \/ memory_domain shared loc) /\
  (forall loc, memory_domain shared' loc -> memory_domain local loc \/ memory_domain shared loc).

Lemma ownership_preserved_refl local shared : ownership_preserved local shared local shared.
Proof. split; intros loc H; [left | right]; exact H. Qed.

Theorem ownership_frame_disjoint frame local shared frame' local' shared' :
  disjoint (memory_domain frame) (memory_domain local) ->
  disjoint (memory_domain frame) (memory_domain shared) ->
  domain_included frame' frame -> ownership_preserved local shared local' shared' ->
  disjoint (memory_domain frame') (memory_domain local') /\
  disjoint (memory_domain frame') (memory_domain shared').
Proof.
  intros Hl Hs Hframe [Hlocal Hshared]. split; intros loc Hf Hr.
  - destruct (Hlocal loc Hr); [apply (Hl loc) | apply (Hs loc)]; [apply Hframe | |apply Hframe |]; assumption.
  - destruct (Hshared loc Hr); [apply (Hl loc) | apply (Hs loc)]; [apply Hframe | |apply Hframe |]; assumption.
Qed.

(** This is the bridge from the new witness obligation to the replacement
    frame lemma. It is not yet the full spatial frame inference rule. *)
Theorem owned_spatial_recombination active frame local shared frame' local' shared' whole' :
  disjoint (memory_domain frame) (memory_domain local) ->
  disjoint (memory_domain frame) (memory_domain shared) ->
  memory_flushes active frame frame' -> ownership_preserved local shared local' shared' ->
  memory_repaired active frame' local' whole' -> memory_spatial frame' local' whole'.
Proof.
  intros Hl Hs Hflush Howned [Hcompat [Hh [Hb Hk]]]. split.
  - split; [|exact (proj1 Hcompat)].
    exact (proj1 (ownership_frame_disjoint _ _ _ _ _ _ Hl Hs
      (flushes_domain_subset _ _ _ Hflush) Howned)).
  - split; [exact Hh |]. split; [intros i; apply ordered_interleaves, Hb | exact Hk].
Qed.

Fixpoint repaired_safe active (n : nat) c s local (invariant post : state_predicate) : Prop :=
  match n with
  | 0 => True
  | S remaining =>
      (terminal c -> post s local) /\
      (forall shared frame whole,
        repaired_environment active invariant s local shared frame whole ->
        ~ abort active c (State s whole)) /\
      (forall shared frame whole next s' whole',
        repaired_environment active invariant s local shared frame whole ->
        step active c (State s whole) next (State s' whole') ->
        exists local' shared' frame',
          repaired_environment active invariant s' local' shared' frame' whole' /\
          memory_flushes active frame frame' /\
          ownership_preserved local shared local' shared' /\
          repaired_safe active remaining next s' local' invariant post)
  end.

Definition repaired_valid_specification active invariant pre c post : Prop :=
  forall s local, repaired_full_satisfies active s local pre ->
    forall n, repaired_safe active n c s local
      (fun s m => repaired_full_satisfies active s m invariant)
      (fun s m => repaired_full_satisfies active s m post).

Definition flush_closed active (p : state_predicate) : Prop :=
  forall s m m', memory_flushes active m m' -> p s m -> p s m'.

Lemma flushes_well_formed active m m' :
  memory_flushes active m m' -> memory_well_formed active m -> memory_well_formed active m'.
Proof. induction 1; intros Hwf; [exact Hwf | apply IHmemory_flushes; eapply flush_preserves_well_formed; eassumption]. Qed.

Lemma flush_preserves_locked active m m' : flush active m m' -> locked active m -> locked active m'.
Proof. intros H [i Hi]. destruct H; exists i; exact Hi. Qed.

Lemma repaired_framed_flush active shared frame local whole whole' :
  repaired_framed active shared frame local whole -> flush active whole whole' ->
  exists local' shared' frame',
    memory_flushes active local local' /\ memory_flushes active shared shared' /\
    memory_flushes active frame frame' /\ repaired_framed active shared' frame' local' whole'.
Proof.
  intros [combined [Hinner Houter]] Hflush.
  destruct (spatial_flush_split _ _ _ _ _ Houter Hflush) as
    [[shared' [Hs Hsp]] | [combined' [Hc Hsp]]].
  - exists local, shared', frame. split; [constructor |].
    split; [econstructor; [exact Hs | constructor] |]. split; [constructor |].
    exists combined; split; assumption.
  - destruct (repaired_flush_split _ _ _ _ _ Hinner Hc) as
      [[frame' [Hf Hsep]] | [local' [Hl Hsep]]].
    + exists local, shared, frame'. split; [constructor |]. split; [constructor |].
      split; [econstructor; [exact Hf | constructor] |]. exists combined'; split; assumption.
    + exists local', shared, frame. split; [econstructor; [exact Hl | constructor] |].
      split; [constructor |]. split; [constructor |]. exists combined'; split; assumption.
Qed.

Theorem repaired_environment_flush active invariant s local shared frame whole whole' :
  flush_closed active invariant ->
  repaired_environment active invariant s local shared frame whole -> flush active whole whole' ->
  exists local' shared' frame',
    repaired_environment active invariant s local' shared' frame' whole' /\
    memory_flushes active local local' /\ memory_flushes active frame frame' /\
    ownership_preserved local shared local' shared'.
Proof.
  intros Hclosed [Hl Hs Hf Hw Hsep Hlock Hinv] Hflush.
  destruct (repaired_framed_flush _ _ _ _ _ _ Hsep Hflush)
    as [local' [shared' [frame' [Hl' [Hs' [Hf' Hsep']]]]]].
  exists local', shared', frame'. split.
  - constructor.
    + eapply flushes_well_formed; eassumption.
    + eapply flushes_well_formed; eassumption.
    + eapply flushes_well_formed; eassumption.
    + eapply flush_preserves_well_formed; eassumption.
    + exact Hsep'.
    + eapply flush_preserves_lock_complete; eassumption.
    + destruct Hinv as [Hinv | Hlocked]; [left; eapply Hclosed | right; eapply flush_preserves_locked]; eassumption.
  - split; [exact Hl' |]. split; [exact Hf' |]. split; intros loc Hdom.
    + left; apply (flushes_domain_subset _ _ _ Hl'), Hdom.
    + right; apply (flushes_domain_subset _ _ _ Hs'), Hdom.
Qed.

Lemma skip_no_abort active annotation s m : ~ abort active (Concurrent.skip annotation) (State s m).
Proof. intros H; inversion H; subst; match goal with H : primitive_abort _ _ _ _ |- _ => inversion H end. Qed.

Lemma skip_step_flush active annotation s m next t m' :
  step active (Concurrent.skip annotation) (State s m) next (State t m') ->
  next = Concurrent.skip annotation /\ t = s /\ flush active m m'.
Proof.
  intros H; inversion H; subst.
  - match goal with H : primitive_step _ _ _ _ _ |- _ => inversion H end.
  - split; [reflexivity |]. split; [reflexivity | assumption].
Qed.

(** All indices, all admissible frames, and every intervening silent flush. *)
Theorem repaired_skip_safe active n annotation invariant post s local :
  flush_closed active invariant -> flush_closed active post -> post s local ->
  repaired_safe active n (Concurrent.skip annotation) s local invariant post.
Proof.
  intros Hinv Hpost. revert s local. induction n; intros s local Hp; [exact I |].
  split; [intros _; exact Hp |]. split; [intros; apply skip_no_abort |].
  intros shared frame whole next t whole' Henv Hstep.
  destruct (skip_step_flush _ _ _ _ _ _ _ Hstep) as [-> [-> Hflush]].
  destruct (repaired_environment_flush _ _ _ _ _ _ _ _ Hinv Henv Hflush)
    as [local' [shared' [frame' [Henv' [Hl [Hf Howned]]]]]].
  exists local', shared', frame'. split; [exact Henv' |]. split; [exact Hf |].
  split; [exact Howned |]. apply IHn. eapply Hpost; eassumption.
Qed.

Lemma repaired_assignment_environment active invariant s local shared frame whole x rhs :
  ~ In x (ConcurrentAssertion.fv invariant) ->
  repaired_environment active (fun s m => repaired_full_satisfies active s m invariant)
    s local shared frame whole ->
  repaired_environment active (fun s m => repaired_full_satisfies active s m invariant)
    (update s x (eval_expr s rhs)) local shared frame whole.
Proof.
  intros Hfresh [Hl Hs Hf Hw Hsep Hlock Hinv]. constructor; try assumption.
  destruct Hinv as [Hinv | Hlocked]; [left | right; exact Hlocked].
  eapply repaired_full_agrees; [apply agrees_update_irrelevant, Hfresh | exact Hinv].
Qed.

Theorem repaired_pure_assignment_valid active invariant b x rhs annotation :
  ~ In x (bexpr_fv invariant) ->
  repaired_valid_specification active (ConcurrentAssertion.Pure invariant)
    (ConcurrentAssertion.Pure (subst_bexpr x rhs b))
    (Concurrent.Prim (Concurrent.Common (Sequential.Assign x rhs)) annotation)
    (ConcurrentAssertion.Pure b).
Proof.
  intros Hfresh s local Hp n. revert s local Hp. induction n; intros s local Hp; [exact I |].
  split; [intros [ann H]; discriminate |]. split.
  - intros shared frame whole Henv Habort. inversion Habort; subst.
    match goal with H : primitive_abort _ _ _ _ |- _ => inversion H end.
  - intros shared frame whole next t whole' Henv Hstep. inversion Hstep; subst.
    + match goal with H : primitive_step _ _ _ _ _ |- _ => inversion H; subst end.
      exists local, shared, frame. split.
      * apply repaired_assignment_environment; [exact Hfresh | exact Henv].
      * split; [constructor |]. split; [apply ownership_preserved_refl |].
        apply repaired_skip_safe.
        -- intros u m m' Hflush Hpure; eapply repaired_full_pure_flushes; eassumption.
        -- intros u m m' Hflush Hpure; eapply repaired_full_pure_flushes; eassumption.
        -- destruct Hp as [r [Hr Hp]]. exists r; split; [exact Hr |].
           change (eval_bexpr s (subst_bexpr x rhs b) = true) in Hp.
           rewrite eval_subst_bexpr in Hp. exact Hp.
    + assert (Hclosed : flush_closed active
        (fun u m => repaired_full_satisfies active u m (ConcurrentAssertion.Pure invariant))).
      { intros u m m' Hflush Hpure; eapply repaired_full_pure_flushes; eassumption. }
      match goal with H : flush _ _ _ |- _ =>
        destruct (repaired_environment_flush _ _ _ _ _ _ _ _ Hclosed Henv H)
          as [local' [shared' [frame' [Henv' [Hl [Hf Howned]]]]]] end.
      exists local', shared', frame'. split; [exact Henv' |]. split; [exact Hf |].
      split; [exact Howned |]. apply IHn. eapply repaired_full_pure_flushes; eassumption.
Qed.

(** Operational adequacy is reproved for this predicate. Restricting the
    framing relation does not imply the old safety predicate. *)
Theorem repaired_safe_execution_residual active n c s whole last t final :
  execution active n c s whole last t final ->
  forall local shared frame invariant post,
    repaired_safe active (S n) c s local invariant post ->
    repaired_environment active invariant s local shared frame whole ->
    exists local' shared' frame',
      repaired_environment active invariant t local' shared' frame' final /\
      memory_flushes active frame frame' /\ repaired_safe active 1 last t local' invariant post.
Proof.
  intros Hrun. induction Hrun; intros local shared frame invariant post Hsafe Henv.
  - exists local, shared, frame. split; [exact Henv |]. split; [constructor | exact Hsafe].
  - destruct Hsafe as [_ [_ Hprogress]].
    destruct (Hprogress _ _ _ _ _ _ Henv H) as
      [local' [shared' [frame' [Henv' [Hflush [_ Hsafe']]]]]].
    destruct (IHHrun _ _ _ _ _ Hsafe' Henv') as
      [local'' [shared'' [frame'' [Henv'' [Hflush' Hsafe'']]]]].
    exists local'', shared'', frame''. split; [exact Henv'' |]. split; [|exact Hsafe''].
    eapply memory_flushes_trans; eassumption.
Qed.

Theorem repaired_safe_execution_no_abort active n c s whole last t final local shared frame invariant post :
  execution active n c s whole last t final ->
  repaired_safe active (S n) c s local invariant post ->
  repaired_environment active invariant s local shared frame whole ->
  ~ abort active last (State t final).
Proof.
  intros Hrun Hsafe Henv.
  destruct (repaired_safe_execution_residual _ _ _ _ _ _ _ _ Hrun _ _ _ _ _ Hsafe Henv)
    as [local' [shared' [frame' [Henv' [_ [_ [Hnoabort _]]]]]]].
  exact (Hnoabort _ _ _ Henv').
Qed.

Theorem repaired_safe_execution_post active n c s whole last t final local shared frame invariant post :
  execution active n c s whole last t final ->
  repaired_safe active (S n) c s local invariant post ->
  repaired_environment active invariant s local shared frame whole -> terminal last ->
  exists local' shared' frame',
    repaired_environment active invariant t local' shared' frame' final /\
    memory_flushes active frame frame' /\ post t local'.
Proof.
  intros Hrun Hsafe Henv Hterminal.
  destruct (repaired_safe_execution_residual _ _ _ _ _ _ _ _ Hrun _ _ _ _ _ Hsafe Henv)
    as [local' [shared' [frame' [Henv' [Hflush [Hpost _]]]]]].
  exists local', shared', frame'. split; [exact Henv' |].
  split; [exact Hflush | apply Hpost, Hterminal].
Qed.
