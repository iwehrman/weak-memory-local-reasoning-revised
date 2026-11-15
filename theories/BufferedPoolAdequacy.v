From Stdlib Require Import List Arith ZArith.
From WMLR Require Import Expressions Languages Machine BufferRelations Separation
  RepairedSeparation GeneralizedFlushing OperationalSemantics ProgramSteps Assertions
  AssertionSemantics ConcreteAssertions PersistentAssertions Safety TemporalSafety
  OwnershipProtocol OwnedSafety OwnedAdequacy FlushAttribution
  BufferedPoolCandidate BufferedPoolResources BufferedPoolRules.
Import ListNotations.

Lemma buffered_empty_frame_intro active J s local pool whole :
  persistent_full_satisfies active s pool J ->
  memory_spatial pool (resource_memory active local) whole -> lock_free whole ->
  buffered_environment active DisjointMode J s local pool (empty_resource_value active) whole.
Proof.
  intros HJ Hsp Hfree; apply buffered_environment_owned.
  apply owned_empty_frame_intro; [exact (proj1 (persistent_full_well_formed _ _ _ _ HJ)) |exact Hsp |].
  split; assumption.
Qed.

Lemma buffered_empty_frame_elim active J s local pool whole :
  buffered_environment active DisjointMode J s local pool (empty_resource_value active) whole ->
  memory_spatial pool (resource_memory active local) whole /\
  lock_free whole /\ persistent_full_satisfies active s pool J.
Proof.
  intros Henv. apply (owned_empty_frame_elim active DisjointMode J s local pool whole PoolFree).
  apply buffered_environment_owned, Henv.
Qed.

Theorem buffered_execution_empty_frame active J n c s whole last t final :
  execution active n c s whole last t final ->
  forall local pool Q,
    buffered_safe active DisjointMode J (S n) c s local Q ->
    buffered_environment active DisjointMode J s local pool (empty_resource_value active) whole ->
    exists local' pool',
      buffered_environment active DisjointMode J t local' pool' (empty_resource_value active) final /\
      buffered_safe active DisjointMode J 1 last t local' Q.
Proof.
  intros Hrun; induction Hrun; intros local pool Q Hsafe Henv.
  - exists local, pool; auto.
  - destruct (state_step_program_or_flush _ _ _ _ _ _ _ H) as [(action & Hprogram) |[-> [-> Hflush]]].
    + destruct (buffered_safe_program_step _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hsafe Henv Hprogram)
        as (local' & pool' & Henv' & Hupdate & Hsafe').
      exact (IHHrun local' pool' Q Hsafe' Henv').
    + destruct (flush_at_exists _ _ _ Hflush) as (actor & Hphysical).
      destruct (proj2 (proj2 (proj2 (Hsafe local (GeneralizedRefl _ _)) _ _ _ Henv)) _ _ Hphysical)
        as (local' & frame' & pool' & Hupdate & Henv' & Hsafe').
      assert (E : frame' = empty_resource_value active).
      { destruct Hupdate as [(_ & E & _) |[(_ & E & _) |(_ & _ & HF & _)]]; [exact E |exact E |].
        exfalso; exact (empty_buffer_cannot_flush active actor (resource_memory active (empty_resource_value active)) _ eq_refl HF). }
      subst frame'; exact (IHHrun local' pool' Q Hsafe' Henv').
Qed.

Theorem buffered_valid_adequacy active J P c Q : buffered_adequacy_statement active J P c Q.
Proof.
  intros _ [_ Hvalid] n s whole last t final local pool HP HJ Hsp Hfree Hrun.
  destruct (buffered_execution_empty_frame _ _ _ _ _ _ _ _ _ Hrun local pool Q
    (Hvalid s local HP (S n)) (buffered_empty_frame_intro _ _ _ _ _ _ HJ Hsp Hfree))
    as (local' & pool' & Henv' & Hsafe').
  split; [eapply buffered_safe_no_abort; eassumption |].
  intros Hlast; exists local', pool'.
  destruct (buffered_empty_frame_elim _ _ _ _ _ _ Henv') as [Hsp' [Hfree' HJ']].
  split; [exact Hsp' |]. split; [exact Hfree' |]. split; [exact HJ' |].
  eapply buffered_safe_terminal; eassumption.
Qed.
