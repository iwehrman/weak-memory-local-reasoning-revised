From Stdlib Require Import List ZArith.
From WMLR Require Import Expressions Languages Machine BufferRelations OrderedBuffers
  Separation RepairedSeparation RepairedFlushing GeneralizedFlushing FrameDecomposition
  OperationalSemantics ProgramSteps Assertions AssertionSemantics PersistentAssertions
  OwnershipProtocol PrivateOwnership SpatialExchange TemporalSafety InvariantFragment
  OwnedSafety OwnedFraming FlushAttribution ResidualUniqueness BufferedPoolCandidate.
Import ListNotations.

(** Foundations for the approved buffered-pool judgment. All theorems here
    refer to the definitions in BufferedPoolCandidate, without changing them. *)
Lemma buffered_pool_flush active J s pool actor pool' :
  persistent_full_satisfies active s pool J -> flush_at active actor pool pool' ->
  persistent_full_satisfies active s pool' J.
Proof.
  intros HJ Hflush. eapply persistent_full_flushing_closed; [|exact HJ].
  econstructor; [exact (flush_at_forget _ _ _ _ Hflush) |constructor].
Qed.



Lemma buffered_environment_spatial active J s local pool frame whole :
  buffered_environment active DisjointMode J s local pool frame whole ->
  exists combined, memory_spatial (resource_memory active frame)
    (resource_memory active local) combined /\ memory_spatial pool combined whole.
Proof.
  intros [_ _ _ _ [combined [Hinner Houter]] Hmode].
  exists (resource_memory active combined); split; [|exact Houter].
  apply (spatiotemporal_spatial_when_compatible active
    (proj1_sig frame) (proj1_sig local) (proj1_sig combined)).
  - split; [exact Hmode |exact (proj1 (proj1 (proj1 Hinner)))].
  - apply repaired_in_original, Hinner.
Qed.

Lemma buffered_environment_intro active J s local pool frame whole combined :
  persistent_full_satisfies active s pool J -> lock_free whole ->
  memory_spatial (resource_memory active frame) (resource_memory active local) combined ->
  memory_spatial pool combined whole ->
  buffered_environment active DisjointMode J s local pool frame whole.
Proof.
  intros HJ Hfree Hinner Houter.
  assert (Hsp : spatial (proj1_sig frame) (proj1_sig local)
    (Generalized combined (fun i => complete (proj1_sig frame) i \/ complete (proj1_sig local) i))).
  { split; [exact Hinner |intros i; reflexivity]. }
  pose (r := exist _ _ (spatial_well_formed _ _ _ _ (proj2_sig frame) (proj2_sig local) Hsp)).
  constructor.
  - exact (proj1 (persistent_full_well_formed _ _ _ _ HJ)).
  - eapply raw_spatial_well_formed; [exact (proj1 (persistent_full_well_formed _ _ _ _ HJ)) | |exact Houter].
    exact (proj1 (proj2_sig r)).
  - exact Hfree.
  - exact HJ.
  - exists r; split; [apply spatial_in_repaired, Hsp |exact Houter].
  - exact (proj1 (proj1 Hinner)).
Qed.

Lemma buffered_flush_free active actor before after :
  flush_at active actor before after -> lock_free before -> lock_free after.
Proof. destruct 1; exact (fun H => H). Qed.

Lemma buffered_component_flush_future active actor before after :
  buffered_component_flush active actor before after -> resource_future active before after.
Proof.
  intros [Hflush Hmarks]. apply generalized_future_one.
  destruct before as [[m marks] Hwf], after as [[m' marks'] Hwf']; cbn in *.
  eapply GeneralizedFlush; [exact Hflush | |exact (proj1 (proj2 Hwf')) |].
  - intros i Hi; apply Hmarks; auto.
  - apply Hmarks; auto.
Qed.

Theorem buffered_environment_flush active J s local pool frame whole actor whole' :
  buffered_environment active DisjointMode J s local pool frame whole ->
  flush_at active actor whole whole' ->
  exists local' frame' pool',
    buffered_flush_update active actor local frame pool local' frame' pool' /\
    buffered_environment active DisjointMode J s local' pool' frame' whole' /\
    resource_future active local local'.
Proof.
  intros Henv Hflush.
  pose proof (buffered_pool_models _ _ _ _ _ _ _ _ Henv) as HJ.
  pose proof (buffered_flush_free _ _ _ _ Hflush
    (buffered_whole_free _ _ _ _ _ _ _ _ Henv)) as Hfree.
  destruct (buffered_environment_spatial _ _ _ _ _ _ _ Henv) as (combined & Hinner & Houter).
  destruct (indexed_spatial_flush_split _ _ _ _ _ _ Houter Hflush)
    as [(pool' & Hpool & Houter') |(combined' & Hcombined & Houter')].
  - exists local, frame, pool'; split; [left; auto |]. split; [|constructor].
    eapply buffered_environment_intro; [eapply buffered_pool_flush; eassumption |exact Hfree |exact Hinner |exact Houter'].
  - destruct (indexed_spatial_flush_split _ _ _ _ _ _ Hinner Hcombined)
      as [(frame_memory & HF & Hinner') |(local_memory & HL & Hinner')].
    + destruct (indexed_flush_resource _ _ _ _ HF) as (frame' & E & Hstep & Hmarks).
      exists local, frame', pool; split.
      * right; right; split; [reflexivity |]. split; [reflexivity |].
        split; [unfold resource_memory; rewrite E; exact HF |exact Hmarks].
      * split; [|constructor]. eapply buffered_environment_intro;
          [exact HJ |exact Hfree | |exact Houter']. unfold resource_memory; rewrite E; exact Hinner'.
    + destruct (indexed_flush_resource _ _ _ _ HL) as (local' & E & Hstep & Hmarks).
      exists local', frame, pool; split.
      * right; left; split; [reflexivity |]. split; [reflexivity |].
        split; [unfold resource_memory; rewrite E; exact HL |exact Hmarks].
      * split; [|apply generalized_future_one, Hstep].
        eapply buffered_environment_intro; [exact HJ |exact Hfree | |exact Houter'].
        unfold resource_memory; rewrite E; exact Hinner'.
Qed.

(** The mark budget prevents an ordinary action from withdrawing a heap
    cell into an initially unmarked private resource. *)
Theorem buffered_unmarked_ordinary_no_heap active local pool local' pool' :
  (forall i, ~ complete (proj1_sig local) i) ->
  buffered_update active OrdinaryAction local pool local' pool' ->
  forall loc, shared_heap (resource_memory active local') loc = None.
Proof.
  intros Hnone [_ Hmarks]. apply (proj2 (proj2 (proj2_sig local'))).
  intros i Hi. destruct (Hmarks i Hi) as [H |H]; [exact (Hnone i H) |exact H].
Qed.

Lemma buffered_environment_joint active J s local pool frame whole :
  buffered_environment active DisjointMode J s local pool frame whole ->
  exists joint, memory_spatial pool (resource_memory active local) joint /\
    memory_spatial (resource_memory active frame) joint whole.
Proof.
  intros Henv. destruct (buffered_environment_spatial _ _ _ _ _ _ _ Henv)
    as (combined & Hinner & Houter).
  destruct (spatial_exchange _ _ _ _ _ (memory_spatial_comm _ _ _ Hinner) Houter) as (joint & Hjoint & Hframe).
  exists joint; split; [apply memory_spatial_comm, Hjoint |exact Hframe].
Qed.

(** At a fixed full pool these environments coincide. The conversion lets
    us reuse algebraic regrouping, not the old safety or transfer clauses. *)
Lemma buffered_environment_owned active mode J s local pool frame whole :
  buffered_environment active mode J s local pool frame whole <->
  owned_environment active mode J s local pool frame whole PoolFree.
Proof.
  split.
  - intros [Hp Hw Hfree HJ Hcomp Hmode]; constructor; auto; split; assumption.
  - intros [Hp Hw Hcomp Hmode [Hfree HJ]]; constructor; assumption.
Qed.

Lemma buffered_repaired_spatial active (a b out : resource active) :
  mode_compatible active DisjointMode a b ->
  repaired_spatiotemporal active (proj1_sig a) (proj1_sig b) (proj1_sig out) ->
  spatial (proj1_sig a) (proj1_sig b) (proj1_sig out).
Proof.
  intros Hd Hrep. eapply spatiotemporal_spatial_when_compatible;
    [split; [exact Hd |exact (proj1 (proj1 (proj1 Hrep)))] |apply repaired_in_original, Hrep].
Qed.

Lemma buffered_environment_unframe active J s (local retained big : resource active) pool frame whole :
  spatial (proj1_sig retained) (proj1_sig local) (proj1_sig big) ->
  buffered_environment active DisjointMode J s big pool frame whole ->
  exists grouped : resource active,
    spatial (proj1_sig frame) (proj1_sig retained) (proj1_sig grouped) /\
    buffered_environment active DisjointMode J s local pool grouped whole.
Proof.
  intros Hinner Henv.
  pose proof (spatial_in_repaired active _ _ _ Hinner) as Hrep.
  destruct (owned_environment_unframe active DisjointMode _ _ _ _ _ _ _ _ _ Hrep
    (proj1 (proj1 (proj1 Hinner))) (proj1 (buffered_environment_owned _ _ _ _ _ _ _ _) Henv))
    as (grouped & Hgroup & Hsmall).
  exists grouped; split.
  - apply buffered_repaired_spatial; [|exact Hgroup].
    exact (proj1 (owned_mode_parts _ _ _ _ _ _ Hrep (buffered_frame_mode _ _ _ _ _ _ _ _ Henv))).
  - apply buffered_environment_owned, Hsmall.
Qed.

Lemma buffered_environment_reframe active J s local (retained : resource active) pool frame grouped whole :
  spatial (proj1_sig frame) (proj1_sig retained) (proj1_sig grouped) ->
  buffered_environment active DisjointMode J s local pool grouped whole ->
  exists big : resource active,
    spatial (proj1_sig retained) (proj1_sig local) (proj1_sig big) /\
    buffered_environment active DisjointMode J s big pool frame whole.
Proof.
  intros Hgroup Henv.
  pose proof (spatial_in_repaired active _ _ _ Hgroup) as Hrep.
  destruct (owned_environment_reframe active DisjointMode _ _ _ _ _ _ _ _ _ Hrep
    (proj1 (proj1 (proj1 Hgroup))) (proj1 (buffered_environment_owned _ _ _ _ _ _ _ _) Henv))
    as (big & Hinner & Hbig).
  exists big; split.
  - apply buffered_repaired_spatial; [|exact Hinner]. intros loc HR HL.
    apply (buffered_frame_mode _ _ _ _ _ _ _ _ Henv loc); [|exact HL].
    apply (resource_repaired_domain _ _ _ _ Hrep); auto.
  - apply buffered_environment_owned, Hbig.
Qed.

Lemma buffered_update_frame active action local pool local' pool'
    (retained big big' : resource active) :
  spatial (proj1_sig retained) (proj1_sig local) (proj1_sig big) ->
  spatial (proj1_sig retained) (proj1_sig local') (proj1_sig big') ->
  buffered_update active action local pool local' pool' ->
  buffered_update active action big pool big' pool'.
Proof.
  intros Hinner Hinner' [Hdomain Hmarks]; constructor.
  - intros loc [Hp |Hbig].
    + destruct (Hdomain loc (or_introl Hp)) as [H |H]; [auto |right].
      apply (spatial_merge_domain _ _ _ (proj2 (proj1 Hinner))); auto.
    + apply (spatial_merge_domain _ _ _ (proj2 (proj1 Hinner'))) in Hbig.
      destruct Hbig as [HR |HL].
      * right; apply (spatial_merge_domain _ _ _ (proj2 (proj1 Hinner))); auto.
      * destruct (Hdomain loc (or_intror HL)) as [H |H]; [auto |right].
        apply (spatial_merge_domain _ _ _ (proj2 (proj1 Hinner))); auto.
  - intros i Hi; apply (proj2 Hinner') in Hi; destruct Hi as [HR |HL].
    + left; apply (proj2 Hinner); auto.
    + destruct (Hmarks i HL); [left; apply (proj2 Hinner); auto |auto].
Qed.

Theorem buffered_joint_buffers_unique frame pool local joint pool' local' joint' whole :
  memory_spatial pool local joint -> memory_spatial frame joint whole ->
  memory_spatial pool' local' joint' -> memory_spatial frame joint' whole ->
  forall actor, buffers joint actor = buffers joint' actor.
Proof.
  intros _ Hleft _ Hright. eapply (repaired_residual_buffers_unique (fun _ => True));
    [apply memory_spatial_in_repaired, Hleft |apply memory_spatial_in_repaired, Hright |reflexivity].
Qed.
