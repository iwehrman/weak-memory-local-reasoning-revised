From Stdlib Require Import List ZArith.
From WMLR Require Import Expressions Machine BufferRelations Separation
  RepairedSeparation GeneralizedFlushing Assertions AssertionSemantics
  PersistentAssertions TemporalSafety InvariantFragment.
Import ListNotations.

Lemma empty_buffer_cannot_flush active i m m' :
  buffers m i = [] -> ~ flush_at active i m m'.
Proof.
  intros Hempty Hflush; inversion Hflush as [before loc v rest Hi Hlive Hhead]; subst.
  rewrite Hempty in Hhead; discriminate.
Qed.

(** First remove the buffer-free pool, then attribute the very same indexed
    machine flush inside #. The pool and the other component remain fixed. *)
Theorem pooled_flush_attribution active i pool frame local combined whole whole' :
  (forall j, buffers pool j = []) ->
  memory_spatial pool combined whole -> memory_repaired active frame local combined ->
  flush_at active i whole whole' ->
  (exists frame' combined', flush_at active i frame frame' /\
    memory_repaired active frame' local combined' /\ memory_spatial pool combined' whole') \/
  (exists local' combined', flush_at active i local local' /\
    memory_repaired active frame local' combined' /\ memory_spatial pool combined' whole').
Proof.
  intros Hempty Hpool Hinner Hflush.
  destruct (indexed_spatial_flush_split _ _ _ _ _ _ Hpool Hflush)
    as [(pool' & Hpoolflush & _) |(combined' & Hcombinedflush & Hpool')].
  - exfalso; exact (empty_buffer_cannot_flush _ _ _ _ (Hempty i) Hpoolflush).
  - destruct (indexed_repaired_flush_split _ _ _ _ _ _ Hinner Hcombinedflush)
      as [(frame' & HF & Hinner') |(local' & HL & Hinner')].
    + left; exists frame', combined'; auto.
    + right; exists local', combined'; auto.
Qed.

(** A single real flush, with precisely its processor's mark added. This
    constructs a resource, without defining another safety/validity notion. *)
Lemma indexed_flush_resource active i (r : resource active) m' :
  flush_at active i (underlying (proj1_sig r)) m' ->
  exists r' : resource active, underlying (proj1_sig r') = m' /\
    generalized_step active (proj1_sig r) (proj1_sig r') /\
    (forall j, complete (proj1_sig r') j <-> complete (proj1_sig r) j \/ j = i).
Proof.
  intros Hflush.
  assert (Hi : active i) by (destruct Hflush; assumption).
  assert (Hstep : generalized_step active (proj1_sig r)
    (Generalized m' (fun j => complete (proj1_sig r) j \/ j = i))).
  { destruct r as [[m marks] Hwf]; cbn in *.
    apply GeneralizedFlush with (i := i); [exact Hflush | | |right; reflexivity].
    - intros j H; left; exact H.
    - intros j [H | ->]; [exact (proj1 (proj2 Hwf) j H) |exact Hi]. }
  exists (exist _ _ (generalized_step_well_formed _ _ _ Hstep (proj2_sig r))).
  split; [reflexivity |]. split; [exact Hstep |intros j; reflexivity].
Qed.

Theorem pooled_resource_flush_attribution active i pool (frame local combined : resource active) whole whole' :
  (forall j, buffers pool j = []) ->
  memory_spatial pool (underlying (proj1_sig combined)) whole ->
  repaired_spatiotemporal active (proj1_sig frame) (proj1_sig local) (proj1_sig combined) ->
  flush_at active i whole whole' ->
  (exists frame' combined' : resource active,
    flush_at active i (underlying (proj1_sig frame)) (underlying (proj1_sig frame')) /\
    generalized_step active (proj1_sig frame) (proj1_sig frame') /\
    (forall j, complete (proj1_sig frame') j <-> complete (proj1_sig frame) j \/ j = i) /\
    repaired_spatiotemporal active (proj1_sig frame') (proj1_sig local) (proj1_sig combined') /\
    memory_spatial pool (underlying (proj1_sig combined')) whole') \/
  (exists local' combined' : resource active,
    flush_at active i (underlying (proj1_sig local)) (underlying (proj1_sig local')) /\
    generalized_step active (proj1_sig local) (proj1_sig local') /\
    (forall j, complete (proj1_sig local') j <-> complete (proj1_sig local) j \/ j = i) /\
    repaired_spatiotemporal active (proj1_sig frame) (proj1_sig local') (proj1_sig combined') /\
    memory_spatial pool (underlying (proj1_sig combined')) whole').
Proof.
  intros Hempty Hpool [Hinner Hmarks] Hflush.
  destruct (pooled_flush_attribution _ _ _ _ _ _ _ _ Hempty Hpool Hinner Hflush)
    as [(fm & cm & HF & Hinner' & Hpool') |(lm & cm & HL & Hinner' & Hpool')].
  - destruct (indexed_flush_resource _ _ _ _ HF) as (frame' & Ef & Hstep & Hmark).
    assert (Hcomposition : repaired_spatiotemporal active (proj1_sig frame') (proj1_sig local)
      (Generalized cm (fun j => complete (proj1_sig frame') j \/ complete (proj1_sig local) j))).
    { split; [cbn; rewrite Ef; exact Hinner' |intros j; reflexivity]. }
    pose (combined' := exist _ _ (repaired_well_formed _ _ _ _ (proj2_sig frame') (proj2_sig local) Hcomposition)).
    left; exists frame', combined'; split; [rewrite Ef; exact HF |].
    split; [exact Hstep |]. split; [exact Hmark |]. split; [exact Hcomposition |exact Hpool'].
  - destruct (indexed_flush_resource _ _ _ _ HL) as (local' & El & Hstep & Hmark).
    assert (Hcomposition : repaired_spatiotemporal active (proj1_sig frame) (proj1_sig local')
      (Generalized cm (fun j => complete (proj1_sig frame) j \/ complete (proj1_sig local') j))).
    { split; [cbn; rewrite El; exact Hinner' |intros j; reflexivity]. }
    pose (combined' := exist _ _ (repaired_well_formed _ _ _ _ (proj2_sig frame) (proj2_sig local') Hcomposition)).
    right; exists local', combined'; split; [rewrite El; exact HL |].
    split; [exact Hstep |]. split; [exact Hmark |]. split; [exact Hcomposition |exact Hpool'].
Qed.

(** The accepted invariant syntax supplies the pool premise. *)
Corollary invariant_pool_flush_attribution active i s invariant
    (pool frame local combined : resource active) whole whole' :
  invariant_fragment invariant -> persistent_models active s pool invariant ->
  memory_spatial (resource_memory active pool) (underlying (proj1_sig combined)) whole ->
  repaired_spatiotemporal active (proj1_sig frame) (proj1_sig local) (proj1_sig combined) ->
  flush_at active i whole whole' ->
  (exists frame' combined' : resource active,
    flush_at active i (underlying (proj1_sig frame)) (underlying (proj1_sig frame')) /\
    generalized_step active (proj1_sig frame) (proj1_sig frame') /\
    (forall j, complete (proj1_sig frame') j <-> complete (proj1_sig frame) j \/ j = i) /\
    repaired_spatiotemporal active (proj1_sig frame') (proj1_sig local) (proj1_sig combined') /\
    memory_spatial (resource_memory active pool) (underlying (proj1_sig combined')) whole') \/
  (exists local' combined' : resource active,
    flush_at active i (underlying (proj1_sig local)) (underlying (proj1_sig local')) /\
    generalized_step active (proj1_sig local) (proj1_sig local') /\
    (forall j, complete (proj1_sig local') j <-> complete (proj1_sig local) j \/ j = i) /\
    repaired_spatiotemporal active (proj1_sig frame) (proj1_sig local') (proj1_sig combined') /\
    memory_spatial (resource_memory active pool) (underlying (proj1_sig combined')) whole').
Proof.
  intros Hfragment Hpool; apply pooled_resource_flush_attribution.
  exact (proj1 (invariant_fragment_shape _ Hfragment active s pool Hpool)).
Qed.
