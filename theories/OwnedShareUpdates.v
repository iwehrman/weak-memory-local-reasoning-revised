From Stdlib Require Import List ZArith.
From WMLR Require Import Expressions Languages Machine Separation RepairedSeparation
  Assertions AssertionSemantics PersistentAssertions OperationalSemantics ProgramSteps
  SpatialExchange TemporalSafety InvariantFragment OwnedSafety OwnedResources OwnedFraming
  OwnedShareResources.
Import ListNotations.

Lemma owned_share_update_acquire active owner local retained big pool local' :
  spatial (proj1_sig retained) (proj1_sig local) (proj1_sig big) ->
  owned_update active (AcquireAction owner) PoolFree (PoolHeld owner)
    local (resource_memory active retained) local' empty_memory ->
  owned_update active (AcquireAction owner) PoolFree (PoolHeld owner)
    big pool local' empty_memory.
Proof.
  intros Hsp [Ht Hd Hm]; constructor; [exact Ht | |].
  - intros loc H; right; apply (spatial_merge_domain _ _ _ (proj2 (proj1 Hsp)) loc),Hd,H.
  - intros i H; destruct (Hm i H) as [Hmark |Hearn]; [left; apply (proj2 Hsp); auto |auto].
Qed.

Lemma owned_share_update_closed active action local retained big local' big' pool :
  (match action with AcquireAction _ | ReleaseAction _ => False | _ => True end) ->
  spatial (proj1_sig retained) (proj1_sig local) (proj1_sig big) ->
  spatial (proj1_sig retained) (proj1_sig local') (proj1_sig big') ->
  owned_update active action PoolFree PoolFree local (resource_memory active retained)
    local' (resource_memory active retained) ->
  owned_update active action PoolFree PoolFree big pool big' pool.
Proof.
  intros Hkind Hsp Hsp' [Ht Hd Hm]; constructor.
  - destruct action; try contradiction.
    all: destruct Ht as [_ [_ Hblocks]]; split; [reflexivity |]; split; [reflexivity |]; intros i;
      rewrite (proj2 (proj2 (proj2 (proj1 Hsp')))), (proj2 (proj2 (proj2 (proj1 Hsp)))), Hblocks;
      reflexivity.
  - intros loc [Hp |Hb]; [auto |right].
    apply (spatial_merge_domain _ _ _ (proj2 (proj1 Hsp)) loc).
    apply (spatial_merge_domain _ _ _ (proj2 (proj1 Hsp')) loc) in Hb.
    destruct Hb as [Hr |Hl]; [auto |apply Hd; auto].
  - intros i H; apply (proj2 Hsp' i) in H; destruct H as [Hr |Hl].
    + left; apply (proj2 Hsp); auto.
    + destruct (Hm i Hl) as [Hp |He]; [left; apply (proj2 Hsp); auto |auto].
Qed.

Lemma owned_share_update_release active owner local local' returned big' :
  spatial (proj1_sig returned) (proj1_sig local') (proj1_sig big') ->
  lock_free (resource_memory active returned) ->
  (forall i, complete (proj1_sig returned) i -> i = owner) ->
  owned_update active (ReleaseAction owner) (PoolHeld owner) PoolFree local empty_memory
    local' (resource_memory active returned) ->
  owned_update active (ReleaseAction owner) (PoolHeld owner) PoolFree local empty_memory big' empty_memory.
Proof.
  intros Hsp Hfree Hmarks [Ht Hd Hm]; destruct Ht as [_ [_ [Hheld Hlocalfree]]].
  constructor.
  - split; [reflexivity |]. split; [reflexivity |]. split; [exact Hheld |].
    exact (spatial_free_union _ _ _ (proj1 Hsp) Hfree Hlocalfree).
  - intros loc [He |Hbig]; [auto |]. apply Hd.
    apply (spatial_merge_domain _ _ _ (proj2 (proj1 Hsp)) loc),Hbig.
  - intros i H; apply (proj2 Hsp i) in H; destruct H as [Hr |Hl].
    + right; apply Hmarks,Hr.
    + apply Hm,Hl.
Qed.
