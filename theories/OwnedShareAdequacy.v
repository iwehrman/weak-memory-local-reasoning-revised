From Stdlib Require Import List ZArith.
From WMLR Require Import Expressions Languages Machine Separation OperationalSemantics
  Assertions AssertionSemantics PersistentAssertions OwnershipProtocol PrivateOwnership
  SpatialExchange Safety TemporalSafety InvariantFragment LockRepresentation OwnedSafety
  OwnedAdequacy OwnedCalculus.
Import ListNotations.

(** Semantic lock-freeness is an assertion property, not another notion of
    program validity. In particular, absence of Lock in the syntax is not
    sufficient. *)
Definition assertion_lock_free active p : Prop :=
  forall s (r : resource active), persistent_models active s r p ->
    lock_free (resource_memory active r).

Lemma invariant_assertion_lock_free active p :
  invariant_fragment p -> assertion_lock_free active p.
Proof. intros Hfragment s r H; exact (proj2 (invariant_fragment_shape _ Hfragment _ _ _ H)). Qed.

(** The top-level operational consequence of restricted SHARE. This does
    not claim validity against arbitrary changing external environments. *)
Theorem owned_share_all_runs active mode invariant pre command post :
  two_active_processors active -> invariant_fragment invariant ->
  assertion_lock_free active pre -> assertion_lock_free active post ->
  owned_valid active mode invariant pre command post ->
  forall s (initial : resource active) n last t final,
    persistent_models active s initial (A.Spatial invariant pre) ->
    execution active n command s (resource_memory active initial) last t final ->
    ~ abort active last (State t final) /\
    (terminal last -> lock_free final /\
      persistent_full_satisfies active t final (A.Spatial invariant post)).
Proof.
  intros Htwo Hfragment HPfree HQfree Hvalid s initial n last t final
    (pool & local & Hsp & HJ & HP) Hrun.
  assert (Hfull : persistent_full_satisfies active s (resource_memory active pool) invariant).
  { destruct Htwo as (first & second & Hfirst & Hsecond & Hne).
    exact (invariant_return_full_completeness active first s pool invariant Hfirst Hfragment HJ). }
  assert (Hfree : lock_free (resource_memory active initial)).
  { eapply spatial_free_union; [exact (proj1 Hsp)
      |exact (invariant_assertion_lock_free _ _ Hfragment _ _ HJ)
      |exact (HPfree _ _ HP)]. }
  destruct (owned_valid_adequacy _ _ _ _ _ _ _ _ _ _ _ _ _ _
    Htwo Hfragment Hvalid HP Hfull Hfree (proj1 Hsp) Hrun) as [Habort Hlast].
  split; [exact Habort |]. intros Hdone.
  destruct (Hlast Hdone) as (local' & pool' & Hsp' & HQ & [Hrestored |Hheld]).
  - split; [exact (proj1 Hrestored) |].
    eapply full_spatial_intro; [exact Hsp' |exact (proj2 Hrestored) |].
    apply persistent_promote_full, HQ.
  - destruct Hheld as (owner & Hheld & _).
    destruct Htwo as (first & second & Hfirst & Hsecond & Hne).
    exfalso; exact (two_processors_separate_free_held active first second
      (resource_memory active local') owner Hfirst Hsecond Hne
      (HQfree _ _ HQ) Hheld).
Qed.

Corollary owned_share_derivation_all_runs active mode invariant pre command post :
  two_active_processors active -> invariant_fragment invariant ->
  assertion_lock_free active pre -> assertion_lock_free active post ->
  owned_derivation active invariant mode pre command post ->
  forall s (initial : resource active) n last t final,
    persistent_models active s initial (A.Spatial invariant pre) ->
    execution active n command s (resource_memory active initial) last t final ->
    ~ abort active last (State t final) /\
    (terminal last -> lock_free final /\
      persistent_full_satisfies active t final (A.Spatial invariant post)).
Proof.
  intros Htwo Hfragment HP HQ Hderive.
  apply (owned_share_all_runs active mode invariant pre command post); try assumption.
  apply owned_calculus_sound; assumption.
Qed.
