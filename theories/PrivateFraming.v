From Stdlib Require Import List ZArith.
From WMLR Require Import Expressions Languages Machine BufferRelations Separation RepairedFlushing
  FrameDecomposition OperationalSemantics Assertions AssertionSemantics PersistentAssertions Safety RepairedSafety
  Specifications OwnershipProtocol PrivateOwnership PrivateRules SpatialExchange.
Import ListNotations.

Lemma spatial_flushes_split active whole whole' : memory_flushes active whole whole' ->
  forall a b, memory_spatial a b whole -> exists a' b',
    memory_flushes active a a' /\ memory_flushes active b b' /\ memory_spatial a' b' whole'.
Proof.
  induction 1; intros left right Hsep.
  - exists left, right; split; [constructor |split; [constructor |exact Hsep]].
  - destruct (spatial_flush_split _ _ _ _ _ Hsep H) as [(a' & Ha & Hsep') |(b' & Hb & Hsep')].
    + destruct (IHmemory_flushes _ _ Hsep') as (a'' & b'' & Ha' & Hb & Hout).
      exists a'', b''; split; [econstructor; eassumption |auto].
    + destruct (IHmemory_flushes _ _ Hsep') as (a'' & b'' & Ha & Hb' & Hout).
      exists a'', b''; split; [exact Ha |split; [econstructor; eassumption |exact Hout]].
Qed.

Lemma spatial_extension_domain a b out a' b' out' :
  memory_spatial a b out -> memory_spatial a' b' out' ->
  domain_included a' a -> domain_included b' b -> domain_included out' out.
Proof.
  intros H H' Ha Hb loc Hloc. apply (spatial_merge_domain _ _ _ (proj2 H)).
  apply (spatial_merge_domain _ _ _ (proj2 H')) in Hloc; destruct Hloc; [left; apply Ha |right; apply Hb]; assumption.
Qed.

Lemma private_region_extend active owner invariant phase s local region retained bigregion :
  private_region active owner invariant phase s local region ->
  memory_well_formed active retained -> lock_free retained -> memory_spatial region retained bigregion ->
  exists biglocal, private_region active owner invariant phase s biglocal bigregion /\ memory_spatial local retained biglocal.
Proof.
  intros [Hl [Hr Hphase]] Hret Hfree Hsep.
  assert (Hbig : memory_well_formed active bigregion) by
    (exact (raw_spatial_well_formed _ _ _ _ Hr Hret Hsep)).
  destruct phase.
  - destruct Hphase as [Hrfree [pool [HJ Hinner]]].
    destruct (proj2 (memory_spatial_associative pool local retained bigregion)
      (ex_intro _ region (conj Hinner Hsep))) as (biglocal & Hlocal & Hpool).
    exists biglocal; split; [|exact Hlocal]. split;
      [exact (raw_spatial_well_formed _ _ _ _ Hl Hret Hlocal) |]. split; [exact Hbig |].
    split; [exact (spatial_free_union _ _ _ Hsep Hrfree Hfree) |exists pool; auto].
  - destruct Hphase as [-> [Hi Hheld]]. exists bigregion; split; [|exact Hsep].
    split; [exact Hbig |]. split; [exact Hbig |]. split; [reflexivity |].
    split; [exact Hi |]. intros i. rewrite (proj2 (proj2 (proj2 Hsep)) i), Hheld.
    split; [intros [H |H]; [exact H |exfalso; exact (Hfree i H)] |auto].
Qed.

Lemma private_environment_unframe active owner invariant phase s local region retained biglocal bigregion external whole :
  private_region active owner invariant phase s local region ->
  private_environment active owner invariant phase s biglocal bigregion external whole ->
  memory_well_formed active retained -> lock_free retained -> memory_spatial region retained bigregion ->
  exists combined, memory_spatial external retained combined /\
    private_environment active owner invariant phase s local region combined whole.
Proof.
  intros Hr [_ He Hw Hefree Houter] Hret Hfree Hinner.
  destruct (proj1 (memory_spatial_associative external retained region whole)
    (ex_intro _ bigregion (conj (memory_spatial_comm _ _ _ Hinner) Houter))) as (combined & Hframe & Hsep).
  exists combined; split; [exact Hframe |]. constructor; try assumption.
  - exact (raw_spatial_well_formed _ _ _ _ He Hret Hframe).
  - exact (spatial_free_union _ _ _ Hframe Hefree Hfree).
Qed.

Lemma private_environment_reframe active owner invariant phase s local region retained external combined whole :
  private_environment active owner invariant phase s local region combined whole ->
  memory_spatial external retained combined -> memory_well_formed active external -> memory_well_formed active retained ->
  exists biglocal bigregion, private_environment active owner invariant phase s biglocal bigregion external whole /\
    memory_spatial local retained biglocal /\ memory_spatial region retained bigregion.
Proof.
  intros [Hr Hc Hw Hfree Houter] Hframe He Hret.
  destruct (spatial_free_parts _ _ _ Hframe Hfree) as [Hefree Hrfree].
  destruct (proj2 (memory_spatial_associative external retained region whole)
    (ex_intro _ combined (conj Hframe Houter))) as (bigregion & Hinner & Hsep).
  pose proof (memory_spatial_comm _ _ _ Hinner) as Hinner'.
  destruct (private_region_extend _ _ _ _ _ _ _ _ _ Hr Hret Hrfree Hinner') as (biglocal & Hbig & Hlocal).
  exists biglocal, bigregion. split; [constructor; assumption |auto].
Qed.

(** Semantic framing: the source premise is validity/safety, not a special
    derivation or a premise that already states the framed conclusion. *)
Theorem private_safe_spatial_frame active owner invariant n command s phase local region finish post retained biglocal bigregion frame_assertion :
  private_safe active owner invariant n command s phase local region finish post ->
  frame_variable_condition command frame_assertion -> persistent_full_satisfies active s retained frame_assertion ->
  lock_free retained -> private_region active owner invariant phase s biglocal bigregion ->
  memory_spatial local retained biglocal -> memory_spatial region retained bigregion ->
  private_safe active owner invariant n command s phase biglocal bigregion finish (A.Spatial post frame_assertion).
Proof.
  revert command s phase local region retained biglocal bigregion.
  induction n; intros command s phase local region retained biglocal bigregion Hsafe Hvariables HR Hfree Hbig Hlocal Hregion;
    [exact I |].
  destruct Hsafe as [Hr [Hterminal [Hnoabort Hprogress]]].
  assert (Hret : memory_well_formed active retained) by exact (proj1 (persistent_full_well_formed _ _ _ _ HR)).
  split; [exact Hbig |]. split.
  - intros Hlast; destruct (Hterminal Hlast) as [E HQ]; split; [exact E |eapply full_spatial_intro; eassumption].
  - split.
    + intros external whole Henv.
      destruct (private_environment_unframe _ _ _ _ _ _ _ _ _ _ _ _ Hr Henv Hret Hfree Hregion)
        as (combined & Hframe & Hsmall).
      exact (Hnoabort _ _ Hsmall).
    + intros external whole next t whole' Henv Hstep.
      destruct (private_environment_unframe _ _ _ _ _ _ _ _ _ _ _ _ Hr Henv Hret Hfree Hregion)
        as (combined & Hframe & Hsmall).
      destruct (Hprogress _ _ _ _ _ Hsmall Hstep)
        as (phase' & local' & region' & combined' & Hsmall' & Hflush & Hdomain & Hsafe').
      destruct (spatial_flushes_split _ _ _ Hflush _ _ Hframe)
        as (external' & retained' & Hef & Hrf & Hframe').
      assert (HR' : persistent_full_satisfies active t retained' frame_assertion).
      { eapply persistent_full_agrees.
        - intros x Hx. apply (step_preserves_unmodified _ _ _ _ _ Hstep x).
          intros Hwrite; exact (Hvariables x Hwrite Hx).
        - eapply persistent_full_flushing_closed; eassumption. }
      assert (He' : memory_well_formed active external').
      { eapply flushes_well_formed; [exact Hef |exact (private_frame_wf _ _ _ _ _ _ _ _ _ Henv)]. }
      destruct (private_environment_reframe _ _ _ _ _ _ _ _ _ _ _ Hsmall' Hframe' He'
        (proj1 (persistent_full_well_formed _ _ _ _ HR')))
        as (biglocal' & bigregion' & Henv' & Hlocal' & Hregion').
      exists phase', biglocal', bigregion', external'. split; [exact Henv' |]. split; [exact Hef |]. split.
      * eapply spatial_extension_domain; [exact Hregion |exact Hregion' |exact Hdomain |].
        eapply flushes_domain_subset; exact Hrf.
      * eapply IHn; [exact Hsafe' | |exact HR' | |exact (private_region_ok _ _ _ _ _ _ _ _ _ Henv') |
          exact Hlocal' |exact Hregion'].
        -- intros x Hwrite Hx. apply (Hvariables x); [eapply step_modifies_subset; eassumption |exact Hx].
        -- exact (proj2 (spatial_free_parts _ _ _ Hframe' (private_frame_free _ _ _ _ _ _ _ _ _ Hsmall'))).
Qed.

(** Closed entry makes the separated frame lock-free automatically. The
    command may acquire and release the lock while the frame is retained. *)
Theorem private_spatial_frame_valid active owner invariant pre command finish post frame_assertion :
  private_valid active owner invariant Closed pre command finish post ->
  frame_variable_condition command frame_assertion ->
  private_valid active owner invariant Closed (A.Spatial pre frame_assertion)
    command finish (A.Spatial post frame_assertion).
Proof.
  intros Hvalid Hvariables s biglocal bigregion Hbig HP n.
  destruct (full_spatial_elim _ _ _ _ _ HP) as (local & retained & Hlocal & Hp & HR).
  destruct Hbig as [Hbl [Hbr [Hfree [pool [HJ Hpool]]]]].
  destruct (proj1 (memory_spatial_associative pool local retained bigregion)
    (ex_intro _ biglocal (conj Hlocal Hpool))) as (region & Hinner & Hregion).
  destruct (spatial_free_parts _ _ _ Hregion Hfree) as [Hrfree Hretfree].
  assert (Hr : private_region active owner invariant Closed s local region).
  { split; [exact (proj1 (persistent_full_well_formed _ _ _ _ Hp)) |]. split.
    - eapply raw_spatial_well_formed;
        [exact (proj1 (persistent_full_well_formed _ _ _ _ HJ)) |
         exact (proj1 (persistent_full_well_formed _ _ _ _ Hp)) |exact Hinner].
    - split; [exact Hrfree |exists pool; auto]. }
  eapply private_safe_spatial_frame;
    [apply Hvalid; [exact Hr |exact Hp] |exact Hvariables |exact HR |exact Hretfree | |exact Hlocal |exact Hregion].
  split; [exact Hbl |]. split; [exact Hbr |]. split; [exact Hfree |exists pool; auto].
Qed.
