From Stdlib Require Import List ZArith.
From WMLR Require Import Expressions Languages Machine BufferRelations Separation
  Assertions AssertionSemantics ConcreteAssertions TransferredCells Safety Specifications
  ExecutionExamples UnlockCounterexample PrintedDerivations.
Import ListNotations.

(** The review's two INV counterexamples, now using exactly the dissertation's
    all-processor points-to abbreviation, in the original [models] semantics.
    The original four-rule [printed] calculus is unchanged. *)
Definition printed_cell x v := A.points_to (EVal (Z.pos x)) (EVal v).

Lemma printed_cell_elim active s r x v :
  models active s r (printed_cell x v) ->
  (exists k, active k) /\
  (forall l, hp (proj1_sig r) l = heap_update empty_heap x v l) /\
  (forall j, bf (proj1_sig r) j = []) /\
  lock_free (gmem active r) /\ (forall j, ~ active j \/ complete (proj1_sig r) j).
Proof.
  intros H; pose proof (points_to_requires_flushed _ _ _ _ _ H)
    as (loc & k & E & Hk & [Hh [Hb [Hf Hc]]] & Hall).
  cbn in E; inversion E; subst loc.
  split; [exists k; exact Hk |]. split; [exact Hh |].
  split; [exact Hb |]. split; [exact Hf |].
  intros j; destruct H as (a & b & Htm & HW & HB).
  specialize (HB (Z.pos j)).
  change (barrier_atom active (update s (fresh []) (Z.pos j) (fresh [])) (proj1_sig b)) in HB.
  rewrite update_same in HB; destruct (proj2 HB) as [Hnot |Hmark]; [left; exact Hnot |].
  right; apply (proj2 (proj2 Htm)); right; exact Hmark.
Qed.

Lemma printed_cell_intro active s r x v :
  (exists k, active k) ->
  (forall l, hp (proj1_sig r) l = heap_update empty_heap x v l) ->
  (forall j, bf (proj1_sig r) j = []) ->
  lock_free (gmem active r) ->
  (forall j, ~ active j \/ complete (proj1_sig r) j) ->
  models active s r (printed_cell x v).
Proof.
  intros [k Hk] Hh Hb Hf Hall.
  destruct (proj2_sig r) as [_ [Hact _]].
  assert (Hew : generalized_well_formed active (Generalized empty_memory (complete (proj1_sig r)))).
  { split; [split; simpl; [intros j H; contradiction |reflexivity] |].
    split; [exact Hact |reflexivity]. }
  exists r, (exist _ _ Hew); split; [|split].
  - simpl; split; [split |split].
    + split; [intros j _ H; contradiction |]. split.
      * intros j _ l _ [w H]; discriminate.
      * intros j j' _ _ _ l _ [w H]; contradiction.
    + split; [intros l; reflexivity |]. split.
      * intros j; simpl; rewrite app_nil_r; reflexivity.
      * intros j; simpl; unfold no_blocked; tauto.
    + intros j _; apply Hb.
    + intros j; simpl; tauto.
  - exists (Z.pos k).
    change (write_atom active (Z.pos x) (update s (fresh []) (Z.pos k) (fresh [])) v (proj1_sig r)).
    rewrite update_same; split; [exact Hk |right].
    split; [exact Hh |]. split; [exact Hb |]. split; [exact Hf |].
    destruct (Hall k); [contradiction |assumption].
  - intros value.
    change (barrier_atom active (update s (fresh []) value (fresh []))
      (Generalized empty_memory (complete (proj1_sig r)))).
    rewrite update_same; split.
    + repeat split; simpl; auto; intros j H; exact H.
    + destruct value; try exact I; apply Hall.
Qed.


Lemma printed_points_invent active x old v i :
  assertion_entails active (A.Spatial (printed_cell x v) (lockA i))
    (A.Temporal (printed_cell x old) (A.Spatial (printed_cell x v) (lockA i))).
Proof.
  intros s r Hr. pose proof Hr as Hr0. destruct Hr as (rc & rl & Hsp & Hc & Hl).
  destruct (printed_cell_elim _ _ _ _ _ Hc) as [[k Hk] (Hch & Hcb & Hcf & Hall)].
  destruct (lock_elim _ _ _ _ Hl) as (Hlh & Hlb & _).
  destruct (spatial_parts _ _ _ Hsp) as (Hh & Hb & Hbk & Hg & _).
  destruct (proj2_sig r) as [_ [Hact _]].
  assert (Hcm : complete (proj1_sig rc) k).
  { destruct (Hall k); [contradiction |assumption]. }
  assert (Hrc : complete (proj1_sig r) k) by (apply Hg; left; exact Hcm).
  assert (Hw : generalized_well_formed active
    (Generalized (Memory (heap_update empty_heap x old) empty_buffers no_blocked) (complete (proj1_sig r)))).
  { split; [split; simpl; [intros j H; contradiction | reflexivity] |].
    split; [exact Hact | intros Hnone; exfalso; exact (Hnone k Hrc)]. }
  exists (exist _ _ Hw), r. split; [| split; [| exact Hr0]].
  - simpl. split; [split | split].
    + split; [intros j H; contradiction |]. split.
      * intros j _ l [w Hw']; contradiction.
      * intros j j' _ _ _ l [w Hw']; contradiction.
    + split.
      * intros l. unfold heap_override. simpl. fold (hp (proj1_sig r) l). rewrite (Hh l).
        unfold heap_override. rewrite Hlh. unfold gmem in Hch. fold (hp (proj1_sig rc) l) in Hch.
        unfold hp in *. rewrite Hch. unfold heap_update, empty_heap. destruct (Pos.eq_dec l x); reflexivity.
      * split; [intros j; reflexivity | intros j; simpl; unfold no_blocked; tauto].
    + intros j _; reflexivity.
    + intros j; simpl; tauto.
  - apply printed_cell_intro; [exists k; exact Hk | | | |].
    + intros; reflexivity.
    + intros; reflexivity.
    + intros j H; exact H.
    + intros j; destruct (Hall j) as [H |H]; [left; exact H |right; apply Hg; left; exact H].
Qed.

Lemma printed_points_unit active x v i :
  assertion_entails active (A.Temporal (printed_cell x v) (A.Spatial A.Emp (lockA i)))
    (A.Spatial (printed_cell x v) (lockA i)).
Proof.
  intros s r (a & m & Ht & Hc & (e & rl & Hsp & He & Hl)).
  destruct (printed_cell_elim _ _ _ _ _ Hc) as [[k Hk] (Hah & Hab & Haf & Hall)].
  destruct (lock_elim _ _ _ _ Hl) as (Hlh & Hlb & Hheld).
  destruct (emp_elim _ _ _ He) as (Heh & Heb & Hek).
  destruct (spatial_parts _ _ _ Hsp) as (Hmh & Hmb & Hmk & Hmg & _).
  destruct (temporal_parts _ _ _ _ Ht) as (Hh & Hb & Hbk & _ & Hg).
  destruct (proj2_sig r) as [_ [Hact _]].
  assert (Hcm : complete (proj1_sig a) k).
  { destruct (Hall k); [contradiction |assumption]. }
  assert (Hrc : complete (proj1_sig r) k) by (apply Hg; left; exact Hcm).
  assert (Hw : generalized_well_formed active (Generalized (underlying (proj1_sig a)) (complete (proj1_sig r)))).
  { split; [exact (proj1 (proj2_sig a)) |].
    split; [exact Hact | intros Hnone; exfalso; exact (Hnone k Hrc)]. }
  assert (Hmnil : forall j, bf (proj1_sig m) j = []).
  { intros j. pose proof (Hmb j) as X. rewrite Heb, Hlb in X. apply interleaves_nil_left in X. exact X. }
  exists (exist _ _ Hw), rl. split; [| split; [| exact Hl]].
  - apply spatial_nobuf.
    + exact Hab.
    + exact Hlb.
    + intros j. rewrite Hb. unfold gmem in Hab. unfold bf in *. rewrite Hab, Hmnil. reflexivity.
    + intros l _ H. apply H, Hlh.
    + intros j H _. exact (Haf j H).
    + intros l. rewrite Hh. unfold heap_override. rewrite Hmh. unfold heap_override.
      rewrite Hlh, Heh. reflexivity.
    + intros j. rewrite Hbk, Hmk. unfold bl; simpl. split.
      * intros [H | [H | H]]; [left; exact H | destruct (Hek j H) | right; exact H].
      * intros [H | H]; [left; exact H | right; right; exact H].
    + intros j. simpl. split; [intros H; left; exact H |].
      intros [H | H]; [exact H |]. apply Hg. right. apply Hmg. right. exact H.
  - apply printed_cell_intro; [exists k; exact Hk |exact Hah |exact Hab |exact Haf |].
    intros j; destruct (Hall j) as [H |H]; [left; exact H |right; apply Hg; left; exact H].
Qed.

Lemma printed_points_donate active x v i :
  assertion_entails active
    (A.Spatial (A.Or A.Emp (printed_cell x v)) (A.Spatial (printed_cell x v) (lockA i)))
    (A.Spatial (A.Or A.Emp (printed_cell x v)) (A.Spatial A.Emp (lockA i))).
Proof.
  intros s r (rJ & rest & Hsp & HJ & (rc & rl & Hsp2 & Hc & Hl)).
  destruct (printed_cell_elim _ _ _ _ _ Hc) as [[k Hk] (Hch & Hcb & Hcf & Hall)].
  destruct (lock_elim _ _ _ _ Hl) as (Hlh & Hlb & Hheld).
  destruct (spatial_parts _ _ _ Hsp) as (Hh & Hb & Hbk & Hg & Hdis).
  destruct (spatial_parts _ _ _ Hsp2) as (Hrh & Hrb & Hrk & Hrg & _).
  unfold hp in Hch.
  unfold gmem in *.
  destruct HJ as [He | HJc].
  2:{ exfalso. destruct (printed_cell_elim _ _ _ _ _ HJc) as [_ (HJh & _)].
      apply (Hdis x v v).
      - unfold hp, gmem in *. rewrite HJh. apply heap_update_same.
      - rewrite Hrh. unfold heap_override. rewrite Hlh. unfold hp. rewrite Hch. apply heap_update_same. }
  destruct (emp_elim _ _ _ He) as (Heh & Heb & Hek).
  assert (Hw : generalized_well_formed active (Generalized (underlying (proj1_sig rl))
    (fun j => complete (proj1_sig rJ) j \/ complete (proj1_sig rl) j))).
  { split; [exact (proj1 (proj2_sig rl)) |]. split.
    - intros j [H | H]; [exact (proj1 (proj2 (proj2_sig rJ)) j H) | exact (proj1 (proj2 (proj2_sig rl)) j H)].
    - intros _ l. apply Hlh. }
  assert (Hrestnil : forall j, bf (proj1_sig rest) j = []).
  { intros j. pose proof (Hrb j) as X. unfold bf in *. rewrite Hcb, Hlb in X.
    apply interleaves_nil_left in X. exact X. }
  exists rc, (exist _ _ Hw). split; [| split].
  - apply spatial_nobuf.
    + exact Hcb.
    + exact Hlb.
    + intros j. pose proof (Hb j) as X. rewrite Heb, Hrestnil in X.
      apply interleaves_nil_left in X. exact X.
    + intros l _ H. apply H, Hlh.
    + intros j H _. exact (Hcf j H).
    + intros l. rewrite Hh. unfold heap_override. rewrite Hrh. unfold heap_override.
      unfold hp at 4; simpl. fold (hp (proj1_sig rl) l). rewrite Hlh, Heh.
      destruct (hp (proj1_sig rc) l); reflexivity.
    + intros j. rewrite Hbk, Hrk. unfold bl; simpl. split.
      * intros [H | H]; [destruct (Hek j H) | exact H].
      * intros H; right; exact H.
    + intros j. simpl. rewrite (Hg j), (Hrg j). tauto.
  - right. exact Hc.
  - exists rJ, rl. split; [| split; [exact He | exact Hl]].
    apply spatial_nobuf.
    + exact Heb.
    + exact Hlb.
    + exact Hlb.
    + intros l H _. apply H, Heh.
    + intros j H _. exact (Hek j H).
    + intros l. unfold heap_override, hp; simpl. fold (hp (proj1_sig rl) l). rewrite Hlh.
      symmetry. apply Heh.
    + intros j. unfold bl; simpl. split; [intros H; right; exact H |].
      intros [H | H]; [destruct (Hek j H) | exact H].
    + intros j. simpl. tauto.
Qed.

Lemma printed_points_import active k x v i : active k ->
  assertion_entails active
    (A.Spatial (printed_cell x v) (A.Spatial A.Emp (lockA i)))
    (A.Spatial (printed_cell x v) (A.Spatial (barA k) (lockA i))).
Proof.
  intros Hactive s r (rJ & rest & Hsp & HJ & (re & rl & Hsp2 & He & Hl)).
  destruct (printed_cell_elim _ _ _ _ _ HJ) as [_ (_ & _ & _ & Hall)].
  destruct (lock_elim _ _ _ _ Hl) as (Hlh & Hlb & Hheld).
  destruct (emp_elim _ _ _ He) as (Heh & Heb & Hek).
  destruct (spatial_parts _ _ _ Hsp2) as (Hrh & _ & _ & Hrg & _).
  assert (Hwe : generalized_well_formed active (Generalized (underlying (proj1_sig re))
    (fun j => complete (proj1_sig re) j \/ complete (proj1_sig rJ) j))).
  { split; [exact (proj1 (proj2_sig re)) |]. split.
    - intros j [H | H]; [exact (proj1 (proj2 (proj2_sig re)) j H) | exact (proj1 (proj2 (proj2_sig rJ)) j H)].
    - intros _ l. apply Heh. }
  assert (Hwr : generalized_well_formed active (Generalized (underlying (proj1_sig rest))
    (fun j => complete (proj1_sig rest) j \/ complete (proj1_sig rJ) j))).
  { split; [exact (proj1 (proj2_sig rest)) |]. split.
    - intros j [H | H]; [exact (proj1 (proj2 (proj2_sig rest)) j H) | exact (proj1 (proj2 (proj2_sig rJ)) j H)].
    - intros _ l. change (hp (proj1_sig rest) l = None). rewrite Hrh. unfold heap_override. rewrite Hlh. apply Heh. }
  exists rJ, (exist _ _ Hwr). split; [| split; [exact HJ |]].
  - split; [exact (proj1 Hsp) |]. intros j. simpl. rewrite (proj2 Hsp j). tauto.
  - exists (exist _ _ Hwe), rl. split; [| split; [| exact Hl]].
    + split; [exact (proj1 Hsp2) |]. intros j. simpl. rewrite (Hrg j). tauto.
    + change (barrier_atom active (Z.pos k) (Generalized (underlying (proj1_sig re))
        (fun j => complete (proj1_sig re) j \/ complete (proj1_sig rJ) j))).
      split; [exact He | right; right; destruct (Hall k); [contradiction |assumption]].
Qed.

Theorem printed_points_derives_stale_value active x old v i :
  printed active (A.Or A.Emp (printed_cell x v))
    (A.Spatial (printed_cell x v) (lockA i)) (skip1 i)
    (A.Spatial (printed_cell x old) (lockA i)).
Proof.
  eapply PCons; [apply printed_points_invent | |apply printed_points_unit].
  apply PFrameTm; [|apply skip_frame_condition].
  apply PInv; eapply PCons; [apply printed_points_donate |apply PSkip |apply entails_refl].
Qed.

Theorem printed_points_derives_foreign_barrier active k x v i R : active k ->
  printed active (printed_cell x v)
    (A.Temporal R (A.Spatial A.Emp (lockA i))) (skip1 i)
    (A.Temporal R (A.Spatial (barA k) (lockA i))).
Proof.
  intros Hk; apply PFrameTm; [|apply skip_frame_condition].
  apply PInv; eapply PCons; [apply printed_points_import,Hk |apply PSkip |apply entails_refl].
Qed.

Lemma printed_points_held7_pre s : full_satisfies two_processors s held7
  (A.Spatial (printed_cell X 7%Z) (lockA P1)).
Proof.
  exists (exist _ _ (two_wf _ held7_wf)). split; [reflexivity |].
  exists (exist _ _ (two_wf _ cell7_wf)), owned_lock_resource. split; [| split].
  - apply spatial_nobuf; unfold hp, bf, bl; simpl; try reflexivity.
    + intros l _ H; apply H; reflexivity.
    + intros j H _; exact H.
    + intros j. unfold no_blocked. tauto.
    + intros j. tauto.
  - apply printed_cell_intro; [exists 1%positive; left; reflexivity | | | |].
    + intros; reflexivity.
    + intros; reflexivity.
    + intros j H; exact H.
    + intros j; destruct (Pos.eq_dec j 1%positive) as [-> |H1];
        [right; left; reflexivity |].
      destruct (Pos.eq_dec j 2%positive) as [-> |H2]; [right; right; reflexivity |].
      left; intros [H |H]; contradiction.
  - change (lock_atom two_processors (Z.pos P1) (Generalized owned_lock_memory two_processors)).
    split; [reflexivity |]. split; [reflexivity | exact owned_lock_held].
Qed.

Lemma printed_points_held7_not_post s : ~ full_satisfies two_processors s held7
  (A.Spatial (printed_cell X 5%Z) (lockA P1)).
Proof.
  intros (r & Hr & (rc & rl & Hsp & Hc & Hl)).
  destruct (printed_cell_elim _ _ _ _ _ Hc) as [_ (Hch & _)].
  destruct (lock_elim _ _ _ _ Hl) as (Hlh & _).
  destruct (spatial_parts _ _ _ Hsp) as (Hh & _).
  specialize (Hh X). unfold heap_override in Hh. rewrite Hlh in Hh.
  unfold hp, gmem in *. rewrite Hch, heap_update_same, Hr in Hh. simpl in Hh.
  rewrite heap_update_same in Hh. discriminate.
Qed.

(** The printed rules derive a specification that is false of a terminal
    state, and invalid for the printed safety predicate. *)
Theorem printed_points_stale_value_unsound :
  let J := A.Or A.Emp (printed_cell X 7%Z) in
  let pre := A.Spatial (printed_cell X 7%Z) (lockA P1) in
  let post := A.Spatial (printed_cell X 5%Z) (lockA P1) in
  printed two_processors J pre (skip1 P1) post /\
  (forall s, full_satisfies two_processors s held7 pre /\
             ~ full_satisfies two_processors s held7 post) /\
  ~ valid_specification two_processors J pre (skip1 P1) post.
Proof.
  split; [apply printed_points_derives_stale_value |].
  split; [intros s; split; [apply printed_points_held7_pre | apply printed_points_held7_not_post] |].
  apply (skip_needs_post _ _ _ _ _ (fun _ => 0%Z) held7); [apply printed_points_held7_pre | apply printed_points_held7_not_post].
Qed.


Theorem printed_points_foreign_barrier_unsound :
  let J := printed_cell X 7%Z in
  let pre := A.Temporal Rpend (A.Spatial A.Emp (lockA P1)) in
  let post := A.Temporal Rpend (A.Spatial (barA P2) (lockA P1)) in
  printed two_processors J pre (skip1 P1) post /\
  (forall s, full_satisfies two_processors s held_pend pre /\
             ~ full_satisfies two_processors s held_pend post) /\
  ~ valid_specification two_processors J pre (skip1 P1) post.
Proof.
  split; [apply printed_points_derives_foreign_barrier; right; reflexivity |].
  split; [intros s; split; [apply held_pend_pre | apply held_pend_not_post] |].
  apply (skip_needs_post _ _ _ _ _ (fun _ => 0%Z) held_pend);
    [apply held_pend_pre | apply held_pend_not_post].
Qed.
