From Stdlib Require Import List ZArith.
From WMLR Require Import Expressions Languages Machine BufferRelations Separation
  Assertions AssertionSemantics ConcreteAssertions TransferredCells Safety Specifications
  ExecutionExamples UnlockCounterexample.
Import ListNotations.
Module A := ConcurrentAssertion.

Definition lockA i := A.Lock (EVal (Z.pos i)).
Definition barA i := A.Barrier (EVal (Z.pos i)).
Definition gmem active (r : resource active) := underlying (proj1_sig r).

Definition cell_shape active (r : resource active) k x v :=
  (forall l, shared_heap (gmem active r) l = heap_update empty_heap x v l) /\
  (forall j, buffers (gmem active r) j = []) /\
  lock_free (gmem active r) /\ complete (proj1_sig r) k.

Lemma cell_elim active s (r : resource active) k x v :
  models active s r (processor_cell k x v) -> active k /\ cell_shape active r k x v.
Proof.
  intros (a & b & Hab & Ha & Hb).
  change (write_atom active (Z.pos x) (Z.pos k) v (proj1_sig a)) in Ha.
  change (barrier_atom active (Z.pos k) (proj1_sig b)) in Hb.
  destruct Ha as [Hi Ha]. destruct Hb as [[Hbh [Hbb Hbk]] Hbi].
  destruct Hbi as [Hn | Hbi]; [contradiction |].
  destruct Hab as [[_ [Hh [Hbuf Hk]]] [Hbefore Hg]].
  split; [exact Hi |].
  destruct Ha as [[_ [Hp _]] | [Hf [Hfb [Hfk _]]]].
  { specialize (Hbefore k Hbi). rewrite Hp, buffer_update_same in Hbefore. discriminate. }
  repeat split.
  - intros l. unfold gmem. rewrite Hh. unfold heap_override. rewrite Hbh. apply Hf.
  - intros j. unfold gmem. rewrite Hbuf, Hfb, Hbb. reflexivity.
  - intros j Hj. apply Hk in Hj. destruct Hj as [Hj | Hj]; [exact (Hfk j Hj) | exact (Hbk j Hj)].
  - apply Hg. right. exact Hbi.
Qed.

Lemma cell_intro active s (r : resource active) k x v :
  active k -> cell_shape active r k x v -> models active s r (processor_cell k x v).
Proof.
  intros Hk (Hh & Hb & Hf & Hc).
  destruct (proj2_sig r) as [_ [Hact _]].
  assert (Hew : generalized_well_formed active (Generalized empty_memory (complete (proj1_sig r)))).
  { split; [split; simpl; [intros j H; contradiction | reflexivity] |].
    split; [exact Hact | reflexivity]. }
  exists r, (exist _ _ Hew). split; [| split].
  - simpl. split; [split | split].
    + split; [intros j _ H; contradiction |]. split.
      * intros j _ l _ [w Hw]; discriminate.
      * intros j j' _ _ _ l _ [w Hw]; contradiction.
    + split; [intros l; reflexivity |].
      split; [intros j; simpl; rewrite app_nil_r; reflexivity |
              intros j; simpl; unfold no_blocked; tauto].
    + intros j _. apply Hb.
    + intros j; simpl; tauto.
  - change (write_atom active (Z.pos x) (Z.pos k) v (proj1_sig r)).
    split; [exact Hk |]. right. repeat split; assumption.
  - change (barrier_atom active (Z.pos k) (Generalized empty_memory (complete (proj1_sig r)))).
    split; [repeat split; simpl; auto; intros j H; exact H | right; exact Hc].
Qed.

Definition hp (g : generalized_memory) := shared_heap (underlying g).
Definition bf (g : generalized_memory) := buffers (underlying g).
Definition bl (g : generalized_memory) := blocked (underlying g).

Lemma spatial_nobuf a b c :
  (forall j, bf a j = []) -> (forall j, bf b j = []) -> (forall j, bf c j = []) ->
  (forall l, hp a l <> None -> hp b l <> None -> False) ->
  (forall i, bl a i -> bl b i -> False) ->
  (forall l, hp c l = heap_override (hp a) (hp b) l) ->
  (forall i, bl c i <-> bl a i \/ bl b i) ->
  completeness_union a b c -> spatial a b c.
Proof.
  unfold hp, bf, bl. intros Ba Bb Bc Hd Kd Hh Hk Hg. split; [split | exact Hg].
  - split; [| intros i; apply Kd].
    intros l [[v Hv] | [j [w Hw]]] [[v' Hv'] | [j' [w' Hw']]].
    + apply (Hd l); congruence.
    + rewrite Bb in Hw'; contradiction.
    + rewrite Ba in Hw; contradiction.
    + rewrite Ba in Hw; contradiction.
  - split; [exact Hh |]. split; [| exact Hk].
    intros j. rewrite Ba, Bb, Bc. constructor.
Qed.

Lemma spatial_parts a b c : spatial a b c ->
  (forall l, hp c l = heap_override (hp a) (hp b) l) /\
  (forall j, interleaves (bf a j) (bf b j) (bf c j)) /\
  (forall i, bl c i <-> bl a i \/ bl b i) /\ completeness_union a b c /\
  (forall l v w, hp a l = Some v -> hp b l = Some w -> False).
Proof.
  intros [[[Hd _] [Hh [Hb Hk]]] Hg].
  split; [exact Hh |]. split; [exact Hb |]. split; [exact Hk |]. split; [exact Hg |].
  intros l v w Ha Hb'. apply (Hd l); left; eexists; eassumption.
Qed.

Lemma lock_elim active s (r : resource active) i : models active s r (lockA i) ->
  (forall l, hp (proj1_sig r) l = None) /\ (forall j, bf (proj1_sig r) j = []) /\
  lock_held active (underlying (proj1_sig r)) i.
Proof. intros H. exact H. Qed.

Lemma emp_elim active s (r : resource active) : models active s r A.Emp ->
  (forall l, hp (proj1_sig r) l = None) /\ (forall j, bf (proj1_sig r) j = []) /\
  (forall j, ~ bl (proj1_sig r) j).
Proof. intros H. exact H. Qed.

(** E2: a current cell (with the lock) entails any stale earlier value before it. *)
Lemma E_invent active k x old v i :
  assertion_entails active (A.Spatial (processor_cell k x v) (lockA i))
    (A.Temporal (processor_cell k x old) (A.Spatial (processor_cell k x v) (lockA i))).
Proof.
  intros s r Hr. pose proof Hr as Hr0. destruct Hr as (rc & rl & Hsp & Hc & Hl).
  destruct (cell_elim _ _ _ _ _ _ Hc) as [Hk (Hch & Hcb & Hcf & Hcc)].
  destruct (lock_elim _ _ _ _ Hl) as (Hlh & Hlb & _).
  destruct (spatial_parts _ _ _ Hsp) as (Hh & Hb & Hbk & Hg & _).
  destruct (proj2_sig r) as [_ [Hact _]].
  assert (Hrc : complete (proj1_sig r) k) by (apply Hg; left; exact Hcc).
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
  - apply cell_intro; [exact Hk |]. repeat split; simpl; auto. intros j H; exact H.
Qed.

Lemma temporal_parts active a b c : temporal active a b c ->
  (forall l, hp c l = heap_override (hp a) (hp b) l) /\
  (forall j, bf c j = bf a j ++ bf b j) /\
  (forall i, bl c i <-> bl a i \/ bl b i) /\
  (forall i, complete b i -> bf a i = []) /\ completeness_union a b c.
Proof.
  intros [[_ [Hh [Hb Hk]]] [Hbefore Hg]].
  split; [exact Hh |]. split; [exact Hb |]. split; [exact Hk |]. split; assumption.
Qed.

(** E3: a cell followed by an emptied lock-holding state is that cell with the lock. *)
Lemma E_unit active k x v i :
  assertion_entails active (A.Temporal (processor_cell k x v) (A.Spatial A.Emp (lockA i)))
    (A.Spatial (processor_cell k x v) (lockA i)).
Proof.
  intros s r (a & m & Ht & Hc & (e & rl & Hsp & He & Hl)).
  destruct (cell_elim _ _ _ _ _ _ Hc) as [Hk (Hah & Hab & Haf & Hac)].
  destruct (lock_elim _ _ _ _ Hl) as (Hlh & Hlb & Hheld).
  destruct (emp_elim _ _ _ He) as (Heh & Heb & Hek).
  destruct (spatial_parts _ _ _ Hsp) as (Hmh & Hmb & Hmk & Hmg & _).
  destruct (temporal_parts _ _ _ _ Ht) as (Hh & Hb & Hbk & _ & Hg).
  destruct (proj2_sig r) as [_ [Hact _]].
  assert (Hrc : complete (proj1_sig r) k) by (apply Hg; left; exact Hac).
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
  - apply cell_intro; [exact Hk |]. repeat split; simpl; assumption.
Qed.

(** E1: the INV premise for donation.  The cell is reassigned to the invariant. *)
Lemma E_donate active k x v i :
  assertion_entails active
    (A.Spatial (A.Or A.Emp (processor_cell k x v)) (A.Spatial (processor_cell k x v) (lockA i)))
    (A.Spatial (A.Or A.Emp (processor_cell k x v)) (A.Spatial A.Emp (lockA i))).
Proof.
  intros s r (rJ & rest & Hsp & HJ & (rc & rl & Hsp2 & Hc & Hl)).
  destruct (cell_elim _ _ _ _ _ _ Hc) as [Hk (Hch & Hcb & Hcf & Hcc)].
  destruct (lock_elim _ _ _ _ Hl) as (Hlh & Hlb & Hheld).
  destruct (spatial_parts _ _ _ Hsp) as (Hh & Hb & Hbk & Hg & Hdis).
  destruct (spatial_parts _ _ _ Hsp2) as (Hrh & Hrb & Hrk & Hrg & _).
  unfold gmem in *.
  destruct HJ as [He | HJc].
  2:{ exfalso. destruct (cell_elim _ _ _ _ _ _ HJc) as [_ (HJh & _)].
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

(** E4: the INV premise for completeness import.  The cell's writer mark is
    copied to the empty private sibling. *)
Lemma E_import active k x v i :
  assertion_entails active
    (A.Spatial (processor_cell k x v) (A.Spatial A.Emp (lockA i)))
    (A.Spatial (processor_cell k x v) (A.Spatial (barA k) (lockA i))).
Proof.
  intros s r (rJ & rest & Hsp & HJ & (re & rl & Hsp2 & He & Hl)).
  destruct (cell_elim _ _ _ _ _ _ HJ) as [Hk (_ & _ & _ & HJc)].
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
      split; [exact He | right; right; exact HJc].
Qed.

(** * The printed rules used below (Figures 4.7 and 4.8): SKIP, CONS, INV, FRAME-TM.
    INV's [J * P * lock_i] is parsed as [J * (P * lock_i)]. *)
Inductive printed active : A.assertion -> A.assertion -> Concurrent.command -> A.assertion -> Prop :=
| PSkip J P annotation : printed active J P (Concurrent.skip annotation) P
| PCons J P P' c Q' Q :
    assertion_entails active P P' -> printed active J P' c Q' -> assertion_entails active Q' Q ->
    printed active J P c Q
| PInv J P Q c i :
    printed active A.Emp (A.Spatial J (A.Spatial P (lockA i))) c (A.Spatial J (A.Spatial Q (lockA i))) ->
    printed active J (A.Spatial P (lockA i)) c (A.Spatial Q (lockA i))
| PFrameTm J P c Q R :
    printed active J P c Q -> frame_variable_condition c R ->
    printed active J (A.Temporal R P) c (A.Temporal R Q).

Lemma entails_refl active p : assertion_entails active p p.
Proof. intros s r H; exact H. Qed.

Lemma skip_frame_condition annotation R : frame_variable_condition (Concurrent.skip annotation) R.
Proof. intros z H. inversion H. Qed.

Definition skip1 i := Concurrent.skip (EVal (Z.pos i)).

(** ** Derivation 1: a skip that "changes" a cell from [v] to [old]. *)
Theorem printed_derives_stale_value active k x old v i :
  printed active (A.Or A.Emp (processor_cell k x v))
    (A.Spatial (processor_cell k x v) (lockA i)) (skip1 i)
    (A.Spatial (processor_cell k x old) (lockA i)).
Proof.
  eapply PCons; [apply (E_invent active k x old v i) | | apply E_unit].
  apply PFrameTm; [| apply skip_frame_condition].
  apply PInv.
  eapply PCons; [apply E_donate | apply PSkip | apply entails_refl].
Qed.

(** ** Derivation 2: a skip that imports the cell writer's barrier past any frame. *)
Theorem printed_derives_foreign_barrier active k x v i R :
  printed active (processor_cell k x v)
    (A.Temporal R (A.Spatial A.Emp (lockA i))) (skip1 i)
    (A.Temporal R (A.Spatial (barA k) (lockA i))).
Proof.
  apply PFrameTm; [| apply skip_frame_condition].
  apply PInv.
  eapply PCons; [apply E_import | apply PSkip | apply entails_refl].
Qed.

(** A terminal command must already satisfy its postcondition (clause 1 of safe). *)
Lemma skip_needs_post active J pre post annotation s m :
  full_satisfies active s m pre -> ~ full_satisfies active s m post ->
  ~ valid_specification active J pre (Concurrent.skip annotation) post.
Proof.
  intros Hpre Hpost Hvalid. apply Hpost.
  destruct (Hvalid s m Hpre 1) as [Hterm _]. apply Hterm. eexists; reflexivity.
Qed.

(** * Countermodels on two processors. Processor 1 holds the lock. *)
Definition P1 : processor := 1%positive.
Definition X : location := 1%positive.
Definition cell7 := Memory (heap_update empty_heap X 7%Z) empty_buffers no_blocked.
Definition held7 := acquire two_processors cell7 P1.

Lemma two_wf m : memory_well_formed two_processors m ->
  generalized_well_formed two_processors (Generalized m two_processors).
Proof.
  intros H. split; [exact H |]. split; [intros i Hi; exact Hi |].
  intros Hnone. exfalso. apply (Hnone 1%positive). left; reflexivity.
Qed.

Lemma cell7_wf : memory_well_formed two_processors cell7.
Proof. split; simpl; [intros j H; contradiction | reflexivity]. Qed.
Lemma held7_wf : memory_well_formed two_processors held7.
Proof. apply acquire_well_formed, cell7_wf. Qed.

Lemma held7_pre s : full_satisfies two_processors s held7
  (A.Spatial (processor_cell P1 X 7%Z) (lockA P1)).
Proof.
  exists (exist _ _ (two_wf _ held7_wf)). split; [reflexivity |].
  exists (exist _ _ (two_wf _ cell7_wf)), owned_lock_resource. split; [| split].
  - apply spatial_nobuf; unfold hp, bf, bl; simpl; try reflexivity.
    + intros l _ H; apply H; reflexivity.
    + intros j H _; exact H.
    + intros j. unfold no_blocked. tauto.
    + intros j. tauto.
  - apply cell_intro; [left; reflexivity |].
    repeat split; simpl; auto; [intros j H; exact H | left; reflexivity].
  - change (lock_atom two_processors (Z.pos P1) (Generalized owned_lock_memory two_processors)).
    split; [reflexivity |]. split; [reflexivity | exact owned_lock_held].
Qed.

Lemma held7_not_post s : ~ full_satisfies two_processors s held7
  (A.Spatial (processor_cell P1 X 5%Z) (lockA P1)).
Proof.
  intros (r & Hr & (rc & rl & Hsp & Hc & Hl)).
  destruct (cell_elim _ _ _ _ _ _ Hc) as [_ (Hch & _)].
  destruct (lock_elim _ _ _ _ Hl) as (Hlh & _).
  destruct (spatial_parts _ _ _ Hsp) as (Hh & _).
  specialize (Hh X). unfold heap_override in Hh. rewrite Hlh in Hh.
  unfold hp, gmem in *. rewrite Hch, heap_update_same, Hr in Hh. simpl in Hh.
  rewrite heap_update_same in Hh. discriminate.
Qed.

(** The printed rules derive a specification that is false of a terminal
    state, and invalid for the printed safety predicate. *)
Theorem printed_calculus_stale_value_unsound :
  let J := A.Or A.Emp (processor_cell P1 X 7%Z) in
  let pre := A.Spatial (processor_cell P1 X 7%Z) (lockA P1) in
  let post := A.Spatial (processor_cell P1 X 5%Z) (lockA P1) in
  printed two_processors J pre (skip1 P1) post /\
  (forall s, full_satisfies two_processors s held7 pre /\
             ~ full_satisfies two_processors s held7 post) /\
  ~ valid_specification two_processors J pre (skip1 P1) post.
Proof.
  split; [apply printed_derives_stale_value |].
  split; [intros s; split; [apply held7_pre | apply held7_not_post] |].
  apply (skip_needs_post _ _ _ _ _ (fun _ => 0%Z) held7); [apply held7_pre | apply held7_not_post].
Qed.

(** Second countermodel: processor 2 has a write pending while processor 1 holds the lock. *)
Definition P2 : processor := 2%positive.
Definition Y : location := 2%positive.
Definition pend := Memory empty_heap (buffer_update empty_buffers P2 [(Y, 17%Z)]) no_blocked.
Definition held_pend := acquire two_processors pend P1.
Definition Rpend := A.LeadsTo (EVal (Z.pos Y)) (EVal (Z.pos P2)) (EVal 17%Z).

Lemma pend_wf : memory_well_formed two_processors pend.
Proof.
  split; simpl; [intros j H; contradiction |].
  intros j Hj. unfold buffer_update. destruct (Pos.eq_dec j P2) as [-> |]; [| reflexivity].
  exfalso. apply Hj. right; reflexivity.
Qed.
Lemma held_pend_wf : memory_well_formed two_processors held_pend.
Proof. apply acquire_well_formed, pend_wf. Qed.

Lemma bare_lock_wf : generalized_well_formed two_processors (Generalized owned_lock_memory no_blocked).
Proof.
  split; [exact (proj1 owned_lock_valid) |]. split; [intros j H; contradiction | reflexivity].
Qed.

Lemma held_pend_pre s : full_satisfies two_processors s held_pend
  (A.Temporal Rpend (A.Spatial A.Emp (lockA P1))).
Proof.
  exists (exist _ _ (two_wf _ held_pend_wf)). split; [reflexivity |].
  exists (exist _ _ (two_wf _ pend_wf)), (exist _ _ bare_lock_wf). split; [| split].
  - simpl. split; [split | split].
    + split; [intros j H; contradiction |]. split.
      * intros j _ l _ [w Hw]; discriminate.
      * intros j j' _ _ _ l _ [w Hw]; contradiction.
    + split; [intros l; reflexivity |].
      split; [intros j; simpl; rewrite app_nil_r; reflexivity |].
      intros j; simpl; unfold no_blocked; tauto.
    + intros j H; contradiction.
    + intros j; simpl; unfold no_blocked; tauto.
  - change (write_atom two_processors (Z.pos Y) (Z.pos P2) 17%Z (Generalized pend two_processors)).
    split; [right; reflexivity |]. left.
    split; [reflexivity |]. split; [reflexivity | intros j H; contradiction].
  - exists (empty_resource_value two_processors), (exist _ _ bare_lock_wf).
    split; [apply spatial_empty_left |]. split.
    + split; [reflexivity |]. split; [reflexivity | intros j H; exact H].
    + change (lock_atom two_processors (Z.pos P1) (Generalized owned_lock_memory no_blocked)).
      split; [reflexivity |]. split; [reflexivity | exact owned_lock_held].
Qed.

Lemma held_pend_not_post s : ~ full_satisfies two_processors s held_pend
  (A.Temporal Rpend (A.Spatial (barA P2) (lockA P1))).
Proof.
  intros (r & Hr & (a & m & Ht & _ & (e & rl & Hsp & He & Hl))).
  change (barrier_atom two_processors (Z.pos P2) (proj1_sig e)) in He.
  destruct He as [[_ [Heb _]] [Hn | Hc]]; [apply Hn; right; reflexivity |].
  destruct (lock_elim _ _ _ _ Hl) as (_ & Hlb & _).
  destruct (spatial_parts _ _ _ Hsp) as (_ & Hmb & _ & Hmg & _).
  destruct (temporal_parts _ _ _ _ Ht) as (_ & Hb & _ & Hbefore & _).
  assert (Hm2 : complete (proj1_sig m) P2) by (apply Hmg; left; exact Hc).
  specialize (Hb P2). rewrite (Hbefore P2 Hm2) in Hb.
  pose proof (Hmb P2) as Xi. unfold bf in *. rewrite Heb, Hlb in Xi.
  apply interleaves_nil_left in Xi. rewrite Xi, Hr in Hb. simpl in Hb.
  rewrite buffer_update_same in Hb. discriminate.
Qed.

Theorem printed_calculus_foreign_barrier_unsound :
  let J := processor_cell P2 X 7%Z in
  let pre := A.Temporal Rpend (A.Spatial A.Emp (lockA P1)) in
  let post := A.Temporal Rpend (A.Spatial (barA P2) (lockA P1)) in
  printed two_processors J pre (skip1 P1) post /\
  (forall s, full_satisfies two_processors s held_pend pre /\
             ~ full_satisfies two_processors s held_pend post) /\
  ~ valid_specification two_processors J pre (skip1 P1) post.
Proof.
  split; [apply printed_derives_foreign_barrier |].
  split; [intros s; split; [apply held_pend_pre | apply held_pend_not_post] |].
  apply (skip_needs_post _ _ _ _ _ (fun _ => 0%Z) held_pend);
    [apply held_pend_pre | apply held_pend_not_post].
Qed.

Print Assumptions printed_calculus_stale_value_unsound.
Print Assumptions printed_calculus_foreign_barrier_unsound.
