From Stdlib Require Import List ZArith.
From WMLR Require Import Expressions Languages Machine BufferRelations Separation
  Assertions AssertionSemantics HeapRules TransferredCells.
Import ListNotations.

(** Experimental, buffer-free ownership algebra. A retirement records the
    loss of current ownership; it is not a machine deallocation. Older heap
    values remain describable by temporal assertions but cannot revive a
    retired cell. This does NOT replace the buffer-aware interpretation. *)
Module RH.

Inductive entry := Live (v : value) | Retired.
Record resource := Resource {
  entries : location -> option entry;
  marks : processor -> Prop
}.

Definition live_heap (r : resource) : heap := fun loc =>
  match entries r loc with Some (Live v) => Some v | _ => None end.
Definition vacant r := forall loc, live_heap r loc = None.
Definition neutral r := forall loc, entries r loc = None.
Definition empty := Resource (fun _ => None) (fun _ => False).
Definition project r := Memory (live_heap r) empty_buffers no_blocked.
Definition override (a b : option entry) := match b with None => a | Some e => Some e end.
Definition compose a b := Resource (fun loc => override (entries a loc) (entries b loc))
  (fun i => marks a i \/ marks b i).
Definition equiv a b := (forall loc, entries a loc = entries b loc) /\
  (forall i, marks a i <-> marks b i).
Definition temporal a b c := equiv c (compose a b).

Definition join_entry a b :=
  match a, b with
  | Some (Live v), _ => Some (Live v)
  | _, Some (Live v) => Some (Live v)
  | Some Retired, _ | _, Some Retired => Some Retired
  | _, _ => None
  end.
Definition join a b := Resource (fun loc => join_entry (entries a loc) (entries b loc))
  (fun i => marks a i \/ marks b i).
Definition spatial a b c :=
  BufferRelations.disjoint (heap_domain (live_heap a)) (heap_domain (live_heap b)) /\
  (forall loc, entries c loc = join_entry (entries a loc) (entries b loc)) /\
  (forall i, marks c i <-> marks a i \/ marks b i).

Definition set_entry r loc e := Resource
  (fun address => if Pos.eq_dec address loc then Some e else entries r address) (marks r).
Definition retire r loc := set_entry r loc Retired.
Definition take r owner loc v := Resource (entries (set_entry r loc (Live v)))
  (fun i => marks r i \/ i = owner).
Definition singleton owner loc v := take empty owner loc v.
Definition marked_empty owner := Resource (fun _ => None) (fun i => i = owner).

Definition cell owner loc v r :=
  (forall address, live_heap r address = heap_update empty_heap loc v address) /\ marks r owner.
Definition interpretation active : interpretation resource := {|
  empty_resource := vacant;
  barrier_resource := fun z r => neutral r /\
    match z with Z.pos i => ~ active i \/ marks r i | _ => True end;
  lock_resource := fun _ _ => False;
  write_resource := fun address proc v r =>
    match address, proc with
    | Z.pos loc, Z.pos owner => active owner /\ cell owner loc v r
    | _, _ => False end;
  spatial_composition := spatial;
  temporal_composition := temporal
|}.
Definition models active s r p := satisfies (interpretation active) s r p.

Lemma equiv_refl r : equiv r r.
Proof. split; intros; reflexivity. Qed.
Lemma temporal_compose a b : temporal a b (compose a b).
Proof. apply equiv_refl. Qed.
Lemma compose_associative a b c : equiv (compose (compose a b) c) (compose a (compose b c)).
Proof.
  split.
  - intros loc; cbn [compose entries]; unfold override; destruct (entries c loc); reflexivity.
  - intros i; cbn [compose marks]; tauto.
Qed.

Theorem temporal_associative a b c out :
  (exists ab, temporal a b ab /\ temporal ab c out) <->
  (exists bc, temporal b c bc /\ temporal a bc out).
Proof.
  split.
  - intros (ab & [Hab Mab] & [Hout Mout]); exists (compose b c); split; [apply temporal_compose |].
    split.
    + intros loc; rewrite Hout; cbn [compose entries]; rewrite Hab.
      unfold compose; cbn [entries]; unfold override; destruct (entries c loc); reflexivity.
    + intros i; rewrite Mout; cbn [compose marks]; rewrite Mab; cbn [compose marks]; tauto.
  - intros (bc & [Hbc Mbc] & [Hout Mout]); exists (compose a b); split; [apply temporal_compose |].
    split.
    + intros loc; rewrite Hout; cbn [compose entries]; rewrite Hbc.
      unfold compose; cbn [entries]; unfold override; destruct (entries c loc); reflexivity.
    + intros i; rewrite Mout; cbn [compose marks]; rewrite Mbc; cbn [compose marks]; tauto.
Qed.

Lemma temporal_live_right a b c loc v : temporal a b c -> live_heap b loc = Some v -> live_heap c loc = Some v.
Proof.
  intros [H _] Hb; unfold live_heap in *; rewrite H; cbn [compose entries].
  destruct (entries b loc) as [[w|]|]; inversion Hb; reflexivity.
Qed.
Lemma temporal_retired_right a b c loc : temporal a b c -> entries b loc = Some Retired -> live_heap c loc = None.
Proof. intros [H _] Hb; unfold live_heap; rewrite H; cbn [compose entries]; rewrite Hb; reflexivity. Qed.

Lemma set_same r loc e : entries (set_entry r loc e) loc = Some e.
Proof. unfold set_entry; cbn; destruct (Pos.eq_dec loc loc); congruence. Qed.
Lemma set_other r loc e address : address <> loc -> entries (set_entry r loc e) address = entries r address.
Proof. intros H; unfold set_entry; cbn; destruct (Pos.eq_dec address loc); congruence. Qed.

Lemma retire_cell_vacant owner loc v r : cell owner loc v r -> vacant (retire r loc).
Proof.
  intros [H _] address; unfold live_heap, retire.
  destruct (Pos.eq_dec address loc) as [-> |Hne].
  - rewrite set_same; reflexivity.
  - rewrite set_other by exact Hne; change (live_heap r address = None).
    rewrite H, heap_update_other by exact Hne; reflexivity.
Qed.
Lemma take_vacant_cell owner loc v r : vacant r -> cell owner loc v (take r owner loc v).
Proof.
  intros H; split; [|right; reflexivity]. intros address.
  unfold live_heap, take; cbn [entries]. destruct (Pos.eq_dec address loc) as [-> |Hne].
  - rewrite set_same, heap_update_same; reflexivity.
  - rewrite set_other, heap_update_other by exact Hne; apply H.
Qed.

Lemma processor_cell_shape active owner loc v s r :
  models active s r (processor_cell owner loc v) -> active owner /\ cell owner loc v r.
Proof.
  intros (a & b & [H M] & [Hi [Ha Hmark]] & Hb & _).
  split; [exact Hi |]. split.
  - intros address; unfold live_heap; rewrite H; cbn [compose entries]; rewrite Hb; apply Ha.
  - apply M; left; exact Hmark.
Qed.
Lemma processor_cell_intro active owner loc v s r : active owner -> cell owner loc v r ->
  models active s r (processor_cell owner loc v).
Proof.
  intros Hi [H M]; exists r, (marked_empty owner); split.
  - split; [intros loc0; reflexivity |]. intros i; cbn [compose marks marked_empty].
    split; [auto |intros [Hmark | ->]; assumption].
  - change ((active owner /\ cell owner loc v r) /\
      (neutral (marked_empty owner) /\ (~ active owner \/ marks (marked_empty owner) owner))).
    split; [split; [exact Hi |split; assumption] |].
    split; [intros address; reflexivity |right; reflexivity].
Qed.

(** The critical changed entailment: temporal emp is not a right unit.
    Its retirement may consume the earlier live ownership. *)
Theorem historical_cell_emp_is_not_current active owner loc old s : active owner ->
  exists r, models active s r (A.Temporal (processor_cell owner loc old) A.Emp) /\
    vacant r /\ ~ models active s r (processor_cell owner loc old).
Proof.
  intros Hi; pose (a := singleton owner loc old); pose (b := retire empty loc).
  assert (Ha : cell owner loc old a) by (apply take_vacant_cell; intros address; reflexivity).
  exists (compose a b); split.
  - exists a, b; split; [apply temporal_compose |]. split; [apply processor_cell_intro; assumption |].
    intros address; unfold b, retire, live_heap; destruct (Pos.eq_dec address loc) as [-> |Hne].
    + rewrite set_same; reflexivity.
    + rewrite set_other by exact Hne; reflexivity.
  - assert (Hvac : vacant (compose a b)).
    { intros address; unfold live_heap, compose, b, retire; cbn [entries].
      destruct (Pos.eq_dec address loc) as [-> |Hne].
      - rewrite set_same; reflexivity.
      - rewrite set_other by exact Hne; cbn [empty entries override].
        change (live_heap a address = None); rewrite (proj1 Ha), heap_update_other by exact Hne; reflexivity. }
    split; [exact Hvac |]. intros Hp; destruct (processor_cell_shape _ _ _ _ _ _ Hp) as [_ [Hcell _]].
    specialize (Hvac loc); rewrite Hcell, heap_update_same in Hvac; discriminate.
Qed.

Lemma join_entry_associative a b c : join_entry (join_entry a b) c = join_entry a (join_entry b c).
Proof. destruct a as [[x|]|], b as [[y|]|], c as [[z|]|]; reflexivity. Qed.

Lemma spatial_domain a b c : spatial a b c -> forall loc,
  heap_domain (live_heap c) loc <-> heap_domain (live_heap a) loc \/ heap_domain (live_heap b) loc.
Proof.
  intros [_ [H _]] loc; unfold heap_domain, live_heap; rewrite H.
  destruct (entries a loc) as [[x|]|], (entries b loc) as [[y|]|];
    cbn [join_entry]; split; intros; try (firstorder congruence); eexists; reflexivity.
Qed.

Theorem spatial_commutative a b c : spatial a b c -> spatial b a c.
Proof.
  intros [Hd [H M]]; split.
  - intros loc Hb Ha; exact (Hd loc Ha Hb).
  - split.
    + intros loc; rewrite H; destruct (entries a loc) as [[x|]|] eqn:Ea,
        (entries b loc) as [[y|]|] eqn:Eb; try reflexivity.
      exfalso; apply (Hd loc); unfold heap_domain, live_heap; [rewrite Ea |rewrite Eb]; eexists; reflexivity.
    + intros i; rewrite M; tauto.
Qed.

Theorem spatial_associative a b c out :
  (exists ab, spatial a b ab /\ spatial ab c out) <->
  (exists bc, spatial b c bc /\ spatial a bc out).
Proof.
  split.
  - intros (ab & Hab & Hout).
    destruct Hab as [Dab [Hab Mab]]; destruct Hout as [Dout [Hout Mout]].
    assert (Eab : forall loc, heap_domain (live_heap ab) loc <->
      heap_domain (live_heap a) loc \/ heap_domain (live_heap b) loc).
    { apply spatial_domain; split; [exact Dab |auto]. }
    assert (Hbc : spatial b c (join b c)).
    { split; [intros loc Hb Hc; apply (Dout loc); [apply Eab; auto |exact Hc] |].
      split; intros; reflexivity. }
    exists (join b c); split; [exact Hbc |]. split.
    + intros loc Ha Hbcdom; apply (spatial_domain _ _ _ Hbc loc) in Hbcdom.
      destruct Hbcdom as [Hb |Hc]; [exact (Dab loc Ha Hb) |].
      apply (Dout loc); [apply Eab; auto |exact Hc].
    + split.
      * intros loc; rewrite Hout, Hab; apply join_entry_associative.
      * intros i; rewrite Mout, Mab; cbn [join marks]; tauto.
  - intros (bc & Hbc & Hout).
    destruct Hbc as [Dbc [Hbc Mbc]]; destruct Hout as [Dout [Hout Mout]].
    assert (Ebc : forall loc, heap_domain (live_heap bc) loc <->
      heap_domain (live_heap b) loc \/ heap_domain (live_heap c) loc).
    { apply spatial_domain; split; [exact Dbc |auto]. }
    assert (Hab : spatial a b (join a b)).
    { split; [intros loc Ha Hb; apply (Dout loc Ha), Ebc; auto |]. split; intros; reflexivity. }
    exists (join a b); split; [exact Hab |]. split.
    + intros loc Habdom Hc; apply (spatial_domain _ _ _ Hab loc) in Habdom.
      destruct Habdom as [Ha |Hb]; [apply (Dout loc Ha), Ebc; auto |exact (Dbc loc Hb Hc)].
    + split.
      * intros loc; rewrite Hout, Hbc; symmetry; apply join_entry_associative.
      * intros i; rewrite Mout, Mbc; cbn [join marks]; tauto.
Qed.

End RH.
