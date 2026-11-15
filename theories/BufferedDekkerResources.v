From Stdlib Require Import List Bool ZArith.
From WMLR Require Import Expressions Languages Machine BufferRelations Separation StableCompatibility
  RepairedSeparation GeneralizedFlushing OperationalSemantics Assertions AssertionSemantics
  ConcreteAssertions RepairedAssertions PersistentAssertions TemporalSafety InvariantFragment
  PrivateOwnership AssertionResourceEquivalence CellFamilies BufferedPoolCandidate.
Import ListNotations.

(** Finite descriptions of the concrete heaps used by Dekker. These are
    proof data, not new assertions or an additional validity judgment. *)
Module BD.
Definition active := BufferedDekker.active.
Definition actor (second : bool) : processor := if second then 2%positive else 1%positive.
Record image := Image { heap_cells : list (location * Z); first_buffer : write_buffer; second_buffer : write_buffer }.
Definition mem (im : image) := Memory (cell_heap (heap_cells im))
  (fun i => if Pos.eq_dec i 1%positive then first_buffer im
            else if Pos.eq_dec i 2%positive then second_buffer im else []) no_blocked.
Definition cell loc v := Image [(loc,v)] [] [].
Definition history loc old (second : bool) v :=
  Image [(loc,old)] (if second then [] else [(loc,v)]) (if second then [(loc,v)] else []).
Definition pending loc (second : bool) v :=
  Image [] (if second then [] else [(loc,v)]) (if second then [(loc,v)] else []).
Definition join a b := Image (heap_cells a ++ heap_cells b)
  (first_buffer a ++ first_buffer b) (second_buffer a ++ second_buffer b).
Definition locations im := map fst (heap_cells im) ++ map fst (first_buffer im) ++ map fst (second_buffer im).
Definition apart a b := forallb (fun x => negb (existsb (Pos.eqb x) (locations b))) (locations a).
Definition one_empty (a b : write_buffer) := match a,b with [],_ |_,[] => true |_,_ => false end.
Definition compatible a b := apart a b && one_empty (first_buffer a) (first_buffer b)
  && one_empty (second_buffer a) (second_buffer b).

Definition full (im : image) : resource active.
Proof.
  refine (exist _ (Generalized (mem im) active) _); split.
  - split; [intros i H; contradiction |]. intros i H; unfold mem; cbn; destruct (Pos.eq_dec i 1%positive), (Pos.eq_dec i 2%positive);
      try reflexivity; subst; exfalso; apply H; unfold active,BufferedDekker.active; auto.
  - split; [auto |]. intros Hnone loc; exfalso; apply (Hnone 1%positive); left; reflexivity.
Defined.

Definition with_marks (im : image) (source : resource active) owner (Hmark : complete (proj1_sig source) owner) : resource active.
Proof.
  refine (exist _ (Generalized (mem im) (complete (proj1_sig source))) _); split.
  - exact (proj1 (proj2_sig (full im))).
  - split; [exact (proj1 (proj2 (proj2_sig source))) |]. intros Hnone loc; exfalso; exact (Hnone owner Hmark).
Defined.

Lemma heap_app a b loc : cell_heap (a ++ b) loc = heap_override (cell_heap a) (cell_heap b) loc.
Proof.
  induction a as [|[address v] rest IH]; cbn [app cell_heap]; unfold heap_override.
  - destruct (cell_heap b loc); reflexivity.
  - rewrite IH; unfold heap_override; destruct (cell_heap b loc); reflexivity.
Qed.

Lemma buffer_join a b i : buffers (mem (join a b)) i = buffers (mem a) i ++ buffers (mem b) i.
Proof. unfold mem,join; cbn; destruct (Pos.eq_dec i 1%positive), (Pos.eq_dec i 2%positive); reflexivity. Qed.

Lemma mem_domain im loc : memory_domain (mem im) loc <-> In loc (locations im).
Proof.
  unfold memory_domain, locations; rewrite !in_app_iff; split.
  - intros [H |[i [v H]]].
    + left; apply cell_heap_domain, H.
    + unfold mem in H; cbn in H; destruct (Pos.eq_dec i 1%positive), (Pos.eq_dec i 2%positive);
        try contradiction; right; [left |left |right]; apply in_map with (f:=fst) in H; exact H.
  - intros [H |[H |H]].
    + left; apply cell_heap_domain, H.
    + apply in_map_iff in H; destruct H as ([l v] & E & H); cbn in E; subst l.
      right; exists 1%positive, v; exact H.
    + apply in_map_iff in H; destruct H as ([l v] & E & H); cbn in E; subst l.
      right; exists 2%positive, v; exact H.
Qed.

Lemma apart_spec a b : apart a b = true <-> disjoint (memory_domain (mem a)) (memory_domain (mem b)).
Proof.
  unfold apart; rewrite forallb_forall; split.
  - intros H loc Ha Hb; specialize (H loc (proj1 (mem_domain _ _) Ha)); apply negb_true_iff in H.
    assert (E : existsb (Pos.eqb loc) (locations b) = true).
    { apply existsb_exists; exists loc; split; [apply mem_domain,Hb |apply Pos.eqb_refl]. }
    congruence.
  - intros H loc Ha; apply negb_true_iff; destruct (existsb (Pos.eqb loc) (locations b)) eqn:E; [|reflexivity].
    apply existsb_exists in E; destruct E as (x & Hx & E); apply Pos.eqb_eq in E; subst x.
    exfalso; apply (H loc); apply mem_domain; assumption.
Qed.

Lemma join_spatial a b : apart a b = true -> memory_spatial (mem a) (mem b) (mem (join a b)).
Proof.
  intros H; split; [split; [apply apart_spec,H |intros i HA; contradiction] |].
  split; [intros loc; apply heap_app |]. split.
  - intros i; rewrite buffer_join; apply interleaves_app.
  - intros i; cbn; unfold no_blocked; tauto.
Qed.

Lemma spatial_equiv a a' b b' out out' :
  memory_equiv a a' -> memory_equiv b b' -> memory_equiv out out' ->
  memory_spatial a b out -> memory_spatial a' b' out'.
Proof.
  intros Ha Hb Ho [[Hd Hk] Hmerge]; split.
  - split.
    + intros loc H1 H2; apply (Hd loc);
        [apply (assertion_domain_equiv _ _ Ha loc),H1 |apply (assertion_domain_equiv _ _ Hb loc),H2].
    + intros i H1 H2; apply (Hk i);
        [apply (proj2 (proj2 Ha) i),H1 |apply (proj2 (proj2 Hb) i),H2].
  - eapply assertion_merge_equiv; eassumption.
Qed.

Lemma one_empty_spec a b : one_empty a b = true -> a = [] \/ b = [].
Proof. destruct a,b; cbn; intros; auto; discriminate. Qed.

Lemma spatial_shape a b whole ia ib :
  memory_spatial a b whole -> memory_equiv a (mem ia) -> memory_equiv b (mem ib) ->
  compatible ia ib = true -> memory_equiv whole (mem (join ia ib)).
Proof.
  intros [_ [Hh [Hb Hk]]] [Ha [Ba Ka]] [HB [BB KB]] Hcompat.
  apply andb_true_iff in Hcompat; destruct Hcompat as [Hcompat H2].
  apply andb_true_iff in Hcompat; destruct Hcompat as [_ H1].
  split.
  - intros loc; rewrite Hh; change (heap_override (shared_heap a) (shared_heap b) loc = cell_heap (heap_cells ia ++ heap_cells ib) loc).
    rewrite heap_app; unfold heap_override; rewrite Ha,HB; reflexivity.
  - split.
    + intros i; rewrite buffer_join. specialize (Hb i); rewrite Ba,BB in Hb.
      assert (He : buffers (mem ia) i = [] \/ buffers (mem ib) i = []).
      { unfold mem; cbn; destruct (Pos.eq_dec i 1%positive); [apply one_empty_spec,H1 |].
        destruct (Pos.eq_dec i 2%positive); [apply one_empty_spec,H2 |auto]. }
      destruct He as [E |E]; rewrite E in *.
      * apply interleaves_nil_left,Hb.
      * rewrite app_nil_r; apply interleaves_nil_right,Hb.
    + intros i; rewrite Hk,Ka,KB; cbn; unfold no_blocked; tauto.
Qed.

Inductive description := Cell (loc : location) (v : Z)
  | History (loc : location) (old : Z) (second : bool) (v : Z)
  | Sep (a b : description) | Or (a b : description).
Fixpoint assertion d := match d with
  | Cell l v => writer_points_to (EVal (Z.pos l)) (EVal v)
  | History l u i v => A.Temporal (writer_points_to (EVal (Z.pos l)) (EVal u))
      (A.LeadsTo (EVal (Z.pos l)) (EVal (Z.pos (actor i))) (EVal v))
  | Sep a b => A.Spatial (assertion a) (assertion b)
  | Or a b => A.Or (assertion a) (assertion b)
  end.
Fixpoint images d := match d with
  | Cell l v => [cell l v]
  | History l u i v => [history l u i v; cell l v]
  | Sep a b => flat_map (fun x => map (join x) (images b)) (images a)
  | Or a b => images a ++ images b
  end.
Fixpoint checked d := match d with
  | Cell _ _ | History _ _ _ _ => true
  | Sep a b => checked a && checked b &&
      forallb (fun x => forallb (compatible x) (images b)) (images a)
  | Or a b => checked a && checked b
  end.
Lemma cell_shape s r loc v : persistent_models active s r (assertion (Cell loc v)) ->
  memory_equiv (resource_memory active r) (mem (cell loc v)) /\
  exists owner, complete (proj1_sig r) owner.
Proof.
  intros H; destruct (writer_points_to_shape _ _ _ _ _ H)
    as (l & owner & E & Hi & Hh & Hb & Hk & Hm).
  cbn in E; injection E as E; subst l; split; [|eauto].
  split; [exact Hh |]. split.
  - intros i; rewrite Hb; unfold mem,cell; cbn; destruct (Pos.eq_dec i 1%positive), (Pos.eq_dec i 2%positive); reflexivity.
  - intros i; split; [intros Hbad; exfalso; exact (Hk i Hbad) |intros Hbad; contradiction].
Qed.

Lemma history_shape s r loc old second v :
  persistent_models active s r (assertion (History loc old second v)) -> lock_free (resource_memory active r) ->
  memory_equiv (resource_memory active r) (mem (history loc old second v)) \/
  memory_equiv (resource_memory active r) (mem (cell loc v)).
Proof.
  intros (a & b & [_ [[_ [Hh [Hb Hk]]] _]] & Ha & Hwrite) Hfree.
  destruct (cell_shape _ _ _ _ Ha) as [[Hah [Hab Hak]] Hmark].
  change (active (actor second) /\
    (pending_atom (actor second) loc v (proj1_sig b) \/ flushed_atom (actor second) loc v (proj1_sig b))) in Hwrite.
  destruct Hwrite as [_ [[Hbh [Hbb Hbk]] |[Hbh [Hbb [Hbk Hbm]]]]].
  - left; split.
    + intros l; unfold resource_memory; rewrite Hh; unfold heap_override; rewrite Hbh; exact (Hah l).
    + split.
      * intros i; unfold resource_memory; rewrite Hb,Hab,Hbb.
        destruct second; unfold actor,mem,cell,history; cbn; unfold buffer_update;
          destruct (Pos.eq_dec i 1%positive), (Pos.eq_dec i 2%positive); try reflexivity; congruence.
      * intros i; split; [intros Hbad; exfalso; exact (Hfree i Hbad) |intros Hbad; contradiction].
  - right; split.
    + intros l; unfold resource_memory; rewrite Hh; unfold heap_override; rewrite Hbh,Hah.
      unfold mem,cell; cbn; unfold heap_override,heap_update; destruct (Pos.eq_dec l loc); reflexivity.
    + split.
      * intros i; unfold resource_memory; rewrite Hb,Hab,Hbb.
        unfold mem,cell; cbn; destruct (Pos.eq_dec i 1%positive), (Pos.eq_dec i 2%positive); reflexivity.
      * intros i; split; [intros Hbad; exfalso; exact (Hfree i Hbad) |intros Hbad; contradiction].
Qed.

Lemma checked_pair a b : checked (Sep a b) = true ->
  checked a = true /\ checked b = true /\
  forall ia ib, In ia (images a) -> In ib (images b) -> compatible ia ib = true.
Proof.
  cbn [checked]; rewrite !andb_true_iff; intros [[Ha Hb] HC]; split; [exact Ha |]. split; [exact Hb |].
  intros ia ib HA HB; rewrite forallb_forall in HC; specialize (HC ia HA).
  rewrite forallb_forall in HC; apply HC,HB.
Qed.

Theorem models_image d : checked d = true -> forall s r,
  persistent_models active s r (assertion d) -> lock_free (resource_memory active r) ->
  exists im, In im (images d) /\ memory_equiv (resource_memory active r) (mem im).
Proof.
  induction d as [loc v|loc old second v|a IHa b IHb|a IHa b IHb]; intros HC s r Hmodel Hfree.
  - exists (cell loc v); split; [left; reflexivity |apply (proj1 (cell_shape _ _ _ _ Hmodel))].
  - destruct (history_shape _ _ _ _ _ _ Hmodel Hfree) as [H |H];
      [exists (history loc old second v) |exists (cell loc v)]; split; [left; reflexivity |exact H |right; left; reflexivity |exact H].
  - destruct (checked_pair _ _ HC) as [CA [CB CAB]].
    destruct Hmodel as (ra & rb & [Hsp Hmarks] & HA & HB).
    destruct (spatial_free_parts _ _ _ Hsp Hfree) as [FA FB].
    destruct (IHa CA _ _ HA FA) as (ia & IA & EA), (IHb CB _ _ HB FB) as (ib & IB & EB).
    exists (join ia ib); split.
    + apply in_flat_map; exists ia; split; [exact IA |apply in_map; exact IB].
    + eapply spatial_shape; [exact Hsp |exact EA |exact EB |apply CAB; assumption].
  - cbn [checked] in HC; apply andb_true_iff in HC; destruct HC as [CA CB].
    destruct Hmodel as [H |H]; [destruct (IHa CA _ _ H Hfree) as (im & HI & HE)
      |destruct (IHb CB _ _ H Hfree) as (im & HI & HE)]; exists im; split; try exact HE;
      apply in_or_app; auto.
Qed.

Lemma full_cell s loc v : persistent_models active s (full (cell loc v)) (assertion (Cell loc v)).
Proof.
  eapply writer_points_to_from_shape with (loc:=loc) (owner:=1%positive).
  - reflexivity.
  - left; reflexivity.
  - intros; reflexivity.
  - intros i; unfold resource_memory,full,mem,cell; cbn; destruct (Pos.eq_dec i 1%positive), (Pos.eq_dec i 2%positive); reflexivity.
  - intros i H; exact H.
  - left; reflexivity.
Qed.

Lemma cell_buffers loc v i : buffers (mem (cell loc v)) i = [].
Proof. unfold mem,cell; cbn; destruct (Pos.eq_dec i 1%positive), (Pos.eq_dec i 2%positive); reflexivity. Qed.

Lemma full_temporal_cell loc old b out : memory_equiv (mem (join (cell loc old) b)) (mem out) ->
  repaired_temporal active (proj1_sig (full (cell loc old))) (proj1_sig (full b)) (proj1_sig (full out)).
Proof.
  intros Heq.
  assert (Hstable : stable_compatible active (mem (cell loc old)) (mem b)).
  { split; [intros i H; contradiction |]. split.
    - intros i Hi l [w H] Hheap; rewrite cell_buffers in H; contradiction.
    - intros i j Hi Hj Hne l [w H] Hbuf; rewrite cell_buffers in H; contradiction. }
  assert (Htemp : repaired_temporal active (proj1_sig (full (cell loc old))) (proj1_sig (full b))
    (proj1_sig (full (join (cell loc old) b)))).
  { split; [exact Hstable |]. split.
    - split; [apply stable_implies_original_compatible,Hstable |].
      split; [intros l; apply heap_app |]. split; [intros i; apply buffer_join |].
      intros i; cbn; unfold no_blocked; tauto.
    - split; [intros i _; apply cell_buffers |intros i; cbn; tauto]. }
  eapply assertion_temporal_equiv; [apply assertion_generalized_equiv_refl |apply assertion_generalized_equiv_refl | |exact Htemp].
  split; [exact Heq |intros; reflexivity].
Qed.

Lemma full_history s loc old second v :
  persistent_models active s (full (history loc old second v)) (assertion (History loc old second v)) /\
  persistent_models active s (full (cell loc v)) (assertion (History loc old second v)).
Proof.
  assert (Hi : active (actor second)) by (destruct second; [right |left]; reflexivity).
  split.
  - exists (full (cell loc old)), (full (pending loc second v)); split.
    + apply full_temporal_cell; split; [intros l; reflexivity |]. split.
      * intros i; rewrite buffer_join,cell_buffers; reflexivity.
      * intros; reflexivity.
    + split; [apply full_cell |]. split; [exact Hi |left]. split; [intros; reflexivity |]. split.
      * intros i; destruct second; unfold resource_memory,full,mem,pending,actor; cbn; unfold buffer_update;
          destruct (Pos.eq_dec i 1%positive), (Pos.eq_dec i 2%positive); try reflexivity; congruence.
      * intros i H; contradiction.
  - exists (full (cell loc old)), (full (cell loc v)); split.
    + apply full_temporal_cell; split.
      * intros l; unfold mem,join,cell; cbn; unfold heap_override,heap_update;
          destruct (Pos.eq_dec l loc); reflexivity.
      * split; [intros i; rewrite buffer_join,!cell_buffers; reflexivity |intros; reflexivity].
    + split; [apply full_cell |]. split; [exact Hi |right]. split; [intros; reflexivity |].
      split; [apply cell_buffers |]. split; [intros i H; exact H |exact Hi].
Qed.

Theorem image_models d : checked d = true -> forall im,
  In im (images d) -> forall s, persistent_models active s (full im) (assertion d).
Proof.
  induction d as [loc v|loc old second v|a IHa b IHb|a IHa b IHb]; intros HC im HI s.
  - destruct HI as [<- |[]]; apply full_cell.
  - destruct HI as [<- |[<- |[]]]; apply full_history.
  - destruct (checked_pair _ _ HC) as [CA [CB CAB]].
    apply in_flat_map in HI; destruct HI as (ia & IA & HI); apply in_map_iff in HI; destruct HI as (ib & <- & IB).
    exists (full ia), (full ib); split.
    + split; [apply join_spatial |intros i; cbn; tauto].
      specialize (CAB ia ib IA IB); apply andb_true_iff in CAB; destruct CAB as [CAB _].
      apply andb_true_iff in CAB; tauto.
    + split; [apply IHa |apply IHb]; assumption.
  - apply andb_true_iff in HC; destruct HC as [CA CB]; apply in_app_or in HI; destruct HI;
      [left; apply IHa |right; apply IHb]; assumption.
Qed.
Fixpoint plain d := match d with Cell _ _ => true |Sep a b => plain a && plain b |_ => false end.
Lemma images_nonempty d : images d <> [].
Proof.
  induction d; cbn; try discriminate.
  - destruct (images d1) as [|a rest] eqn:E; [contradiction |]. cbn; intros H; apply app_eq_nil in H.
    destruct (images d2); [contradiction |destruct H as [H _]; discriminate].
  - intros H; apply app_eq_nil in H; tauto.
Qed.
Definition only_image d := hd (Image [] [] []) (images d).
Lemma only_image_in d : In (only_image d) (images d).
Proof. unfold only_image; destruct (images d) eqn:E; [exfalso; exact (images_nonempty d E) |left; reflexivity]. Qed.

Lemma plain_images d : plain d = true -> images d = [only_image d].
Proof.
  induction d; cbn [plain]; intros H; try discriminate; [reflexivity |].
  apply andb_true_iff in H; destruct H as [HA HB]. specialize (IHd1 HA); specialize (IHd2 HB).
  cbn [images]; rewrite IHd1,IHd2; unfold only_image at 3; cbn [images]; rewrite IHd1,IHd2; reflexivity.
Qed.

Lemma plain_mark d : plain d = true -> forall s r,
  persistent_models active s r (assertion d) -> exists owner, complete (proj1_sig r) owner.
Proof.
  induction d; cbn [plain]; intros H s r HP; try discriminate.
  - exact (proj2 (cell_shape _ _ _ _ HP)).
  - apply andb_true_iff in H; destruct H as [HA HB].
    destruct HP as (a & b & [Hsp Hmarks] & Ha & Hb).
    destruct (IHd1 HA _ _ Ha) as (owner & H); exists owner; apply Hmarks; auto.
Qed.

Lemma marked_image_models d : plain d = true -> checked d = true -> forall im,
  In im (images d) -> forall s source owner Hmark,
  persistent_models active s (with_marks im source owner Hmark) (assertion d).
Proof.
  induction d as [loc v|loc old second v|a IHa b IHb|a IHa b IHb]; intros HP HC im HI s source owner Hmark;
    try discriminate.
  - destruct HI as [<- |[]]; eapply writer_points_to_from_shape with (loc:=loc) (owner:=owner).
    + reflexivity.
    + exact (proj1 (proj2 (proj2_sig source)) owner Hmark).
    + intros; reflexivity.
    + apply cell_buffers.
    + intros i H; exact H.
    + exact Hmark.
  - apply andb_true_iff in HP; destruct HP as [PA PB].
    destruct (checked_pair _ _ HC) as [CA [CB CAB]].
    apply in_flat_map in HI; destruct HI as (ia & IA & HI); apply in_map_iff in HI; destruct HI as (ib & <- & IB).
    exists (with_marks ia source owner Hmark), (with_marks ib source owner Hmark); split.
    + split; [apply join_spatial |intros i; cbn; tauto].
      specialize (CAB ia ib IA IB); apply andb_true_iff in CAB; destruct CAB as [CAB _].
      apply andb_true_iff in CAB; tauto.
    + split; [apply IHa |apply IHb]; assumption.
Qed.

Definition value_eqb a b := match a,b with Some x,Some y => Z.eqb x y |None,None => true |_,_ => false end.
Lemma value_eqb_spec a b : value_eqb a b = true -> a=b.
Proof. destruct a,b; cbn; intros H; try discriminate; [f_equal; apply Z.eqb_eq,H |reflexivity]. Qed.
Fixpoint buffer_eqb (a b : write_buffer) := match a,b with
  |[],[] => true |(l,v)::xs,(k,w)::ys => Pos.eqb l k && Z.eqb v w && buffer_eqb xs ys |_ ,_ => false end.
Lemma buffer_eqb_spec a b : buffer_eqb a b = true -> a=b.
Proof.
  revert b; induction a as [|[l v] xs IH]; intros [|[k w] ys] H; try discriminate; [reflexivity |].
  cbn in H; rewrite !andb_true_iff in H; destruct H as [[HL HV] HT].
  apply Pos.eqb_eq in HL; apply Z.eqb_eq in HV; subst; f_equal; apply IH,HT.
Qed.
Definition image_eqb a b :=
  forallb (fun l => value_eqb (cell_heap (heap_cells a) l) (cell_heap (heap_cells b) l))
    (map fst (heap_cells a) ++ map fst (heap_cells b)) &&
  buffer_eqb (first_buffer a) (first_buffer b) && buffer_eqb (second_buffer a) (second_buffer b).
Lemma image_eqb_spec a b : image_eqb a b = true -> memory_equiv (mem a) (mem b).
Proof.
  unfold image_eqb; rewrite !andb_true_iff; intros [[HH HB1] HB2].
  apply buffer_eqb_spec in HB1; apply buffer_eqb_spec in HB2.
  rewrite forallb_forall in HH; split.
  - intros l; cbn [mem shared_heap].
    destruct (in_dec Pos.eq_dec l (map fst (heap_cells a) ++ map fst (heap_cells b))) as [H |H].
    + apply value_eqb_spec,HH,H.
    + destruct (cell_heap (heap_cells a) l) eqn:EA, (cell_heap (heap_cells b) l) eqn:EB; try reflexivity;
        exfalso; apply H; apply in_or_app; [left |left |right]; apply cell_heap_domain; eexists; eassumption.
  - split; [|intros; reflexivity]. intros i; unfold mem; cbn;
      destruct (Pos.eq_dec i 1%positive), (Pos.eq_dec i 2%positive); assumption || reflexivity.
Qed.
Lemma plain_buffers d : plain d = true -> forall im, In im (images d) ->
  first_buffer im = [] /\ second_buffer im = [].
Proof.
  induction d; intros H im HI; try discriminate.
  - destruct HI as [<- |[]]; split; reflexivity.
  - apply andb_true_iff in H; destruct H as [HA HB].
    apply in_flat_map in HI; destruct HI as (ia & IA & HI); apply in_map_iff in HI; destruct HI as (ib & <- & IB).
    destruct (IHd1 HA ia IA) as [A1 A2], (IHd2 HB ib IB) as [B1 B2].
    cbn [join first_buffer second_buffer]; rewrite A1,A2,B1,B2; auto.
Qed.
End BD.
