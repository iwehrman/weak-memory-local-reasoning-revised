From Stdlib Require Import List ZArith.
From WMLR Require Import Expressions Machine BufferRelations.
Import ListNotations.

(** A conservative candidate repair of list overriding. A future write may
    be selected only after every past write to its address has been selected.
    This tracks order of events, not just equality of final lookup values.
    The original separation model is retained unchanged in Separation.v. *)
Inductive ordered_overrides : write_buffer -> write_buffer -> write_buffer -> Prop :=
| OrderedNil : ordered_overrides [] [] []
| OrderedLeft w past future out :
    ordered_overrides past future out ->
    ordered_overrides (w :: past) future (w :: out)
| OrderedRight w past future out :
    ~ buffer_domain past (fst w) -> ordered_overrides past future out ->
    ordered_overrides past (w :: future) (w :: out).

Lemma ordered_interleaves past future out :
  ordered_overrides past future out -> interleaves past future out.
Proof. induction 1; constructor; assumption. Qed.

Lemma ordered_domain past future out loc :
  ordered_overrides past future out ->
  (buffer_domain out loc <-> buffer_domain past loc \/ buffer_domain future loc).
Proof.
  intros H. unfold buffer_domain. split.
  - intros [v Hv]. apply (interleaves_in _ _ _ _ (ordered_interleaves _ _ _ H)) in Hv.
    destruct Hv; [left | right]; exists v; assumption.
  - intros [[v Hv] | [v Hv]]; exists v;
      apply (interleaves_in _ _ _ _ (ordered_interleaves _ _ _ H)); auto.
Qed.

Theorem ordered_is_override past future out :
  ordered_overrides past future out -> buffer_overrides past future out.
Proof.
  intros H. split; [apply ordered_interleaves, H |].
  induction H as [|[a v] past future out H IH |[a v] past future out Hfresh H IH];
    intros loc; simpl; [reflexivity | |]; rewrite IH; unfold heap_override.
  - destruct (buffer_lookup future loc); [reflexivity |].
    destruct (buffer_lookup past loc); reflexivity.
  - destruct (buffer_lookup future loc); [reflexivity |].
    destruct (Pos.eq_dec loc a) as [Heq | Hneq].
    + subst loc. rewrite (proj2 (buffer_lookup_none past a) Hfresh). reflexivity.
    + destruct (buffer_lookup past loc); reflexivity.
Qed.

Lemma ordered_append past future : ordered_overrides past future (past ++ future).
Proof.
  induction past; simpl; [induction future |]; constructor; try assumption.
  intros [v H]; contradiction.
Qed.

(** Associativity is constructive: the proof constructs a middle list. *)
Theorem ordered_assoc_right a bc out : ordered_overrides a bc out ->
  forall b c, ordered_overrides b c bc ->
  exists ab, ordered_overrides a b ab /\ ordered_overrides ab c out.
Proof.
  intros H. induction H as [|w a bc out H IH |w a bc out Hfresh H IH]; intros b c Hbc.
  - inversion Hbc; subst. exists []; split; constructor.
  - destruct (IH _ _ Hbc) as [ab [Hab Hout]]. exists (w :: ab).
    split; constructor; assumption.
  - inversion Hbc as [|w' b' c' bc' Hinner |w' b' c' bc' HfreshB Hinner]; subst.
    + destruct (IH _ _ Hinner) as [ab [Hab Hout]]. exists (w :: ab).
      split; [apply OrderedRight; assumption | constructor; assumption].
    + destruct (IH _ _ Hinner) as [ab [Hab Hout]]. exists ab.
      split; [exact Hab |]. apply OrderedRight; [|exact Hout].
      intros Hdom. apply (ordered_domain _ _ _ _ Hab) in Hdom. tauto.
Qed.

Theorem ordered_assoc_left ab c out : ordered_overrides ab c out ->
  forall a b, ordered_overrides a b ab ->
  exists bc, ordered_overrides b c bc /\ ordered_overrides a bc out.
Proof.
  intros H. induction H as [|w ab c out H IH |w ab c out Hfresh H IH]; intros a b Hab.
  - inversion Hab; subst. exists []; split; constructor.
  - inversion Hab as [|w' a' b' ab' Hinner |w' a' b' ab' HfreshA Hinner]; subst.
    + destruct (IH _ _ Hinner) as [bc [Hbc Hout]]. exists bc.
      split; [exact Hbc | constructor; exact Hout].
    + destruct (IH _ _ Hinner) as [bc [Hbc Hout]]. exists (w :: bc).
      split; [constructor; exact Hbc | apply OrderedRight; assumption].
  - destruct (IH _ _ Hab) as [bc [Hbc Hout]]. exists (w :: bc). split.
    + apply OrderedRight; [|exact Hbc]. intros Hb.
      apply Hfresh, (ordered_domain _ _ _ _ Hab). right; exact Hb.
    + apply OrderedRight; [|exact Hout]. intros Ha.
      apply Hfresh, (ordered_domain _ _ _ _ Hab). left; exact Ha.
Qed.

Theorem ordered_associative a b c out :
  (exists bc, ordered_overrides b c bc /\ ordered_overrides a bc out) <->
  (exists ab, ordered_overrides a b ab /\ ordered_overrides ab c out).
Proof.
  split; intros [middle [Hfirst Hsecond]].
  - exact (ordered_assoc_right _ _ _ Hsecond _ _ Hfirst).
  - exact (ordered_assoc_left _ _ _ Hsecond _ _ Hfirst).
Qed.

Theorem ordered_head_origin a b w rest : ordered_overrides a b (w :: rest) ->
  (exists tail, a = w :: tail /\ ordered_overrides tail b rest) \/
  (exists tail, b = w :: tail /\ ~ buffer_domain a (fst w) /\ ordered_overrides a tail rest).
Proof. inversion 1; subst; [left | right]; eauto. Qed.

Lemma interleaves_singletons {T} (a b : T) out :
  interleaves [a] [b] out -> out = [a; b] \/ out = [b; a].
Proof.
  intros H. inversion H; subst.
  - left. f_equal. eapply interleaves_nil_left; eassumption.
  - right. f_equal. eapply interleaves_nil_right; eassumption.
Qed.

Definition write_one : location * value := (1%positive, 1%Z).
Definition write_two : location * value := (1%positive, 2%Z).
Definition write_three : location * value := (1%positive, 3%Z).

(** Proposition 2(2) is false for the original lookup-based operation, even
    after its prose restriction to interleavings has been made explicit. *)
Theorem original_buffer_override_not_associative :
  (exists bc, buffer_overrides [write_two] [write_three] bc /\
    buffer_overrides [write_one] bc [write_two; write_one; write_three]) /\
  ~ (exists ab, buffer_overrides [write_one] [write_two] ab /\
    buffer_overrides ab [write_three] [write_two; write_one; write_three]).
Proof.
  split.
  - exists [write_two; write_three]. split; [apply append_overrides |]. split.
    + apply InterleaveRight, InterleaveLeft, InterleaveRight, InterleaveNil.
    + intros loc. cbn [buffer_lookup write_one write_two write_three].
      unfold heap_override. destruct (Pos.eq_dec loc 1%positive); reflexivity.
  - intros [ab [[Hab Hlookup] [Hout _]]].
    destruct (interleaves_singletons _ _ _ Hab) as [Heq | Heq]; subst ab.
    + inversion Hout; discriminate.
    + specialize (Hlookup 1%positive). discriminate.
Qed.

Theorem disjoint_interleaves_ordered a b out :
  interleaves a b out -> disjoint (buffer_domain a) (buffer_domain b) ->
  ordered_overrides a b out.
Proof.
  intros H. induction H as [|[loc v] a b out H IH |[loc v] a b out H IH]; intros Hd.
  - constructor.
  - constructor. apply IH. intros address [w Hw] Hb.
    apply (Hd address); [exists w; right; exact Hw | exact Hb].
  - apply OrderedRight.
    + intros Ha. apply (Hd loc Ha). exists v; left; reflexivity.
    + apply IH. intros address Ha [w Hw].
      apply (Hd address Ha). exists w; right; exact Hw.
Qed.
