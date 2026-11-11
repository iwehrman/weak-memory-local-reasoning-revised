From Stdlib Require Import List ZArith Lia.
From WMLR Require Import Expressions Machine.
Import ListNotations.

(** Section 2.1.3, pp. 14-15. Interleavings preserve each input's order and
    multiplicity. No write may be invented, duplicated or dropped. *)
Inductive interleaves {T : Type} : list T -> list T -> list T -> Prop :=
| InterleaveNil : interleaves [] [] []
| InterleaveLeft x xs ys zs :
    interleaves xs ys zs -> interleaves (x :: xs) ys (x :: zs)
| InterleaveRight y xs ys zs :
    interleaves xs ys zs -> interleaves xs (y :: ys) (y :: zs).

Lemma interleaves_comm {T} (xs ys zs : list T) :
  interleaves xs ys zs -> interleaves ys xs zs.
Proof. induction 1; constructor; assumption. Qed.

Lemma interleaves_app {T} (xs ys : list T) : interleaves xs ys (xs ++ ys).
Proof.
  induction xs; simpl; [induction ys |]; constructor; assumption.
Qed.

Lemma interleaves_nil_left {T} (ys zs : list T) :
  interleaves [] ys zs -> zs = ys.
Proof.
  intros H. remember (@nil T) as xs eqn:E in H.
  induction H; [reflexivity | discriminate |].
  f_equal. apply IHinterleaves. exact E.
Qed.

Lemma interleaves_nil_right {T} (xs zs : list T) :
  interleaves xs [] zs -> zs = xs.
Proof. intros H; apply interleaves_nil_left, interleaves_comm, H. Qed.

Lemma interleaves_length {T} (xs ys zs : list T) :
  interleaves xs ys zs -> length zs = length xs + length ys.
Proof. induction 1; simpl; [reflexivity | congruence | rewrite IHinterleaves; lia]. Qed.

Lemma interleaves_in {T} (xs ys zs : list T) x :
  interleaves xs ys zs -> (In x zs <-> In x xs \/ In x ys).
Proof. induction 1; simpl; [tauto | rewrite IHinterleaves; tauto | rewrite IHinterleaves; tauto]. Qed.

Definition buffer_domain (b : write_buffer) (loc : location) : Prop :=
  exists v, In (loc, v) b.

Definition heap_domain (h : heap) (loc : location) : Prop :=
  exists v, h loc = Some v.

Definition disjoint {T} (a b : T -> Prop) : Prop :=
  forall x, a x -> b x -> False.

Definition heap_override (past future : heap) : heap :=
  fun loc => match future loc with Some v => Some v | None => past loc end.

(** The equation on p. 14 must be read with the preceding restriction to
    interleavings. Lookup equality alone would admit dropped or extra writes. *)
Definition buffer_overrides (past future result : write_buffer) : Prop :=
  interleaves past future result /\
  forall loc, buffer_lookup result loc =
    heap_override (buffer_lookup past) (buffer_lookup future) loc.

Lemma buffer_lookup_none b loc :
  buffer_lookup b loc = None <-> ~ buffer_domain b loc.
Proof.
  induction b as [|[a v] rest IH]; simpl.
  - unfold buffer_domain. simpl. firstorder.
  - unfold buffer_domain in *. simpl.
    destruct (buffer_lookup rest loc) eqn:Hrest.
    + split; [discriminate |]. intros H.
      exfalso. assert (Hnot : ~ exists w, In (loc, w) rest).
      { intros [w Hw]. apply H. exists w; right; exact Hw. }
      pose proof (proj2 IH Hnot). discriminate.
    + destruct (Pos.eq_dec loc a) as [Heq | Hneq].
      * subst. split; [discriminate |]. intros H; exfalso; apply H; exists v; auto.
      * pose proof (proj1 IH eq_refl) as Hnot. split.
        -- intros _ [w [H | H]]; [inversion H; congruence | eauto].
        -- intros _; reflexivity.
Qed.

Lemma buffer_lookup_disjoint_left a b loc :
  disjoint (buffer_domain a) (buffer_domain b) ->
  buffer_domain a loc -> buffer_lookup b loc = None.
Proof. intros Hd Ha. apply buffer_lookup_none. exact (Hd loc Ha). Qed.

Lemma interleaves_lookup_disjoint a b c :
  interleaves a b c -> disjoint (buffer_domain a) (buffer_domain b) ->
  forall loc, buffer_lookup c loc =
    heap_override (buffer_lookup a) (buffer_lookup b) loc.
Proof.
  intros H. induction H as [|[x v] xs ys zs H IH |[y v] xs ys zs H IH];
    intros Hd loc; simpl; [reflexivity | |].
  - assert (Hd' : disjoint (buffer_domain xs) (buffer_domain ys)).
    { intros a [w Hw] Hys. apply (Hd a); [exists w; right; exact Hw | exact Hys]. }
    rewrite (IH Hd'). unfold heap_override.
    destruct (buffer_lookup ys loc) eqn:Hy; [reflexivity |].
    destruct (buffer_lookup xs loc); reflexivity.
  - assert (Hd' : disjoint (buffer_domain xs) (buffer_domain ys)).
    { intros a Hxs [w Hw]. apply (Hd a); [exact Hxs | exists w; right; exact Hw]. }
    rewrite (IH Hd'). unfold heap_override.
    destruct (buffer_lookup ys loc) eqn:Hy; [reflexivity |].
    destruct (Pos.eq_dec loc y) as [Heq | Hneq].
    + subst loc. assert (Hx : buffer_lookup xs y = None).
      { apply buffer_lookup_none. intros Hx. apply (Hd y Hx). exists v; left; reflexivity. }
      rewrite Hx; reflexivity.
    + destruct (buffer_lookup xs loc); reflexivity.
Qed.

Theorem disjoint_interleaves_override a b c :
  disjoint (buffer_domain a) (buffer_domain b) ->
  interleaves a b c -> buffer_overrides a b c.
Proof. intros Hd Hi; split; [exact Hi | apply interleaves_lookup_disjoint; assumption]. Qed.

Theorem append_overrides a b : buffer_overrides a b (a ++ b).
Proof. split; [apply interleaves_app | intros loc; apply buffer_lookup_app]. Qed.
