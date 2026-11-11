From Stdlib Require Import List ZArith Bool.
From WMLR Require Import Expressions Machine BufferRelations OrderedBuffers.
Import ListNotations.

(** Finite search makes the existential buffer reassociations usable as
    functions. In particular, lifting them to arbitrary processor arrays
    does not require a choice axiom or a finite processor domain. *)
Definition address_present loc (b : write_buffer) : bool :=
  existsb (fun w => Pos.eqb loc (fst w)) b.

Lemma address_present_spec loc b :
  address_present loc b = true <-> buffer_domain b loc.
Proof.
  unfold address_present, buffer_domain. rewrite existsb_exists. split.
  - intros [[a v] [Hin Heq]]. apply Pos.eqb_eq in Heq; simpl in Heq.
    subst a. exists v; exact Hin.
  - intros [v Hin]. exists (loc, v). split; [exact Hin | apply Pos.eqb_refl].
Qed.

Lemma address_absent_spec loc b :
  address_present loc b = false <-> ~ buffer_domain b loc.
Proof.
  rewrite <- address_present_spec. destruct (address_present loc b); intuition discriminate.
Qed.

Fixpoint ordered_results (past : write_buffer) : write_buffer -> list write_buffer :=
  match past with
  | [] => fun future => [future]
  | w :: tail =>
      fix go (future : write_buffer) : list write_buffer :=
        let from_left := map (cons w) (ordered_results tail future) in
        match future with
        | [] => from_left
        | v :: ys =>
            if address_present (fst v) (w :: tail) then from_left
            else from_left ++ map (cons v) (go ys)
        end
  end.

Lemma ordered_results_sound a b out :
  In out (ordered_results a b) -> ordered_overrides a b out.
Proof.
  revert b out. induction a as [|w a IHa]; intros b.
  - intros out [Heq | Hfalse]; [subst out; apply ordered_append | contradiction].
  - induction b as [|v b IHb]; intros out; cbn [ordered_results].
    + intros Hin. apply in_map_iff in Hin. destruct Hin as [tail [Heq Hin]].
      subst out. constructor. apply IHa, Hin.
    + destruct (address_present (fst v) (w :: a)) eqn:Hfresh.
      * intros Hin. apply in_map_iff in Hin. destruct Hin as [tail [Heq Hin]].
        subst out. constructor. apply IHa, Hin.
      * rewrite in_app_iff. intros [Hin | Hin]; apply in_map_iff in Hin;
          destruct Hin as [tail [Heq Hin]]; subst out.
        -- constructor. apply IHa, Hin.
        -- apply OrderedRight; [apply address_absent_spec, Hfresh | apply IHb, Hin].
Qed.

Lemma ordered_results_left w a b out :
  In out (ordered_results a b) -> In (w :: out) (ordered_results (w :: a) b).
Proof.
  intros Hin. destruct b as [|v b]; cbn [ordered_results].
  - apply in_map, Hin.
  - destruct (address_present (fst v) (w :: a));
      [apply in_map | apply in_or_app; left; apply in_map]; exact Hin.
Qed.

Lemma ordered_results_complete a b out :
  ordered_overrides a b out -> In out (ordered_results a b).
Proof.
  induction 1 as [|w a b out H IH |w a b out Hfresh H IH].
  - left; reflexivity.
  - apply ordered_results_left, IH.
  - destruct a as [|v a].
    + simpl in IH. destruct IH as [Heq | Hfalse]; [subst out; left; reflexivity | contradiction].
    + cbn [ordered_results]. rewrite (proj2 (address_absent_spec _ _) Hfresh).
      apply in_or_app; right; apply in_map, IH.
Qed.

Theorem ordered_results_spec a b out :
  In out (ordered_results a b) <-> ordered_overrides a b out.
Proof. split; [apply ordered_results_sound | apply ordered_results_complete]. Qed.

Definition write_eq_dec (x y : location * value) : {x = y} + {x <> y}.
Proof. decide equality; [apply Z.eq_dec | apply Pos.eq_dec]. Defined.

Definition buffer_eq_dec : forall x y : write_buffer, {x = y} + {x <> y} :=
  list_eq_dec write_eq_dec.

Definition ordered_test a b out : bool :=
  if in_dec buffer_eq_dec out (ordered_results a b) then true else false.

Lemma ordered_test_spec a b out :
  ordered_test a b out = true <-> ordered_overrides a b out.
Proof.
  unfold ordered_test. destruct (in_dec buffer_eq_dec out (ordered_results a b));
    rewrite <- ordered_results_spec; intuition discriminate.
Qed.

Definition select_buffer (candidates : list write_buffer) (test : write_buffer -> bool) :=
  match find test candidates with Some b => b | None => [] end.

Lemma select_buffer_spec candidates test :
  (exists b, In b candidates /\ test b = true) ->
  In (select_buffer candidates test) candidates /\ test (select_buffer candidates test) = true.
Proof.
  intros [b [Hin Htest]]. unfold select_buffer.
  destruct (find test candidates) eqn:Hfind.
  - apply find_some in Hfind; exact Hfind.
  - pose proof (find_none _ _ Hfind _ Hin). congruence.
Qed.

Definition select_left a b c out :=
  select_buffer (ordered_results a b) (fun ab => ordered_test ab c out).

Definition select_right a b c out :=
  select_buffer (ordered_results b c) (fun bc => ordered_test a bc out).

Theorem select_left_spec a b c bc out :
  ordered_overrides b c bc -> ordered_overrides a bc out ->
  ordered_overrides a b (select_left a b c out) /\
  ordered_overrides (select_left a b c out) c out.
Proof.
  intros Hbc Hout. destruct (ordered_assoc_right _ _ _ Hout _ _ Hbc) as [ab [Hab Habc]].
  unfold select_left. assert (Hex : exists x, In x (ordered_results a b) /\ ordered_test x c out = true).
  { exists ab. split; [apply ordered_results_complete, Hab | apply ordered_test_spec, Habc]. }
  destruct (select_buffer_spec _ _ Hex) as [Hin Htest]. split.
  - apply ordered_results_sound, Hin.
  - apply ordered_test_spec, Htest.
Qed.

Theorem select_right_spec a b c ab out :
  ordered_overrides a b ab -> ordered_overrides ab c out ->
  ordered_overrides b c (select_right a b c out) /\
  ordered_overrides a (select_right a b c out) out.
Proof.
  intros Hab Hout. destruct (ordered_assoc_left _ _ _ Hout _ _ Hab) as [bc [Hbc Habc]].
  unfold select_right. assert (Hex : exists x, In x (ordered_results b c) /\ ordered_test a x out = true).
  { exists bc. split; [apply ordered_results_complete, Hbc | apply ordered_test_spec, Habc]. }
  destruct (select_buffer_spec _ _ Hex) as [Hin Htest]. split.
  - apply ordered_results_sound, Hin.
  - apply ordered_test_spec, Htest.
Qed.
