From Stdlib Require Import List ZArith.
From WMLR Require Import Expressions Languages Machine OperationalSemantics Assertions AssertionSemantics
  InvariantFragment CellFamilies RegionRules NamedLockSyntax.
Import ListNotations.

Definition mailbox_flag value := concrete_cell 2%positive value.
Definition mailbox_invariant items := A.Or (mailbox_flag 0%Z) (A.Spatial (mailbox_flag 1%Z) (cell_family items)).
Definition mailbox_locks items : nl_family := [(1%positive,mailbox_invariant items)].
Definition mailbox_store actor value := nl_store actor 2%positive value.
Definition mailbox_set value := C.Prim (C.Common (S.Assign 1 (EVal value))) (EVal 2%Z).

Definition mailbox_producer items := C.Seq (fill_region 1%positive items)
  (C.Seq (nl_acquire 1%positive 1%positive 0)
    (C.Seq (mailbox_store 1%positive 1%Z) (nl_release 1%positive 1%positive))).
Definition mailbox_take_yes := C.Seq (mailbox_store 2%positive 0%Z)
  (C.Seq (nl_release 2%positive 1%positive) (mailbox_set 0%Z)).
Definition mailbox_take_no := C.Seq (nl_release 2%positive 1%positive) (mailbox_set 1%Z).
Definition mailbox_attempt := C.Seq (nl_acquire 2%positive 1%positive 1)
  (C.Seq (nl_load 2%positive 2%positive 1)
    (C.if_then_else (EVal 2%Z) (nl_is 1 1%Z) mailbox_take_yes mailbox_take_no)).
Definition mailbox_retry := C.Seq (mailbox_set 1%Z)
  (C.while_do (EVal 2%Z) (nl_is 1 1%Z) mailbox_attempt).
Definition mailbox_consumer items := C.Seq mailbox_retry (read_region 2%positive 2 items).
Definition mailbox_program items := C.Parallel (mailbox_producer items) (mailbox_consumer items).
Definition mailbox_read_cases items := A.Or (A.And (mailbox_flag 0%Z) (A.Pure (nl_is 1 0%Z)))
  (A.And (A.Spatial (mailbox_flag 1%Z) (cell_family items)) (A.Pure (nl_is 1 1%Z))).

Lemma mailbox_flag_fv value : A.fv (mailbox_flag value) = [].
Proof. apply nl_cell_fv. Qed.

Lemma mailbox_invariant_fv items : A.fv (mailbox_invariant items) = [].
Proof. cbn [mailbox_invariant A.fv]; rewrite !mailbox_flag_fv,cell_family_fv; reflexivity. Qed.

Lemma mailbox_pool_fv items : A.fv (nl_pool (mailbox_locks items)) = [].
Proof. cbn [mailbox_locks nl_pool A.fv]; rewrite nl_component_fv,mailbox_invariant_fv; reflexivity. Qed.

Lemma mailbox_pool_fragment items : invariant_fragment (nl_pool (mailbox_locks items)).
Proof.
  apply nl_pool_fragment; constructor; [|constructor].
  constructor; [constructor |constructor; [constructor |apply cell_family_fragment]].
Qed.

Lemma mailbox_producer_modifies items : C.modifies (mailbox_producer items) = [0;0].
Proof. cbn [mailbox_producer C.modifies]; rewrite fill_region_modifies; reflexivity. Qed.

Lemma mailbox_producer_fv items x : In x (C.fv (mailbox_producer items)) -> x = 0.
Proof. cbn [mailbox_producer C.fv]; rewrite fill_region_fv; cbn; intuition congruence. Qed.

Lemma mailbox_consumer_modifies items x : In x (C.modifies (mailbox_consumer items)) -> x = 1 \/ x = 2.
Proof.
  cbn [mailbox_consumer C.modifies]; rewrite in_app_iff; intros [H |H].
  - cbn in H; intuition congruence.
  - right; apply read_region_modifies in H; exact H.
Qed.

Lemma mailbox_consumer_fv items x : In x (C.fv (mailbox_consumer items)) -> x = 1 \/ x = 2.
Proof.
  cbn [mailbox_consumer C.fv]; rewrite in_app_iff; intros [H |H].
  - cbn in H; intuition congruence.
  - right; apply read_region_fv in H; exact H.
Qed.
