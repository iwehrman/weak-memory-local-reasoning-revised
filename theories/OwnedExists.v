From Stdlib Require Import List.
From WMLR Require Import Expressions Languages OperationalSemantics Assertions AssertionSemantics
  PersistentAssertions OwnedSafety OwnedInterference.
Import ListNotations.

(** EX keeps the command, postcondition and shared invariant independent
    of the witness. No restriction is imposed on occurrences in the precondition. *)
Theorem owned_exists_valid active mode invariant pre command post x :
  ~ In x (A.fv invariant) -> ~ In x (C.fv command) -> ~ In x (A.fv post) ->
  owned_valid active mode invariant pre command post ->
  owned_valid active mode invariant (A.Exists x pre) command post.
Proof.
  intros HJ HC HQ Hvalid s local [v HP] n.
  eapply owned_safe_stack_agrees with (s := update s x v)
    (variables := A.fv invariant ++ C.fv command ++ A.fv post).
  - intros y Hy; apply in_or_app; auto.
  - intros y Hy; apply in_or_app; right; apply in_or_app; auto.
  - intros y Hy; apply in_or_app; right; apply in_or_app; auto.
  - intros y Hy; apply update_other. intros E; subst y.
    repeat rewrite in_app_iff in Hy; tauto.
  - apply Hvalid, HP.
Qed.
