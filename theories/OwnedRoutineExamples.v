From Stdlib Require Import List ZArith.
From WMLR Require Import Expressions Languages Machine Separation OperationalSemantics ProgramSteps
  ExecutionExamples Assertions AssertionSemantics PersistentAssertions AssertionSubstitution Safety
  TemporalSafety RegionalResources InvariantFragment InvariantFragmentExamples OwnedSafety OwnedAdequacy OwnedResources
  OwnedAcceptance OwnedStructural OwnedPrimitives.
Import ListNotations.

Definition capture_post := A.Exists 1 (A.And (A.Pure (BEq (EVar 0) (EVar 1)))
  (A.Pure (BEq (EVar 1) (EVal 9%Z)))).

(** A capturing replacement would make this assertion true for every stack.
    Correct replacement retains the free occurrence of register 1. *)
Theorem substitution_capture_regression active s r :
  persistent_models active s r (assertion_subst 0 (EVar 1) capture_post) <-> s 1 = 9%Z.
Proof.
  rewrite persistent_assertion_subst.
  change ((exists v, Z.eqb (s 1) v = true /\ Z.eqb v 9%Z = true) <-> s 1 = 9%Z).
  split.
  - intros (v & Hleft & Hright); apply Z.eqb_eq in Hleft, Hright; congruence.
  - intros ->; exists 9%Z; split; apply Z.eqb_refl.
Qed.

Theorem owned_capture_assignment_valid mode :
  owned_valid two_processors mode acceptance_invariant (assertion_subst 0 (EVar 1) capture_post)
    (C.Prim (C.Common (S.Assign 0 (EVar 1))) (EVal 1%Z)) capture_post.
Proof. apply owned_assignment_valid; intros H; contradiction. Qed.

Definition routine_fence := C.Prim (C.Common S.Fence) (EVal 2%Z).
Definition routine_fence_after := flush_write acceptance_initial 2%positive 3%positive 17%Z [].

Theorem owned_pending_fence_valid mode :
  owned_valid two_processors mode acceptance_invariant checkpoint_foreign_write routine_fence
    (A.Temporal checkpoint_foreign_write (A.Barrier (EVal 2%Z))).
Proof. apply owned_fence_general_valid. Qed.

Theorem owned_pending_fence_initial mode s :
  persistent_models two_processors s checkpoint_foreign_pending checkpoint_foreign_write /\
  owned_environment two_processors mode acceptance_invariant s checkpoint_foreign_pending
    (resource_memory two_processors checkpoint_full_cell) (empty_resource_value two_processors)
    acceptance_initial PoolFree.
Proof.
  split.
  - split; [right; reflexivity |left]. split; [intros; reflexivity |].
    split; [intros; reflexivity |intros i H; contradiction].
  - apply owned_empty_frame_intro.
    + exact (proj1 (proj2_sig checkpoint_full_cell)).
    + exact (proj1 checkpoint_cell_pending_spatial).
    + split; [intros i H; exact H |].
      exists checkpoint_full_cell; split; [reflexivity |apply checkpoint_full_cell_models].
Qed.

Theorem owned_pending_fence_trace s :
  execution two_processors 2 routine_fence s acceptance_initial halt s routine_fence_after /\
  buffers acceptance_initial 2%positive = [(3%positive,17%Z)] /\
  buffers routine_fence_after 2%positive = [] /\ shared_heap routine_fence_after 3%positive = Some 17%Z.
Proof.
  split.
  - eapply ExecuteNext; [apply StepFlush; apply FlushWrite with (i := 2%positive); [right; reflexivity |intros H; exact H |reflexivity] |].
    eapply ExecuteNext; [|constructor]; eapply StepPrimitive; [reflexivity |].
    apply PrimitiveFence; [right; reflexivity |reflexivity].
  - repeat split; reflexivity.
Qed.

Theorem owned_pending_fence_waits s :
  forall action next final, ~ program_step two_processors action routine_fence (State s acceptance_initial) next final.
Proof.
  intros action next final Hstep; inversion Hstep; subst.
  match goal with E : eval_expr _ (EVal 2%Z) = Z.pos _ |- _ => cbn in E; inversion E; subst end.
  match goal with H : primitive_step _ _ _ _ _ |- _ => inversion H; subst end; discriminate.
Qed.
