From Stdlib Require Import ZArith.
From WMLR Require Import Machine Separation RepairedSeparation ExecutionExamples
  TemporalSafety ResidualUniqueness FrameShapeCounterexample.

(** Keeping the regrouped frame fixed excludes the precise bad residuals
    from checkpoint 3. These are checks of the new buffer theorem, not
    assertions of soundness for a new safety definition. *)
Theorem fixed_frame_excludes_assume_counterexample :
  ~ repaired_spatiotemporal two_processors
    (proj1_sig FrameShapeCounterexample.grouped)
    (proj1_sig FrameShapeCounterexample.local_after)
    (proj1_sig FrameShapeCounterexample.whole).
Proof.
  intros H; pose proof (resource_residual_buffers_unique _ _ _ _ _ _
    FrameShapeCounterexample.initial_small H eq_refl 1%positive) as E.
  discriminate E.
Qed.

Theorem fixed_frame_excludes_acquire_counterexample :
  ~ repaired_spatiotemporal two_processors
    (proj1_sig FrameShapeCounterexample.grouped)
    (proj1_sig FrameShapeCounterexample.acquire_local_after)
    (proj1_sig FrameShapeCounterexample.acquire_whole_after).
Proof.
  intros H; pose proof (repaired_residual_buffers_unique _ _ _ _ _ _
    (proj1 FrameShapeCounterexample.initial_small) (proj1 H) (fun i => eq_refl) 1%positive) as E.
  discriminate E.
Qed.
