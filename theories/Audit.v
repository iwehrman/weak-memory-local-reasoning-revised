From WMLR Require Import Expressions Languages Assertions AssertionSemantics Specifications Examples.
From WMLR Require Import Machine OperationalSemantics ExecutionExamples.

(** Compiling this file reports the assumptions of the main proved facts. *)
Print Assumptions eval_expr_agrees.
Print Assumptions eval_bexpr_agrees.
Print Assumptions eval_subst_expr.
Print Assumptions eval_subst_bexpr.
Print Assumptions fresh_not_in.
Print Assumptions sequential_mod_in_fv.
Print Assumptions concurrent_mod_in_fv.
Print Assumptions embedding_preserves_modifies.
Print Assumptions embedding_fv.
Print Assumptions ConcurrentAssertion.points_to_fv.
Print Assumptions satisfies_agrees.
Print Assumptions assignment_preserves_invariant.
Print Assumptions assignment_can_break_pure_invariant.
Print Assumptions buffer_lookup_newest.
Print Assumptions enqueue_read_own_write.
Print Assumptions enqueue_other_processor_read.
Print Assumptions lemma2.
Print Assumptions steps_fv_subset.
Print Assumptions steps_modifies_subset.
Print Assumptions steps_preserve_unmodified.
Print Assumptions steps_preserve_well_formed.
Print Assumptions steps_preserve_lock_complete.
Print Assumptions store_buffering_zero_zero.
Print Assumptions store_fence_trace.
Print Assumptions lock_store_unlock_trace.
Print Assumptions blocked_load_waits_even_for_own_buffer.
Print Assumptions blocked_buffer_cannot_flush.
