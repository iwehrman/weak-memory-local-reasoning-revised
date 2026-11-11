From WMLR Require Import Expressions Languages Assertions AssertionSemantics Specifications Examples.

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
