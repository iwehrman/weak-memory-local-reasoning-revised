# Theorems behind claims the report does not name

The report cites only its principal definitions and theorems. This file
gives the Rocq name behind each remaining claim, by section. All names are
at commit `521acd6`, and the theorems appear in `theories/Audit.v`.

## What was wrong

| Claim | Theorem |
| --- | --- |
| `assign` fails for an invariant mentioning the variable | `original_assignment_invalid` |
| Buffer overriding is not associative | `original_buffer_override_not_associative` |
| Spatiotemporal separation is not associative | `original_spatiotemporal_not_associative` |
| Assertions are not closed under flushing | `original_flushing_closure_false` |
| Conjecture 1 is false | `original_conjecture1_false` |
| `unlock` fails for an arbitrary invariant | `original_arbitrary_invariant_unlock_invalid` |
| `inv` alone takes a true specification to a false one | `original_inv_alone_counterexample` |

## What changed, the model, the calculus

| Claim | Theorem |
| --- | --- |
| On one processor the calculus derives a false specification | `owned_soundness_without_two_processors_refuted` |
| A frame that steps freely breaks the frame lemma | `overlap_frame_shape_counterexample` |
| Each flush belongs to the frame or the local resource | `pooled_resource_flush_attribution` |
| The local residual's buffers are unique | `ordered_residual_unique` |
| A fragment invariant is buffer-free and mark-insensitive | `invariant_fragment_remark` |
| `frame-tm` is derived for commands without `unlock` | `owned_derive_temporal_frame_unlock_free` |
| Overlap-mode derivability coincides with having no `unlock` | `owned_overlap_derivable_iff_unlock_free` |
| `frame-tm` over a release can be invalid | `owned_disjoint_temporal_frame_counterexample` |
| Without the fragment, `lock` derives a false specification | `owned_soundness_without_fragment_refuted` |
| Repaired buffer overriding (a definition) | `ordered_overrides` |
| Repaired temporal compatibility (a definition) | `stable_compatible` |

## Soundness and adequacy

| Claim | Theorem |
| --- | --- |
| An `unlock`-free derivation replays in overlap mode | `owned_derivation_unlock_free_overlap` |
| The original `share` is unsound beside the transferring `lock` | `owned_original_share_lock_counterexample` |
| `share` is sound for lock-free pre- and postconditions | `owned_share_valid`, `owned_share_overlap_valid` |
| From `emp` to `emp`, completed executions restore the pool | `owned_emp_derivation_restores` |

## How proofs proceed

| Claim | Theorem |
| --- | --- |
| Store then fence on a cell | `owned_derive_store_fence_cell` |
| The same without the fence is invalid | `owned_plain_store_cell_invalid` |
| Loading one's own buffered write | `owned_derive_load_after_history` |
| The container | `owned_container_derived` |
| Its 24-step execution with a foreign write pending | `owned_container_trace`, `owned_container_foreign_pending_throughout` |
| Completed container executions restore the invariant | `owned_container_completed_restores` |
| The retrying container | `owned_retrying_container_derived` |
| Message passing: the three specifications | `mp_sender_derived`, `mp_receiver_derived`, `mp_parallel_derived` |
| Message passing ends with `d ↦ x + 1` | `message_passing_points_to` |
| Named-lock rules | `named_lock_acquire_family`, `named_lock_release_family` |
| The mailbox: the three specifications | `mailbox_producer_derived`, `mailbox_consumer_derived`, `mailbox_parallel_derived` |

## Unlocked access

| Claim | Theorem |
| --- | --- |
| Each daring rule has a valid premise with an invalid conclusion | `daring_load_honest_counterexample`, `daring_store_honest_counterexample` |
| A load or store gives no cell to a thread without a mark | `buffered_unmarked_ordinary_no_heap` |
| A thread starting from `emp` may have no mark | `buffered_emp_load_withdrawal_premise_invalid` |
| Two threads can each start with their own barrier | `buffered_barrier_parallel_initial_adequacy` |
| The six atomic premises of the Dekker proof | `buffered_dekker_store0_premise` and its companions |

## What remains open

| Claim | Theorem |
| --- | --- |
| The frame property for a single spatial and temporal split | `owned_safe_common_frame` |
