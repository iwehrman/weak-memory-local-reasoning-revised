From WMLR Require Import Separation RepairedSeparation GeneralizedFlushing.

(** Checkpoint-3 baseline after the bounded temporal-only search. This is a
    resource lemma with a single owned suffix, not a new validity predicate
    or a soundness theorem for ownership transfer. *)
Theorem temporal_frame_shape active (frame retained grouped grouped_after local_after whole_after : resource active) :
  repaired_temporal active (proj1_sig frame) (proj1_sig retained) (proj1_sig grouped) ->
  resource_future active grouped grouped_after ->
  repaired_temporal active (proj1_sig grouped_after) (proj1_sig local_after) (proj1_sig whole_after) ->
  exists frame_after retained_after framed_local : resource active,
    resource_future active frame frame_after /\ resource_future active retained retained_after /\
    repaired_temporal active (proj1_sig frame_after) (proj1_sig retained_after) (proj1_sig grouped_after) /\
    repaired_temporal active (proj1_sig retained_after) (proj1_sig local_after) (proj1_sig framed_local) /\
    repaired_temporal active (proj1_sig frame_after) (proj1_sig framed_local) (proj1_sig whole_after).
Proof.
  intros Hgroup Hfuture Hafter.
  destruct (resource_temporal_future_split _ _ _ _ _ Hfuture Hgroup)
    as (frame_after & retained_after & HF & HR & Hsplit).
  destruct (proj2 (repaired_temporal_resource_associative active frame_after retained_after local_after whole_after)
    (ex_intro _ grouped_after (conj Hsplit Hafter))) as (framed_local & Hinner & Houter).
  exists frame_after, retained_after, framed_local; split; [exact HF |].
  split; [exact HR |]. split; [exact Hsplit |]. split; assumption.
Qed.
