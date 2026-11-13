From Stdlib Require Import List ZArith.
From WMLR Require Import Expressions Machine BufferRelations Separation OrderedBuffers OrderedSeparation.
Import ListNotations.

(** A second candidate repair: compatibility must survive regrouping even
    when another component contributes blocked processors. Omitting the
    blocking exception is conservative and makes this property provable. *)
Definition stable_compatible (active : processor_domain) a b : Prop :=
  disjoint (blocked a) (blocked b) /\
  (forall i, active i ->
    disjoint (buffer_domain (buffers a i)) (heap_domain (shared_heap b))) /\
  (forall i j, active i -> active j -> i <> j ->
    disjoint (buffer_domain (buffers a i)) (buffer_domain (buffers b j))).

Theorem stable_implies_original_compatible active a b :
  stable_compatible active a b -> temporal_compatible active a b.
Proof.
  intros [Hk [Hh Hb]]. split; [exact Hk |]. split.
  - intros i [Hi _]; apply Hh, Hi.
  - intros i j [Hi _] [Hj _] Hneq; apply Hb; assumption.
Qed.

Definition temporal_join a b := Memory
  (heap_override (shared_heap a) (shared_heap b))
  (fun i => buffers a i ++ buffers b i)
  (fun i => blocked a i \/ blocked b i).

Lemma buffer_app_domain a b loc :
  buffer_domain (a ++ b) loc <-> buffer_domain a loc \/ buffer_domain b loc.
Proof. unfold buffer_domain. setoid_rewrite in_app_iff. firstorder. Qed.

Lemma heap_override_domain a b loc :
  heap_domain (heap_override a b) loc <-> heap_domain a loc \/ heap_domain b loc.
Proof.
  unfold heap_domain, heap_override. destruct (b loc) eqn:Hb; split.
  - intros; right; eauto.
  - intros; eauto.
  - intros; left; assumption.
  - intros [H | [v H]]; [exact H | discriminate].
Qed.

(** Associativity of the definedness conditions of a partial operation, not
    just associativity of its total underlying tuple constructor. *)
Theorem stable_compatibility_associative active a b c :
  (stable_compatible active a (temporal_join b c) /\ stable_compatible active b c) <->
  (stable_compatible active a b /\ stable_compatible active (temporal_join a b) c).
Proof.
  split; intros [[Hk1 [Hh1 Hb1]] [Hk2 [Hh2 Hb2]]].
  - split.
    + split.
      * intros i Ha Hb. apply (Hk1 i Ha). left; exact Hb.
      * split.
        -- intros i Hi loc Ha Hb. apply (Hh1 i Hi loc Ha), heap_override_domain.
           left; exact Hb.
        -- intros i j Hi Hj Hneq loc Ha Hb.
           apply (Hb1 i j Hi Hj Hneq loc Ha), buffer_app_domain. left; exact Hb.
    + split.
      * intros i [Ha | Hb] Hc.
        -- apply (Hk1 i Ha). right; exact Hc.
        -- exact (Hk2 i Hb Hc).
      * split.
        -- intros i Hi loc Hab Hc. apply buffer_app_domain in Hab.
           destruct Hab as [Ha | Hb].
           ++ apply (Hh1 i Hi loc Ha), heap_override_domain. right; exact Hc.
           ++ exact (Hh2 i Hi loc Hb Hc).
        -- intros i j Hi Hj Hneq loc Hab Hc. apply buffer_app_domain in Hab.
           destruct Hab as [Ha | Hb].
           ++ apply (Hb1 i j Hi Hj Hneq loc Ha), buffer_app_domain. right; exact Hc.
           ++ exact (Hb2 i j Hi Hj Hneq loc Hb Hc).
  - split.
    + split.
      * intros i Ha [Hb | Hc].
        -- exact (Hk1 i Ha Hb).
        -- apply (Hk2 i); [left; exact Ha | exact Hc].
      * split.
        -- intros i Hi loc Ha Hbc. apply heap_override_domain in Hbc.
           destruct Hbc as [Hb | Hc].
           ++ exact (Hh1 i Hi loc Ha Hb).
           ++ apply (Hh2 i Hi loc); [apply buffer_app_domain; left; exact Ha | exact Hc].
        -- intros i j Hi Hj Hneq loc Ha Hbc. apply buffer_app_domain in Hbc.
           destruct Hbc as [Hb | Hc].
           ++ exact (Hb1 i j Hi Hj Hneq loc Ha Hb).
           ++ apply (Hb2 i j Hi Hj Hneq loc);
                [apply buffer_app_domain; left; exact Ha | exact Hc].
    + split.
      * intros i Hb Hc. apply (Hk2 i); [right; exact Hb | exact Hc].
      * split.
        -- intros i Hi loc Hb Hc. apply (Hh2 i Hi loc);
             [apply buffer_app_domain; right; exact Hb | exact Hc].
        -- intros i j Hi Hj Hneq loc Hb Hc. apply (Hb2 i j Hi Hj Hneq loc);
             [apply buffer_app_domain; right; exact Hb | exact Hc].
Qed.

Theorem temporal_join_associative a b c :
  memory_equiv (temporal_join a (temporal_join b c)) (temporal_join (temporal_join a b) c).
Proof.
  split.
  - intros loc. cbn [temporal_join shared_heap]. unfold heap_override.
    destruct (shared_heap c loc); [reflexivity |].
    destruct (shared_heap b loc); reflexivity.
  - split.
    + intros i; cbn [temporal_join buffers]. apply app_assoc.
    + intros i; cbn [temporal_join blocked]; tauto.
Qed.

(** The original compatibility relation can be made true by placing a
    blocking fact in a later group. Thus ordered lists alone do not fix
    associativity of complete memory systems. *)
Definition every_processor : processor_domain := fun _ => True.
Definition masked_past := Memory empty_heap
  (buffer_update empty_buffers 1%positive [(1%positive, 1%Z)]) no_blocked.
Definition masked_future := Memory (heap_update empty_heap 1%positive 2%Z)
  empty_buffers no_blocked.
Definition later_blocker := Memory empty_heap empty_buffers (fun i => i = 1%positive).

Lemma masked_future_blocker_ordered :
  memory_ordered every_processor masked_future later_blocker (temporal_join masked_future later_blocker).
Proof.
  split.
  - split; [intros i H; contradiction |]. split.
    + intros i _ loc [v H] _; contradiction.
    + intros i j _ _ _ loc [v H] _; contradiction.
  - split; [intros; reflexivity |]. split; [intros i; apply ordered_append | intros i; reflexivity].
Qed.

Lemma masked_group_ordered :
  memory_ordered every_processor masked_past (temporal_join masked_future later_blocker)
    (temporal_join masked_past (temporal_join masked_future later_blocker)).
Proof.
  split.
  - split; [intros i H; contradiction |]. split.
    + intros i [_ [_ Hblocked]] loc [v Hv] _.
      cbn [masked_past buffers] in Hv. unfold buffer_update in Hv.
      destruct (Pos.eq_dec i 1%positive) as [Heq | Hneq]; [|contradiction].
      apply Hblocked. right; exact Heq.
    + intros i j _ _ _ loc _ [v Hv]. contradiction.
  - split; [intros; reflexivity |]. split; [intros i; apply ordered_append | intros i; reflexivity].
Qed.

Lemma masked_pair_incompatible : ~ temporal_compatible every_processor masked_past masked_future.
Proof.
  intros [_ [Hheap _]].
  assert (Hjoint : jointly_unblocked every_processor masked_past masked_future 1%positive).
  { split; [exact I |]. split; intros H; contradiction. }
  apply (Hheap 1%positive Hjoint 1%positive).
  - exists 1%Z. cbn [masked_past buffers]. rewrite buffer_update_same; left; reflexivity.
  - exists 2%Z. apply heap_update_same.
Qed.

Theorem original_memory_compatibility_not_associative :
  (exists bc, memory_ordered every_processor masked_future later_blocker bc /\
    memory_ordered every_processor masked_past bc
      (temporal_join masked_past (temporal_join masked_future later_blocker))) /\
  ~ (exists ab, memory_ordered every_processor masked_past masked_future ab /\
    memory_ordered every_processor ab later_blocker
      (temporal_join masked_past (temporal_join masked_future later_blocker))).
Proof.
  split.
  - exists (temporal_join masked_future later_blocker).
    split; [apply masked_future_blocker_ordered | apply masked_group_ordered].
  - intros [ab [[Hcompat _] _]]. apply masked_pair_incompatible, Hcompat.
Qed.

Corollary original_spatiotemporal_not_associative :
  (exists bc, memory_spatiotemporal every_processor masked_future later_blocker bc /\
    memory_spatiotemporal every_processor masked_past bc
      (temporal_join masked_past (temporal_join masked_future later_blocker))) /\
  ~ (exists ab, memory_spatiotemporal every_processor masked_past masked_future ab /\
    memory_spatiotemporal every_processor ab later_blocker
      (temporal_join masked_past (temporal_join masked_future later_blocker))).
Proof.
  split.
  - exists (temporal_join masked_future later_blocker). split;
      apply ordered_in_original;
      [apply masked_future_blocker_ordered | apply masked_group_ordered].
  - intros [ab [[Hcompat _] _]]. apply masked_pair_incompatible, Hcompat.
Qed.
