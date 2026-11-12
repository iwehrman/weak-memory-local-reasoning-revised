From Stdlib Require Import List ZArith.
From WMLR Require Import Expressions Machine BufferRelations Separation RepairedSeparation
  Assertions AssertionSemantics ConcreteAssertions RepairedAssertions PersistentAssertions
  PersistentRules RegionalResources AssertionResourceEquivalence.
Import ListNotations.

(** Audit E1/E2: arbitrary formulas, including all three wands, on every
    processor domain. No wand-free, finite-domain or lock-state premise. *)
Theorem assertion_unit_spatial_right active p s (r : resource active) :
  persistent_models active s r (A.Spatial p A.Emp) <-> persistent_models active s r p.
Proof.
  split.
  - intros (a & b & [[_ [Hheap [Hbuffers Hblocks]]] Hmarks] & HP & [Hh [Hb Hk]]).
    eapply persistent_models_mark_extension; [| |exact HP].
    + split.
      * intros loc; symmetry; rewrite Hheap; unfold heap_override; rewrite Hh; reflexivity.
      * split.
        -- intros i; specialize (Hbuffers i); rewrite Hb in Hbuffers.
           symmetry; apply interleaves_nil_right,Hbuffers.
        -- intros i; rewrite Hblocks; split; [auto |intros [H |H]; [exact H |exfalso; exact (Hk i H)]].
    + intros i H; apply Hmarks; auto.
  - intros HP; exists r,(bare_resource active); split; [apply spatial_empty_right |].
    split; [exact HP |apply bare_resource_models].
Qed.

Theorem assertion_unit_spatial_left active p s (r : resource active) :
  persistent_models active s r (A.Spatial A.Emp p) <-> persistent_models active s r p.
Proof.
  split.
  - intros (a & b & Hsp & HE & HP); apply (proj1 (assertion_unit_spatial_right active p s r)).
    exists b,a; split; [apply spatial_comm,Hsp |auto].
  - intros HP; exists (bare_resource active),r; split; [apply spatial_empty_left |].
    split; [apply bare_resource_models |exact HP].
Qed.

Theorem assertion_unit_temporal_right active p s (r : resource active) :
  persistent_models active s r (A.Temporal p A.Emp) <-> persistent_models active s r p.
Proof.
  split.
  - intros (a & b & [_ [[_ [Hheap [Hbuffers Hblocks]]] [Hbefore Hmarks]]] & HP & [Hh [Hb Hk]]).
    eapply persistent_models_mark_extension; [| |exact HP].
    + split.
      * intros loc; symmetry; rewrite Hheap; unfold heap_override; rewrite Hh; reflexivity.
      * split.
        -- intros i; rewrite Hbuffers,Hb,app_nil_r; reflexivity.
        -- intros i; rewrite Hblocks; split; [auto |intros [H |H]; [exact H |exfalso; exact (Hk i H)]].
    + intros i H; apply Hmarks; auto.
  - intros HP; exists r,(bare_resource active); split; [apply repaired_temporal_bare_right |].
    split; [exact HP |apply bare_resource_models].
Qed.

Theorem assertion_unit_temporal_left active p s (r : resource active) :
  persistent_models active s r (A.Temporal A.Emp p) <-> persistent_models active s r p.
Proof.
  split.
  - intros (a & b & [_ [[_ [Hheap [Hbuffers Hblocks]]] [Hbefore Hmarks]]] & [Hh [Hb Hk]] & HP).
    eapply persistent_models_mark_extension; [| |exact HP].
    + split.
      * intros loc; symmetry; rewrite Hheap; unfold heap_override; rewrite Hh.
        destruct (shared_heap (underlying (proj1_sig b)) loc); reflexivity.
      * split.
        -- intros i; rewrite Hbuffers,Hb; reflexivity.
        -- intros i; rewrite Hblocks; split; [auto |intros [H |H]; [exfalso; exact (Hk i H) |exact H]].
    + intros i H; apply Hmarks; auto.
  - intros HP; exists (bare_resource active),r; split; [apply repaired_temporal_bare_left |].
    split; [apply bare_resource_models |exact HP].
Qed.

Theorem assertion_unit_strong_right active p s (r : resource active) :
  persistent_models active s r (A.strong_temporal p A.Emp) <-> persistent_models active s r p.
Proof.
  split; [intros [Hsp Htm]; apply (proj1 (assertion_unit_spatial_right _ _ _ _)),Hsp |].
  intros HP; split; [apply (proj2 (assertion_unit_spatial_right _ _ _ _))
    |apply (proj2 (assertion_unit_temporal_right _ _ _ _))]; exact HP.
Qed.

Theorem assertion_unit_strong_left active p s (r : resource active) :
  persistent_models active s r (A.strong_temporal A.Emp p) <-> persistent_models active s r p.
Proof.
  split; [intros [Hsp Htm]; apply (proj1 (assertion_unit_spatial_left _ _ _ _)),Hsp |].
  intros HP; split; [apply (proj2 (assertion_unit_spatial_left _ _ _ _))
    |apply (proj2 (assertion_unit_temporal_left _ _ _ _))]; exact HP.
Qed.
