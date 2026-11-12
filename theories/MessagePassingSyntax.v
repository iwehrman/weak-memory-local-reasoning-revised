From Stdlib Require Import List ZArith.
From WMLR Require Import Expressions Languages Machine OperationalSemantics Assertions AssertionSemantics
  InvariantFragment AssertionCellSubstitution.
Import ListNotations.

(** Section 4.1's program, with result register 0 and address register 1.
    The token addresses parameterize assertions only, never the commands. *)
Definition mp_address := EVar 1.
Definition mp_data v := writer_points_to mp_address (EVal v).
Definition mp_token loc := writer_points_to (EVal (Z.pos loc)) (EVal 0%Z).
Definition mp_invariant t r := A.Or (mp_data 0%Z)
  (A.Or (A.Spatial (mp_data 1%Z) (mp_token t)) (A.Spatial (mp_token t) (mp_token r))).
Definition mp_guard v := BEq (EVar 0) (EVal v).
Definition mp_lock owner := A.Lock (EVal (Z.pos owner)).
Definition mp_held owner p := A.Spatial (mp_lock owner) p.
Definition mp_store owner v := C.Prim (C.Common (S.Store mp_address (EVal v))) (EVal (Z.pos owner)).
Definition mp_acquire owner := C.Prim C.Lock (EVal (Z.pos owner)).
Definition mp_release owner := C.Prim C.Unlock (EVal (Z.pos owner)).
Definition mp_load := C.Prim (C.Common (S.Load 0 mp_address)) (EVal 2%Z).
Definition mp_fence := C.Prim (C.Common S.Fence) (EVal 2%Z).
Definition mp_sender := C.Seq (mp_acquire 1%positive)
  (C.Seq (mp_store 1%positive 1%Z) (mp_release 1%positive)).
Definition mp_private := C.Seq (mp_store 2%positive 2%Z) mp_fence.
Definition mp_tail := C.if_then_else (EVal 2%Z) (mp_guard 1%Z) mp_private (C.skip (EVal 2%Z)).
Definition mp_receiver := C.Seq (mp_acquire 2%positive)
  (C.Seq mp_load (C.Seq (mp_release 2%positive) mp_tail)).
Definition mp_program := C.Parallel mp_sender mp_receiver.
Definition mp_received r v := A.Or (A.And (mp_token r) (A.Pure (mp_guard 0%Z)))
  (A.And (mp_data v) (A.Pure (mp_guard 1%Z))).
Definition mp_load_cases t r := A.Or (mp_held 2%positive (A.Spatial (mp_data 0%Z) (mp_token r)))
  (mp_held 2%positive (A.Spatial (mp_data 1%Z) (A.Spatial (mp_token t) (mp_token r)))).
Definition mp_read_cases t r := A.Or
  (A.And (mp_held 2%positive (A.Spatial (mp_data 0%Z) (mp_token r))) (A.Pure (mp_guard 0%Z)))
  (A.And (mp_held 2%positive (A.Spatial (mp_data 1%Z) (A.Spatial (mp_token t) (mp_token r))))
    (A.Pure (mp_guard 1%Z))).

Lemma mp_invariant_fragment t r : invariant_fragment (mp_invariant t r).
Proof. repeat constructor. Qed.

Lemma mp_token_fv loc : A.fv (mp_token loc) = [].
Proof. apply assertion_writer_cell_fv. Qed.

Lemma mp_data_fv value : A.fv (mp_data value) = [1].
Proof. apply assertion_writer_cell_fv. Qed.

Lemma mp_invariant_fv t r : A.fv (mp_invariant t r) = [1;1].
Proof. cbn [mp_invariant A.fv]; rewrite !mp_data_fv,!mp_token_fv; reflexivity. Qed.

Lemma mp_sender_modifies : C.modifies mp_sender = [].
Proof. reflexivity. Qed.

Lemma mp_receiver_modifies : C.modifies mp_receiver = [0].
Proof. reflexivity. Qed.
