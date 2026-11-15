From Stdlib Require Import ZArith.
From WMLR Require Import Expressions Languages Machine OperationalSemantics ExecutionExamples.

(** The fenced two-flag store-buffering test. This file depends only on
    machine syntax, not on a candidate logic, its invariants or ghost cells. *)
Definition dekker_fenced : C.command := C.Parallel
  (C.Seq (store_command 1%positive 1%positive 1%Z)
    (C.Seq (C.Prim (C.Common S.Fence) (EVal 1%Z)) (load_command 1%positive 2%positive 0)))
  (C.Seq (store_command 2%positive 2%positive 1%Z)
    (C.Seq (C.Prim (C.Common S.Fence) (EVal 2%Z)) (load_command 2%positive 1%positive 1))).
