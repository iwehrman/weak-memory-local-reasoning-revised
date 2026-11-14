# Request: settle the status of the daring rules

Ian asked what became of the dissertation's "daring" rules. Today the
repository only says they are unavailable. This request asks for a
definite answer about the basic rules, in two stages. Stage 1 is small and
I expect it to succeed. Stage 2 is exploratory: statement and bounded
search first, and check in before any general proof.

Nothing here should change `owned_safe`, `owned_derivation`, or any
existing theorem. New files only. Do not edit `paper/`.

## The rules

From the dissertation (`dissertation.tex`, lines 2171 to 2178):

```
DARING-LOAD    emp ⊢ {J * P} x := [e]_i {J * Q}
               ─────────────────────────────────
               J ⊢ {P} x := [e]_i {Q}

DARING-STORE   emp ⊢ {J * P} [e] := e'_i {J * Q}
               ─────────────────────────────────
               J ⊢ {P} [e] := e'_i {Q}
```

DARING-STORE-2, which only restores `J` after a barrier, is out of scope.

## Stage 1: the basic rules are unsound in the repaired calculus

I believe both rules, read as rules of `owned_derivation`, are refuted by
a thread that holds the lock. These are paper arguments; I have been wrong
on paper several times in this project, so please check them rather than
trust them.

**N1. Adding DARING-LOAD to the calculus breaks adequacy.** Take
`J = d ↣ 0` and the program

```
lock_1 ; [d] := 5_1 ; x := [d]_1
```

After `lock_1` and the cell store, the thread holds

```
P  =  (lock_1 * (d ↣ 0)) ; bar_1 ; d ⇝_1 5      (up to the derived shape)
```

`J * P` is unsatisfiable, because cells at one address exclude each other.
So the premise `emp ⊢ {J * P} x := [d]_1 {J * (P ∧ x = 0)}` is derivable
from a false precondition (for example, FRAME-SP with frame `false`, then
CONS). DARING-LOAD then gives `J ⊢ {P} x := [d]_1 {P ∧ x = 0}`, and by SEQ
the whole program gets postcondition `x = 0` from precondition `emp`. The
machine reads 5 from the thread's own buffer.

Requested: an extended inductive (the 21 constructors plus DARING-LOAD,
like `original_with_stm` in `OriginalStrongFrame.v`), the derivation, and
a concrete complete execution ending with `x = 5`, giving a theorem of the
form "the extended calculus derives a specification that the adequacy
conclusion contradicts".

**N2. The conclusion is semantically invalid even when the premise is
honest.** Take the premise `emp ⊨ {d ↣ 0} x := [d]_1 {d ↣ 0 ∧ x = 0}`,
which is valid by LOAD-ANY (here `P = emp`, so nothing vacuous). The
conclusion `J ⊨ {emp} x := [d]_1 {x = 0}` should fail under `owned_valid`
in both modes: choose an environment in phase `held(1)` with empty pool
and a frame that holds the token for processor 1 and the history
`d ↣ 0 ; d ⇝_1 5`. The load is enabled, because processor 1 is the
holder, and reads 5.

Requested: this as a theorem about `owned_valid`, for both modes if both
hold.

**N3. The same for DARING-STORE.** I expect N2's environment also refutes
a store instance, or that a simpler obstruction exists: with the lock
free, the store leaves a buffered write to an address in the pool, and the
pool is required to be buffer-free and to satisfy `J` at the next step.
Please find the smallest refutation of the conclusion for an honest
premise, or report that the store instance is valid.

If any of N1 to N3 fails, stop and report why. That would be more
interesting than the expected outcome.

## Stage 2: is there a sound restricted form? Statement and search only

The Stage 1 obstructions all use a thread that holds the lock. The
intended use is the opposite: a thread outside any critical section. So
the natural question is whether DARING-LOAD is sound for a judgment that
only considers environments in which the acting processor does not hold
the lock.

Please propose, as a statement file before proving anything:

1. A candidate validity notion, for example `owned_valid` restricted to
   environments whose phase is not `held(i)` for the command's processor
   `i`, with the smallest change to the update conditions that a daring
   load needs. A load does not change memory, so I would first try
   keeping `pool' = pool`.
2. A candidate rule that is sound for it. If the dissertation's premise
   allows the `J` part to be re-split in the postcondition (ownership of
   cells swapping between pool and thread), say whether that must be
   excluded.
3. Which existing rules survive under the candidate notion, at the level
   of bounded search only: FRAME-SP, FRAME-TM, SEQ, and CONC with a thread
   that takes the lock. I expect the frame rules to need a lock-free
   frame, as restricted SHARE needs lock-free endpoints.

Then run a bounded search in the style of `scripts/search_owned_*.py` for
counterexamples to the candidate, and report the result.

For DARING-STORE, Stage 2 asks only for a classification: is there any
candidate for which the bounded search finds no counterexample, given that
the pool must stay buffer-free? A plain "no candidate found, for this
reason" is a complete answer.

**Check in after the statement and search.** I will review the candidate
before any general proof is attempted. A proof of a restricted
DARING-LOAD, and fenced Dekker as a client, would be a separate request.

## Report

A file in `review/` with: the Stage 1 theorem names and whether each
holds; the Stage 2 statement, the search bounds and what was found; the
commit; and the `make check` count.
