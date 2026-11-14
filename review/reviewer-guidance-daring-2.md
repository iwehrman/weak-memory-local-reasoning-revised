# Reviewer guidance after the daring-rules checkpoint

Responds to `review/lead-daring-rules.md` and
`review/daring-lock-free-candidate.md` at `94776a4`.

## Verified

A clean clone of `94776a4` passes `make check` (1,316 closed
declarations) and `make -f Makefile.daring check` (25 more, no axioms). I
read the statements of the three packaged Stage 1 theorems and they say
what the report says.

## Stage 1: accepted

N1, N2 and N3 stand. The basic daring rules are refuted for the repaired
calculus, in both modes, and N3 is better than I asked for: the store
fails with the lock free, by an ownership swap, with no vacuous premise.

**Please fold the Stage 1 files into the main build now**:
`DaringExtension.v` and `DaringCounterexamples.v` into `_CoqProject`, and
their audited declarations into `Audit.v`. The paper will cite
`daring_load_extension_breaks_adequacy`,
`daring_load_honest_counterexample` and
`daring_store_honest_counterexample`. Leave `DaringCandidate.v` out of the
main build; it states a design we are abandoning. Report the new commit
and count and I will update the paper.

## Stage 2: the pool-first candidate is withdrawn

Your search is decisive and I agree with every failure. Two of them are
errors in my design, not gaps to patch:

- Composing the pool temporally before the threads gives up spatial
  exclusivity for everything, ghost cells included. My token argument
  assumed exclusivity that the composition I proposed had just removed.
- Stability of one issued store says nothing about the writes an
  arbitrary frame may hold. I wrote that compatibility gave a
  single-writer discipline. It does not.

I do not want to repair this by adding address classes and a rely
condition on frames, as your suggestions 1 to 3 would. I think there is a
simpler design that needs neither.

## Stage 2, second candidate: let the invariant own the pending write

**Idea.** Keep the pool spatially separate from the frame and the local
resource, exactly as in `owned_environment`. Drop the requirement that the
pool is buffer-free. A daring store puts its write *into the pool*, and
the invariant describes it. This is the dissertation's own reading of
DARING-STORE ("requires the invariant J to encompass the newly added
buffered write"), which it set aside as inconvenient, not as unsound.

Why this should dissolve each failure you found:

| Failure at `94776a4` | Under this candidate |
| --- | --- |
| Frame holds a pending write to a pool address | Impossible: the pool is spatially separate, buffers included. |
| Token exclusion fails | Restored: ghost cells are spatially exclusive again. |
| Copying a shared cell out with `J ; J` | The premise is `J * P`, so nothing can be copied. |
| A second writer to the same flag | The premise must return `J`, and `J` names the writer of each pending write. No separate permission system. |
| A flush breaks `J` | Assertions are closed under futures (`persistent_assertion_flushing_closed`). A flush of a pool write is a future of the pool, so `J` survives with no stability premise. |
| N2, the thread holds the lock | The judgment is for lock-free commands and every environment is lock-free, as in your candidate. |
| N3, an ordinary step keeps the pool fixed | Daring steps may change the pool. That is the point of the rule. |

### What changes relative to `owned_safe`

1. **Lock-free only**, as in your candidate: no phases, whole memory
   unblocked.
2. **The pool may hold buffered writes** and satisfies `J`. `J` comes from
   a fragment extended with write histories on cells; see the risk on
   marks below.
3. **Three-way flush attribution**: a machine flush belongs to the pool,
   the frame or the local resource. A pool flush takes the pool to a
   future of itself.
4. **A daring step may re-split pool and local.** Footprint and mark
   budget stay as they are.

### The rule

For a single primitive `a` of processor `i` that is a store, load, fence,
assignment, assume or assert (not skip, as you say):

```
⟨J * P⟩ a ⟨J * Q⟩
──────────────────
J ⊩ {P} a {Q}
```

I suggest the premise be a direct one-step semantic triple, not
`owned_valid` under `emp`: for every pool satisfying `J` and local
resource satisfying `P` that compose spatially, the step from their
composition does not abort, and every result splits into a pool
satisfying `J` and a local resource satisfying `Q`, with the footprint
bound and with the local part's marks inside the local marks plus what
the step earns. Sufficient conditions in terms of the existing calculus
can come later. For Dekker each premise is a small finite fact.

Plus ordinary SKIP, SEQ, CONS, DISJ, CHOICE, LOOP, EX, FRAME-SP, CONC, and
the ordinary private axioms for cells the thread owns outright.

### Risks, in the order I would search them

1. **Marks when the pool is lent to a thread.** This is the one I am least
   sure of. Today the pool is read at full completeness and the
   buffer-free fragment makes that harmless (`invariant_fragment_remark`).
   With write histories in `J`: at what marks is the pool read, is
   satisfaction of the extended fragment still independent of the marks,
   and can a thread leave a daring step with a mark it did not earn? The
   budget in the premise is meant to stop the last one. Please try to
   break it.
2. **A fence by `i` over a pool that holds `i`'s write.** The premise
   reasons with `(J * P) ; bar_i`. That is justified only because the
   machine requires all of buffer `i` to be empty at the step. Check the
   real step against the premise when the pool's write by `i` has and has
   not flushed.
3. **Reading a cell with another processor's pending write.** Dekker needs
   processor `i` to load from `e ↣ u ; e ⇝_j v` with `i ≠ j` and get `u`
   or `v`. No current axiom covers this. With a direct semantic premise it
   is just a fact to prove; confirm the load is safe and returns one of
   the two.
4. **FRAME-SP and CONC reconstruction** when the other component's step
   changed the pool.
5. **Residual uniqueness and flush attribution** with a pool that has
   buffers. The pool is spatially disjoint from the rest, so I expect the
   existing lemmas to lift, but your counts will say.

### Candidate proof of Dekker

Ghost cells per thread `k`: `a_k`, `b_k` (has it stored), `q_k`, `t_k`
(has it fenced), `p_k` (has it won); and one prize `w`.

```
G_k  =  (b_k * q_k * f_k ↣ 0)                        not yet stored
     ∨  (a_k * q_k * (f_k ↣ 0 ; f_k ⇝_k 1))          stored, maybe pending
     ∨  (a_k * t_k * f_k ↣ 1)                        fenced

F_k  =  a_k * t_k * f_k ↣ 1

J    =  (w * G_0 * G_1)  ∨  (p_0 * F_0 * G_1)  ∨  (p_1 * F_1 * G_0)
```

Initially the pool holds `w`, `b_k`, `q_k`, `f_k ↣ 0`; thread `k` holds
`a_k * t_k * p_k`.

| Step of thread 0 | Before | After | Why |
| --- | --- | --- | --- |
| `[f0] := 1` | `a_0 * t_0 * p_0` | `b_0 * t_0 * p_0` | Holding `a_0` forces `G_0` unstored. Store into the pool's cell, swap `a_0` for `b_0`. |
| `fence` | `b_0 * t_0 * p_0` | `b_0 * q_0 * p_0` | Holding `b_0` and `t_0` forces `G_0` stored. The fence drains processor 0, so the history collapses to `f0 ↣ 1`. Swap `t_0` for `q_0`. |
| `r0 := [f1]` | `b_0 * q_0 * p_0` | `(r0 = 1 ∧ b_0 * q_0 * p_0) ∨ (r0 = 0 ∧ b_0 * q_0 * w)` | Holding `p_0` excludes disjunct 2. In disjunct 3, `f1 ↣ 1`, so the load reads 1. In disjunct 1, if it reads 0, take `w` and deposit `p_0`; holding `q_0` shows `G_0` is `F_0`, so the pool is disjunct 2. |

Thread 1 is symmetric. The final state gives
`(r0 = 0 ⇒ w) * (r1 = 0 ⇒ w)`, and `w * w` is false. If one thread has
taken `w`, the other finds the pool in the winner's disjunct, where the
winner's flag is 1.

The second form of `G_k` is where the race lives: thread 1 may read `f0`
while thread 0's write is pending in the pool, and gets 0 or 1.

Please enumerate this before trusting it. I had the previous token
argument wrong.

## What I am asking for

1. Fold Stage 1 into the build (above).
2. A statement file for the second candidate. Depart from the above
   wherever it is wrong, and say where.
3. A bounded search covering the five risks, and an enumeration of the
   Dekker invariant: for each of the six thread steps, check the one-step
   premise over all models of `J * P`.
4. Check in. No general proof yet.

If you think the address-class design in your suggestions is better than
this one, argue it in the report. I prefer this one because it adds no
new composition and no rely condition, but I have been wrong twice on
this topic already.
