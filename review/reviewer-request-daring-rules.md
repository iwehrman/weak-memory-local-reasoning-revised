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

## Stage 2: a restricted form that proves fenced Dekker

Ian's goal: a sound restricted form of the daring rules in which fenced
Dekker can be derived, ending in a machine-level mutual-exclusion theorem.

```
T0:  [f0] := 1_0 ; fence_0 ; r0 := [f1]_0
T1:  [f1] := 1_1 ; fence_1 ; r1 := [f0]_1
```

Target theorem: from a heap with `f0 = f1 = 0`, no execution aborts and no
terminating execution ends with `r0 = 0` and `r1 = 0`. A companion result
should show the unfenced program does reach `r0 = r1 = 0`, so the fences
are doing the work.

Everything below is my paper analysis. Treat it as a proposal to test.

### 2a. Why the present model cannot express Dekker

Between T0's store and its fence, the heap cell `f0` still holds 0 and T1
may read it, while T0's write to `f0` sits in T0's buffer. So the shared
cell must be readable by T1 at the same time as T0 owns a pending write to
it. In `owned_environment` the pool is spatially separate from the frame
and the local resource, and address domains include buffered writes, so
this state has no decomposition. No rule can fix that; the safety
predicate has to change. I do not see a way round this. If you do, say so
before building anything.

### 2b. Proposed scope: a separate judgment for lock-free commands

Dekker takes no lock. I suggest a separate judgment, say
`daring_derivation`, for commands that contain no lock and no unlock, with
its own safety predicate. That avoids phases and transfer at lock steps,
and leaves `owned_safe` and `owned_derivation` untouched. Combining the
two judgments (for a spinlock released by a plain store) is a later
question.

Proposed semantic change: the pool is composed *temporally before* the
threads, so a thread or the frame may hold pending writes to pool
addresses.

```
μ0 ∈ μ_J ⊲ (ν_F # ν)      instead of      μ0 ∈ μ_J * (ν_F # ν)
```

The pool stays buffer-free and satisfies `J` at full completeness. The
existing compatibility relation already forbids two processors from both
having pending writes to one address, which gives each shared cell at most
one pending writer at a time.

Consequences to design for:

- **A flush can change the pool.** When a pending write to a pool address
  flushes, the pool's cell changes value with no program step. So `J` must
  be stable under every write that a daring store may issue.
- **The pool can change at ordinary steps**, by re-splitting ownership
  between pool and thread. Dekker needs this for ghost tokens.

### 2c. Candidate rules

1. **Invariant access at one non-store step.** For a primitive `a` of
   processor `i` that is a load, fence, assignment, assume, assert or
   skip:

   ```
   emp ⊨ {J ⊲ P} a {J ⊲ Q}
   ────────────────────────
   J ⊩ {P} a {Q}
   ```

   The premise is validity (or derivability) in the existing calculus
   under the empty invariant. `J ⊲ P` and not `J * P`, because `P` may
   contain pending writes to cells of `J`. For a fence the premise's
   postcondition comes from `(J ⊲ P) ⊲ bar_i` and drained-history
   collapse. This is the dissertation's DARING-LOAD generalised to every
   primitive whose effect on memory is atomic.

2. **Daring store.** If every model of `J` contains address `e`, and `J`
   is stable under setting `e` to `e'`, then

   ```
   J ⊩ {P} [e] := e'_i {P ⊲ e ⇝_i e'}
   ```

   The thread gains the pending write and the pool is untouched. Please
   pick the precise stability condition; the simplest I can state is that
   updating `e` to `e'` in any model of `J` gives a model of `J`.

3. The structural rules: SEQ, CONS, DISJ, CHOICE, LOOP, EX, FRAME-SP and
   CONC, with whatever side conditions the search shows are needed. I do
   not need FRAME-TM for Dekker.

### 2d. Candidate proof of Dekker

Ghost cells, never read or written by the program, as in the
message-passing proof: `w` (the winner's prize), and for each thread `k`
three tokens `t_k`, `q_k`, `p_k`. Initially the pool holds `f0 ↣ 0`,
`f1 ↣ 0`, `w`, `q0`, `q1`; thread `k` holds `t_k` and `p_k`.

```
G_k  =  (q_k * (f_k ↣ 0 ∨ f_k ↣ 1))  ∨  (t_k * f_k ↣ 1)

J    =  (w * G_0 * G_1)
     ∨  (p_0 * t_0 * f0 ↣ 1 * G_1)
     ∨  (p_1 * t_1 * f1 ↣ 1 * G_0)
```

`G_k` says thread `k` has either not yet fenced (the pool has `q_k`), or
has fenced (the pool has `t_k`, and then the flag is 1). The second and
third disjuncts of `J` say thread `k` has taken `w`, having fenced first.
`J` is in the invariant fragment and is stable under `f_k := 1`.

Thread 0, symmetric for thread 1:

| After | Thread 0 holds | Why |
| --- | --- | --- |
| start | `t_0 * p_0` | |
| `[f0] := 1` | `(t_0 * p_0) ⊲ f0 ⇝_0 1` | daring store |
| `fence` | `q_0 * p_0` | Holding `t_0` and `p_0` rules out every case but `G_0` unfenced. The fence drains the write, so `f0 ↣ 1`; swap `t_0` for `q_0`. |
| `r0 := [f1]` | `(r0 = 1 ∧ q_0 * p_0) ∨ (r0 = 0 ∧ q_0 * w)` | Holding `p_0` rules out disjunct 2, and holding `q_0` means the pool has `t_0 * f0 ↣ 1`. In disjunct 3 the flag `f1` is 1. In disjunct 1, if the load reads 0, take `w` and deposit `p_0`, which gives disjunct 2. |

By CONC the final state has `(r0 = 0 ⇒ w) * (r1 = 0 ⇒ w)`, and `w * w`
is false. The token cells are then erased from the conclusion by the same
lifting argument as `message_passing_all_runs`.

### 2e. What I am asking for, in order

1. **Statement file.** The safety predicate, validity, the rules, and the
   adequacy statement. Say where you depart from 2b and 2c and why.
2. **Bounded search** for counterexamples to each rule against that
   predicate, in the style of `scripts/search_owned_*.py`. I am most
   worried about three things:
   - FRAME-SP and CONC when the frame holds a pending write to a pool
     address;
   - the invariant-access rule when the pool changes by a flush between
     the environment being chosen and the step being taken;
   - whether residual uniqueness and flush attribution survive with the
     pool temporally first.
3. **Check in** with the statement and the search results. I will review
   before any general proof.
4. Then, if the candidate stands: soundness, adequacy, the Dekker
   derivation, the machine-level theorem, and the unfenced counterexample.

If the search refutes the candidate and you see a repair, propose it in
the same report. If the pool-first composition turns out to break the
foundations, report that; it is a result worth stating in the paper.

## Report

A file in `review/` with: the Stage 1 theorem names and whether each
holds; the Stage 2 statement, the search bounds and what was found; the
commit; and the `make check` count.
