# Deferred design notes: the Section 4.1 example

These notes respond to [the paper work queue](work-queue-for-paper.md).
**Deferred under the revised order at `f4899e0`: the assertion algebra audit,
entailment rule system, and container reconstruction come first.** The
current audit target is recorded in
[paper-algebra-audit-statement.md](paper-algebra-audit-statement.md).

The theorems below are targets, not checked results. No calculus, safety,
assertion, or machine definition has been changed. When priority 1 begins,
its derivations should use the new assertion proof system for CONS/UNLOCK,
extending that system with proved rules as needed and naming any entailment
left semantic.

The proposed route uses the two token cells suggested in the queue and
recovers the original token-free execution conclusion by an operational
extension/erasure argument. That avoids making priority 1 depend on a new
SHARE rule. The design should be reviewed again against the completed
assertion system before its program proofs are written.

## What the original derivation actually does

I compared the queue with the original LaTeX, Section 4.1, including the
sender's ATOMIC premise and the final AUX step. The source inspected earlier
in this project is `dissertation.tex`, blob
`ac4c24370dc22b3ca0892294206c2c6ac138d993`:
[example and proof](https://github.com/iwehrman/Weak-Memory-Local-Reasoning/blob/master/dissertation.tex#L1383-L1477),
[LOCKED and ATOMIC](https://github.com/iwehrman/Weak-Memory-Local-Reasoning/blob/master/dissertation.tex#L2164-L2169).

There is an important qualification to the queue's freshness diagnosis.
The sender's `s := 1` is proved **under invariant `emp` inside ATOMIC's
premise**, with `I` temporarily in the local assertion. Therefore that
assignment instance is not rejected merely because `s` occurs in `I`.
An attempted direct proof under shared invariant `I` would fail the new
assignment condition; that is not the literal displayed proof.

| Original proof step | Status in the current repaired calculus |
| --- | --- |
| Choose `I = (x=0 ∧ (s=0 ∨ s=1) ∧ d↦s) ∨ (x=1 ∧ s=1 ∧ emp)` | The printed all-processor cell is outside the current invariant fragment. Replacing it by `C(d,s)` and putting the pure guards into the fragment's guarded form addresses that issue, but does not remove `x,s` from `fv(I)`. |
| Prove the sender's body, including `s := 1`, under `emp` | The assignment freshness condition is satisfied there. This step is not, by itself, the known counterexample to unrestricted assignment. Its specific assertion entailments still need checking in the final interpretation. |
| Export the sender's body proof using ATOMIC; similarly reason about the receiver's locked load | ATOMIC is not a constructor or a derived rule of `owned_derivation`. It changes which invariant is held in the environment. We cannot simply use an `emp`-invariant derivation as a derivation under `I`. A direct LOAD under `I` also fails destination freshness because `x ∈ fv(I)`. The receiver's atomic body is only sketched in the source. |
| Combine the two threads under `I` using PAR/CONC | The current invariant-variable conditions fail: the augmented sender modifies `s`, and the receiver modifies `x`, both free in `I`. This is a definite syntactic rejection of the displayed composition. |
| Apply SHARE to move `I` into the pre/postconditions | SHARE is deliberately absent. This specific application is not thereby proved unsound; the separate priority-3 task tests the general rule. |
| Apply AUX to remove the sender's auxiliary assignment | No AUX rule is implemented. The dissertation explicitly says in its footnote that it does not formalize auxiliary-variable elimination. |

These findings establish that the displayed proof does not port as written.
They do **not** establish that its particular program specification is false,
nor that its exact ATOMIC or SHARE instances are unsound. The existing
`printed_assignment_invalid` is a different, checked bad assignment instance;
it must not be cited as a refutation of this sender body. If investigation
finds a false instance in this derivation, I will isolate it as a separate
result instead of conflating rejection with invalidity.

## Same program, different ownership invariant

Keep both commands unchanged, with no auxiliary assignment and no token
accesses. Renumber the printed processors `0,1` to Rocq's positive IDs `1,2`.
The address expression `d` can remain a read-only register expression; its
register name must differ from destination register `x`, as in the example.

Let `C(a,v)` be the existing `writer_points_to` abbreviation. Choose two
distinct token addresses `t,r`, different from the initial address denoted
by `d`. Their values are fixed at zero for convenience. These are ordinary
allocated cells in an auxiliary initial heap, not a new ghost atom or an
allocation instruction. The proof must later erase their presence.

```text
T = C(t,0)             U = C(r,0)
J = C(d,0) ∨ (C(d,1) * T) ∨ (T * U)

sender   = acquire(1); [d] := 1₁; release(1)
receiver = acquire(2); x := [d]₂; release(2);
           if x = 1 then ([d] := 2₂; fence₂) else skip
```

`J` is a fragment invariant and mentions neither `x` nor auxiliary progress
registers. If `d` is a register expression, it is the only program variable
free in `J`, and neither thread modifies it.

Proposed derivations, in disjoint mode:

```text
J ⊢ᴰᴶ {T} sender {emp}

J ⊢ᴰᴶ {x=0 ∧ U} receiver
       {(x=0 ∧ U) ∨ (x=1 ∧ C(d,2))}

J ⊢ᴰᴶ {T * (x=0 ∧ U)} sender || receiver
       {emp * ((x=0 ∧ U) ∨ (x=1 ∧ C(d,2)))}
```

These are intended derivation trees using the existing program rules and
derived assertion entailments, not new axioms. An unframed whole-machine conclusion under invariant `emp` is a
separate adequacy-level target below, not assumed to follow by SHARE.

### Sender

The sender retains `T` spatially while acquiring. Both the second and third
branches of `J` also own `t`, so they conflict with its retained ownership.
Only `C(d,0)` remains possible. It writes 1 to `d`, then releases, donating
both the completed `d` cell and `T` to the second invariant branch. Release's
existing drain condition completes the buffered store. The sender finishes
with `emp`.

### Receiver

The receiver retains `U` spatially while acquiring. This excludes the third
branch, which also owns `r`. It can acquire either `C(d,0)` or `C(d,1) * T`.
LOAD-ANY supplies the loaded value without requiring the receiver to be the
cell's writer.

- If it reads 0, it releases with `C(d,0)` as the pool and retains `U`.
  The conditional does nothing.
- If it reads 1, it releases with `T * U` as the pool and retains `C(d,1)`.
  It then writes 2 privately and fences, producing `C(d,2)`.

The branch choice in this proof is assertion disjunction around the same
release command. It does not insert a branch or token operation into the
original code. The existing command conditional remains after release.

The intended proof uses spatial framing through acquisition and the current
UNLOCK entailment. It should need neither FRAME-STM nor an additional rule
for modifying invariant variables. As before, this is a proof plan until
checked against all admissible frames and local futures.

## Recovering the original conclusion

There are two distinct tasks. Neither should be hidden by weakening the
requested theorem to a token-augmented starting state.

### 1. Relate the terminal pool to the actual augmented heap

Apply the existing soundness and adequacy theorems to the parallel derivation
from an initial pool `C(d,0)` and local tokens `T * U`, with `x=0` and empty
buffers. The final local assertion owns no lock token (no blocked bits).
With two active processors and an empty external
frame, this forces the final lock to be free, so the final pool satisfies `J`.

For `x=1`, the local `C(d,2)` excludes both invariant branches containing
`d`. Thus the final pool is `T * U` and the actual data value is 2.

For `x=0`, retained `U` excludes `T * U`, but leaves **two** apparent pool
branches: `C(d,0)` and `C(d,1) * T`. This is the remaining proof risk. The
first would leave the sender's token `t` absent from the entire final
decomposition. The physical machine has no deallocation, so exact
preservation of the total address domain should exclude it. A one-way
footprint bound is insufficient. I propose proving exact preservation of
`memory_domain` along actual successful steps/executions and using it here.
That selects `C(d,1) * T`, giving data value 1.

The target is a relation about the **actual final memory**, including empty
buffers and a free lock, not merely the existence of some unrelated heap
satisfying the invariant. The exact domain lemma has not yet been added or
proved.

### 2. Remove the unused token cells from the execution statement

Prove that every execution of these commands from the original one-cell
heap lifts to an execution with two extra, untouched token cells. The
commands access only the address denoted by the unchanged `d`, so all reads,
writes and guards agree; buffers and lock state agree as well. Prove the
corresponding abort-preservation fact so that no-abort of the extended run
implies no-abort of the original run. Fresh token addresses are chosen in
the proof and do not remain hypotheses on the original starting state.

After using the augmented derivation, project away the token cells. The
intended theorem for the **original program and original initial heap** is:

```text
Initially: x = 0, d denotes an allocated address ℓ,
           heap = [ℓ ↦ 0], every buffer empty, lock free.

For every finite execution of sender || receiver:
  no abort;
  if terminal, then
    x ∈ {0,1}, heap = [ℓ ↦ x+1], every buffer empty, lock free.
```

At full completeness this should also yield the dissertation's own
all-processor `d ↦ x+1` assertion, rather than only its weakened cell
abbreviation. The plan is a checked execution theorem plus assertion
corollary. It does not yet promise an `owned_derivation` under invariant
`emp` of the printed triple, nor a general SHARE or AUX rule.

The token extension/erasure proof and exact domain preservation are the
specific obligations needed to avoid charging the original program for
extra allocated cells. If either route fails, I will report that before
claiming the original conclusion has been recovered.

## Proposed implementation and searches

Before general proofs, run a bounded check of the relevant resource
entailments: token branch exclusion at each acquisition, both release
splits, the buffered-store/barrier completion, and the terminal pool cases.
Include all writer-mark choices on two processors and both store-pending
and store-flushed states. Report the finite scope; it is screening evidence,
not a substitute for validity over all frames and futures.

Then formalize in this order:

1. The commands, `J`, token assertions, intended triples and static variable
   checks, with no change to the existing calculus.
2. Derived assertion rules needed for the branch exclusions and donations,
   followed by the sender, receiver and parallel derivations. Extend the
   assertion system with sound rules as needed; explicitly report any
   residual semantic entailment.
3. Exact physical address-domain preservation and final-state extraction.
4. Unused-cell execution/abort lifting and the original-heap corollary.
5. Concrete complete traces for both results. The `x=1` trace must exhibit
   the receiver's pending private write before its fence; the `x=0` trace
   must let the receiver finish before the sender stores and releases.

The paper-facing result report will distinguish the original proof's
rejected steps, any actually refuted instances, the token-assisted
derivation, and the token-free operational conclusion. Termination and
fairness remain outside the claim, including the guarded-choice encoding's
possibility of waiting on a false assumption.

These are retained preparatory notes, not a request to change the revised
order. No priority-1 proof or search result is claimed yet, and priority 2
has not been started.
