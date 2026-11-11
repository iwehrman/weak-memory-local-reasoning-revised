# Independent review at checkpoint 66106f1

Scope: the Rocq development at `66106f1`, the notes under `notes/`, and the
dissertation's LaTeX source (Chapter 4 and Appendix A). Nothing in `theories/`
was modified. Scratch proofs are in `review/Review.v` and
`review/Derivations.v`; compile either with
`rocq compile -Q theories WMLR review/<file>.v` after `make`.

Every claim below is tagged:

- **[K]** kernel-checked, in the repository or in the two `review/` files
  (each reports `Closed under the global context`)
- **[R]** rigorous paper argument, each step small, not machine-checked
- **[C]** conjecture or design judgment

## 1. Verdict

The build claim holds **[K]**: a clean clone passes `make check`, and all 368
audited declarations are closed under the global context.

The direction is wrong in one respect and right in another.

Right: the diagnosis of the early failures (assignment, buffer overriding,
blocking-sensitive compatibility, pointwise wands, printed unlock) is faithful
to the printed definitions, and the first-generation repairs are reasonable.

Wrong: the last two stages treat two obstructions as defects of a particular
resource decomposition and respond by changing the model. Both obstructions
are already inconsistencies of the *printed calculus*, derivable from INV,
CONS and FRAME-TM alone (section 2). No choice of safety predicate or resource
representation can remove them. Each needs a change to a rule, and the
smallest such changes are much smaller than the ones adopted:

- The completeness-import problem is caused by the all-processor points-to
  abbreviation. Re-marking acquired cells with the acquirer's completeness
  only removes it without separate protected and private compartments.
- The donation problem is an instance of a four-assumption trilemma. The
  retirement experiment resolves it by giving up `emp`'s unit law, which is
  the most expensive of the available exits, and its interpretation has an
  additional flaw the notes do not record (section 3.1).

My recommendation is to keep the original algebra intact and restrict
FRAME-TM to commands that do not release ownership, keeping FRAME-STM and
FRAME-SP unrestricted (section 5).

## 2. Two inconsistencies of the printed calculus

Both derivations use only SKIP, CONS, INV and FRAME-TM from Figures 4.7 and
4.8, and both are now **[K]** in `review/Derivations.v`. The checked versions
use the owner-specific cell `x ↦_k v ; bar(k)`, which is in the printed
grammar, and parse INV's `J * P * lock_i` as `J * (P * lock_i)`. Each theorem
has three parts: the derivation, a concrete two-processor state that
satisfies the precondition but not the postcondition, and invalidity for the
printed `safe` predicate. Below, `x ↦ v` abbreviates that cell.

### 2.1 Stale-history forgery (the donation obstruction)

Take `J = emp ∨ x ↦ 7`.

1. `emp ⊢ {J * x↦7 * lock_i} skip {J * emp * lock_i}` by SKIP and CONS. The
   disjunct `x↦7 * x↦7` is inconsistent; in the other, the cell is simply
   reassigned to `J`.
2. `J ⊢ {x↦7 * lock_i} skip {emp * lock_i}` by INV.
3. `J ⊢ {x↦5 ; (x↦7 * lock_i)} skip {x↦5 ; (emp * lock_i)}` by FRAME-TM.
4. `J ⊢ {x↦7 * lock_i} skip {x↦5 * lock_i}` by CONS.

Step 4 uses `x↦7 * lock_i ⊨ x↦5 ; (x↦7 * lock_i)`. The printed model records
the current memory, not a history, so a current flushed cell entails any
stale earlier value at the same address (`E_invent`).

The conclusion says a `skip` changes the contents of `x` from 7 to 5. The
checked theorem is `printed_calculus_stale_value_unsound`. The same
calculation for the all-processor points-to is **[R]**.

### 2.2 Completeness import (the regional obstruction)

Take `J = x ↦_2 7 ; bar(2)`, a cell flushed by processor 2, and
`R = y ↦_2 17`.

1. `emp ⊢ {J * emp * lock_1} skip {J * bar(2) * lock_1}` by SKIP and CONS
   (`E_import`, the analogue of the repository's `cell_emp_entails_barrier`).
2. `J ⊢ {emp * lock_1} skip {bar(2) * lock_1}` by INV.
3. `J ⊢ {R ; (emp * lock_1)} skip {R ; (bar(2) * lock_1)}` by FRAME-TM.

In the checked state processor 1 holds the lock and processor 2's write to
`y` is pending. That state satisfies the precondition and not the
postcondition, since a barrier for processor 2 cannot follow its pending
write. The theorem is `printed_calculus_foreign_barrier_unsound`.

`regional-ownership.md` says its counterexample "is not a claim that this
particular derivation has already been reproduced using only the
dissertation's printed rules". It can be: the derivation above is that
reproduction.

### 2.3 The general trilemma

`trilemma` in `review/Review.v` **[K]** is the abstract form. Assume:

- **F**: FRAME-TM with no restriction on the frame
- **C**: consequence on postconditions
- **U**: `R ; emp ⊨ R`
- **T**: some valid transfer-out contract `{P} c {emp}`
- **A**: adequacy

Then `{R ; P} c {R}` is valid for every `R`. So if a single execution starts
in `R ; P` and ends in a state whose remaining local resource does not
satisfy `R`, the five assumptions are contradictory.

In any model where a later value overrides an earlier one, such executions
exist as soon as `R` and `P` mention the same cell. The STORE axiom's own
postcondition, `(old ⋉ P) ; e ↦_i e'`, produces exactly that shape, so
overlapping history cannot be avoided by convention.

This is a general incompatibility, not a property of the decomposition
`(history ; private) * protected`. Every sound design drops one assumption:

| Dropped | Design | Status in the repository |
| --- | --- | --- |
| T | No donation | Separated model |
| U | `emp` admits retirement entries | Retirement experiment |
| T, replaced | Transfer-out returns an explicit tombstone, not `emp` | Not tried |
| F, minimally | FRAME-TM excludes frames overlapping the released footprint | Not tried |

The last row is tight: the trilemma refutes every frame that overlaps a
released cell, so the restriction cannot be weakened further **[R]**.

## 3. Audit of the stated claims

### 3.1 Incorrect or incomplete claims

**The retirement interpretation loses more than `emp`'s unit law.** In
`RetiredHeaps.v`, `cell` constrains only the live heap, so a write atom may
carry retirement entries at other addresses. Consequently an ordinary later
cell can erase an earlier, unrelated one:

```text
processor_cell(i,y,3) ; processor_cell(i,x,7)   does not entail ownership of y
```

This is `retired_later_cell_can_erase_earlier` **[K]**. Under that
interpretation the STORE postcondition would not retain its own frame `P`.
The experiment has no store rule, which is why its examples do not expose it.
`retired-ownership.md` discusses only the barrier being strict.

**The donation obstruction is described as model-specific.**
`ownership-transfer.md` presents `retained_history_prevents_donation` as a
structural limit of the separated environment. Sections 2.1 and 2.3 show it
is a property of the printed rules.

**Overlapping flushed history carries no information in the printed model.**
By `printed_history_invention`, `C(x,5) ; C(x,7)` and `C(x,7)` are
equivalent. Only flushed-then-pending overlap is informative. This matters
for assessing cost: stale flushed history can always be discarded by
consequence before a transfer.

### 3.2 Claims that hold

- Assignment needs `x ∉ FV(J)`. This is the standard CSL side condition and a
  real omission in Figure 4.7.
- Proposition 2(2) fails. The dissertation defines `m ▷ n` by lookup equality
  on interleavings; the transcription and the `[2,1,3]` counterexample are
  faithful.
- Blocking-sensitive temporal compatibility is not associative. Stable
  compatibility costs nothing outside the "daring" rules, which are the only
  place a non-holder writes to cells it does not own **[R]**.
- The pointwise right temporal wand is not flush-closed. Quantifying over
  futures is the ordinary Kripke reading of implication over the flushing
  preorder; I regard it as the canonical repair, not an ad hoc one.
- Printed UNLOCK is invalid for printed `safe`. More strongly, printed
  `safe` forgets that `J` held at acquisition, so INV is not semantically
  justified either **[R]**. CSL-style transfer at lock and unlock is required.
- The printed semantic frame lemma evaluates `R` and `P` each at full
  completeness. That proves a rule for `#`, not for `;`, where the two halves
  share one completeness set. Marked local resources are therefore required.

### 3.3 Avoidable restrictions

- **Separate protected and private compartments.** They exist to stop
  all-processor completeness leaking out of `J`. The withdrawal rule already
  does the right thing for one cell: it re-marks with the issuing processor
  only. Doing that for the whole invariant at acquisition makes the
  compartments, and componentwise consequence, unnecessary **[R]**.
- **`processor_cell` as a weaker contract.** It is the strongest contract a
  lock acquisition can earn. All-processor completeness can never be
  established by a command, only inherited from a precondition, and it forces
  every temporal frame before it to be fully drained. I consider the
  all-processor abbreviation the anomaly. The dissertation's stated reason for
  it (a pending write on processor 0 before a cell flushed by processor 1
  "should arguably" have no models) describes a reachable, stable TSO state.
- **Completeness has no role in load soundness.** Stability of a loaded cell
  follows from the compatibility conditions. Completeness is needed for
  barriers and for FIFO consistency of same-processor chains **[R]**.

## 4. Alternatives compared

| | A. Separated (current) | B. Retirement (current) | C. Explicit tombstones | D. Mode-restricted FRAME-TM |
| --- | --- | --- | --- | --- |
| `emp` two-sided unit | Yes | No | Yes | Yes |
| Overlapping history | Private only | Yes | Yes | Yes |
| FRAME-TM | Original | Original, weaker meaning | Original | Original for unlock-free commands |
| FRAME-STM, FRAME-SP | Not proved | Not proved | Expected | Unrestricted |
| Donation | No | Yes | Yes, post is `x ↛` | Yes, post is `emp` |
| Withdrawal | Yes | Yes | Yes | Yes |
| Consequence | Componentwise | Ordinary | Ordinary, tombstones not weakenable | Ordinary |
| Judgment shape | `{S \| P}` pairs | `{S \| P}` pairs | Original | Original plus one side condition |
| Original entailments | Kept | Changed | Kept for wand-free formulas | Kept |
| Main risk | Dead end for containers | Buffered port; atom laxity (3.1) | Tombstone clutter in every later spec | Frame-shape lemma (section 6) |

Notes on C. Entries are absent, live or retired; atoms and `emp` are strict
(no retired entries); a new atom `x ↛` holds exactly one retired entry.
Temporally the later entry wins; spatially live absorbs retired. Then
`x↦5 ; x↛ ≡ x↛` and `x↛ ; x↦7 ≡ x↦7`. The weakening test passes: `x ↛ ⊭ emp`,
and `x↛ * A ⊭ A` unless `A` is live at `x`. The cost is that any thread that
has ever donated carries tombstones it can never discard, so unrelated
postconditions become `Q * gone`. C is B done honestly, with a true unit
retained. **[R]** for the algebra, **[C]** for the calculus.

## 5. Recommended design (D)

All of this section is **[C]** supported by **[R]** arguments; none of it is
machine-checked.

### 5.1 Assertions

Unchanged grammar and algebra, with stable compatibility, ordered overriding
and future-quantified wands as now. One change of abbreviation:

```text
x ↦ v  ≝  ∃k. (x ↦_k v ; bar(k))        flushed by its writer
```

Invariants `J` are built from this points-to, `*`, `∨`, `∃` and pure
formulas. Such `J` is buffer-free and insensitive to which processors are
marked complete, as long as one is.

### 5.2 Rules

Figures 4.7 and 4.8 with these changes:

```text
ASSIGN    adds  x ∉ FV(J)
LOAD, STORE     accept a flushed cell written by any processor

LOCK      J ⊢ {emp} lock_i {(lock_i * J) ; bar(i)}

UNLOCK    A ; bar(i) ⊨ J * B
          --------------------------------
          J ⊢ {lock_i * A} unlock_i {B}

FRAME-TM  adds  "c contains no unlock"
FRAME-STM, FRAME-SP, CONS, SEQ, CONC, SHARE   unchanged
INV       removed (subsumed by LOCK and UNLOCK)
```

LOCK hands over the pool's cells marked complete for `i` only. That mark is
earned: the machine's lock step requires buffer `i` to be empty.

### 5.3 Semantics

One safety predicate with a mode `k ∈ {ov, dj}`:

- Local resources are generalized memories with their real completeness marks.
- The environment is `whole ∈ pool ⊎ (F # ν)`, with `#` the repaired
  spatiotemporal composition. The pool satisfies `J` at full completeness, or
  is held.
- Mode `ov` quantifies over all compatible frames `F`. Mode `dj` additionally
  requires `dom(F) ∩ dom(ν) = ∅`.
- Local flushes are a closure clause on `ν`, not an existential repartition,
  so two threads see the same decomposition.
- The combined footprint of pool and local may not grow.

`valid^ov` implies `valid^dj`. The soundness theorem is a simultaneous
induction: derivable implies `valid^dj`, and derivable for an unlock-free
command implies `valid^ov`.

Why each rule lands where it does **[R]**:

- LOCK is `ov`: the frame is disjoint from the pool because the pool is
  spatially separate from `F # ν`, and the `i` mark is earned.
- UNLOCK is `dj` only: the donated cells become the pool, which must be
  disjoint from `F`. In `ov` this is exactly the trilemma.
- FRAME-TM is `ov`: reassociate `F # (ν_R ; ν_P)` into `(F # ν_R) # ν_P`.
- FRAME-STM is sound in both modes: a frame disjoint from `ν_P` stays
  disjoint from everything `ν_P` later acquires or releases.

### 5.4 The troublesome examples

- **Foreign barrier.** `{emp} lock_1; unlock_1 {bar(2)}` is not derivable:
  the acquired resource is marked for processor 1 only.
- **Stale-history forgery.** Section 2.1 needs FRAME-TM across a release;
  the side condition blocks it.
- **Donation with overlapping history.** `(x↦5 ; x↦_i 7)` is donated whole:
  with `bar(i)` it entails `x ↦ 7`, and the stale value is dropped by
  consequence inside the UNLOCK premise. No frame is involved.
- **Shared container, with processor 2's write to `y` pending throughout.**
  Let `J = f↦0 ∨ (f↦1 * ∃v. x↦v)` and `R = y ↦_2 17`.
  1. `lock_i` under FRAME-TM gives `R ; ((lock_i * J) ; bar(i))`.
  2. Load `f`, take the branch `f = 1`, store `f := 0`.
  3. `unlock_i` with `B = R ⋉ x↦v`; the premise holds because
     `f↦1 ; f↦_i 0 ; bar(i) ⊨ f↦0`.
  4. Use `x` privately, for example `[x] := 9`, creating overlapping history.
  5. `lock_i` again under FRAME-TM, take the branch `f = 0`, store `f := 1`.
  6. `unlock_i` with `B = R`; the premise holds because the private chain on
     `x` followed by `bar(i)` entails `x ↦ 9`.

  The lock is acquired inside the proof, the invariant is nonempty in both
  directions, and `R` is never drained.

### 5.5 Cost

A stale frame cannot be carried temporally across an `unlock` when it
overlaps cells the thread still holds; the proof must fold it into the
footprint first. I could not construct a proof that needs otherwise, since
flushed stale history is information-free (3.1). Threads that use one cell
from several processors need the generalized LOAD and STORE.

If unrestricted FRAME-TM is non-negotiable, C is the fallback, not B.

## 6. Decisive next steps

1. **Done:** sections 2.1 and 2.2 are kernel-checked in
   `review/Derivations.v`. Worth moving into `theories/` and `Audit.v`.
2. **Prototype D on the separated model's environment.** Merge the protected
   compartment into the local resource with re-marking at acquisition, add
   the mode, and prove LOCK, UNLOCK, FRAME-TM (`ov`) and FRAME-STM (`dj`) with
   pending foreign frames. The counterexample search that could kill it: an
   invariant in the proposed fragment that holds at full completeness but
   fails when marked for the acquirer only.
3. **The frame-shape lemma**, which is the hardest missing piece and the true
   successor of Conjecture 1. If `m ∈ F # (ν_R ∘ ν_P)` for `∘` among `*`, `;`
   and `⋉`, and a step yields `m' ∈ F'' # ν_P'` with `F''` a future of
   `F # ν_R` and `ν_P'` within the footprint bound, then `F''` splits as
   `F' # ν_R'` with `m' ∈ F' # (ν_R' ∘ ν_P')`, marks included. Spatial framing,
   temporal framing and CONC all reduce to it. Search small buffers for a
   counterexample before attempting the proof; the risky case is `F` and
   `ν_P` writing the same address on the same buffer.

## 7. What is and is not established

| Claim | Status |
| --- | --- |
| Build and audit at `66106f1` | K |
| Abstract trilemma | K (`trilemma`) |
| Retirement atoms let a later cell erase an earlier one | K (`retired_later_cell_can_erase_earlier`) |
| History invention in the printed interpretation | K for owner-specific cells, with and without the lock; R for all-processor points-to |
| Printed-rule derivations 2.1 and 2.2, with countermodels | K (`printed_calculus_stale_value_unsound`, `printed_calculus_foreign_barrier_unsound`) |
| Tightness of the FRAME-TM restriction | R |
| Algebra of design C | R |
| Soundness of design D, including the container proof | C, with R arguments per rule |
| Frame-shape lemma | C |
