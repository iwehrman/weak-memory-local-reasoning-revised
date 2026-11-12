# Weak-Memory Local Reasoning, revisited — outline

Draft 1. Status markers: **[have]** the result is checked at `0e1ae5f`;
**[queued]** it is in `review/work-queue-for-paper.md`; **[open]** a decision
for Ian.

## Reader and stance

The reader knows the 2012 dissertation and has forgotten its details. The
paper is chronological and puts the differences first. It is not a
submission, so it can be candid about what was wrong and does not need to
sell the result.

The organizing fact is in the dissertation itself. Its "Contributions and
Status" section names two major components left unfinished, and one
admitted gap:

1. There is no proof system for the assertion language.
2. The soundness proof for the specification logic is incomplete.
3. It "gives little indication of how proofs ought to proceed in the logic".

The paper reports on each. Item 2 is done, for a repaired calculus. Item 3
is addressed by the derivations. Item 1 is **[queued]**, in a bounded form; see the last
section of this outline.

## 1. Introduction

- What the dissertation set out to do: local reasoning for x86-TSO, with
  spatial, temporal and strong temporal separation.
- Where it stopped, in its own words (the three items above).
- What this paper reports:
  - Theorem 1 does not hold as printed. The printed rules derive false
    specifications. **[have]**
  - A repaired calculus is sound, with operational adequacy, fully
    mechanized in Rocq. **[have]**
  - What survived: the assertion language, `emp` as a unit, the temporal
    frame rule, the printed LOAD and STORE axioms. **[have]**, exact list
    **[queued]**
  - Derivations beyond the dissertation's examples. Container **[have]**;
    Section 4.1 example and the ambitious derivation **[queued]**
- How the work was done: a mechanization with an independent review loop,
  bounded search before each general proof, and kernel-checked
  counterexamples. One paragraph here; details in section 9.

## 2. The original model, in brief

A reminder, not a re-derivation. Each item gets the definition and one
example.

- The machine: heap, per-processor FIFO buffers, the blocked set, flushing,
  and the global lock that blocks every other processor.
- Generalized memories and the completeness set.
- The three separations and their compatibility conditions.
- Assertions: `emp`, `bar`, `lock`, leads-to, the conjunctions, the three
  wands, and points-to as an abbreviation with all-processor completeness.
- The rules: Figures 4.7 and 4.8, reproduced.
- The intended semantics: `safe_n` and Theorem 1.
- What the dissertation proved, what it sketched, and what it conjectured
  (Conjecture 1, Proposition 9, Proposition 2).

## 3. What was wrong

Ordered from local to structural, which is also the order of discovery.

### 3.1 Local errors with local repairs

| Printed claim | Finding | Repair |
| --- | --- | --- |
| ASSIGN with any invariant | False: assignment can break the invariant | `x ∉ fv(J)` |
| Buffer overriding is associative (Prop. 2) | False: `[2,1,3]` | Ordered overriding |
| Temporal compatibility composes associatively | False: blocking-sensitive | Stable compatibility |
| Assertions are flush-closed (Prop. 9) | False for the pointwise right wand | Wands quantify over futures |
| Conjecture 1 | False as stated | Not needed in the final proof |
| UNLOCK with any invariant | Invalid for printed `safe` | Transferring lock rules |

All **[have]**. Each row cites its counterexample theorem.

### 3.2 The calculus is inconsistent

Two derivations from SKIP, CONS, INV and FRAME-TM alone:

- a `skip` that changes a cell from 7 to 5 (stale-value forgery);
- a `skip` that imports another processor's barrier past its pending write.

Both **[have]**, with countermodels. In the dissertation's all-processor
points-to: **[queued]**.

Supporting fact: the printed model does not record history, so a current
cell entails any stale earlier value before it. **[have]**

### 3.3 Why no semantics could fix it

The trilemma: unrestricted FRAME-TM, consequence, `R ; emp ⊨ R`, and any
transfer-out contract `{P} c {emp}` cannot all hold in an adequate logic.
**[have]** This is the conceptual centre of the paper. It explains why the
repair had to change a rule, and it applies to any logic with a
non-cancellative sequential conjunction and ownership transfer.

### 3.4 The dissertation's own example

Section 4.1's message-passing proof uses an invariant over registers that
the threads modify. State exactly what fails and give the repaired
derivation. **[queued]**, priority 1.

## 4. What changed

One table, each row marked **error** (the printed statement is false) or
**choice** (a design decision with alternatives), with the justifying
theorem. Source: `notes/current-calculus.md`, to be made uniform
**[queued]**.

| Change | Kind |
| --- | --- |
| `x ∉ fv(J)` on ASSIGN, LOAD, CONC, EX | error |
| Ordered overriding, stable compatibility, future-quantified wands | error |
| INV removed; LOCK and UNLOCK transfer the invariant | error |
| FRAME-TM only from overlap-mode validity | error (tight by the trilemma) |
| FRAME-STM omitted | error for the printed `⋉`; repair not pursued |
| SHARE omitted or restricted | consequence of the new LOCK **[queued]** |
| Cell flushed by its writer; any-writer LOAD and STORE | choice |
| Guarded invariant fragment | choice |
| At least two active processors | forced by the lock encoding |

Then a short account of the directions tried and abandoned, because they
show the trilemma's other exits: separate protected and private assertions
(no donation), retirement (`emp` stops being a unit), explicit tombstones
(not built).

## 5. The new model

- One owned resource with real completeness marks; a separate invariant
  pool; an external frame composed by `#`.
- The environment: free, held locally, held by another thread, and split
  tokens.
- The safety predicate, clause by clause: frames re-quantified at each step
  and fixed within a step; closure under local futures; the footprint bound;
  the mark budget.
- The two modes, and why each mode-specific rule lands where it does.
- Three lemmas that carry the proof: residual uniqueness, flush attribution,
  re-marking of fragment invariants.
- What a completeness mark means, since the dissertation left this informal.

All **[have]**.

## 6. The calculus

The 21 rules as a figure, in the dissertation's notation, with the mode
index. Derived rules: the dissertation's own list (FENCE-G, LOCK-G,
UNLOCK-G, LOAD-P, STORE-P, LOCKED, ATOMIC) with the status of each
**[queued]**.

## 7. Results

- Soundness by induction on derivations. **[have]**
- Adequacy: no abort on any finite execution; on termination, the
  postcondition and the ownership decomposition. The stronger restoration
  corollary for `emp`-to-`emp` clients. **[have]**
- What the theorems do not say: no termination, no fairness, no progress.

## 8. How proofs proceed

The dissertation's third gap.

- The container, step by step, as the worked example: acquire, remove,
  release, private write, reacquire, return, with a foreign write pending.
  Where FRAME-SP is enough, where FRAME-TM is essential. **[have]**
- The retrying container: loops, choice, and a branch excluded by ownership.
  **[have]**
- Section 4.1's example, repaired. **[queued]**
- The ambitious derivation: named locks as derived rules, and a
  producer/consumer client. **[queued]**
- The cost: entailment obligations counted and classified. **[have]** for
  the container.
- Opening pair: a fenced store gives the textbook rule, and the unfenced
  one is invalid. **[queued]**
- Reading your own buffered write: derivable, or a new rule. **[queued]**

## 9. The mechanization

- Size, structure, audit: figures **[queued]**.
- Method: independent review, statement before proof, bounded search before
  proof, kernel-checked counterexamples. Include the two occasions where
  search or checking refuted a confident paper argument (the frame-shape
  lemma, FRAME-STM), since they are the evidence that the method mattered.
- What is trusted: the Rocq kernel and the transcription of the machine.

## 10. Later work

Brief. How temporal separation as a connective compares with later
approaches to weak-memory program logics. Needs a literature pass before
any claim is written. **[open]**: scope and depth.

## 11. What remains

- Releases outside the global lock (the "daring" rules; fenced Dekker).
  **[queued]** for a one-paragraph confirmation.
- A strong temporal connective with a common split. Its frame property at
  the resource level is **[queued]**; the connective itself is not planned.
- Allocation, recursive predicates, permissions (Chapter 5).
- Expression-valued lock identifiers.
- Completeness and automation for the assertion proof system.

## Decided: a proof system for assertions

Approved and queued as priority 4 in `review/work-queue-for-paper.md`: an
audit of Figures 4.5 and 4.6, a sound rule set, and a container derivation
with no semantic entailment premises. Completeness is out of scope. It
becomes a section between 6 and 7, and the audit table also feeds section 4.
