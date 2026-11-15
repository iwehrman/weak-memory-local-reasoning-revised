# Buffered-pool calculus integration and withdrawal checkpoint

Response to `reviewer-guidance-daring-4.md` at `339698e` (including the addendum).

**Proof commit: 521acd600bf4b6352c21946d1526c49367402dec.**

Items 1–4 are complete. The approved buffered-pool definition supports every
remaining proposed rule, an inductive calculus, and a Dekker derivation whose
soundness is now used by the original-machine all-execution theorem. No rule
statement, mark budget, assertion interpretation, or safety definition changed.

The addendum has a qualified positive result for initial barriers and a
negative result for the proposed automatic mark gain. Details and the exact
boundary between checked theorems and bounded search follow below.

## Main-build integration and validation

- `make check` now covers both the lock calculus and the separate buffered-pool
  development, including all new proofs below. There is one audit with **1,483
  closed declarations**, no axioms reported, and no admitted proofs.
- The buffered overlay's 108 audits were incorporated in `Audit.v`; this batch
  adds 34 further audits. The previous main count was 1,341.
- `_CoqProject` lists **218 theory files and 33,687 physical lines**, including
  comments, audits, counterexamples and superseded developments. These figures
  describe the whole checked repository, not only the active proof.
- `Makefile.buffered`, `BufferedPoolAudit.v`, and the withdrawn
  `DaringCandidate.v`, `DaringAudit.v`, `Makefile.daring` are deleted.
  `BufferedPoolCandidate.v` remains, with only its opening comment changed.
- `notes/paper-theorem-index.md` contains the new entry points, updated counts,
  and no longer says fenced Dekker lacks a shared-access rule.
- A fresh local clone of the proof commit passes `make -j2 check` (exit 0):
  exactly 1,483 closed reports, no axioms, followed by a successful `rocq check`.
  The withdrawal-budget search also reproduces its checked-in JSON byte for byte
  in that clone. Toolchain: Rocq 9.3.0, OCaml 5.5.2.

The accepted `owned_safe` and `owned_derivation` paths and `paper/` are
unchanged. Original daring-rule counterexamples remain in the main audit.

## The remaining rules and derivation system

`BufferedPoolStructural.v` proves DISJ, CHOICE, LOOP and EX.
`BufferedPoolPrimitives.v` proves private LOAD, STORE, FENCE, assignment,
assume and assert. Each theorem is an inhabitant of its approved proposition
in `BufferedPoolCandidate.v`; none failed or required an extra condition.
EX retains freshness from the invariant, command and postcondition; private
load retains the specified destination freshness; assignment retains invariant
freshness. These are the proposed conditions, not additions in this batch.

`BufferedPoolCalculus.v` defines `buffered_derivation` with sixteen
constructors: SKIP, ATOMIC, assignment, assume, assert, private LOAD/STORE/FENCE,
SEQ, CONS, DISJ, CHOICE, LOOP, EX, FRAME-SP, and CONC. The ATOMIC premise stays
semantic, and consequence uses semantic assertion entailment. No constructor
assumes safety or validity.

- `buffered_calculus_sound` proves soundness by induction into `buffered_valid`.
- `buffered_derivation_adequacy` gives the concrete all-execution theorem
  directly from a derivation, with the buffered invariant-fragment hypothesis
  stated once. Neither theorem needs processor finiteness or two active processors.
- `buffered_dekker_thread0_derived`, `buffered_dekker_thread1_derived`, and
  `buffered_dekker_derived` in `BufferedDekkerDerivation.v` combine the six
  earlier atomic certificates using SEQ and CONC.
- The proof of `buffered_dekker_augmented_all_runs` now invokes derivation
  adequacy. Therefore `dekker_fenced_all_runs` reaches the machine through the
  inductive calculus, not merely a separately composed semantic validity proof.
  The machine theorem's statement is unchanged.

Your proposed paper description did not overstate the accepted result. It may
now additionally claim the remaining rules and an inductive calculus, with
fenced store buffering derived in that calculus. It still must not claim the
full retrying Dekker algorithm or integration with the lock-transfer judgment.

## Addendum 5: initial barriers work, allocation is a separate obligation

All results in this section are checked in `BufferedPoolBarriers.v`.

1. `buffered_initial_barriers_split` gives two threads their own barriers in a
   spatial split whose underlying memory is exactly empty.
2. `buffered_barrier_parallel_initial_adequacy` combines arbitrary derivations
   from those barriers using CONC and adequacy, with the existing variable
   conditions. It starts from the original shared memory, with no added heap
   cells or machine steps. It is stronger than the requested empty-buffer start:
   the shared buffers need not be empty, because these marks describe empty
   *private* histories and do not claim that the whole buffer is drained.
   This chooses initial ghost marks; it does not add an entailment `emp ⊨ bar_i`.
3. `buffered_barrier_load_withdrawal_premise_invalid` rejects the literal
   `{bar_1} r := [x]_1 {bar_1 * x ↣ 0}` with `J = emp ∨ x ↣ 0`.
   The initial private memory and the pool can both be empty, so the load aborts.
   The proof uses this empty-pool input; it is independent of the mark budget.
4. `buffered_marked_cell_withdrawal` proves that on the allocated pool branch,
   the desired successor *can* be constructed with exactly the old private
   marks. This isolates and removes the previous mark obstruction.
5. A nearby true atomic rule is proved, derived and shown to have an enabled
   load. Let
   ```
   Jg = (r != 0 ∧ x ↣ 0) ∨ (r = 0 ∧ emp).
   {r != 0 ∧ bar_1} r := [x]_1 {bar_1 * x ↣ 0}
   ```
   `buffered_guarded_barrier_withdrawal_premise`, `_derived`, `_valid`, and
   `_enabled` establish this protocol. The checked start has `r = -1`, a free
   lock, empty buffers, and the pooled cell `x = 0`. The load sets `r = 0`,
   selects the empty invariant branch and transfers the cell without earning
   any new mark.

This guarded example is deliberately a single-thread allocation protocol. Its
load changes a register free in `Jg`, so it is not an instance to which CONC's
invariant-preservation condition applies. The general two-thread initialization
and adequacy theorem remains valid, but it is not a parallel derivation of this
particular withdrawal protocol.

Thus an initial barrier solves the mark problem for a protocol that guarantees
allocation. It does not make the unconditional optional-cell load safe. I would
retain that distinction in the paper rather than describe all withdrawal limits
as merely a choice of precondition.

## Conditional addendum 6: the proposed relaxation fails reconstruction

Since the literal test in item 5 fails and the nearby true protocol does not
establish a general concurrent withdrawal rule, I also tested the conditional
alternative. This is a **bounded search result**, not a new Rocq soundness
or unsoundness theorem. No approved definition was edited and no general proof
for the proposed budget was attempted.

The exact statement is in `daring-withdrawal-budget-proposal.md`. Receiving a
cell is interpreted narrowly: the same heap cell moves from the pool into
private ownership. A new mark is then allowed if that processor's private
buffer is empty. The search tests three readings: empty before, empty after,
and empty both before and after the step.

`python3 scripts/search_withdrawal_budget.py` reproduces
`daring-withdrawal-budget-search.json`: **1,600 cases per reading, with 128
failures of fixed spatial-frame reconstruction in each**. Two processors,
two addresses, values 0/1, and at most one frame write suffice. The counterexample
has a heap-backed pending write, not an unallocated buffer entry:

```
local before: empty, no marks
pool before:  x = 0
local after:  x = 0, mark 1
pool after:   empty
fixed frame:  y = 0, processor 1 buffer [y := 0], mark 2
```

On the small local resource, the proposed budget permits mark 1 on withdrawal.
With the fixed frame included, processor 1 has a pending write both before and
after the step; mark 1 was absent initially, so the same budget forbids the
required successor mark. All compositions are spatial, both resources obey
mark/heap well-formedness, the joint footprint is unchanged, and the whole
memory is unchanged as for an ordinary assignment.

This rejects the proposed replacement for `buffered_update_frame`, the update
reconstruction used by spatial framing and concurrency. It does not refute
every imaginable way to authorize new marks. My recommendation is to keep the
proved budget, use initial barriers where appropriate, and require an explicit
allocation/transfer protocol. This is the requested check-in before pursuing
any different budget or a general proof.

## Embedding in the lock calculus: open, with concrete obstacles

A direct embedding under the same invariant is not available. The lock
calculus's free pool is buffer-free, and ordinary steps leave its pool fixed;
this judgment permits buffered pools and ordinary atomic transfers. Moreover,
a lock-calculus environment may have the lock held by another thread and the
invariant's cells in the frame, whereas buffered validity assumes a free lock
and a pool satisfying its invariant at each step. A combined design would need
to specify when each protocol governs the shared resource and prove the switch
between them, or give the two protocols separate resources. I would call that
**open**, not blocked: these are obstacles to reusing the present judgments
unchanged, not an impossibility result for a combined logic. No such combination
was implemented in this batch.
