# Checkpoint 8 — parallel composition proved

**Subsequent result:** [checkpoint 9](checkpoint-9.md) proves the requested
routine rules, printed strong-temporal LOAD/STORE forms, and explicit
any-writer cell extensions. The report below records checkpoint 8's scope
and the work that was open then.

**The semantic parallel rule is proved in both ownership modes.** The only
addition to the printed variable condition is the agreed requirement that
neither command modifies variables free in the shared invariant. The safety
definition, assertion interpretation, machine semantics, and existing
entailments are unchanged. No new validity predicate or thread certificate
was introduced.

The bounded searches completed before the general proof attempt. The new
proofs and concrete examples pass `make check`; all **510** audited
declarations are closed under the global context, including 24 added at
this checkpoint. There are no declared axioms or admitted proofs.

## Exact rule and scope

[`OwnedParallel.v`](../theories/OwnedParallel.v) proves
`owned_parallel_valid`:

```text
valid^k J {P1} c1 {Q1}       valid^k J {P2} c2 {Q2}
mod(c1) disjoint fv(P2,c2,Q2)
mod(c2) disjoint fv(P1,c1,Q1)
mod(c1) disjoint fv(J)       mod(c2) disjoint fv(J)
------------------------------------------------------------
valid^k J {P1 * P2} (c1 || c2) {Q1 * Q2}
```

The premises and conclusion use the same mode `k`, which may be overlap or
disjoint. The two interthread conditions are exactly
`parallel_variable_condition`; the additional invariant conditions are
`frame_variable_condition c1 J` and `frame_variable_condition c2 J`.

The theorem covers arbitrary assertions and commands, including commands
containing parallel composition. It needs neither `invariant_fragment J`
nor any assumption about the processor domain. The existing lock rules and
top-level adequacy theorem retain their two-active-processors and fragment
requirements. Parallel composition does not make an otherwise invalid
primitive specification valid.

Register updates are allowed: a thread can assign or load into variables
absent from the other thread's specification and the shared invariant.
There is no register-preservation premise. If one premise is known in
overlap mode and the other only in disjoint mode, the existing mode-inclusion
theorem permits composition in disjoint mode; it does not promote the result
to overlap mode.

## Search results

The attempted rule and bounds were recorded in
[`checkpoint-8-statement.md`](checkpoint-8-statement.md).
[`search_owned_parallel.py`](../scripts/search_owned_parallel.py) extends
the checkpoint-7 finite reconstruction model. Its complete output is
[`checkpoint-8-search.jsonl`](checkpoint-8-search.jsonl).

| Mode | Admissible input environments | Admissible component successors reconstructed, both directions | Acquire-then-blocked-store traces |
| --- | ---: | ---: | ---: |
| Overlap | 11,485 | 279,715 | 48 |
| Disjoint | 1,947 | 36,156 | 48 |

Every reconstructed successor also gives the unchanged sibling a fresh
admissible environment containing the changed component. Both directions
have nonzero coverage for stores, fences, acquisition, release, and
unchanged-memory actions. All five recorded searches completed without a
counterexample, including **297,918** finite primitive stack-agreement
checks covering assignment, load, store, assume, assert, fence, lock and
unlock. Processor annotations can themselves use registers.

The memory bounds are two processors, three addresses, values 0/1, all mark
sets, up to one heap cell per input component, and at most three input
pending writes. A store can add a fourth. The overlapping-buffer family is
enumerated; a seed-7, 4,000-draw sample covers additional inputs, including
held locks. The stack search uses three registers ranging over 0/1/2, all
support supersets, and three selected physical memories. Counts measure
checks and need not count distinct physical configurations.

These are finite searches of sufficient reconstruction and support
obligations, **not exhaustive searches of semantic Hoare validity**. The
unbounded Rocq proofs do not depend on the scripts or their output.

## How the proof composes threads

1. **Split every local future.** The existing spatial future-splitting
   theorem gives a future for each thread, and both component safeties
   remain available at the original index. This includes mark-only futures
   and local flushes blocked by an external token.
2. **Run one component with its sibling in the frame.** From an external
   frame `F` and spatial resources `L * R`, the acting thread uses the grouped
   frame `F # R` (or `F # L`). Its safety keeps that grouped frame exactly
   fixed within the program step.
3. **Reconstruct the combined successor.** `owned_spatial_component_step`
   uses checkpoint 7's reconstruction and update lemmas. The sibling
   resource stays exactly unchanged, while the executing thread may acquire
   cells from the pool or return cells to it. The combined update satisfies
   the existing action-transfer, footprint, and mark-budget conditions.
   This also supplies the lock-token reasoning; no new token-placement
   premise is needed.
4. **Transport the sibling to the changed stack.**
   [`OwnedInterference.v`](../theories/OwnedInterference.v) first proves
   program-step and abort transport on agreeing stacks, then
   `owned_safe_stack_agrees` for the full safety predicate. The interference
   conditions preserve the sibling command and postcondition. Invariant
   freshness preserves the meaning of every freshly quantified pool
   environment. This is where the additional condition is used.
5. **Carry finished postconditions with FRAME-SP.** When the semantics erases
   a finished branch, its resource becomes a spatial assertion frame for
   the remaining branch at the required index. The right-finished case also
   uses spatial commutativity and checked postcondition monotonicity.

`owned_safe_parallel` is the same-index safety theorem underlying the
validity rule. It is proved by induction on the safety index. Each recursive
call quantifies over new frames and pools, as the unchanged safety
definition requires. Nested parallel commands are covered by the command
quantifiers and the program-step transport induction.

## Checked applications and inhabited starts

[`OwnedParallelExamples.v`](../theories/OwnedParallelExamples.v) establishes:

- **Acquisition alongside a private store**, in both modes. The initial
  invariant owns `2 ↦ 7`; the other thread owns `3 ↦ 3`. A checked trace
  acquires on processor 1 and then enqueues `3 := 9` on processor 2 while
  processor 2 is blocked. The initial precondition and concrete free-pool
  environment are proved inhabited. `owned_parallel_acquire_store_valid`
  proves validity for all initial resources satisfying the precondition,
  not just the exhibited trace.
- **Either branch may finish first.** The left-finished and right-finished
  specifications retain a lock token and its cell while the sibling stores
  to its private cell. These instantiate the general parallel rule, rather
  than only its component-step lemma.
- **Both threads may modify registers.** One assigns `x := 7`, the other
  `y := 9`, with distinct registers. The postconditions retain both values.
  `owned_parallel_registers_valid` uses the general parallel theorem and a
  small, separately checked constant-assignment specification. The enabled
  example proves the initial environment and actual two-step register
  changes; it cannot pass by forbidding stack changes.

The examples use the existing two-processor domain. The general parallel
theorems are not restricted to that domain.

## Remaining work

This proves the parallel rule for the active target; it is **not** a full
calculus soundness theorem. Next come:

1. General sequencing, consequence, disjunction, choice, loop, assignment,
   base load/store, and fence rules. Postcondition monotonicity and the
   constant-assignment regression do not constitute that suite.
2. LOAD and STORE in the dissertation's existing strong-temporal form.
   FRAME-STM remains omitted, and the `⋉` abbreviation remains unchanged.
   A failure of these axioms would reopen the connective question.
3. The container derivation: acquire, remove, release, private use, and
   return, with a foreign write pending.
4. A derivation system tracking overlap-mode specifications, followed by
   soundness by induction on derivations and the existing adequacy result.

The structural combination of ownership, spatial framing, temporal framing,
and concurrency now checks in one safety predicate. That is a substantial
reason for optimism. The strong-temporal primitive rules and container
derivation are still unproved, so they remain tests of the design's
usefulness and of how much of the original calculus can be preserved.
