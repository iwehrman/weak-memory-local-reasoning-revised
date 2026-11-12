# Checkpoint 7 — frame-rule statements before the bounded searches

The accepted checkpoint-6 response drops FRAME-STM from the current target.
Its existing conjunction abbreviation remains unchanged, including in the
LOAD/STORE statements to be checked later. Neither overlap-mode FRAME-STM
nor a transfer of its counterexample to the printed calculus is assumed.

## Semantic rule targets

For any guarded-fragment invariant `J`, arbitrary assertions `P,Q,R`, and
command `c`, with the usual `mod(c) ∩ fv(R) = ∅` condition:

```text
FRAME-SP, for k = overlap or disjoint:
  owned_valid k J P c Q
  -----------------------------------------
  owned_valid k J (R * P) c (R * Q)

FRAME-TM, for overlap mode:
  owned_valid overlap J P c Q
  -----------------------------------------
  owned_valid overlap J (R ; P) c (R ; Q)
```

These statements add no no-unlock condition, no lock-free-frame condition,
and no new restriction on assertion syntax. The approved two-active-processor
assumption may be retained if needed; the resource lemmas will avoid it
where possible. Neither rule changes the safety or assertion definitions.

## Obligations searched before the general proofs

Write `K` for `*` in FRAME-SP and `;` in FRAME-TM. Starting from
`K(R,P,L)` and `pool ⊎ (F # L)`, find a grouped frame `G = F # R` with
`pool ⊎ (G # P)` and the required mode. During a program step `G` remains
exactly fixed. For every successor `P',pool'` allowed by that step,
composition, action transfer, footprint bound and mark budget, find `L'`
with `K(R,P',L')`, `pool' ⊎ (F # L')`, and the corresponding update bound
for `L -> L'`. The retained resource `R` is unchanged during the step.

Local-future closure is tested separately: every one-step local flush or
mark addition to `L` must admit a `K` split into actual futures of `R` and
`P`. The existing general future-splitting theorems remain available.

The search uses the checkpoint-3 executable resource relations, two active
processors, three addresses, values 0/1, all four mark sets, at most one
heap cell per input component, and at most three input pending writes in
total. Program steps are unchanged-memory steps, every enabled store to
these addresses, fences, acquisition and release. Store may add a fourth
write. Pools are empty or one cell; all are buffer-free and lock-free.
Successor local heaps and marks and candidate pools are exhaustively
enumerated within these bounds, including disappearance of heap ownership.
Successor buffers are recovered from the fixed frame and actual machine
buffer and independently checked by composition.

Input coverage combines an exhaustive family of same-processor overlapping
buffers with reproducible random sampling of the stated finite universe
(seed 7, 4,000 draws per rule/mode). It is not an exhaustive search of that
entire universe or of assertions/programs. Both input grouping and output
reconstruction are checked. Inactive processors, unbounded heaps/buffers,
arbitrary assertions, and arbitrary executions belong to the Rocq proofs.
Passing is evidence about these proof obligations, not a soundness theorem.

The script is `scripts/search_owned_frames.py`. Results are written to
`review/checkpoint-7-search.jsonl`. Any reported counterexample must be
checked in Rocq before changing a definition or rejecting a rule. If a rule
fails or needs a new condition, stop and report before parallel composition.
