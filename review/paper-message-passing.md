# Priority 1: the original message-passing program

**The Section 4.1 program has a checked derivation and its original
one-cell execution conclusion is recovered.** The proof uses the approved
token invariant and erases the untouched tokens operationally. There is
no auxiliary assignment, added fence, new assertion rule, program rule,
side condition or change to the safety definition.

This follows the [restated target](paper-priority-1-statement.md), the
[accepted design discussion](reviewer-guidance-after-audit-statement.md)
and the completed 4B/4C work. Ian authorized continuing through the queue
while the reviewer is offline. This report is a review checkpoint, not a
claim that the new proofs have already received independent review.

## Derivations

Use `C` for the existing writer-existential cell, `d` for address register 1
and `x` for result register 0. Processor IDs 1,2 represent the printed 0,1.

```text
T = C(t,0)                    U = C(r,0)
J = C(d,0) ∨ ((C(d,1) * T) ∨ (T * U))

sender   = acquire(1); [d] := 1₁; release(1)
receiver = acquire(2); x := [d]₂; release(2);
           if x=1 then ([d] := 2₂; fence₂) else skip

J ⊢ᴰᴶ {T} sender {emp}
J ⊢ᴰᴶ {U} receiver {(U ∧ x=0) ∨ (C(d,2) ∧ x=1)}
J ⊢ᴰᴶ {T * U} sender || receiver {(U ∧ x=0) ∨ (C(d,2) ∧ x=1)}
```

These are `mp_sender_derived`, `mp_receiver_derived` and
`mp_parallel_derived` in
[MessagePassingDerivation.v](../theories/MessagePassingDerivation.v).
The command definitions in
[MessagePassingSyntax.v](../theories/MessagePassingSyntax.v) contain no
token address. The receiver's unnecessary initial `x=0` condition was
dropped: its first load overwrites the register. The original precondition
is therefore covered as a special case.

All CONS and UNLOCK obligations use assertion proof trees. Nine
client-specific entailment derivations in
[MessagePassingAssertions.v](../theories/MessagePassingAssertions.v)
handle acquisition normalization, ownership exclusions, the three
donations and conditional selection. Seven reusable assertion helpers in
[AssertionClientRules.v](../theories/AssertionClientRules.v) and five
derived program helpers in
[OwnedClientRules.v](../theories/OwnedClientRules.v) supply spatial
rearrangement, pure framing, load under a spatial frame, and store/fence
completion. **No semantic resource-entailment premise remains in these
derivations. The basis still has 47 assertion and 21 program constructors.**

The syntax-level derivations are parameterized by the active domain and
the token addresses. The concrete adequacy theorem instantiates processors
1 and 2 and chooses distinct fresh token addresses internally. Ordinary
load and parallel variable conditions are discharged: only `x` is modified,
and `J` mentions only `d`.

## The original heap and conclusion

`message_passing_all_runs` in
[MessagePassingAdequacy.v](../theories/MessagePassingAdequacy.v) states:

```text
Initially: d = ℓ, heap = [ℓ ↦ 0], all buffers empty, lock free.

Every finite execution of sender || receiver avoids abort.
If the execution terminates:
  x ∈ {0,1}, heap = [ℓ ↦ x+1], all buffers empty, lock free.
```

There is no token resource, existential token choice, extra allocated-cell
premise or initial condition on `x` in that theorem. Its assertion
corollary, `message_passing_points_to`, establishes the **original
all-processor** `d ↦ x+1` at full completeness, together with `x=0 ∨ x=1`,
on the actual final memory.

The proof has three parts:

1. Apply `owned_derivation_adequacy` to `mp_parallel_derived` in the
   token-augmented initial memory. The final local postcondition is
   lock-free. With two processors it cannot own a held global lock, so
   the actual final pool satisfies `J`.
2. Extract the final data value. If `x=1`, the local data cell excludes
   both pool branches owning `d`. If `x=0`, the retained receiver token
   excludes the third branch. The first branch would lose the sender
   token from the whole memory. `execution_preserves_domain` excludes
   that branch, leaving data value 1. This uses exact physical domain
   preservation, not the safety predicate's one-way footprint bound.
3. Lift an arbitrary original execution by adding two unused cells, apply
   the augmented result, and remove the cells. The new general
   `execution_heap_extension` preserves the command, step count, stacks,
   buffers and blocked bits. `abort_heap_extension` preserves an abort
   when the accessed address is outside the added heap. The unchanged
   address register and `accesses_only` establish that condition for
   every reachable residual command. Original domain preservation then
   gives the exact singleton final heap.

[HeapExtension.v](../theories/HeapExtension.v) is an operational relation
between concrete machines, not another validity or safety predicate.
Successful-execution lifting is general; the abort lemma explicitly checks
that the extra heap does not supply the failing address. All relations
are pointwise, so no functional extensionality is used.

This recovers the requested execution conclusion. It is **not** a claim
that an `emp`-invariant derivation of the printed triple has been built.
No SHARE or AUX rule is smuggled into the calculus.

## Non-vacuity and search

[MessagePassingTrace.v](../theories/MessagePassingTrace.v) proves, for any
positive data address and any initial result register:

- `message_passing_zero_trace`: a complete **16-step** original-heap
  execution; the receiver finishes before the sender stores, ending with
  `x=0` and data value 1.
- `message_passing_one_trace`: a complete **20-step** original-heap
  execution; the sender finishes first, ending with `x=1` and data value 2.
- `message_passing_one_pending_trace`: its **17-step prefix** has the
  global lock free, physical data value 1, and the receiver's `d:=2`
  pending. `message_passing_private_write_pending` checks this state and
  the final value after flushing; the last three steps flush, advance the
  sequence and execute the fence.

The finite screening run is reproducible with
`python3 scripts/search_message_passing.py`; its full output is
[paper-priority-1-search.jsonl](paper-priority-1-search.jsonl).
It covers two processors, the data and two token addresses, nonempty cell
mark sets, all empty/lock mark sets, pending/flushed writes, acquisition
branch exclusions, release obligations and terminal pool cases with the
preserved domain. It found no counterexample. The general Rocq proofs,
not this finite search, establish validity over all permitted frames.

## What changes in the account of the dissertation

The [original-proof diagnosis](paper-priority-1-design.md#what-the-original-derivation-actually-does)
stands. The sender's auxiliary assignment is under `emp` inside ATOMIC's
premise; it is not itself an instance rejected by invariant freshness.
Export via ATOMIC is unavailable, the displayed parallel composition
modifies variables in its invariant, and SHARE/AUX are absent. This is a
failure to port that derivation as written, not a refutation of its
particular triple. The new result proves the same program's requested
physical conclusion by a different invariant and an explicit operational
argument.

No termination, fairness or deadlock-freedom claim is made. A wrong
guarded-choice branch can wait at a false assumption, as in the existing
language. Safety covers every finite prefix; final heap assertions apply
to terminal runs only.

## Validation and next work

The nine new theory files contain **1,025 physical lines and 79 audited
declarations**. The full project has **166 theory files, 27,053 physical
lines and 1,107 audited declarations**. `make check` passes, including the independent `rocq check`, with all
1,107 audited declarations closed and no axioms or admitted proofs.

The next queue item is priority 2A: named spinlocks derived under the one
physical lock, followed by the producer/consumer region client. The design
and explicit side conditions will be stated and screened before general
proofs. Restricted SHARE remains after those items in the latest order.
