# Retaining history after returning ownership

**Status after independent review: not the development direction.** The
review checks an additional defect: permissive later cell atoms can erase
unrelated earlier cells (`retired_later_cell_can_erase_earlier` in
`review/Review.v`). Together with the loss of `emp`'s right-unit law, this
rules out continuing this interpretation as the preferred repair. The
proofs below retain their stated, limited meanings. See
[the review](../review/independent-review.md) and
[the development response](../review/lead-response.md) for the replacement
direction and required checkpoints.

The retirement experiment proves both directions of cell transfer, including
at unlock, together with the original variable condition for FRAME-TM. It
resolves the overlapping-heap obstruction **in a buffer-free fragment**.
It is a separate interpretation and validity predicate, not a replacement
for the buffer-aware separated calculus. Full corrected soundness is still
open.

There is also a checked bridge toward buffered histories: masking relinquished
heap observations commutes with arbitrary finite flush sequences when no
pending write targets a masked address. The existing stable compatibility
condition supplies that premise for addresses owned by the current heap.
This does not yet establish flushing decomposition or assertion closure for
a complete retirement-aware buffered model.

## What changes in assertions

An entry at an address now has three possible states:

| Entry | Meaning for current ownership |
| --- | --- |
| Absent | This resource says nothing about the address |
| Live value | This resource owns a cell containing that value |
| Retired | This resource has relinquished the address |

Temporal composition uses the later entry when present. In particular,
retirement overrides an earlier live entry. Spatial composition requires
disjoint **live** heaps; retirement is not ownership. Temporal associativity,
spatial commutativity, and spatial associativity are proved, including the
definedness conditions for spatial composition. The implementation uses
pointwise relations and needs no functional extensionality or choice.

The assertion grammar is reused. Its private interpretation changes:

- `emp` means that there are no live cells. It may contain retirement entries.
- A flushed cell requires a live cell at its address. Retirement does not
  satisfy that assertion.
- A barrier has no address entries, including retirement entries. This keeps
  a cell followed by a barrier live, as the `processor_cell` abbreviation
  requires. Completeness marks remain a separate field.
- Private lock atoms are false: the lock stays in the protected compartment.
- Writes in this fragment describe flushed cells only. Pending-write atoms
  are not modeled here.

The exact lost entailment is checked in both interpretations:

```text
Previous persistent interpretation:
  processor_cell(i,x,v) ; emp  entails  processor_cell(i,x,v)

Retirement interpretation:
  that entailment is false
```

`prior_processor_cell_emp_entails_current` proves the first claim;
`RH.historical_cell_emp_is_not_current` supplies the second model. Thus this
repair changes assertion reasoning, despite adding no syntax constructor.
It cannot preserve every previous entailment unchanged.

The change is intentional: after returning a cell to the pool, `R ; emp`
may remember its old value through the temporal decomposition without
granting present access. A program must reacquire ownership before using
that remembered cell as a current cell. The private load rule requires a
live cell, and `retired_pool_excludes_private_cell` proves that a protected
cell cannot simultaneously be live in the private compartment.

## Transfer and frame rules

The protected and private assertion positions remain separate. Let
`C = processor_cell(i,x,v) = write(i,x,v) ; barrier(i)`.

```text
Open {lock(i) * S | C}
    fence(i)
Open {lock(i) * (S * C) | emp}

Invariant J = S * C:
Open {lock(i) * S | C}
    unlock(i)
Closed {emp | emp}

Open {lock(i) * (J * C) | emp}
    unlock(i)
Closed {emp | C}
```

Donation installs a retirement entry in the private resource. Withdrawal
replaces it with a live entry and adds only the issuing processor's mark.
Protected completeness is not copied into the private resource. The first
rule transfers while keeping the lock; the latter two transfer at unlock
without an additional machine fence.

`retired_FRAME_TM` proves the general semantic rule across arbitrary phase
boundaries, for every assertion in this interpretation:

```text
{S | P} c {T | Q}       mod(c) intersect FV(R) = empty
----------------------------------------------------
{S | R ; P} c {T | R ; Q}
```

There is no disjointness condition on the retained heap history. Reassociation
of temporal composition proves framing, and the external history is retained
exactly. Register agreement handles modifying commands such as loads.
The restriction is instead explicit in the model: all private and external
histories have empty buffers, and the protected pool must also have empty
buffers. The actual machine transition relation is unchanged.

`retired_calculus_sound` proves a small derivation system with skip,
acquire/release, donation, withdrawal, private loads, sequence and FRAME-TM.
No constructor assumes program validity or safety. Execution adequacy checks
every finite execution from an admissible initial environment; it does not
claim termination or fairness.

## Nonempty examples

Both examples start with processor 1 holding the lock, a private cell
currently containing 7, and a retained earlier value 5 at the **same address**.
The pool initially contains only the lock token.

1. **Return at unlock.** The invariant requires the cell in the pool once
   the lock is free. An actual unlock restores this invariant. All executions
   are safe. On termination the protected cell contains 7, the private
   resource no longer owns it, and the earlier value 5 is still described by
   `R ; emp`. The one-step terminating trace is checked.

2. **Return, withdraw, read.** Under an empty invariant, an owner fence
   donates the cell while the lock is held. Unlock takes it back, restoring
   the empty pool. A subsequent private load returns 7. FRAME-TM retains the
   earlier value 5 throughout, including the intermediate `R ; emp` state.
   Safety and the result register are proved for all executions; the
   five-step terminating trace is checked.

These start at concrete open states. They are not complete concurrent
container examples, and the experiment has no concurrency composition rule.

## The buffered bridge and its limit

`mask_history` removes selected heap observations while preserving every
pending write and the blocked set. `retirement_flush_simulation` and
`retirement_flushes_simulation` prove that the masked history can match every
actual flush, provided no pending write targets a masked location. Other
buffers may remain nonempty. The proof preserves their FIFO behavior and
does not require a finite processor domain.

`stable_history_can_retire` derives this premise from the existing
`stable_compatible` relation when the masked locations are in the current
heap. Therefore the bridge does not impose an additional whole-machine
drain on a currently owned, flushed cell. Conversely,
`masking_a_pending_write_does_not_commute` checks why a pending write cannot
itself be discarded as history: it can still flush and change the live heap.

The remaining work is to build and check the combined buffer/retirement
composition, its compatibility and associativity, generalized-future
decomposition with completeness marks, and assertion closure including
wands. Then the transfer and frame proofs must be ported to that model and
tested with genuinely pending foreign histories and the foreign-barrier
counterexample. The current buffer-free experiment cannot test that
counterexample; its rejection remains proved only in the preceding separated
model.

The combined-footprint bound from `separated_safe` is not yet part of
`retired_safe`; progress is constrained by exact machine reassembly instead.
No general spatial frame or parallel theorem is asserted for this new
validity. Those ownership bounds and composition obligations must be settled
before integrating it with the rest of the logic.

All principal declarations are in `Audit.v`. The experiment adds no axioms,
admitted proofs, choice, extensionality, or finite-processor assumptions.
