# Priority 2B: arbitrary-length producer/consumer mailbox

**The region mailbox is derived for an arbitrary finite message, including
the empty message.** The producer fills the cells with ordinary stores,
uses the derived named lock, and donates them without a fence. The consumer
retries until full, withdraws the cells, releases the named lock, and reads
them privately. Every assertion obligation is a proof tree in the same
47-constructor basis; the program calculus still has 21 constructors.

This completes the part-B target from the
[named-lock design](paper-named-locks-design.md). The
[buffered-contract statement](paper-mailbox-statement.md) records the
additional derived interfaces before their proofs. This batch awaits
independent review along with the earlier offline checkpoints.

## The generic client

The parameter is a list `items` of positive addresses and integer values.
Its length is `K`; no fixed-size fallback is used. Write `D(items)` for the
spatial product of the corresponding writer-existential cells, with unit
`emp`. The two reserved flags have addresses 1 (named lock) and 2 (mailbox):

```text
I = C(2,0) ∨ (C(2,1) * D(items))
J = ((C(1,0) * I) ∨ C(1,1)) * emp

producer:
  fill each message cell with its specified value;
  acquire_named(1, processor 1, scratch 0);
  [2] := 1₁;
  release_named(1, processor 1)

consumer:
  repeat using a while loop:
    acquire_named(1, processor 2, scratch 1);
    scratch 1 := [2]₂;
    if full:
      [2] := 0₂; release_named(1, processor 2); mark loop done
    else:
      release_named(1, processor 2); mark loop to retry;
  read every message cell privately
```

The retry status uses the existing scratch register. The private loads
reuse register 2; the specification records ownership and contents of the
entire region, not a vector of returned registers. Each load is justified
by its cell's specified value. No assertion instruction, allocation,
auxiliary ownership atom or recursive assertion constructor is introduced.

The main derivation, `mailbox_parallel_derived` in
[MailboxDerivation.v](../theories/MailboxDerivation.v), is:

```text
J ⊢ᴰᴶ {D(zero-filled addresses(items))}
       producer(items) || consumer(items)
       {D(items)}.
```

The producer and consumer theorems are separately available as
`mailbox_producer_derived` and `mailbox_consumer_derived`. The parallel
conditions are proved: the producer modifies only register 0; the consumer
modifies only registers 1 and 2; the invariant and region assertions are
closed. All CONS/UNLOCK applications, including loop and cell-access
helpers, use assertion derivations. There are no remaining semantic
resource-entailment obligations in this client.

## Buffered contracts for the unchanged named-lock code

The simple part-A interfaces forget draining information. The new
`named_lock_acquire_retained_family` and
`named_lock_release_buffered_family` in
[NamedBufferedRules.v](../theories/NamedBufferedRules.v) prove:

```text
J ⊢ᴰᴶ {R} acquire_named(l,i,x) {I_l * (R ; bar(i))}

A ; bar(i) ⊢ₐ I_l       I_l * I_l ⊢ₐ false
------------------------------------------------
J ⊢ᴰᴶ {A} release_named(l,i) {emp}.
```

Only the existing scratch freshness requirements and explicit assertion
proofs appear. There is no change to the named-lock implementations, the
machine, safety or the interpretation of `bar(i)`.

The proof keeps retained resources inside the physical UNLOCK premise.
Barrier distribution completes the acting processor's writes. A failed
acquire attempt discards that extra information and retries; the successful
attempt exposes it. This avoids temporally framing a macro containing a
release. For buffered named release, completing `A` inside the final
physical release premise yields `I_l`; its exclusivity certificate rejects
the already-free flag branch at that point. No early completeness claim
is made while the write is still pending.

`history_family_complete` in [RegionRules.v](../theories/RegionRules.v)
performs this completion for an arbitrary product of cell histories.
`fill_region_derived` and `read_region_derived` prove the two region
operations by induction over the list. `mailbox_exclusive` in
[MailboxAssertions.v](../theories/MailboxAssertions.v) uses the mailbox
flag, so the invariant is exclusive even when `K=0`.

The zero-length case is handled explicitly by the general proof: a cell
product admits contraction because it is `emp` when empty and exclusive
otherwise. This permits a single producer derivation for all lengths,
without adding `K>0` or changing the invariant fragment.

The buffered named-lock contracts were screened before their general
proofs by `scripts/search_named_buffered.py`. The
[recorded output](paper-named-buffered-search.jsonl) covers both actors,
all mark choices, own and foreign pending/flushed retained writes, both
named-flag branches and buffered return. No counterexample was found.
These finite checks are not the proof of the arbitrary-list theorem.

## Actual initial memories and all finite executions

`mailbox_all_runs` in
[MailboxAdequacy.v](../theories/MailboxAdequacy.v) specializes derivation
adequacy to an actual initial memory, for any `items`:

- flags 1 and 2 contain zero;
- each message address contains zero;
- processor 3 has one unrelated `foreign := 17` write pending;
- other buffers are empty and the physical global lock is free.

Its layout condition is `NoDup (1 :: 2 :: foreign :: addresses(items))`.
This is the ordinary distinct-address condition for the concrete allocated
layout, stated in the design. No token erasure or extra ghost allocation is
needed. The domain is processors 1,2,3; the two-active-processors hypothesis
is discharged internally.

Every finite execution avoids abort. On termination, the actual final
memory splits into a restored invariant pool and the local postcondition
`W(foreign,3,17) * D(items)`, and the physical lock is free. The foreign
write assertion allows a pending or flushed write; arbitrary executions
may flush it. Remaining pending throughout is a property of the concrete
witness below, not a restriction on all executions.

## Non-vacuity: transfer, retry and foreign pending write

[MailboxTrace.v](../theories/MailboxTrace.v) instantiates two message cells,
addresses 3 and 4 with target values 7 and 9, and foreign address 5:

- `mailbox_parallel_trace` is a **95-step** complete execution of the actual
  parallel program. The producer completes first, then the consumer.
- `mb_fill_trace` reaches a state with both producer writes pending while
  the shared message cells still contain zero. No fence instruction occurs
  in the client or named-lock implementations. The acting buffer is flushed
  before the relevant physical lock acquisition can proceed.
- `mailbox_foreign_pending_throughout` checks processor 3's pending write
  in the memory states used by both traces, including the internal
  acquire/store/flush/release states of the named operations.
- `mailbox_trace_contents` checks both final flags are zero, the message
  contains 7 and 9, processors 1 and 2 have empty buffers, processor 3's
  write remains pending, the physical lock is free, and the last private
  load put 9 in register 2.
- `mailbox_failed_iteration_retries` is a **41-step** iteration from an
  empty mailbox back to the same retry loop, with the physical lock
  released. It does not assume a successful mailbox read.

`mailbox_example_all_runs` applies the generic theorem to this inhabited
two-cell configuration. The trace is a witness, not the sole safety claim.

The status remains partial correctness: the guarded-choice language can
wait on a false assumption, and no fairness, deadlock-freedom or termination
theorem is claimed. The trace is fixed at two cells; the derivations and
the actual-initial-memory adequacy theorem are fully list-parametric.

## Validation and remaining queue

The nine new theory files contain **956 physical lines and 75 audited
declarations**. The complete checked development has **182 theory files,
28,865 physical lines and 1,232 audited declarations**. `make check` passes, including the independent `rocq check`, with all
1,232 audited declarations closed and no axioms or admitted proofs.

The main remaining queue item is restricted SHARE with semantic lock-free
pre/postconditions, treating disjoint and overlap mode questions separately.
The earlier retrying-container module still contains some old semantic
entailments; the original container and the new retrying mailbox use
assertion proof trees throughout. No completeness/automation result is
claimed for the assertion calculus.
