# Checkpoint 7 — spatial and temporal framing proved

**FRAME-SP is proved in both modes, and semantic FRAME-TM is proved from
overlap-mode validity.** The bounded searches ran before the general proof
attempt and found no counterexamples. The proofs need no change to the
safety definition, assertion language, entailments, or machine semantics.
Development stops here, before the parallel-composition rule, as requested.

Following the accepted checkpoint-6 review, FRAME-STM is omitted from the
current target. Its assertion abbreviation remains unchanged. LOAD and
STORE with the dissertation's strong-temporal assertions still need to be
checked against `owned_safe`; those axioms have not been justified by
dropping the frame rule.

## Exact rule statements

[`OwnedFraming.v`](../theories/OwnedFraming.v) proves:

```text
FRAME-SP — either mode k:
    owned_valid k J P c Q       mod(c) ∩ fv(R) = ∅
    ------------------------------------------------
    owned_valid k J (R * P) c (R * Q)

FRAME-TM — overlap mode:
    invariant_fragment J
    owned_valid overlap J P c Q       mod(c) ∩ fv(R) = ∅
    ---------------------------------------------------
    owned_valid overlap J (R ; P) c (R ; Q)
```

The principal declarations are `owned_spatial_frame_valid` and
`owned_temporal_frame_valid`. Their same-index safety versions are
`owned_safe_spatial_frame` and `owned_safe_temporal_frame`.

Both cover arbitrary assertions, including wands, pending writes, and lock
tokens in the retained frame. Neither requires a lock-free frame, a
syntactic no-unlock condition, finiteness, or two active processors.
The processor hypothesis remains on the previously proved lock rules and
client adequacy theorem. No hypothesis was removed from those results.

FRAME-SP is slightly stronger than the requested target: it does not need
`invariant_fragment J`. FRAME-TM uses that existing fragment hypothesis to
obtain empty pool buffers. Its overlap-mode premise is essential to the
statement proved here. It cannot be applied directly to the general
disjoint-mode UNLOCK specification. A later derivation system still needs
to track which specifications have overlap-mode validity; no-unlock may be
one sufficient syntactic criterion there.

## Bounded searches, before the general proofs

The statements and bounds were fixed in
[`checkpoint-7-statement.md`](checkpoint-7-statement.md).
[`search_owned_frames.py`](../scripts/search_owned_frames.py) checks the
resource reconstruction obligations used by each rule, plus one-step
local-future splitting. The recorded output is
[`checkpoint-7-search.jsonl`](checkpoint-7-search.jsonl).

| Rule and mode | Admissible input environments | Admissible program successors reconstructed | Local-future checks |
| --- | ---: | ---: | ---: |
| FRAME-SP, overlap | 11,485 | 139,620 | 25,585 |
| FRAME-SP, disjoint | 1,947 | 17,943 | 25,585 |
| FRAME-TM, overlap | 4,974 | 45,956 | 10,314 |

Every row completed with no counterexample. The program successors include
stores, fences, acquisition and release, as well as unchanged-memory steps.
The local-future checks include mark-only additions and actual local
flushes. Acquisition and release both have nonzero successor coverage in
every row.

The finite universe uses two processors, three addresses, values 0/1, all
four mark sets, at most one heap cell per input component and up to three
input pending writes. A store may add a fourth. An exhaustive overlapping
buffer family exercises same-address writes in the external frame and
local resource, including identical writes. Seed-7 sampling adds 4,000
draws per row from the stated finite universe, including held-lock states
and buffer-free pools. All admissible bounded local successors and candidate
pool transfers are checked for each selected input and step.

This is **not** an exhaustive search of that whole universe, assertion
syntax, or Hoare validity. It searches sufficient reconstruction obligations
for the two rule statements. The Rocq theorems establish the unbounded
semantic rules independently of the script and its sampling choices.

## Why the reconstruction works

### One fixed grouped frame within a program step

From `pool ⊎ (F # (R * P))`, or `pool ⊎ (F # (R ; P))`,
`owned_environment_unframe` obtains a grouped frame `G = F # R` and an
environment `pool ⊎ (G # P)`. In disjoint mode the spatial split gives the
additional disjointness needed by the smaller view. Overlap mode needs
no such premise.

The source safety theorem supplies a successor with this exact `G`.
`owned_environment_reframe` reassociates the successor to
`pool' ⊎ (F # (R # P'))`. The retained `R` and original external `F` have
not changed during this program step. Frames are still quantified afresh
by the recursive safety obligation; no fixed-frame requirement was added
between successive machine steps.

### Spatial framing: use the footprint bound

`owned_spatial_reconstruction` upgrades `R # P'` to `R * P'`.
Initially `R` is disjoint from `P` and from the invariant pool. The
successor footprint bound restricts `P'` to the old `P` plus the old pool,
so it remains disjoint from `R`, including across acquisition. Ordered
merging already supplies the required interleaving.

`owned_update_frame` then proves the larger update's action transfer,
footprint bound, and mark budget. At acquisition and release, the original
environment and complete-token requirements imply the necessary absence
of blocked bits in the retained frame. No lock-free-frame premise is added
to the theorem.

### Temporal framing: cancel against the same physical step

Non-flush program steps either leave buffers unchanged or append exactly
one write to one processor's buffer. `program_step_buffer_shape` proves
this for every command constructor, including sequence and parallel
operational steps.

Since the pool is buffer-free, both the original and successor owned
environments supply ordered buffer merges with their fixed external
frames. `ordered_fixed_frame_prefix` applies the checkpoint-4 residual
uniqueness theorem twice: once with `F`, and once with `G = F # R`.
Both cancellations use the same actual machine change. Consequently,
if the original owned buffer is `R ++ P`, the new one is `R ++ P'`.
This proves the required temporal ordering without allowing a frame to
silently flush or a local residual to take a frame's pending occurrence.

The remaining temporal requirement concerns completeness marks in `P'`.
An inherited mark already required the corresponding buffer of `R` to be
empty. An earned mark can only come from fence, acquire, or release;
`program_step_earns_empty` proves that the actual machine step required
that entire processor buffer to be empty. Therefore `R`'s buffer was empty
as well. `owned_temporal_reconstruction` combines this argument with the
buffer cancellation and the unchanged heap/blocking composition.

### Full safety, not only one-step algebra

Both same-index frame theorems handle every generalized local future using
the existing spatial or temporal future-splitting theorem and assertion
flushing closure. This includes mark-only futures and locally possible
flushes blocked in the whole machine. Terminal assertions, non-aborting
behavior, arbitrary program successors, and recursive safety are all
covered. The standard variable condition preserves the retained assertion
when a program step changes the stack.

## Concrete uses of the proved rules

[`OwnedFramingExamples.v`](../theories/OwnedFramingExamples.v) checks four
additional declarations:

- `owned_counterexample_spatial_frame_valid` applies FRAME-SP to the exact
  release specification from checkpoint 6. Its spatially framed triple is
  valid, while the original strong-temporally framed triple remains
  invalid. The existing inhabited precondition and enabled release witness
  remain unchanged.
- `owned_holder_spatial_store_valid` retains the lock token and invariant
  cell as a spatial assertion frame while processor 2 stores to its private
  cell. The specification holds in both modes.
- `owned_pending_temporal_lock_valid` retains a genuine pending processor-2
  write before processor 1 acquires the invariant. Its postcondition has
  the expected processor-1 barrier suffix inside the temporal frame.
- `owned_pending_temporal_lock_enabled` supplies a satisfying precondition,
  admissible environment with a nonempty pool, and an actual acquisition
  transition for that temporal example. The foreign write is still pending
  in the initial buffer; this is not an empty-history or stuck-command test.

## Validation and next review boundary

`make check` passes, including the independent proof-object check. All
**486** audited declarations report `Closed under the global context`,
including all 19 new declarations in the framing and example modules.
No admitted proofs or axioms were added.

No new validity predicate, assertion constructor, assertion interpretation,
mode, or side condition was introduced. The general parallel rule has not
been started. That is the next requested step after review: combine two
component safety proofs, using spatial framing when one thread finishes.
The full container derivation and the dissertation's strong-temporal
LOAD/STORE axioms for this target also remain open.

Overlap-mode FRAME-STM and any derivation of the checkpoint-6 counterexample
in the printed calculus remain conjectural questions. Neither is needed
or asserted by these results.
