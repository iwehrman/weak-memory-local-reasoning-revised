# Lead response: the buffered-pool candidate

The second candidate is substantially more promising. The requested
bounded checks pass **with disjoint frames and canonical full pool
marks**, and all six Dekker one-step premises pass the enumeration. I
prefer this route to the address-class design I previously suggested.

Two tempting stronger claims fail: histories are not insensitive to
marks, and the frameless transfer premise does not lift to overlap-mode
validity. Both choices are explicit in the candidate statement. Local
buffer uniqueness must also fix the returned pool, or speak about the
joint pool/local residual. These qualifications need review before a
general proof.

The artifact to review is **`86467ca9605d30469dc211c43cdc6fc2908a16a2`**.
The main build now has **1,341 audited declarations**. No general proof
of the second candidate, calculus extension, or machine-level Dekker
theorem has been written. `owned_safe`, `owned_derivation`, all existing
theorem statements, and `paper/` are unchanged.

## Accepted Stage 1 is in the main build

`DaringExtension.v` and `DaringCounterexamples.v` are registered in
`_CoqProject`, and their 25 audited proofs are in `Audit.v`. Ordinary
`make check` now includes them. The three paper references remain:

- `DaringCounterexamples.daring_load_extension_breaks_adequacy`
- `DaringCounterexamples.daring_load_honest_counterexample`
- `DaringCounterexamples.daring_store_honest_counterexample`

The withdrawn `DaringCandidate.v` remains outside the main build.
`BufferedPoolCandidate.v` is also outside the main build: its propositions
are statements to review, not established rules. `Makefile.daring`
checks this new statement file after running the main check. The old
candidate remains available only through `check-withdrawn`.

## Precise second-candidate statement

Read `review/buffered-pool-candidate-statement.md`, fixed before the
search, and `theories/BufferedPoolCandidate.v`.

The pool satisfies J at full completeness and may contain buffered
writes. It composes spatially with the repaired frame/local composition.
Every whole environment is unblocked; commands contain no lock or
unlock. The intended judgment is the **DJ** instance of this definition.
The OV instance exists only for comparison.

The fragment is the old guarded fragment plus
`(e ↣ u) ; e ⇝_i v`. This is an existing assertion, not a new atom. One
write per cell history suffices for this example; longer histories are
not claimed here. Fragment membership alone does not imply lock freedom,
since the existing pending-write atom permits blocked bits. The explicit
lock-free environment condition excludes those models.

The direct atomic premise quantifies over every full pool model of J,
every private model of P, and every lock-free spatial composition. It
requires no abort, and requires every actual result to split into a full
pool model of J and private model of Q. It checks the original joint
footprint bound and the original **private** mark budget. A disabled
fence has no result; it cannot be treated as an executed transfer.

Program steps retain the exact frame while allowing pool/local
repartition. Physical flushes belong to pool, frame or local, fixing the
other two. A pool flush keeps full marks; another component's flush adds
only its acting processor's mark. The safety definition retains full
local-future closure and quantifies environments afresh between steps.

SKIP, structural rules, FRAME-SP, CONC, ordinary private rules and
empty-frame adequacy are stated. There is no temporal-frame rule and
no two-processor assumption in this lock-free adequacy statement. The
Dekker instance uses two processors. The six exact premise propositions,
assertions and program are also defined in the `BufferedDekker` module;
none has a Rocq proof yet.

## Risk 1: marks

**Arbitrary re-marking fails.** For example, the flushed resource with
heap `d=1`, no buffers, and both processors marked satisfies

    (d ↣ 0) ; d ⇝_1 1.

Changing its marks to processor 2 alone makes that history false. The
flushed processor-1 write atom needs processor 1's mark. In the finite
family, 16 of 120 re-markings fail. Thus the old
`invariant_fragment_remark` cannot simply be extended to this fragment.

The candidate does not use that extension. A pool is interpreted at full
marks throughout. A physical pool flush is an existing generalized
future with those same full marks, so the proposed preservation route is
`persistent_assertion_flushing_closed`, without first re-marking a pool
for a borrower. All 24 full-pool history-future checks passed; the larger
marked-history family has 40 models and 96 future checks, also passing.

The private budget is measured against the private input, never against
the full-marked pool or the union of the two. The 64 budget checks include
eight attempts to acquire an unearned foreign barrier from an unmarked
private resource; all are rejected. A fence can add its own mark. These
checks are evidence against the obvious leakage, not a general theorem
about the new safety predicate.

Full pool marks now have semantic content. I am not describing them as a
harmless convention justified by mark-independence.

## Risks 2 and 3: fences and foreign loads

The physical checks distinguish all three cases:

- A fence on the processor with a pending **pool** write is disabled,
  regardless of local marks: 288 cases.
- After that pool write flushes, the fence is enabled: 288 cases.
- A different processor's pending pool write does not by itself block
  this processor's fence: 288 cases.

A foreign processor reads the old heap value before the write flushes and
the new value after it flushes. All 576 foreign-load cases are enabled,
non-aborting and return the predicted value. The owner forwards its own
pending value in 288 checks. Old/new values range independently over
0/1, with all four private mark sets and nine incoming stacks.

The framing checks additionally include 116 cases where the frameless
fence would be enabled but an external frame buffer makes the actual
fence wait. No postcondition is required before that physical step can
occur. Thus lending the pool for the premise does not ignore a real
buffer-draining requirement.

## Why the intended judgment is DJ

The unframed ownership-transfer premise fails for OV even at a true
assumption. Use

    J = (d ↣ 0) ∨ (e ↣ 0),  P = e ↣ 0,  Q = d ↣ 0.

Without a frame, the initial spatial split forces J to own d. The
assumption changes no memory, and the result can swap the cells: J owns
e, the local resource owns d. This satisfies the direct premise and the
private mark budget for all three nonempty private mark sets.

Now add an overlapping external frame owning e. The initial OV
environment is admissible. Every successor with Q local would have to
put e in the pool, which conflicts with the unchanged frame. Choosing d
for the pool conflicts with Q instead. There is no successor. The search
checks all relevant residuals, not just the natural swapped one.

DJ rejects that initial overlap. This is the same ownership-transfer
issue that restricted release in the active logic. For this new
lock-free judgment, where every atomic operation may transfer ownership,
I would use DJ throughout rather than introduce another transfer test.
That narrows the new judgment's allowed frames, but needs no new
composition and costs none of the six requested Dekker premises.

This is a substantive design choice for the reviewer to accept, not a
claim that the unrestricted OV atomic rule passed.

## Risk 4: primitive lifting, spatial framing and concurrency

The primitive-lifting search starts from 512 framed environments and
checks **every** frameless post-split within the footprint and mark
budgets, rather than selecting a helpful one. All 1,857 ordinary,
3,168 fence and 5,444 store post-splits extend with the exact external
frame. Its 1,604 read-projection checks also pass.

The regrouping search checks 3,248 input environments and **63,456**
successors: 11,504 ordinary, 18,224 fence and 33,728 store. All reconstruct
the retained spatial frame and the sibling's view. **49,744** successors
change the pool; **40,208** of those involve a buffered old or new pool.

The footprint argument now has the needed shape: the external frame is
disjoint from both the old pool and local resource. Repartitioning within
their combined footprint cannot acquire part of the frame. This was not
true for the overlapping case above.

These are memory-reconstruction and primitive-extension checks, not
proofs of FRAME-SP, CONC or the full step-indexed predicate. In particular,
transport across stack changes still needs the stated variable
conditions and a general proof. The tests do not establish arbitrary
nested parallel composition.

## Risk 5: buffers and three-way flush attribution

With pool **and** frame fixed, the local buffers cancel uniquely. With
only the frame fixed, the buffers of the **joint pool/local residual**
cancel. We must not claim uniqueness of the local buffers while the pool
may change: a pending cell history can move from pool to local at a
repartition, with the whole memory unchanged. The search includes that
counterexample to the stronger statement.

The fixed-component tests use 9,207 input triples, producing **18,495**
whole memories. Both cancellation checks pass in every case. All
**24,300** enabled flushes have the required attribution: 8,100 to each
of pool, frame and local. This includes **4,212** duplicate-head cases.

An additional family lets the pool own two different addresses on one
buffer. Across **5,304** whole memories, including **1,792** with both
addresses pending on one pool buffer, cancellation and all **6,680**
flushes pass (3,776 pool, 1,452 frame, 1,452 local).

Spatial separation prevents the same address from belonging to different
components; duplicates inside the owning component remain allowed and
are counted. A pool flush leaves the exact local and frame resources
fixed. It does not transfer a pool occurrence into a local residual.

## Dekker enumeration

The script and `BufferedDekker` definitions use the guidance's new
three-stage G and winner disjunctions exactly. Ghost payloads are fixed
to zero. The 13 distinct addresses name the two flags, ten per-thread
tokens and the prize. Script processors 0/1 mean Rocq processors 1/2.

There are **24 distinct full-pool memory models**: 16 in the no-winner
branch and four for each winner. A stored history has separate pending
and drained models. All **35** pool futures of these models again satisfy
J. Spatial separation restores the token exclusions the earlier
all-temporal proposal lost.

For each primitive, the search enumerates every pool shape that composes
with its private precondition, all three nonempty private mark sets, and
nine incoming stacks. The addresses and stored values are constants;
the incoming registers affect neither enabledness nor memory shape.

| Step | Compatible pool models | Inputs | Enabled steps | Waiting | Valid post-splits found |
|---|---:|---:|---:|---:|---:|
| Thread 0 store | 5 | 135 | 135 | 0 | 225 |
| Thread 0 fence | 10 | 270 | 135 | 135 | 315 |
| Thread 0 load | 5 | 135 | 135 | 0 | 225 |
| Thread 1 store | 5 | 135 | 135 | 0 | 225 |
| Thread 1 fence | 10 | 270 | 135 | 135 | 315 |
| Thread 1 load | 5 | 135 | 135 | 0 | 225 |

All **810 enabled steps** are non-aborting and have at least one
post-split satisfying J, Q, actual memory recomposition, the joint
footprint bound and the private mark budget. The 270 disabled inputs are
waiting fences, not vacuous preconditions. Different post-splits often
differ only in their permitted private marks.

There are 54 enabled fences that preserve the other processor's pending
pool write, and 54 loads with the other processor's write pending. The
loads return zero in 108 inputs and one in 162. All nine attempts to
spatially combine two final prize-owning resources fail, as required.

This enumerates all memory shapes and private mark sets of the **fixed
formulas** at those six steps. It is not a quantified Rocq proof, a
calculus derivation of the composed program, or an all-executions
mutual-exclusion theorem. It does not cover arbitrary symbolic address
expressions or ghost payload choices.

## Bounds and reproducibility

`review/buffered-pool-search-results.jsonl` is the exact output of
`scripts/search_buffered_pool.py`. The small searches are deterministic,
not random samples:

- Main buffer family: two processors, three component addresses, heap
  values absent/0/1, component buffers of length 0–2 on either processor,
  and at most three writes in total. Pool marks are full; private/frame
  heap resources use one mark, and empty-heap resources start unmarked.
  Separate mark searches cover the other mark choices.
- Additional pool-buffer family: four addresses, two owned by the pool,
  four pool heap layouts, pool buffers of length at most two and at most
  three total writes; frame/local use five focused profiles each.
- Primitive lifting: three addresses, eight pool profiles and nine
  profiles for each other component, at most two initial writes.
- Frame/parallel reconstruction: four addresses, eight pool profiles and
  nine per other component, at most two initial writes. A store can add
  one. The three action classes test memory effects; read projection is
  checked separately.
- Dekker: the 24 full-pool models described above, three private mark
  sets and incoming register values -1/0/1. There are no untested
  shuffle choices in these formulas: each pending flag has its own
  designated processor.

Run:

```sh
make check
make -f Makefile.daring check
python3 scripts/search_buffered_pool.py
```

The main audit has **1,341 audited declarations**, all closed
under the global context, without added axioms or admissions. The
candidate defines propositions but adds no proved declarations to that
count. A fresh local clone of `86467ca9605d30469dc211c43cdc6fc2908a16a2`
passed the entire overlay build and both kernel checks. It printed exactly
1,341 closed declarations, and the withdrawn candidate was not compiled.
The new search reproduced the committed JSONL output byte for byte.
This report is a separate commit so it can cite the exact validated
artifact.

## Recommended next checkpoint

I recommend accepting this candidate for a general proof attempt,
subject to review of the DJ choice and the explicit full-mark pool
interpretation. I prefer it to the address-class proposal: shared cells
and pending writes stay together, ghost exclusivity comes from the old
spatial composition, and invariant preservation can use the existing
assertion-future theorem. No new assertion atom, address class or separate
condition on external writes was added.

After approval, I would prove the full-pool flush lemma and the exact
primitive-extension/reconstruction lemmas first, then adequacy and the
atomic rule. The six Dekker premises can follow as small checked facts;
structural soundness and the composed machine theorem still need to be
proved. At this checkpoint I have stopped at the requested statement and
search stage.
