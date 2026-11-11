# Checkpoint 3 — temporal baseline proved; proposed `#` lemma refuted

**The temporal-only resource lemma is proved. The first generalization to
external `#` and internal `;` is false under the proposed assumptions.**
There are kernel-checked counterexamples for an assume-true step and for
acquisition from a nonempty, admissible invariant pool. Development stops
at this checkpoint; no new safety predicate or rule restriction has been
introduced.

The [statement recorded before searching](checkpoint-3-statement.md) fixes
the quantifiers, composition relations, completeness marks, resource futures,
footprint bound and overlap-permitting mode. The counterexample refutes an
auxiliary lemma, **not a derivation from design D's proof rules**.

## Search and proof outcomes

The deterministic search is in
[`scripts/search_frame_shape.py`](../scripts/search_frame_shape.py), with
[recorded output](frame-shape-search.jsonl). Run:

```sh
python3 scripts/search_frame_shape.py
```

The family has two processors, values 0/1, two buffer addresses, and a third
fresh address for the acquisition pool. Initially there is one pending write
in each of `F`, `R`, and `P`, all on the same processor; `F` and `P` write `x`
and `R` writes distinct `y`. The frame also owns a heap cell at `x`. Both
processors, both address orders, all 16 choices of the four 0/1 values (one
heap value and three writes), and all initially well-formed mark choices
are enumerated, subject to composition. A store can
increase the whole buffer from three to four writes.

The search enumerates all finite generalized futures and residual local
heaps/buffer subsequences in this family, with the local/pool footprint
bound. Local marks are preserved for assume/store/flush candidates; for
acquisition the acquirer's mark is added. Thus the failure does not rely on
assigning an unrelated new completeness mark to the local resource.

| Outer composition | Search outcome |
| --- | --- |
| `;` | 768 initial decompositions; 5,952 admissible residuals across assume, store, flush and acquire; no counterexample |
| `#` | Counterexamples for assume, store and acquire; 6,272 flush residuals without a counterexample in this family |

The `#` search stops checking an action once it has found its first failure;
its per-action counts are therefore not comparable coverage measurements.
These are bounded-family results, not exhaustive exploration of all small
memories. Python is only a discovery tool.

After reporting the search outcome:

- [`temporal_frame_shape`](../theories/FrameShape.v) proves the temporal
  baseline for arbitrary well-formed resources and processor domains. It
  uses the existing future-splitting theorem and temporal associativity.
  There are no protected/private assertion slots in its statement.
- [`FrameShapeCounterexample.v`](../theories/FrameShapeCounterexample.v)
  checks the initial decompositions, an actual machine step, the abstract
  frame future, the final decomposition, the footprint bound, and the
  **nonexistence of any reconstruction** for both assume and acquisition.
  The store witness remains search evidence, not a separately checked theorem.

## The smallest reported obstruction

All listed buffer entries are on processor 1, oldest first. Let `X` mean
`x := 0` and `Y` mean `y := 0`, with distinct addresses.

| Component | Heap | Buffer | Completeness |
| --- | --- | --- | --- |
| External frame `F` | `x = 0` | `[X]` | `{1}` |
| Retained assertion resource `R` | empty | `[Y]` | empty |
| Local resource `P` | empty | `[X]` | empty |

Initially `R ; P` has buffer `[Y,X]`. A valid outer `#` composition gives
the whole buffer `[X,Y,X]`. Regrouping the external and retained frames gives
`G = F # R` with heap `x = 0` and buffer `[X,Y]`.

The whole machine takes `assume true`; its memory does not change. The
proposed lemma nevertheless permits this residual decomposition:

```text
G' : heap x = 0, buffer [Y]      a genuine abstract flush-future of G
P' : empty heap, buffer [X,X]    still mentions only P's original address x
G' # P' : heap x = 0, buffer [X,Y,X]
```

The abstract flush of `G` writes the value already in its heap, so the heap
still matches. The pending occurrence removed from the frame is assigned
to `P'`. The decomposition preserves the whole buffer and obeys the
location-based footprint bound.

But reconstruction is impossible. A future of `F` cannot contain `Y`, and
`G'` contains only `Y`. Therefore any split of `G'` into futures of `F` and
`R` has an empty frame buffer and retained buffer `[Y]`. The required
`R' ; P'` then has `[Y,X,X]`. An empty external buffer cannot turn that
into the actual `[X,Y,X]`.

`no_reconstruction` proves this even without requiring `R'` to be a future
of `R`: the frame's future and the two buffer shapes already suffice.
Completeness marks are included in all compositions; changing them cannot
fix the conflicting buffer order.

## Acquisition also fails the proposed lemma

The second checked witness adds an initially shared cell `z = 0`, spatially
disjoint from `F # (R ; P)`. Its invariant is the checkpoint-2 cell formula
`C(z,0)`, proved to be in the fragment and satisfied by the pool.

Processor 2 acquires the lock. Its buffer is empty, so this is an enabled
machine step. The pool becomes empty, and the chosen local residual contains
`z`, the lock token, and exactly processor 2's completeness mark. Its footprint
is contained in the old local footprint plus the pool's footprint.

The same erroneous reassignment leaves `[Y]` in `G'` and `[X,X]` in the local
residual, although the whole pending buffer remains `[X,Y,X]`. The checked
`overlap_acquire_frame_shape_counterexample` includes the pool separation,
invariant satisfaction, actual acquisition, owner-only local marks, empty
final pool, footprint bound, and failure of reconstruction. Thus including
ownership growth does not rescue the proposed lemma.

## Consequence for the plan

The footprint bound controls **which addresses** the local resource can
own. It does not control **which pending occurrences** it can acquire from
an overlapping frame. The failed lemma quantifies over every residual
decomposition satisfying that bound. Its assumptions are insufficient.

This does not establish that FRAME-TM, acquisition, or design D is unsound.
For example, the ordinary local execution of `assume true` leaves one local
`X`; it does not create the two occurrences in the bad witness. A full
semantic validity premise, or a construction tied to the primitive action,
could supply information that the refuted structural lemma omits.

My preferred next investigation is a replacement lemma about residuals
constructed from the actual local action and corresponding flush events,
preserving the contribution of each component. It would need to show that
this choice is available throughout consequence, sequencing, framing and
concurrency. Such a proof could leave the user-facing rules unchanged.
This is a proposed proof strategy, not a theorem or a silently added
condition. Simply requiring disjoint external/local footprints would exclude
this witness but would give up the overlapping temporal reasoning that the
`ov` mode is intended to support.

No new validity predicate, assertion atom, entailment change, or program
side condition has been added. The spatial and strong-temporal cases and
the complete container command derivation remain open. A new safety model
should wait until the replacement residual lemma is agreed and tested.

## Validation

Both proof modules are in `_CoqProject`, and their four principal results
are in `Audit.v`. `make check` passed, including the independent proof-object
check; all 389 audited declarations reported `Closed under the global context`.
There are no admitted proofs or added axioms. The Python witness is not used
as an axiom or trusted computation in either Rocq counterexample.
