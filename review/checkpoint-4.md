# Checkpoint 4 — fixed-frame buffers and actual flush attribution proved

**Both proposed lemmas pass and are proved in Rocq.** Duplicate writes are
allowed. No new safety predicate, rule side condition, assertion atom, or
entailment change has been introduced.

The [statements recorded before the search](checkpoint-4-statement.md) fix
the quantifiers and scope. The [search](../scripts/search_residual_flush.py)
uses the existing checkpoint-3 executable relations; its
[recorded output](checkpoint-4-search.jsonl) is reproducible with:

```sh
PYTHONDONTWRITEBYTECODE=1 python3 scripts/search_residual_flush.py
```

The bounded searches ran first, and their passing results were reported
before the general proofs were written. Python supplies discovery evidence;
the Rocq theorems do not trust or import the search output.

## Residual uniqueness

[`ordered_residual_unique`](../theories/ResidualUniqueness.v) proves:

```text
ordered_overrides F L W
ordered_overrides F L' W
-----------------------
L = L'
```

This is equality of the entire buffer, including order, values and
multiplicity. It needs no disjointness, unique-write assumption, or fixed
length bound. The memory and resource corollaries give equality of local
buffers for every processor. In fact, equality of the two output buffer
arrays suffices; the outputs' heaps and marks need not be equal.

The reason is stronger than agreement of final lookups. When the next output
write's address still occurs in the frame, ordered overriding forbids taking
that write from the local buffer. If it does not occur in the frame, the
write must be local. In a valid merge these choices determine the residual
buffer, including the order between different addresses.

The search checked all **7,225 frame/local input pairs** of buffers of length
0–3 over two addresses and values 0/1, producing **19,745 ordered merges**.
There was no pair of different local buffers for the same frame/output pair.
The proof covers arbitrary finite buffers and arbitrary processor domains;
no finite-processor assumption is needed.

## Flush attribution with the pool fixed

[`pooled_flush_attribution`](../theories/FlushAttribution.v) first removes
the pool from a particular machine flush and then applies the existing
indexed ordered flush decomposition inside `#`.

The marked-resource theorem `pooled_resource_flush_attribution` proves that
an actual flush on processor `i` of

```text
pool spatially composed with (F # local)
```

can be represented by a single actual flush of either `F` or `local` on the
same processor. The other resource, including its completeness marks, stays
exactly fixed. The pool also stays fixed, and the final components recompose
to the actual resulting machine memory.

The affected resource gains exactly `{i}` in addition to its previous
completeness set. Its proof uses `GeneralizedFlush` once, not a mark-only
change or an arbitrary abstract future. No unrelated mark is added.

The pool must have empty buffers. This is already supplied by the accepted
guarded invariant fragment; `invariant_pool_flush_attribution` connects the
two results. It also holds for an empty pool. Without that premise a write
in the pool could itself flush, so a two-way frame/local statement would be
incorrect. This is not an additional restriction on the accepted invariants.

The physical search covered **629,424 enabled machine flushes** from
738,915 pool compositions. It enumerated two processors, arbitrary frame/local
heaps on two addresses with values 0/1, up to three pending writes across the
four buffers, compatible complete-lock blocking assignments, and an empty
or one-cell disjoint pool on three possible addresses. All physical search
resources were fully marked; the general resource proof handles arbitrary
initial marks and the precise mark gained by a flush.

## Duplicate writes do not create the suspected ambiguity

In **22,104** searched cases both source buffers had exactly the same next
write. Each surviving attribution was to the frame. No machine flush in
the searched family admitted both attributions.

Two general checked results explain the duplicate case:

- `ordered_duplicate_head_from_frame`: if the frame and local buffers both
  start with the same write, the next merged occurrence comes from the frame.
- `local_flush_cannot_pass_frame`: flushing a local write while a frame write
  to that address remains would put the address into the local heap, violating
  stable compatibility with the still-pending frame write. No such final `#`
  composition exists, even if the values are identical.

The main attribution theorem states existence of one of the two alternatives;
it does not package a general exclusive-or theorem for arbitrary memory
witnesses. The duplicate-head case has the separate general proofs above.

## Direct checks against checkpoint 3

[`FixedFrameExamples.v`](../theories/FixedFrameExamples.v) proves that keeping
the regrouped frame `G` fixed excludes both checked bad decompositions from
checkpoint 3:

- the local residual with two pending `X` writes after `assume true`;
- the local residual with those two writes after acquiring the fresh pool cell.

Both would have to have the same buffers as the original one-write local
resource, by residual uniqueness. The contradiction also holds in the
acquisition case, where the whole heap and lock state legitimately change
but its buffers do not.

## What this permits next, and what it does not prove

These results support the proposed safety change: non-flush program steps
leave the external frame unchanged, and actual machine flushes are handled
by attribution plus local flushing closure. They remove the two specific
obligations requested for checkpoint 4. They do not yet prove the complete
frame rule, soundness of design D, concurrency, or the container derivation.
Buffer uniqueness also does not imply uniqueness of a local heap or mark set.

The new single target would **replace `separated_safe` / `separated_valid`
as the active development path**. It would combine the owned assertion into
one resource, retain a separate invariant pool, and use the proposed
overlap/disjoint modes. Its unchanged-frame clause is a genuine change from
the existing program-step clause, which admits arbitrary frame futures.
Existing theorems about earlier predicates will retain their old meaning;
they are not automatically proofs about this replacement.

No target predicate has been written. Before doing so, the next checkpoint
should specify its complete definition, including the distinction between
non-flush program steps and local closure, step indices, marks, lock
ownership, pool shape, and the two modes. That definition should be reviewed
as the one intended soundness target, rather than added as another independent
experimental validity family.

## Validation

The three new modules are included in `_CoqProject` and their 12 principal
declarations in `Audit.v`. `make check` passed, including the independent
proof-object check. All **401** audited declarations reported `Closed under
the global context`; there are no admitted proofs or added axioms. No search
result is assumed by the proofs.
