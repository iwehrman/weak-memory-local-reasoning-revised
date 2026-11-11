# Checkpoint 4 — statements before the search

No safety predicate is defined at this checkpoint. The two proposed properties
are tested against the existing ordered `#`, stable compatibility, generalized
resources, and machine flush relation.

## 1. Residual buffer uniqueness

At the single-buffer level, state:

```text
ordered_overrides F L W and ordered_overrides F L' W imply L = L'.
```

The frame buffer and whole buffer are fixed, including order, values and
multiplicity. There is no disjointness hypothesis, and identical writes may
occur repeatedly in both components.

Lift this pointwise to memories/resources: two `#` compositions with the same
frame and the same underlying output memory have equal local buffers for
every processor. The assertion concerns buffers, not uniqueness of local
heaps, blocking sets or completeness marks. Equality of output buffers alone
is sufficient for the buffer conclusion.

The finite search enumerates all frame and local buffers of length at most
three over two addresses and values 0/1. It groups all ordered merges by
the pair `(frame, output)` and looks for unequal local buffers. Outputs can
have length six. The eventual theorem must cover arbitrary finite buffers
and need no finite bound on the processor domain.

## 2. Attribution of a particular machine flush

Write `O(F,L,C)` for the repaired `#` composition of generalized resources.
Let `pool` be a raw memory with empty buffers. Require

```text
O(F,L,C)
memory_spatial pool (memory C) whole
flush_at active i whole whole'
```

The target is one of these alternatives:

```text
an actual flush of F on i, producing F',
O(F',L,C'), and memory_spatial pool (memory C') whole'
```

or

```text
an actual flush of L on i, producing L',
O(F,L',C'), and memory_spatial pool (memory C') whole'.
```

The affected resource gains exactly processor `i`'s completeness mark in
addition to its existing marks; the unaffected resource is the same resource,
not an arbitrary future. The pool also stays exactly fixed. The affected
resource's change must be a single `GeneralizedFlush`, not a sequence or an
unrelated mark-only transition. No new safety/validity notion is needed to
state this.

The pool's empty buffers are an existing consequence of the guarded invariant
fragment (and hold for an empty pool). Without that premise a pool write
could itself flush; omitting it would make the two-way statement false.
This is not a new restriction on the already accepted invariant fragment.

The search uses two processors, two addresses for frame/local resources,
values 0/1, arbitrary frame/local heaps on those addresses, and up to three
pending writes in total across their four buffers. It includes all disjoint
blocking-set assignments whose union is a complete lock state. The pool is
empty or one cell at any of three addresses, filtered by spatial separation;
it always has empty buffers and is lock-free. All resources in this physical
search are fully marked; the mark-sensitive lift is a separate proof
obligation. Every enabled machine flush is tested for an attribution with
the other component and pool fixed. Count cases where both source buffers
have identical heads, and check whether more than one attribution survives.

## 3. The proposed safety replacement, not implemented here

The single target would replace `separated_safe` / `separated_valid` as the
active development path. Their permanently separate protected/private
assertion arguments and their program-step permission for an arbitrary
frame future would not carry over. Earlier predicates remain historical
experiments with their own proved theorems; those results are not silently
reinterpreted as results about the new target.

The proposed target has one owned local resource and an invariant pool, with
the previously discussed overlap/disjoint modes. Non-flush program steps
would leave the external frame exactly unchanged. Local flushing closure
and attribution of actual global flushes would replace arbitrary silent
frame progress inside a program-step witness. The exact treatment of marks,
step indices, lock ownership and closure must be written down and reviewed
before a replacement predicate is added.

Passing the two lemmas does not establish the full frame rule, concurrency,
the container derivation, or the adequacy of this prospective safety target.
