# Checkpoint 2 — guarded invariants survive acquisition re-marking

**Result: pass for the guarded fragment proposed in the review follow-up.**
The re-marking theorem and buffer-freeness theorem are proved in Rocq, with
direct release-premise checks. No replacement safety predicate, command rule,
or frame-shape proof has been introduced.

This continues [the checkpoint-1 response](lead-response.md). The independent
review remains unchanged as a historical document. Its author subsequently
accepted all four qualifications in that response, corrected the bare-pure
buffer-freeness claim, and proposed the syntactic guard tested here.

## Exact fragment and interpretation

Write `C(e,v)` for the existing-language abbreviation

```text
C(e,v) = exists k. (write(k,e,v) ; bar(k))
```

The binder is chosen fresh for both expressions. The checked fragment is

```text
H ::= emp | C(e,v) | H * H | H or H | exists x. H | (b and H)
```

Here `b` is a pure boolean assertion. Guards can occur at any depth, but
every guard has a heap-accounting conjunct. Bare `true`, `false`, or another
pure assertion is not a fragment constructor. In particular, `b and emp`
is allowed. This is a restriction on admissible invariants, not a change to
the semantics of pure assertions in other preconditions or postconditions.

`writer_points_to` and `invariant_fragment` in
[`InvariantFragment.v`](../theories/InvariantFragment.v) formalize the
abbreviation and syntactic classification. The assertion grammar,
`persistent_models`, composition relations, entailment interpretation, and
old all-processor `A.points_to` are unchanged. The new abbreviation is
deliberately named separately from that old, stronger contract.

## Checked results

### Acquisition: the same memory satisfies the invariant after re-marking

`invariant_fragment_remark` proves a slightly stronger result than requested:
if two resources have exactly the same underlying memory, the first satisfies
`H`, and the second has any nonempty well-formed completeness set, the second
also satisfies `H`.

`invariant_singleton_remark` specializes this to the proposed acquisition:
from a pool satisfying `H` at full completeness and an active processor `i`,
it constructs a resource with **exactly the same memory**, **exactly the
singleton completeness set `{i}`**, and the same invariant satisfaction.
No finite-processor assumption is needed.

The cell proof changes the existential processor witness to a processor in
the target completeness set. The model does not retain an immutable writer
identity after the write has flushed. For spatial composition, both heap
pieces can carry the target marks: their union is still the target set,
and their heaps and buffers are unchanged. These are properties of the
existing interpretation, not added entailments.

`invariant_return_full_completeness` proves the corresponding assertion
obligation on return to the pool: a fragment assertion on a marked resource
also holds at full completeness, with the same memory, provided there is an
active processor. Neither re-marking theorem claims that changing marks is
a physical flush or an executable machine step.

### Resource shape: every invariant has empty buffers and no lock token

`invariant_fragment_shape` proves that every satisfying resource has empty
buffers for every processor and is lock-free. The proof follows the fragment
syntax. The pure-guard case inherits these properties from its heap conjunct.
The result covers arbitrary address/content expressions, existential values,
disjunctions and spatial combinations, not just constant cells.

The original bare-pure claim remains false. `bare_pure_is_not_buffer_free`
checks a fully marked model of `Pure true` with processor 2's write to
address 3 still pending. The guard prevents that model from being an invariant
without changing what `Pure true` means.

### Release: pending writes stay in the retained resource

`invariant_spatial_pending_retained` proves that whenever a resource splits
as `H * B`, with `H` in the fragment:

- every buffer in the `B` component is exactly the corresponding buffer in
  the combined resource, preserving order and multiplicity;
- an address targeted by any of those pending writes is outside the donated
  invariant's entire domain.

`invariant_unlock_premise_pending_retained` applies this result to the proposed
premise `A ; bar(i) entails H * B`. Thus an invariant cannot absorb a pending
foreign write from the resource governed by that premise. If `B = emp`,
there can be no pending writes at all (`invariant_cannot_absorb_pending`).

This is a release-*premise* theorem, not an UNLOCK safety theorem. Pending
writes in an external frame still require the ownership/frame decomposition
argument. That obligation has not been assumed or proved here.

## Concrete checks

[`InvariantFragmentExamples.v`](../theories/InvariantFragmentExamples.v)
contains the following checked cases:

1. A resource contains only processor 2's pending write `3 := 17`, with
   completeness for processor 1 only. It satisfies `write(2,3,17) ; bar(1)`.
   The unguarded release premise can assign all of it to `Pure true` and
   retain `emp`. No invariant in the guarded fragment can do so.
2. A nonempty flushed cell `2 := 7` can occupy the invariant component while
   that unrelated write remains in the retained component. The combined
   resource satisfies both the release payload and that payload followed
   by `bar(1)`, and processor 2's buffer is still `[(3,17)]`. This is a
   concrete assertion check, not a universal entailment or command proof.
3. A fully marked cell continues to satisfy `C(2,7)` after receiving only
   processor 1's mark. The resulting resource does **not** satisfy
   `C(2,7) * bar(2)`, so the old foreign-barrier import is unavailable in
   this concrete re-marked resource.
4. The review's container invariant
   `C(f,0) or (C(f,1) * exists v. C(x,v))`, instantiated with distinct
   addresses 1 and 2, belongs to the fragment. Its acquisition re-marking
   obligation is proved, as is admission of a pure guard on this invariant.
   The acquire/remove/release/private-use/return command derivation remains
   future work; this checkpoint does not claim it.

## Validation and next boundary

Both new modules are part of `_CoqProject`, and their 17 principal declarations
are included in `Audit.v`. `make check` passed, including the independent
proof-object check. All 385 audited declarations reported `Closed under the
global context`; there are no admitted facts or added axioms.

The guard is the restriction explicitly proposed in the review follow-up.
No further side condition, assertion atom, changed entailment or additional
safety/validity predicate was needed for these results. The syntactic
fragment predicate only classifies formulas.

Checkpoint 2 removes the proposed invariant-fragment obstruction. It does
not establish the soundness of design D. The next checkpoint is the precise
frame-shape statement and bounded small-buffer search, especially overlapping
writes by the same processor. Report that search before a general proof;
report the first general proof attempt separately. No downstream safety
development has started.
