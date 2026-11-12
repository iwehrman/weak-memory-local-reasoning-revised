# Checkpoint 9 — routine rules and heap rules proved

**The requested routine rules, the printed strong-temporal LOAD/STORE
forms, and the any-writer cell forms are proved for `owned_valid` in both
modes.** The existing `⋉` abbreviation is sufficient. No safety definition,
assertion interpretation, entailment, or machine rule changed.

`make check` passes with **580** audited declarations closed under the
global context, including 70 new declarations. No axioms or admitted proofs
were added. This is the requested check-in after the heap rules, before
the container derivation.

## Exact heap rules

Write `W_i(e,v)` for `A.LeadsTo e i v`, `C(e,v)` for the existing
`writer_points_to e v`, and `H ⋉ P` for `(H * P) ∧ (H ; P)`.
[`OwnedHeap.v`](../theories/OwnedHeap.v) proves, for either mode and any
shared invariant `J`:

```text
LOAD:       {W_i(e,v) ⋉ P} x := [e]_i {(W_i(e,v) ⋉ P) ∧ x=v}
STORE:      {W_i(e,old) ⋉ P} [e] := v_i {(W_i(e,old) ⋉ P) ; W_i(e,v)}
LOAD-ANY:   {C(e,v) ⋉ P} x := [e]_i {(C(e,v) ⋉ P) ∧ x=v}
STORE-ANY:  {C(e,old) ⋉ P} [e] := v_i {(C(e,old) ⋉ P) ; W_i(e,v)}
```

Their declarations are `owned_load_valid`, `owned_store_valid`,
`owned_load_any_writer_valid`, and `owned_store_any_writer_valid`.
The address, contents, and processor annotation are arbitrary expressions;
`P` is an arbitrary assertion, including quantifiers and wands. There is no
processor-count or invariant-fragment hypothesis.

LOAD has explicit conditions `x ∉ fv(J)` and
`x ∉ fv(e,i,v,P)`. LOAD-ANY has `x ∉ fv(J)` and
`x ∉ fv(e,v,P)`; it need not preserve the processor expression because that
expression does not occur in its retained cell assertion. STORE and
STORE-ANY require no variable condition. The destination freshness keeps
the unchanged precondition and the expression `v` meaningful after the
register update. The dissertation's appendix already states expression
and assertion freshness for LOAD, and its proof also uses invariant
freshness. This checkpoint makes both explicit rather than relying on the
unqualified display in Figure 4.7. See the
[original source, concurrent axioms and load proof](https://github.com/iwehrman/Weak-Memory-Local-Reasoning/blob/master/dissertation.tex).

**LOAD-ANY and STORE-ANY are explicit rule extensions.** They accept a cell
flushed by any writer, expressed using the weakened points-to abbreviation
already approved at checkpoint 2. They are not claimed to follow from the
printed writer-specific axioms. The old all-processor points-to assertion
is unchanged. Useful base forms without a trailing `⋉ P` are also proved
as `owned_load_cell_valid` and `owned_store_cell_valid`.

## Why the conjunction does not cause another failure

The general proof only uses the spatial conjunct to justify access.
The write/cell owns its address, so the other spatial component has neither
a heap cell nor a pending write at that address. The external frame's
ordered composition preserves the current write's value. If allocation
exists only as a pending write in the issuing processor's buffer, that is
enough; no heap-cell premise is silently imposed.

For LOAD, the resource itself remains unchanged. The environment is
transported to the updated stack using invariant freshness, and the old
precondition is preserved using destination freshness. No mark is earned.

For STORE, the proof enqueues the write in the owned resource, keeping the
external frame and pool exactly fixed. Spatial separation also establishes
that no *other* owned processor buffer writes to the same address. This is
the compatibility fact needed to place the new pending write temporally
after the **entire old resource**. That old resource still satisfies its
whole old assertion, including both independently witnessed conjuncts of
`⋉`. The proof never regroups those conjuncts through a presumed common
split and never applies FRAME-STM.

The core lemmas are in
[`OwnedHeapResources.v`](../theories/OwnedHeapResources.v):
`owned_read_preserved`, `repaired_enqueue_read_right`,
`owned_environment_enqueue_read`, `owned_enqueue_read_update`, and
`owned_enqueue_temporal_post`. `owned_primitive_rule` then lifts the
concrete obligations to all safety indices, including all local futures.
It is a proof helper with discharged operational premises, not a new
validity predicate or a calculus constructor assuming safety.

## Searches before the heap proofs

The statements and bounds were fixed in
[`checkpoint-9-statement.md`](checkpoint-9-statement.md).
[`search_owned_heap.py`](../scripts/search_owned_heap.py) searches the
stronger spatial-only access and enqueue obligations used by the proofs.
The output is in [`checkpoint-9-search.jsonl`](checkpoint-9-search.jsonl).

| Family | Mode | Admissible environments | Enabled loads | Blocked loads | Store successors |
| --- | --- | ---: | ---: | ---: | ---: |
| Printed write atom | Overlap | 70,212 | 40,942 | 29,270 | 140,424 |
| Printed write atom | Disjoint | 13,476 | 8,027 | 5,449 | 26,952 |
| Any-writer cell | Overlap | 13,160 | 8,772 | 4,388 | 26,320 |
| Any-writer cell | Disjoint | 5,356 | 3,568 | 1,788 | 10,712 |

All four searches completed without a counterexample: **102,204**
admissible environments and **204,408** store successors. Every store
successor retains the exact frame/pool, satisfies the update bounds, and
is a temporal composition of the entire old local resource with the new
write. Blocked loads are counted separately; the model does not pretend
they execute. The any-writer rows include cells without the loader's mark.

The finite universe has two processors, three addresses, values 0/1, all
mark sets, and free or held locks. The focused family enumerates same-address
older writes, identical duplicates, stale heaps, and a separate retained
address and optional pool cell. A seed-9, 4,000-draw sample per family varies
addresses and up to three pending writes across the frame and retained
component. Including the distinguished pending write gives at most four
input writes; STORE may add a fifth. Counts include repeated configurations.

This is finite evidence about sufficient resource obligations, not an
exhaustive search of assertions or semantic Hoare validity. In particular,
it does not enumerate `⋉` with one shared witness. The general Rocq proofs
are independent of the script.

## Routine rules completed

[`OwnedStructural.v`](../theories/OwnedStructural.v) proves skip,
consequence, disjunction, sequencing, choice, and loop. Sequence and choice
also have same-index safety lemmas. None needs a new side condition.

[`OwnedPrimitives.v`](../theories/OwnedPrimitives.v) proves assume, assert,
assignment, and fence. Assignment has its previously accepted condition
`x ∉ fv(J)`, with an arbitrary postcondition:

```text
{Q[e/x]} x := e_i {Q}
```

[`AssertionSubstitution.v`](../theories/AssertionSubstitution.v) supplies
total capture-avoiding substitution for the complete assertion grammar.
Its semantic theorem covers all quantifiers and all three future-aware
wands. Binders are freshened during simultaneous substitution; no fresh-name
side condition is imposed on users of ASSIGN, and no axiom or extensionality
principle is used.

Fence is proved both in the small form `{emp} fence_i {bar(i)}` and the
general form `{P} fence_i {P ; bar(i)}`, in either mode. It earns only the
executing processor's mark, and the actual machine guard supplies the
necessary buffer-draining fact.

## Checked regressions

[`OwnedRoutineExamples.v`](../theories/OwnedRoutineExamples.v) checks a
substitution that would incorrectly become universally true if it captured
a free variable. Correct substitution holds exactly when that free
register is 9. It also checks an inhabited pending-write fence specification,
an actual flush-then-fence trace, and that the fence cannot step before the
flush.

[`OwnedHeapExamples.v`](../theories/OwnedHeapExamples.v) checks:

- A cell containing 7, marked only for processor 1, can be loaded and stored
  by processor 2 using the any-writer rules. Both examples have concrete
  admissible environments and enabled machine steps. Their explicit
  successors still have **no processor-2 mark**.
- That same cell does **not** satisfy the write-by-processor-2 atom needed
  by the printed axiom. This pins down the need for the rule extension.
- A buffered load followed by a store behind two identical older writes
  in the external frame. The composed specification uses the new sequence,
  consequence, LOAD and STORE rules. Its initial assertion and overlap-mode
  environment are inhabited, and the three-step trace checks. Allocation
  is supplied by the local pending write, with no heap cell at that address.
- A store whose precondition is proved with an empty spatial tail and an
  overlapping-cell temporal tail. The result preserves that complete
  precondition as its temporal prefix. These are deliberately different
  witnesses; the example does not assert that every possible pair of
  witnesses must differ.

## Next boundary and remaining limits

The next substantive task is the container derivation: acquire, remove,
release, use privately, and return, with a foreign write pending. That work
has not started at this checkpoint. It must test the practical cost of
omitting FRAME-STM and limiting FRAME-TM to overlap-mode validity.

There is still no active derivation system or calculus-level soundness
theorem. The routine rules completed above are the requested list; this
checkpoint also does not establish the printed EX or SHARE rules for
`owned_valid`. Any later calculus including those rules must justify them.
INV remains removed and FRAME-STM remains omitted. The existing lock,
unlock, frame, parallel, and adequacy results are unchanged.

The heap-rule result removes the immediate concern about needing a new
strong-temporal connective. The container remains the required test before
settling the derivation system.
