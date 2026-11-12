# Checkpoint 9 — heap-rule statements before search

The routine rules are being proved for the unchanged `owned_valid` in both
modes. Assignment uses capture-avoiding substitution for the whole assertion
grammar and the already accepted condition `x ∉ fv(J)`. No new condition has
arisen for skip, sequence, consequence, disjunction, choice, loop or fence.

The heap-rule target has four schemas, in either mode. Write `W_i(e,v)` for
`A.LeadsTo e i v`, `C(e,v)` for `writer_points_to e v`, and
`H ⋉ P = (H * P) ∧ (H ; P)` for the existing abbreviation.

```text
LOAD:       {W_i(e,v) ⋉ P} x := [e]_i {(W_i(e,v) ⋉ P) ∧ x=v}
STORE:      {W_i(e,old) ⋉ P} [e] := v_i {(W_i(e,old) ⋉ P) ; W_i(e,v)}
LOAD-ANY:   {C(e,v) ⋉ P} x := [e]_i {(C(e,v) ⋉ P) ∧ x=v}
STORE-ANY:  {C(e,old) ⋉ P} [e] := v_i {(C(e,old) ⋉ P) ; W_i(e,v)}
```

The first two follow Figure 4.7's forms. LOAD requires the destination to
be absent from the free variables of the invariant, address, value,
processor expression and retained assertion. The appendix's load lemma
already states the assertion/expression freshness condition and its proof
also uses invariant freshness. LOAD-ANY needs freshness for the invariant,
address, value and retained assertion; its postcondition does not retain
the processor expression. These restrictions preserve the old precondition
and the meaning of `v` after updating the destination register.

The any-writer forms are an **explicit rule extension** for the weakened
cell abbreviation, not a claim that the printed writer-specific axiom can
load arbitrary acquired cells. No assertion atom or meaning changes.
The printed all-processor points-to abbreviation remains separate.

## Search and proof obligations

First search the stronger spatial-only footprint obligations. Given a
spatial split of a local resource into the write/cell and an arbitrary
retained resource, test:

1. Every admissible external frame and pool preserves the value seen by the
   loading processor. A blocked load is stuck, not an abort.
2. Enqueueing at the address gives an admissible successor with the exact
   frame and pool fixed and the same footprint and marks.
3. The enqueued resource is the temporal composition of the **entire old
   resource** and the new pending-write atom. Thus the complete old `⋉`
   assertion, with both independently chosen witnesses, can be retained.

If these stronger obligations hold, no common split of the two `⋉`
conjuncts is assumed. Their arbitrary assertion content is handled by the
general proof, not by an assertion-enumeration shortcut in the search.

The finite model has two processors, three addresses, values 0/1, all mark
sets, and free or held locks. An enumerated family puts the tested write at
address 1, another resource at address 2, and an optional pool cell at
address 3. External frames include identical/unequal older writes to address
1, duplicate occurrences, and stale heaps at that address. Input resources
include pending and flushed writer-specific atoms and buffer-free cells
whose only mark belongs to a different processor from the loader. A seed-9,
4,000-draw sample per rule family additionally varies addresses and up to
three pending writes across the external and retained resources.

This is a bounded search of sufficient resource obligations, not an
exhaustive enumeration of Hoare specifications. Run
`PYTHONDONTWRITEBYTECODE=1 python3 scripts/search_owned_heap.py` and record
its output before writing the general heap proofs. Check in on the heap
result either way, before the container derivation.

Source inspected: [author's LaTeX, concurrent axioms and load appendix](https://github.com/iwehrman/Weak-Memory-Local-Reasoning/blob/master/dissertation.tex).
