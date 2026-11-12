# Early paper check-in: units and reading one's buffered write

Both early questions in [the reviewer's guidance](reviewer-guidance-after-audit-statement.md)
have positive answers:

1. **`emp` is a two-sided unit for all three conjunctions, for arbitrary
   assertions including wands.**
2. **Reading one's own buffered write is already derivable in
   `owned_derivation`, with an arbitrary spatial tail.** No new LOAD
   constructor is needed.

This is the requested early check-in, not the completed priority 4A table.
The rest of the algebra audit remains open. No assertion rule set for 4B
has been chosen. The safety definition, assertion interpretation, grammar,
invariant fragment and 21-constructor program calculus are unchanged.

## E1/E2: the complete unit results

All six equivalences are proved in
[`AssertionUnits.v`](../theories/AssertionUnits.v), in the final
`persistent_models` interpretation:

| Instance | Status | Theorem |
| --- | --- | --- |
| E1, `P * emp ≡ P` | Proved | `assertion_unit_spatial_right` |
| E2, `emp * P ≡ P` | Proved | `assertion_unit_spatial_left` |
| E1, `P ; emp ≡ P` | Proved | `assertion_unit_temporal_right` |
| E2, `emp ; P ≡ P` | Proved | `assertion_unit_temporal_left` |
| E1, `P ⋉ emp ≡ P` | Proved | `assertion_unit_strong_right` |
| E2, `emp ⋉ P ≡ P` | Proved | `assertion_unit_strong_left` |

These are equivalences, not just introduction directions. They quantify
over every processor domain, stack, resource and assertion. They need no
wand-free, finite-domain, two-processor, invariant-fragment or admissible-
environment premise. `⋉` retains its existing independent-witness
conjunction definition.

The gap in `container_spatial_emp_elim` was a limitation of that helper's
proof, not a counterexample to the general law. Composing with an `emp`
resource can add completeness marks while leaving the memory pointwise
unchanged. The general elimination proofs therefore need satisfaction to
survive that change even when the assertion contains a wand.

[`AssertionResourceEquivalence.v`](../theories/AssertionResourceEquivalence.v)
provides the missing general facts:

- `persistent_models_resource_equiv`: pointwise equivalent resources
  satisfy the same assertions, including all three future-aware wands.
- `persistent_models_mark_extension`: pointwise unchanged memory and an
  enlarged mark set preserve every assertion.

The first proof transports future steps and extension compositions, so it
handles a wand's universal quantification over futures. The second uses the
existing mark-only future and the already proved flushing closure. It adds
no future transition or axiom. Functional extensionality is not required.
The temporal unit proofs use the same facts; the strong-temporal units
follow from the spatial and temporal units.

### Bounded screening

Before the general proofs, `scripts/search_assertion_units.py` screened a
finite interpretation with two processors, one address, values 0 and 1,
at most one buffered write per processor, and all blocked and mark sets.
It covered 360 resources and 2,548 formulas, including each kind of wand
and nested wands: 5,503,680 resource/formula/unit checks. No counterexample
was found. The output is in [`paper-unit-search.jsonl`](paper-unit-search.jsonl).

This search omits compositions that leave its finite universe. Its result
is only bounded screening; the unrestricted Rocq theorems establish the
laws for the actual resource semantics.

## Priority 5.1: the existing calculus derives the load

Write `W(a,i,v)` for the existing write atom. The main derived rule is:

```text
J ⊢ᵐ {(R ; W(a,i,v)) * T}
       x := [a]_i
     {((R ; W(a,i,v)) * T) ∧ x = v}
```

Here `m` is either mode, and `R` and `T` are arbitrary assertions, including
wands. The destination must be absent from `fv(J)`, `fv(R)`, `fv(T)`, and
the free variables of the address, processor annotation and value
expressions. These are the existing LOAD and frame freshness conditions.
There is no extra resource condition or processor-domain restriction on
the derivation theorem. Applying calculus soundness still uses its two
standing hypotheses: a fragment invariant and two active processors.

The proof in [`OwnedBufferedLoad.v`](../theories/OwnedBufferedLoad.v) uses
only existing constructors:

1. Instantiate printed LOAD with an `emp` tail and use consequence to derive
   `{W(a,i,v)} load {W(a,i,v) ∧ x=v}`.
2. Apply FRAME-TM in overlap mode with `R` as the older history. Pull the
   pure equality out of the temporal conjunction by consequence.
3. Apply FRAME-SP for the arbitrary tail `T`.
4. Use OV-to-DJ weakening when a disjoint-mode result is wanted.

The old cell does not have to be spatially separated from the new write:
it is the **temporal frame**, while the newest write is the LOAD axiom's
owned resource. That is the missing derivation in the reviewer's tentative
reading. No new constructor or semantic command-validity premise is used.
Consequence still uses semantic assertion entailments, as it does elsewhere
in the current calculus; replacing those premises belongs to 4B/4C.

| Result | Theorem |
| --- | --- |
| LOAD on the write alone | `owned_derive_load_write` |
| Arbitrary older history, overlap mode | `owned_derive_load_after_history_overlap` |
| Arbitrary older history, either mode | `owned_derive_load_after_history` |
| Arbitrary older history and spatial tail, either mode | `owned_derive_load_after_history_spatial` |
| Queue's instance, `R = ∃u.C(a,u)`, with an arbitrary spatial tail | `owned_derive_load_own_buffered_write` |

For the last row, choose the existential binder fresh for the address as
usual. Its freshness premise for the destination uses the free variables
of the whole existential formula; the destination may coincide with the
bound variable. The no-tail version follows directly from
`owned_derive_load_after_history` with this same `R`.

### Concrete pending, flushed and other-processor tests

[`OwnedBufferedLoadExamples.v`](../theories/OwnedBufferedLoadExamples.v)
checks the actual history from the queue, not only an isolated write:

- The heap contains `a ↦ 7`; processor 2's buffer contains `a := 9`.
  The resource satisfies `(∃u.C(a,u)) ; W(a,2,9)`, in a concrete free-lock,
  empty-pool environment at either mode. Processor 2 loads 9 and retains
  the history and the pending write, without acquiring mark 2.
  This is `buffered_load_pending_enabled`.
- `buffered_load_flush_future` constructs its actual flush future.
  `buffered_load_after_flush_enabled` shows that the same history assertion
  still holds and the load now returns 9 from the heap, with the buffer
  empty.
- `buffered_load_other_processor_reads_old` shows processor 1 can instead
  load 7 before processor 2 flushes. The derived rule uses the processor
  named by the write; it does not promise the latest value to a different
  processor.
- `buffered_load_history_derived` is the corresponding derivation in the
  existing calculus, at either mode. Its existential binder and load
  destination are both register 0, exercising the binding qualification.

## T7/T8: interpretation of the prose

My reading of the dissertation's prose is **uniform connective inclusion**:
the discussion describes a lattice of the three connectives and small
exchange laws, so the intended ordering appears to be between connectives,
not an accidental entailment for one pair of assertions. This is an
interpretation of the prose, not a checked mathematical result.

The displayed side condition nevertheless mentions the particular `P` and
`P'`. The audit will therefore retain both targets: the formula-specific
printed premise and the uniform premise `∀A B, A • B ⊨ A ○ B`. A failure of
the former will be reported as such, even if the latter succeeds; it will
not be dismissed as a transcription error. The source is the
[Concurrent Algebra subsection](https://github.com/iwehrman/Weak-Memory-Local-Reasoning/blob/master/dissertation.tex#L1928-L1980),
whose figure inventory was fixed in the audit statement. No T7/T8 result is
claimed by this early report.

## Validation and next work

The four new Rocq files add 34 named lemmas, theorems and corollaries, all
included in `Audit.v`. `make check` passes, with **717 declarations closed
under the global context** and no axioms or admitted proofs.

Next is the rest of the 4A table, particularly strong-temporal
associativity, lock multiplication, barrier distribution and exchange.
Priority 5 items 2–4 remain queued. No assertion rule set for 4B will be
selected before the complete 4A report.
