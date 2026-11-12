# Paper checkpoint 4B: assertion soundness and derived cell rules

Responds to [the review after the independent batch](reviewer-guidance-after-independent-batch.md).
All 47 approved assertion constructors are sound. All four planned cell
rules are derived within that basis, and CONS/UNLOCK now have interfaces
that accept assertion proof trees. **Final counts: 47 assertion
constructors and 21 program constructors; additions: zero.**

This is the requested check-in after step 1, before the 4C container
reconstruction. The assertion grammar, interpretation, machine, invariant
fragment, `owned_safe` and program constructors are unchanged. No new side
condition, connective, validity predicate or semantic entailment oracle
was introduced.

## Soundness and the constructor map

The principal theorem in [AssertionSoundness.v](../theories/AssertionSoundness.v) is:

```coq
Theorem assertion_derivation_sound active p q :
  assertion_derivation active p q -> persistent_entails active p q.
```

It is an induction on the exact approved definition. It covers arbitrary
assertions, including all three future-aware wands, on every processor
domain. There is no global processor-count, finiteness, invariant-fragment
or wand-free premise. The individual common-blocker and named-writer
activity conditions remain explicit in their existing constructors.

The requested **47-row constructor-to-semantic-lemma table** is in
[the writer's index](../notes/paper-theorem-index.md#every-assertion-constructor-and-its-semantic-lemma),
next to the corresponding program-rule table. The proof follows that table
in constructor order. New logical lemmas are in
[AssertionLogicalRules.v](../theories/AssertionLogicalRules.v); the two new
cell schemas are proved in
[AssertionCellAlgebra.v](../theories/AssertionCellAlgebra.v).

The distinct-cell proof uses the singleton heap and empty buffers to show
that the same pair of resources witnesses either separator. The overwrite
proof uses the later singleton heap and its existing mark. Neither proof
assigns a new processor's mark. The earlier bounded search is now supported
by these general proofs.

## Derived cell rules

Here `C(a,v)` is `writer_points_to`, `W(a,i,v)` is the write atom and `B(i)`
is the barrier atom. Every row below is an `assertion_derivation` theorem
in [AssertionDerivedRules.v](../theories/AssertionDerivedRules.v), with no
semantic entailment premise or semantic proof step.

| Rule | Declaration | Freshness / proof ingredients |
| --- | --- | --- |
| `C(a,u) * C(a,v) ⊢ₐ false` | `assert_derive_cells_exclusive` | No external freshness condition. Rename the two hidden writers to fresh, distinct names; move both existentials out; discard barrier suffixes; use write exclusion. |
| `W(a,i,v) ; B(i) ⊢ₐ C(a,v)` | `assert_derive_drained_write_cell` | No external condition. Existential introduction with witness `i`, using the cell abbreviation's fresh bound writer. |
| `C(a,v) ⊢ₐ ∃x.C(a,x)` | `assert_derive_cell_value_hiding` | `x ∉ fv(a)`. Existential introduction and exact capture-avoiding substitution normalization. The value expression may contain `x`. |
| `((∃x.C(a,x)) ; W(a,i,v)) ; B(i) ⊢ₐ C(a,v)` | `assert_derive_drained_history` | `x ∉ fv(a) ∪ fv(v)`. Distribute the barrier, discard its left copy, turn the right drained write into a cell, move the value existential out, then use cell overwrite. |

The drained-history result needs **less freshness than the proposed proof
route**: `x` may occur in the writer annotation `i`. The barrier is
distributed and its left copy discarded before the value binder moves,
so that binder never crosses the annotation. This is a stronger derived
theorem, not a weakened constructor or a new side condition.

### Bound-variable renaming

- **Cell exclusion explicitly renames both hidden writers.**
  `assert_derive_cell_named` and `assert_derive_named_cell` derive the
  conversion using the approved existential introduction/elimination rules.
  There is no alpha-conversion constructor.
- **Value hiding uses the existing substitution's automatic renaming.**
  `assertion_substitute_writer_cell` proves a syntactic equation: simultaneous
  capture-avoiding substitution of the cell abbreviation is exactly the
  cell of the substituted address and value. Its proof reasons about syntax,
  free-variable lists and fresh names, not resource satisfaction.
- **Drained-write conversion introduces a fresh writer binder** without
  renaming an existing bound variable. Drained history needs no independent
  renaming of its value binder and reuses drained-write conversion.

[AssertionDerivationExamples.v](../theories/AssertionDerivationExamples.v)
checks a concrete substitution that must rename the hidden writer from 1
to 2 when inserting free value variable 1; the resulting value-hiding
derivation; exclusion where one cell's default writer name is the other's
free value name; and history collapse with the value binder also used
freely in the external writer annotation.

## Program interfaces

[OwnedAssertionRules.v](../theories/OwnedAssertionRules.v) provides:

- `owned_assertion_consequence`: two assertion derivations and the body
  derivation yield the consequence instance, at either mode.
- `owned_assertion_unlock`: an assertion derivation of
  `A ; B(i) ⊢ₐ J * Q` yields the existing disjoint-mode release rule.

Both are derived wrappers: they apply `assertion_derivation_sound` and the
existing constructor. The old program judgment still permits semantic
entailments; these interfaces let clients discharge those premises entirely
with assertion proofs. They do not assert that the existing examples have
already been rebuilt that way.

As a small integration check, `owned_assertion_return_invariant` derives
release with the invariant restored and `owned_assertion_lock_round_trip`
derives `emp ⟶ acquire(i); release(i) ⟶ emp`, using these wrappers and
assertion proof trees throughout. They are syntactic program derivations;
their semantic soundness has the same standing invariant-fragment and
two-active-processor hypotheses as every other program derivation.

## Validation and next boundary

`make check` passes with **1,007 audited declarations closed**, including
all 60 new lemmas/theorems/examples. The independent `rocq check` pass also
completed. No axioms or admitted proofs were added. The seven new files
have 634 physical lines; the full checked tree has 155 theory files and
25,666 physical lines, including audit commands, comments and historical
experiments. The approved constructor definition changed only in its
status comment.

The next checkpoint is 4C: rebuild the selected-branch one-item container's
entailment obligations as assertion derivations and use the new wrappers.
That work has not begun in this batch. Restricted SHARE remains deferred
until after 4C and priority 1, with the approved semantic lock-free
pre/post premises; the overlap-mode question remains separate. No
common-split connective or new program rule was added.
