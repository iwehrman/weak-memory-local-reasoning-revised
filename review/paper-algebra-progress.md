# Algebra audit progress: associativity and lock countermodels

**Follow-up:** the [complete 4A audit](paper-algebra-audit.md) settles every
instance left open here, including the other associativity direction and
all exchange cases. This report records the earlier 761-declaration batch.

The approved 4A audit can proceed while the reviewer is offline. This batch
proves more of the existing assertion laws and checks two failures, without
changing the assertion interpretation or choosing the 4B rule set.

**Strong-temporal associativity fails, and the failure also refutes one
small-exchange instance under either reading of its side condition.**
The printed lock-multiplication law also fails on a two-processor assertion
resource. Both countermodels are checked against the final interpretation
and the dissertation's original interpretation.

This is a progress report, not the completed 4A table. The new files are
[`AssertionAlgebra.v`](../theories/AssertionAlgebra.v) and
[`AssertionAlgebraCounterexamples.v`](../theories/AssertionAlgebraCounterexamples.v).
`conjunction_kind` is only an audit index for the existing `*`, `;` and `⋉`;
it adds no constructor to assertions or to the derivation system.

## E3: strong-temporal associativity is false

Use one address `a`, value 0, and processor 1, with processor 2 also active.
Let

```text
P = true
Q = bar(1)
R = emp ∨ W(a,1,0)

heap:    a ↦ 0
buffer1: [(a,0)]
buffer2: []
marks:   {1}
lock:    free
```

This resource satisfies `P ⋉ (Q ⋉ R)` but not `(P ⋉ Q) ⋉ R`.
It is a small witness: one heap cell and one pending write, with no differing
values or lock tokens. `assertion_associativity_countermodel_environment`
places it in an admissible empty-pool environment in either mode. The
failure does not depend on a resource that cannot occur in the machine.

The positive formula can use two different decompositions:

- For its outer spatial conjunct, `P` takes the entire heap and buffer.
  `Q ⋉ R` takes an empty resource marked for processor 1 and selects
  `R`'s `emp` branch.
- For its outer temporal conjunct, `P` takes the heap cell. `Q ⋉ R` takes
  the pending write, with mark 1, and selects `R`'s write branch. The earlier
  heap resource has no pending write, so the mark's temporal condition holds.

The other bracketing cannot satisfy even its outer spatial conjunct.
`P ⋉ Q` requires processor 1's buffer to be empty. Consequently `R` must
contain the pending write; its `emp` branch and a flushed write cannot do
that. A pending write atom has an empty heap, so the heap cell must belong
to `P ⋉ Q`. Both sides would then own address `a`, violating spatial
disjointness.

| Claim | Checked theorem |
| --- | --- |
| Right bracketing holds | `assertion_strong_associativity_right_model` |
| Left bracketing does not hold | `assertion_strong_associativity_left_not_model` |
| Entailment right-to-left is false | `assertion_strong_associativity_refuted` |
| Same positive/negative facts in the original interpretation | `assertion_strong_associativity_printed_right_model`, `assertion_strong_associativity_printed_left_not_model` |

Thus the issue comes from the original abbreviation
`P ⋉ Q = (P * Q) ∧ (P ; Q)`, whose conjuncts have independent witnesses.
It was not introduced by future-aware wands or the repaired compatibility
condition. Spatial and temporal associativity separately remain proved.

### Consequence for T7

Take both schematic connectives to be `⋉`. T7 then asks for exactly the
failed entailment above. Both the literal side condition and the uniform
one hold by reflexivity:

```text
∀A B. A ⋉ B ⊨ A ⋉ B
```

`assertion_small_exchange_strong_refuted` packages that premise together
with the counterexample. The distinction between the two readings of the
prose cannot rescue this instance.

The search also found a candidate for the opposite associativity direction,
using two addresses. That second candidate has not yet been formalized;
T8 with both connectives `⋉` remains unclassified in the checked table.

## E6: opposite lock atoms can compose on two processors

With exactly processors 1 and 2 active, use empty heaps and buffers and no
marks. A `lock(1)` resource blocks processor 2; a `lock(2)` resource blocks
processor 1. These blocked sets are disjoint, so the resources compose by
all three conjunctions. Their result blocks both processors.

Thus `lock(1) • lock(2) ≡ false` fails for `*`, `;` and `⋉`, even under the
calculus's standing two-active-processors assumption.

| Claim | Checked theorem |
| --- | --- |
| Countermodel for all three conjunctions | `assertion_lock_multiplication_model` |
| Entailment to false is refuted | `assertion_lock_multiplication_refuted` |
| Same countermodel in the original interpretation | `assertion_lock_multiplication_printed_model` |
| Result is not lock-complete | `assertion_lock_countermodel_not_lock_complete` |
| Result has no admissible owned environment, with any pool or frame | `assertion_lock_countermodel_no_environment` |

Unlike the associativity witness, this resource cannot appear in any
admissible machine environment. It is nevertheless in the assertion
resource universe, so an unconditional semantic entailment must account
for it. This distinction explains why the finding does not refute the
proved lock rules or adequacy theorem.

Two useful qualifications are proved:

- `assertion_lock_multiplication_common_blocker`: if some active processor
  differs from both lock owners, both tokens would block it and their
  composition is impossible. This covers a third active processor distinct
  from the two owners.
- `assertion_same_lock_exclusive`: composing two copies of the **same**
  lock atom entails false under the existing two-active-processors
  assumption.

These qualify an assertion law. They introduce no new processor assumption
on the program calculus and no new side condition on any existing program
rule.

## Other completed instances

These results concern the final `persistent_models` interpretation. Except
for the explicitly qualified lock results, they require no processor-count,
wand-free, invariant-fragment or admissible-environment assumption.

| Audit instance | Status | Theorem |
| --- | --- | --- |
| E1/E2, all three conjunctions | Proved previously; packaged uniformly here | `assertion_conjunction_unit_right`, `assertion_conjunction_unit_left` |
| E3, spatial | Proved | `assertion_spatial_associative` |
| E3, temporal | Proved | `assertion_temporal_associative` |
| E4, spatial commutativity | Proved | `assertion_spatial_commutative` |
| E7, barrier idempotence, all three conjunctions | Proved | `assertion_barrier_idempotent` |
| E9, `P ⋉ bar(i) ≡ P ; bar(i)` | Proved | `assertion_strong_barrier_temporal` |
| E10, lock/barrier temporal versus spatial composition | Proved; even independent annotations work | `assertion_lock_barrier_temporal_spatial` |
| E11, spatial exclusion of writes to the same address | Proved | `assertion_spatial_writes_exclusive` |
| T1, barrier entails emp | Proved | `assertion_barrier_entails_emp` |
| T2/T3, monotonicity, all three conjunctions | Proved | `assertion_conjunction_mono` |
| T5/T6, strong-temporal projections | Proved | `assertion_strong_entails_spatial`, `assertion_strong_entails_temporal` |
| T7/T8, both connectives spatial, or both temporal | Proved by the respective associativity directions | `assertion_spatial_associative`, `assertion_temporal_associative` |

The expression-valued laws quantify over arbitrary annotations, including
inactive or nonpositive values where the atomic interpretation gives them
meaning. E11 permits different writer and value expressions on its two
sides. No active-annotation premise is silently inserted.

## Search and proof checks

`scripts/search_assertion_algebra.py` uses two processors, two possible
addresses, value 0, at most one pending write per processor, and all marks
and blocked sets. It enumerates 468 resources and 65 distinct denotations
of atoms and their pairwise disjunctions. Both candidate directions of
strong-temporal associativity were found within 6,240 tested triples.
The output is in [`paper-algebra-search.jsonl`](paper-algebra-search.jsonl).
As before, compositions outside the finite universe are omitted; only the
Rocq countermodels establish failures in the actual semantics.

The earlier unit search's write-atom enumerator was corrected to include
the allowed blocked-writer bit on a pending write. The corrected search
again reports 360 resources, 2,548 formulas and 5,503,680 checks, with no
counterexample. The general unit proofs were unaffected.

`make check` passes with **761 declarations closed under the global
context**, including all 44 new named results. No axioms, admitted proofs,
assertion grammar changes, semantic changes or program-rule changes were
introduced.

## Remaining work and review boundary

The complete 4A table still needs E5 (lock symmetry), E8 (barrier
distribution), E12 (successive-write collapse), T4 (the two cell notions),
the other T7/T8 instances and T9 (full exchange). The opposite-direction
strong-associativity search candidate belongs with that remaining work.

Those searches and proofs can continue independently. Selecting the 4B
assertion rule set remains after the complete 4A report, and its soundness
proof remains after the separate rule-statement checkpoint. In particular,
there is no proposal here to change `⋉` or silently add associativity to
the forthcoming assertion rules.
