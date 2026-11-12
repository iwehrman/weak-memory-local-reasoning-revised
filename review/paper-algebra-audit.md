# Paper checkpoint 4A: complete assertion-algebra audit

The audit of Figures 4.5 and 4.6 is complete for the final
`persistent_models` / `persistent_entails` interpretation. Every displayed
schema, every choice of schematic connective, and both readings of the
small-exchange premise have a checked classification.

**The units, spatial and temporal associativity, lock symmetry, barrier
laws, and successive-write collapse survive. Strong-temporal associativity
fails in both directions, and all small-exchange cases with `⋉` as the
outer connective fail, even with the uniform inclusion premise. Full
exchange also fails.** The printed lock-exclusion law and points-to/write
entailment require the qualifications below.

`make check` passes with **830 audited declarations closed under the global
context**, including all 69 new named results since `96f91bd`. There are no
axioms or admitted proofs. This work changes no assertion constructor,
atomic interpretation, composition relation, future relation, safety
predicate, program rule, or standing hypothesis. It does not select the 4B
assertion rule set.

## Reading the tables

Write `W(a,i,v)` for the existing write atom, `B(i)` for barrier, `L(i)` for
lock, and `C(a,v)` for `writer_points_to`. The printed all-processor
`a ↦ v` abbreviation remains distinct from `C(a,v)`. Write `H` for `⋉`
only in the small-exchange matrix. Its definition remains

```text
P ⋉ Q = (P * Q) ∧ (P ; Q)
```

The two conjuncts may choose different decompositions. No common-split
connective is introduced.

Unless a row states otherwise, a proved law quantifies over every processor
domain, arbitrary expression annotations, and the entire assertion
grammar, including all three wands. It is a law on all well-formed assertion
resources, without an admissible-environment restriction. The refutations
with a fixed domain use exactly two active processors, so they also refute
a universal claim under the calculus's standing processor hypothesis.

These tables concern the final interpretation. The earlier one-cell
associativity countermodel and opposite-lock countermodel were additionally
checked in the original `models` interpretation. The other new negative
results below are not being claimed as separately checked original-model
theorems.

Proof files:

- [A: AssertionAlgebra.v](../theories/AssertionAlgebra.v),
  [U: AssertionUnits.v](../theories/AssertionUnits.v),
  [K: AssertionAlgebraCounterexamples.v](../theories/AssertionAlgebraCounterexamples.v).
- [B: AssertionBarrierAlgebra.v](../theories/AssertionBarrierAlgebra.v),
  [L: AssertionLockAlgebra.v](../theories/AssertionLockAlgebra.v),
  [W: AssertionWriteAlgebra.v](../theories/AssertionWriteAlgebra.v),
  [WX: AssertionWriteExamples.v](../theories/AssertionWriteExamples.v).
- [X: AssertionExchange.v](../theories/AssertionExchange.v),
  [XS: AssertionExchangeCounterexamples.v](../theories/AssertionExchangeCounterexamples.v),
  [XR: AssertionExchangeRight.v](../theories/AssertionExchangeRight.v),
  [XT: AssertionExchangeTemporal.v](../theories/AssertionExchangeTemporal.v),
  [XTR: AssertionExchangeTemporalRight.v](../theories/AssertionExchangeTemporalRight.v).

## Figure 4.5: equivalences

“All three” below classifies `*`, `;`, and `⋉` separately with the same
status. An equivalence marked proved has both directions checked.

| ID | Instance | Status | Checked evidence |
| --- | --- | --- | --- |
| E1 | `P • emp ≡ P`, all three | Proved | A: `assertion_conjunction_unit_right`; full-grammar proofs in U |
| E2 | `emp • P ≡ P`, all three | Proved | A: `assertion_conjunction_unit_left`; full-grammar proofs in U |
| E3 | `(P * Q) * R ≡ P * (Q * R)` | Proved | A: `assertion_spatial_associative` |
| E3 | `(P ; Q) ; R ≡ P ; (Q ; R)` | Proved | A: `assertion_temporal_associative` |
| E3 | `(P ⋉ Q) ⋉ R ≡ P ⋉ (Q ⋉ R)` | Refuted in both directions | K: `assertion_strong_associativity_refuted` (right-to-left); XR: `assertion_small_exchange_strong_right_refuted` (left-to-right); witnesses A and B below |
| E4 | `P * Q ≡ Q * P` | Proved | A: `assertion_spatial_commutative` |
| E5 | `P • L(i) ≡ L(i) • P`, all three | Proved | L: `assertion_lock_symmetric` |
| E6 | `L(i) • L(j) ≡ false`, all three | Refuted as printed; qualified forms proved | K: `assertion_lock_multiplication_refuted`; A: `assertion_lock_multiplication_common_blocker`, `assertion_same_lock_exclusive`; witness E below |
| E7 | `B(i) • B(i) ≡ B(i)`, all three | Proved | A: `assertion_barrier_idempotent` |
| E8 | `(P • Q) ; B(i) ≡ (P ; B(i)) • (Q ; B(i))`, all three | Proved | B: `assertion_barrier_distribution`, with separate spatial, temporal and strong proofs |
| E9 | `P ⋉ B(i) ≡ P ; B(i)` | Proved | A: `assertion_strong_barrier_temporal` |
| E10 | `L(i) ; B(i) ≡ L(i) * B(i)` | Proved, even with independent lock and barrier annotations | A: `assertion_lock_barrier_temporal_spatial` |
| E11 | `W(a,i,v) * W(a,j,w) ≡ false` | Proved | A: `assertion_spatial_writes_exclusive` |
| E12 | `(W(a,i,u) ; W(a,i,v)) ; B(i) ≡ W(a,i,v) ; B(i)` | Proved | W: `assertion_successive_writes_collapse` |

E5 is stronger than symmetry alone: both `P ; L(i) ≡ P * L(i)` and
`L(i) ; P ≡ L(i) * P` are proved in L. A lock resource has empty heap and
buffers, and its optional marks can be moved to the other component using
full-grammar mark extension. This is why the result includes wands.

E8 also includes wands and inactive or nonpositive annotations. Its proof
uses an exact characterization of a barrier suffix
(`assertion_barrier_suffix_shape`). For the reverse direction it intersects
the two barrier witnesses' marks, so it needs no decision procedure for
membership in the processor domain.

E12 allows arbitrary old and new value expressions, including different
values. It has no active-annotation premise: an invalid address or writer
makes both sides false. The proof first distributes the barrier, then uses
the flushed-write shapes. It does not use strong-temporal associativity.

For E6, a common blocked processor rules out the composition: if an active
`k` differs from both owners, both lock tokens would block `k`. In
particular, two copies of the same lock atom are exclusive under the
existing two-active-processors hypothesis. This does not require adding a
third processor to the calculus.
The checked qualified E6 statements use constant positive owner
annotations; the unrestricted refutation uses such constants as well.

## Figure 4.6: entailments other than small exchange

| ID | Instance | Status | Checked evidence |
| --- | --- | --- | --- |
| T1 | `B(i) ⊨ emp` | Proved | A: `assertion_barrier_entails_emp` |
| T2 | Left monotonicity of `•`, all three | Proved | A: `assertion_conjunction_mono` |
| T3 | Right monotonicity of `•`, all three | Proved | A: `assertion_conjunction_mono` |
| T4 | `a ↦ v ⊨ W(a,i,v)` for arbitrary annotation | Refuted as printed; holds when the annotation denotes an active processor at every stack | W: `assertion_points_to_write_active`; WX: `assertion_points_to_invalid_writer_refuted` |
| T4 extension | `C(a,v) ⊨ W(a,i,v)` | Refuted even for an active writer; exact per-resource condition proved | W: `assertion_writer_cell_named_write`; WX: `assertion_writer_cell_foreign_write_refuted` |
| T5 | `P ⋉ Q ⊨ P * Q` | Proved | A: `assertion_strong_entails_spatial` |
| T6 | `P ⋉ Q ⊨ P ; Q` | Proved | A: `assertion_strong_entails_temporal` |
| T9 | `(P * Q) ⋉ (R * S) ⊨ (P ⋉ R) * (Q ⋉ S)` | Refuted | XS: `assertion_full_exchange_refuted`; witness A below |

The T4 distinction matters. On a resource satisfying `C(a,v)`, the named
write atom holds **exactly when** its annotation denotes a processor whose
mark is present on that resource. Resource well-formedness then implies
that processor is active. An arbitrary active processor need not have a
mark. In contrast, the printed `a ↦ v` carries every active processor's
mark, so activity alone suffices. Witness F below gives inhabited examples
of both failures.

## T7 and T8: every pair, both premise readings

The schemas are

```text
T7: P • (Q ○ R) ⊨ (P • Q) ○ R
T8: (P ○ Q) • R ⊨ P ○ (Q • R)

literal premise: P • Q ⊨ P ○ Q
uniform premise: ∀A B. A • B ⊨ A ○ B
```

I read the dissertation's intended connective comparison as **uniform**.
The text introduces schematic connectives and describes them as forming a
lattice just before asserting the small-exchange laws. That supports an
inclusion of binary operations, rather than an accident of one pair of
formulas. This is an interpretation of the prose; the displayed premise
really does use the particular `P,Q`, without the universal quantifier.
Both readings are therefore reported. The source was rechecked at blob
`ac4c24370dc22b3ca0892294206c2c6ac138d993` in the
[Concurrent Algebra subsection](https://github.com/iwehrman/Weak-Memory-Local-Reasoning/blob/master/dissertation.tex#L1928-L1977).

In the table, `S = *`, `T = ;`, and `H = ⋉`. Each cell explicitly gives the
status of both T7 and T8.

| `(•,○)` | Literal premise: T7 / T8 | Uniform premise: T7 / T8 | Checked evidence |
| --- | --- | --- | --- |
| `(S,S)` | Proved / Proved | Proved / Proved | A: the two directions of `assertion_spatial_associative` |
| `(S,T)` | Refuted / Refuted for any nonempty active domain | Proved / Proved; premise forces empty domain | X: `assertion_literal_exchange_spatial_refuted`, `assertion_uniform_incomparable_exchange` |
| `(S,H)` | Refuted / Refuted for any nonempty active domain | Proved / Proved; premise forces empty domain | Same two theorems in X |
| `(T,S)` | Refuted / Refuted for any nonempty active domain | Proved / Proved; premise forces empty domain | X: `assertion_literal_exchange_temporal_refuted`, `assertion_uniform_incomparable_exchange` |
| `(T,T)` | Proved / Proved | Proved / Proved | A: the two directions of `assertion_temporal_associative` |
| `(T,H)` | Refuted / Refuted for any nonempty active domain | Proved / Proved; premise forces empty domain | Same two theorems in X as `(T,S)` |
| `(H,S)` | Refuted / Refuted | Refuted / Refuted | XS: `assertion_exchange_strong_spatial_left_refuted`; XR: `assertion_small_exchange_strong_spatial_right_refuted` |
| `(H,T)` | Refuted / Refuted | Refuted / Refuted | XT: `assertion_small_exchange_strong_temporal_left_refuted`; XTR: `assertion_small_exchange_strong_temporal_right_refuted` |
| `(H,H)` | Refuted / Refuted | Refuted / Refuted | K: `assertion_small_exchange_strong_refuted`; XR: `assertion_small_exchange_strong_right_refuted` |

For the four incomparable cases, the uniform theorem is real but unusable
under the calculus's standing hypothesis. `assertion_uniform_incomparable_empty`
proves that its premise implies there are no active processors. On that
domain all resources have empty memory and no marks, and all three
conjunctions reduce to ordinary conjunction
(`assertion_empty_domain_conjunction`). Thus both exchanges hold there.
The literal counterexamples do not apply to the empty domain, where both
laws hold even without an inclusion premise.

For the three rows with `H` outside, the uniform premise itself is proved:
it is a projection for `S` or `T`, and identity for `H`. Thus these failures
are not artifacts of reading the displayed premise too weakly. Under two
active processors, of the five pairs whose uniform premise holds, only the
two ordinary associativity pairs survive.

## Countermodels in words

These are the smallest witnesses used in the checked proofs, after reducing
the search candidates where possible. No global minimality theorem is
claimed. All unmentioned buffers are empty; all values below are zero
except in the T4 cell example. “Mark 1” means the resource's completeness
set is exactly `{1}`. Apart from the generic witnesses G and H, the active
domain is exactly `{1,2}`.

### A. One cell and one write: E3 right-to-left, T7 `(H,H)` and `(H,S)`, T9

Use heap `a ↦ 0`, processor 1's buffer `[(a,0)]`, mark 1, and a free lock.
Let `P = true`, `Q = B(1)`, `D = emp ∨ W(a,1,0)`.

The resource satisfies `P ⋉ (Q ⋉ D)` and `P ⋉ (Q * D)`, but not even
`(P ⋉ Q) * D`. The positive spatial decomposition assigns everything to
`P` and selects the empty branch of `D`; the positive temporal decomposition
assigns the heap to `P` and selects the pending-write branch in the suffix.
In the negative formula, `P ⋉ Q` must be drained on processor 1. `D` must
therefore take the write, leaving the heap cell to the other spatial part.
Both would own address `a`, which is forbidden by `*`.

For T9 substitute `P=true`, `Q=emp`, `R=B(1)`, `S=D`. The proved unit laws
reduce the conclusion to the same impossible spatial formula. The T9
search first found a more complicated formula; this is the smaller checked
witness. Resource name: K's `algebra_whole`. Its admissible empty-pool
environment is checked in both modes.

### B. One heap cell and two writes: E3 left-to-right and T8 `(H,H)`, `(H,S)`

Use heap `b ↦ 0`, processor 1's buffer `[(a,0)]`, processor 2's buffer
`[(b,0)]`, mark 1, free lock, with `a ≠ b`. Let `P=true`,
`Q=W(a,1,0)`, `R=B(1) ∨ W(b,2,0)`.

`(P ⋉ Q) ⋉ R` holds, but `P * (Q ⋉ R)` does not. A spatial write atom
at `b` cannot account for both the heap cell and its pending write, so the
spatial part of `Q ⋉ R` must select `R`'s barrier branch. Its temporal part
can then select neither branch: the barrier would require the pending
`a` write to have drained, and the other branch would require a `b`
resource that this spatially selected part lacks. Resource name:
XR's `exchange_right_whole`.

### C. One cell, one write and a lock: T7 `(H,T)`

Use heap `a ↦ 0`, processor 1's buffer `[(a,0)]`, mark 1, and the token
for lock owner 1 (processor 2 blocked). Let `P=true`,
`Q=L(1) ∨ W(a,1,0)`, `R=B(1) ∨ L(1)`.

`P ⋉ (Q ; R)` holds: its spatial split can use `L(1) ; B(1)` on the
right, while its temporal split uses `W(a,1,0) ; L(1)` on the right.
`(P ⋉ Q) ; R` fails. A final barrier would require an empty processor-1
buffer. A final lock prevents the earlier `Q` from choosing a second lock;
choosing a write instead runs into the same heap/write spatial conflict
as witness A. Resource name: XT's `exchange_temporal_whole`.

### D. Two cells and one write: T8 `(H,T)`

Use heap `a ↦ 0, b ↦ 0`, processor 1's buffer `[(a,0)]`, mark 1,
free lock, with `a ≠ b`. Let `P=Q=W(a,1,0)` and `R=true`.

`(P ; Q) ⋉ R` holds. Its spatial split puts the heap and pending write
at `a` into `P ; Q` and gives `b` to `R`. Its temporal split gives the
flushed `a` cell to `P ; Q`, and `b` plus the pending write to `R`.
The latter prefix satisfies two successive flushed writes by E12.

`P ; (Q ⋉ R)` fails. If the first `P` is pending, the suffix needs a
mark for its heap cell at `b`; only mark 1 is available, which would require
that prefix write to be drained. If `P` is flushed, the suffix retains
the pending write at `a`. Its `Q ⋉ R` then cannot contain a heap:
the spatial split excludes heap `a`, forcing the temporal `Q` to be
pending, and the only available mark cannot occur after that write.
`assertion_strong_write_single_mark_heap_empty` states the last fact
generally. Resource name: XTR's `exchange_temporal_right_whole`.

### E. Empty memory, both blocked: E6 for all three conjunctions

Use no heap, no buffers, no marks, and both processors blocked.
`L(1)` blocks only processor 2 and `L(2)` blocks only processor 1. Those
tokens compose by each conjunction. Resource name:
K's `algebra_both_blocked`.

This resource is not lock-complete and has **no admissible owned
environment**, for any pool or frame. It is nevertheless a well-formed
assertion resource, so it refutes the unrestricted assertion law. The
checked results do not refute LOCK, UNLOCK, parallel composition or
adequacy.

### F. A flushed cell: the two T4 failures

With heap `2 ↦ 7`, no buffers, free lock, and both marks, the printed
all-processor points-to holds. A write annotation of 0, a negative integer,
or inactive processor 3 makes the write atom false. WX's
`assertion_points_to_invalid_writer_refuted` covers every such constant.

With the same heap but only mark 1, `C(2,7)` holds and `W(2,2,7)` does
not, even though processor 2 is active. The resources are the existing
`checkpoint_full_cell` and `heap_foreign_cell`, respectively.

### G. A marked pending write: literal `(S,T)` and `(S,H)`, both laws

For any active `i`, use no heap, just `[(a,0)]` in buffer `i`, mark `i`,
free lock. Take `P=true`, `Q=emp`, `R=B(i)`. The literal premise holds
by the unit laws, while either exchange conclusion would turn
`true * B(i)` into a formula requiring `true ; B(i)`. The latter is
false because the write has not drained. Resource name:
X's `exchange_pending`.

### H. Heap and pending write at one address: literal `(T,S)` and `(T,H)`

For any active `i`, use heap `a ↦ 0`, buffer `i` containing `[(a,0)]`,
mark `i`, free lock. Take `P=true`, `Q=emp`, `R=W(a,i,0)`. The premise
again holds by the units. The resource satisfies `true ; W(a,i,0)` but
not `true * W(a,i,0)`: a write atom can own the heap cell or the pending
write, not both, while a spatial partner cannot own the other at the same
address. Resource name: X's `exchange_mixed`.

## Search and verification

[The expanded bounded search](../scripts/search_assertion_algebra.py) uses
468 resources, two active processors, two possible addresses, value 0,
at most one buffered write per processor, all mark subsets and blocked
sets, and 65 distinct denotations of atoms and pairwise disjunctions.
Its complete output is [paper-algebra-search.jsonl](paper-algebra-search.jsonl).

- E8: 12,675 instances per connective, both directions, no counterexample.
- E5: 130 instances per connective, both directions, no counterexample.
- E3 for `⋉`: both candidate failures found within 6,240 tested triples.
- T7/T8: every pair tested; both failures found in every pair other than
  `(S,S)` and `(T,T)`. The script tests the formula-specific premise in its
  finite interpretation; the actual semantic premises are justified in
  Rocq, not by those finite inclusion tests.
- T9: an initial candidate found after 20,957 quadruples, from exhaustive
  atom cases followed by deterministic disjunctive sampling. Witness A is
  the subsequently simplified, checked countermodel.

Compositions outside this bounded universe are omitted, so neither a
negative search result nor a finite inclusion is a proof. No wands are
enumerated. All positive laws above are separately proved for the full
grammar. The exact-atom
[successive-write search](../scripts/search_write_collapse.py) keeps all
intermediate compositions, including two pending writes, and checks all
eight combinations of processor and old/new values from `{0,1}`.
[Its output](paper-write-collapse-search.jsonl) has no failure; the general
expression-valued theorem is the authoritative result.

The final build compiled the additions and ran `rocq check` on `WMLR.Audit`
and its dependencies. All new lemmas and theorems are included in
`Print Assumptions`; the log has 830 closed declarations, zero axiom lists
and zero errors. The previously checked program-calculus soundness,
adequacy, framing, heap rules and container derivations still pass. No
existing theorem relied on the refuted assertion laws.

## Checkpoint boundary

This completes 4A and is the requested check-in before 4B. The findings
call for selecting the valid assertion laws, not assuming that `⋉` can be
rebracketed. They do not yet establish whether omitting its exchange laws
causes a practical cost in the planned derivations; 4C and the later
examples will test that.

The earlier [buffered-load result](paper-units-and-buffered-load.md) remains
settled: the current program calculus already derives reading one's own
buffered write. There is no new LOAD constructor to propose. The next
agreed deliverable is the 4B assertion-rule statement, using the audited
laws, first-order reasoning, existing wand adjunctions and the recurring
container entailments, without an unrestricted semantic-entailment escape
hatch. Its soundness proof follows the separate rule-statement check-in.
