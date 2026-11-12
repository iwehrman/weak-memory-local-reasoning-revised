# Paper priority 4A: assertion-algebra audit targets

This is the statement of work before proofs, following the revised queue at
`f4899e0`. The active order is **4A → 4B → 4C → 1 → 2**, with priority 3
independent. The accepted base remains checkpoint 11: 683 audited
declarations. This document inventories the laws and proof obligations; it
does not claim that the audit is complete or that an unchecked law holds.

**Early result:** [E1/E2 and the buffered-load check-in](paper-units-and-buffered-load.md)
proves all six unit equivalences for arbitrary assertions, including wands,
and derives reading one's own buffered write using the existing calculus.
The remaining rows below have not yet been classified by this audit.

**Further progress:** [associativity and lock countermodels](paper-algebra-progress.md)
classifies additional instances, including checked failures of E3 for `⋉`,
T7 for `(⋉,⋉)`, and E6 for all three conjunctions. That report gives the
surviving laws and explicitly lists the still-unclassified instances.

## Interpretation and scope

Every result must concern `persistent_models` / `persistent_entails`, with
the current resource universe, repaired separation and future-aware wands.
Do not substitute the printed, pointwise repaired, regional, separated, or
retirement interpretations. The assertion grammar and interpretation stay
unchanged. `P ⋉ Q` means `(P * Q) ∧ (P ; Q)`, including its independent
witnesses.

The source is the dissertation's Figures 4.5–4.6, in the
[Concurrent Algebra subsection](https://github.com/iwehrman/Weak-Memory-Local-Reasoning/blob/master/dissertation.tex#L1928-L1977).
The inspected `dissertation.tex` blob is
`ac4c24370dc22b3ca0892294206c2c6ac138d993`. I also checked
[`definitions.tex`](https://github.com/iwehrman/Weak-Memory-Local-Reasoning/blob/master/definitions.tex):
`gensym` expands to the same bullet used in the schematic laws. Both bullet
and circle range over `*`, `;`, and `⋉`; `#` is not an assertion connective
and is not an extra schematic instance here.

Use `W(a,i,v)` for the existing write atom, `B(i)` for barrier, `L(i)` for
lock, and `C(a,v)` for `writer_points_to`. Keep the printed all-processor
`a ↦ v` abbreviation distinct from `C(a,v)`.

Statements must distinguish:

- arbitrary processor domains from the calculus's standing two-active-
  processors hypothesis;
- arbitrary expressions from expressions denoting an active processor;
- arbitrary assertions, including wands, from proved wand-free restrictions;
- equivalence from a single entailment direction;
- results on all valid assertion resources from results only on
  lock-complete machine states or admissible Hoare environments.

Those distinctions can affect truth. The table must expose them instead of
silently narrowing the printed statement.

## Figure 4.5: twelve displayed equivalence schemas

For each schematic row, give separate results for each of the three
connectives. An equivalence has two proof obligations.

| ID | Printed target |
| --- | --- |
| E1 | `P • emp ≡ P` |
| E2 | `emp • P ≡ P` |
| E3 | `(P • Q) • R ≡ P • (Q • R)` |
| E4 | `P * Q ≡ Q * P` |
| E5 | `P • L(i) ≡ L(i) • P` |
| E6 | `L(i) • L(j) ≡ false` |
| E7 | `B(i) • B(i) ≡ B(i)` |
| E8 | `(P • Q) ; B(i) ≡ (P ; B(i)) • (Q ; B(i))` |
| E9 | `P ⋉ B(i) ≡ P ; B(i)` |
| E10 | `L(i) ; B(i) ≡ L(i) * B(i)` |
| E11 | `W(a,i,v) * W(a,j,w) ≡ false` |
| E12 | `(W(a,i,v) ; W(a,i,w)) ; B(i) ≡ W(a,i,w) ; B(i)` |

Particular risks to check first are E3 for `⋉`, E6 on the two-processor
blocked-set representation, and E8/E9 with arbitrary assertions containing
wands. Existing proofs with a wand-free premise do not establish the fully
schematic laws. The known FRAME-STM counterexample is a reason to search;
it is not itself a proof that any specific assertion equivalence fails.

## Figure 4.6: nine displayed entailment schemas

| ID | Printed target |
| --- | --- |
| T1 | `B(i) ⊨ emp` |
| T2 | `P • Q ⊨ P' • Q` if `P ⊨ P'` |
| T3 | `P • Q ⊨ P • Q'` if `Q ⊨ Q'` |
| T4 | `a ↦ v ⊨ W(a,i,v)`; also test `C(a,v) ⊨ W(a,i,v)` separately |
| T5 | `P ⋉ Q ⊨ P * Q` |
| T6 | `P ⋉ Q ⊨ P ; Q` |
| T7 | `P • (Q ○ R) ⊨ (P • Q) ○ R`, under the printed inclusion premise |
| T8 | `(P ○ Q) • R ⊨ P ○ (Q • R)`, under the printed inclusion premise |
| T9 | `(P * Q) ⋉ (R * S) ⊨ (P ⋉ R) * (Q ⋉ S)` |

T7/T8 require care in transcription. The displayed side condition is
`P • Q ⊨ P ○ Q`, while the surrounding prose describes an inclusion between
connectives. Test the literal formula-specific premise, and distinguish it
from the uniform premise `∀A B, A • B ⊨ A ○ B`. If only the latter supports
a theorem, record it as an explicit modified form, not the printed result.
Inventory all nine choices of `(•,○)`, including equal-connective cases;
do not assume comparability of `*` and `;`.

For T4, test active and inactive annotation values and both cell
abbreviations. A proof for the printed all-processor cell cannot silently
stand in for a proof about the writer-existential cell.

## Existing proofs to reuse, with their actual limits

| Candidate evidence | What it already states |
| --- | --- |
| `container_spatial_mono`, `container_temporal_mono` in `OwnedContainerEntailments.v` | Monotonicity in the final interpretation. |
| `container_spatial_comm`, `container_spatial_assoc` in that file | Spatial commutativity and associativity for arbitrary assertions in the final interpretation. |
| `container_spatial_emp_elim` | One unit direction, with a wand-free premise; not yet the general unit theorem. |
| `container_barrier_spatial` | One barrier-distribution direction for an active constant owner and wand-free operands. |
| `container_history_complete` | Collapse of the specific writer-cell/store history used by the container. Compare its statement with E12; they are not interchangeable without proof. |
| `repaired_temporal_resource_associative` in `RepairedSeparation.v` | Resource regrouping available to lift to arbitrary final-interpretation assertions. The separate `repaired_temporal_assertion_associative` is stated for the older pointwise interpretation. |
| `persistent_spatial_wand_adjoint`, `persistent_temporal_wand_left_adjoint`, `persistent_temporal_wand_right_adjoint` in `PersistentRules.v` | All three adjunctions already hold in the final interpretation. |
| `persistent_assertion_flushing_closed` in `PersistentAssertions.v` | Closure of every assertion under the current generalized future relation. |

The result table will give exact theorem names and files for each instance,
including wrappers or generalizations where necessary. Existing resource
algebra can be reused; a similarly named theorem about a different assertion
interpretation cannot be counted without a valid transport argument.

## Search, proof, and reporting procedure

1. State the general final-interpretation targets in Rocq before proving
   them. Retain the ID above in comments or theorem names.
2. Screen the risky schemas with small heaps/buffers, duplicate writes,
   mark subsets, both held-lock tokens, and disjunctive formulas permitting
   independent split witnesses. Include processor counts relevant to the
   lock encoding and inactive annotation values. Report search bounds.
3. Prove each surviving instance generally, or formalize an explicit
   countermodel. For a failed general statement, state and check any useful
   restricted form without changing satisfaction.
4. Add every new named result to `_CoqProject`/`Audit.v` and run the proof
   checks. Search output alone is not a refutation or a proof.
5. Report the complete result table at the 4A checkpoint, before choosing
   the inductive rule set for 4B. If a result contradicts a current checked
   claim or suggests a change to the grammar/interpretation, report that
   immediately.

Part 4B should use the surviving laws, first-order rules, adjunctions and
the recurring container entailments. Its inductive constructors must not
include an unrestricted `persistent_entails P Q` escape hatch. Pure boolean
and arithmetic side conditions remain allowed, as agreed. The rule
statements get a separate check-in before their soundness proof.

Part 4C then supplies CONS/UNLOCK variants taking entailment derivations and
reconstructs the one-item container. A remaining semantic premise must be
named. Sound additional assertion rules needed by later examples can be
added without requesting approval; the next report will list them.

The earlier [Section 4.1 token design](paper-priority-1-design.md) is parked
until this work is complete. No new semantic derivation of that example is
being built ahead of the assertion proof system.
