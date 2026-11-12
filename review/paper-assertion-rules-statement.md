# Paper checkpoint 4B: proposed assertion rules

**Follow-up:** the reviewer approved this exact 47-constructor basis.
[The soundness checkpoint](paper-assertion-soundness.md) now proves all
constructors and the four planned derived cell rules, without adding rules.
The text below records the original statement-stage proposal.

This is the rule-statement checkpoint requested after the accepted
[4A audit](paper-algebra-audit.md). The precise inductive definition is
[AssertionDerivation.v](../theories/AssertionDerivation.v).
**It type-checks; soundness is the next proof obligation.** Nothing in the
current program calculus depends on this proposed relation yet.

The design has 47 constructors: 18 logical/substitution rules, 11 rules for
spatial and temporal conjunction, six directions of wand adjunction, four
barrier rules, three lock rules, three write rules, and two cell rules.
Several constructors encode both directions of an equivalence with a
direction parameter. This count is separate from the existing 21 program
rule constructors.

## Judgment, scope and intended theorem

Write `P ⊢ₐ Q` for `assertion_derivation active P Q`. It is a syntactic
derivation judgment indexed only by the active processor domain. It has no
mode or invariant parameter. Assertions keep their existing syntax and
interpretation, including future-aware wands and

```text
P ⋉ Q = (P * Q) ∧ (P ; Q).
```

There is no proof rule indexed by `⋉`. Its introduction and projections
are ordinary `∧` rules applied to the expansion. Its units, monotonicity,
lock symmetry and barrier idempotence are derived in the same way; its
associativity and exchange laws are absent.

The intended theorem, not assumed or admitted in the source, is:

```coq
Theorem assertion_derivation_sound active p q :
  assertion_derivation active p q -> persistent_entails active p q.
```

The target has no global processor-count, finiteness, invariant-fragment or
wand-free hypothesis. Individual atomic rules expose their processor
conditions. The standing fragment/two-processor hypotheses on the existing
program soundness-plus-adequacy theorem remain as before.

No rule takes arbitrary `persistent_entails`, `models`, `persistent_models`,
command safety or command validity as a premise. Pure boolean/arithmetic
facts remain semantic side conditions, as authorized. Syntactic freshness
and explicit processor membership are also permitted premises.

In the tables, `⊗` ranges only over `*` and `;`. An `≡ₐ` row means two
oriented derivation rules. `C(a,v)` denotes the existing writer-existential
cell, not the all-processor `a ↦ v`. `P[x:=e]` uses the already checked
capture-avoiding `assertion_subst` operation.

## Logical and substitution rules

| Constructor(s) | Rule |
| --- | --- |
| `AssertRefl`, `AssertTrans` | Identity and composition of derivations |
| `AssertTrue`, `AssertFalse` | `P ⊢ₐ true`; `false ⊢ₐ P` |
| `AssertAndIntro` | From `P ⊢ₐ Q` and `P ⊢ₐ R`, infer `P ⊢ₐ Q ∧ R` |
| `AssertAndLeft`, `AssertAndRight` | The two conjunction projections |
| `AssertOrLeft`, `AssertOrRight` | The two disjunction injections |
| `AssertOrCases` | From `K ∧ P ⊢ₐ R` and `K ∧ Q ⊢ₐ R`, infer `K ∧ (P ∨ Q) ⊢ₐ R` |
| `AssertExistsIntro` | `P[x:=e] ⊢ₐ ∃x.P` |
| `AssertExistsElim` | From `K ∧ P ⊢ₐ R`, infer `K ∧ (∃x.P) ⊢ₐ R`, provided `x ∉ fv(K) ∪ fv(R)` |
| `AssertForallIntro` | From `P ⊢ₐ Q`, infer `P ⊢ₐ ∀x.Q`, provided `x ∉ fv(P)` |
| `AssertForallElim` | `∀x.P ⊢ₐ P[x:=e]` |
| `AssertSubstitute` | From `P ⊢ₐ Q`, infer `P[x:=e] ⊢ₐ Q[x:=e]` |
| `AssertPure` | A finite conjunction of pure booleans entails a pure boolean if that implication holds at every stack |
| `AssertPureCases` | From `P ∧ b ⊢ₐ Q` and `P ∧ ¬b ⊢ₐ Q`, infer `P ⊢ₐ Q`, for a boolean expression `b` |
| `AssertEquality` | `(e=f) ∧ P[x:=e] ⊢ₐ P[x:=f]` |

`K` is an assertion used as additive context, not a heap frame. The
contextual disjunction and existential elimination rules retain it in
each branch. Uncontextual versions follow by choosing `K=true`. The
freshness conditions include that context explicitly.

`AssertPure` is restricted to a list of the existing boolean expressions.
`pure_assumptions [] = true`, and a nonempty list expands to nested `∧`.
It cannot import a heap, lock, barrier or wand entailment. `AssertPureCases`
uses the decidability of boolean evaluation, not a general classical
assertion-negation principle. `AssertEquality` rewrites using the checked
substitution semantics; it does not assume a semantic equivalence of
arbitrary assertions.

## Spatial and temporal conjunction

| Constructor(s) | Rule |
| --- | --- |
| `AssertSeparateMono` | From `P ⊢ₐ P'` and `Q ⊢ₐ Q'`, infer `P ⊗ Q ⊢ₐ P' ⊗ Q'` |
| `AssertUnitLeft`, `AssertUnitRight` | `emp ⊗ P ≡ₐ P` and `P ⊗ emp ≡ₐ P` |
| `AssertAssociative` | `(P ⊗ Q) ⊗ R ≡ₐ P ⊗ (Q ⊗ R)` |
| `AssertSpatialComm` | `P * Q ⊢ₐ Q * P` |
| `AssertOrSeparateLeft`, `AssertOrSeparateRight` | Distribution of `⊗` over `∨` in either argument, in both directions |
| `AssertExistsSeparateLeft` | `(∃x.P) ⊗ Q ≡ₐ ∃x.(P ⊗ Q)`, provided `x ∉ fv(Q)` |
| `AssertExistsSeparateRight` | `P ⊗ (∃x.Q) ≡ₐ ∃x.(P ⊗ Q)`, provided `x ∉ fv(P)` |
| `AssertPureSeparateLeft` | `(b ∧ P) ⊗ Q ≡ₐ b ∧ (P ⊗ Q)` |
| `AssertPureSeparateRight` | `P ⊗ (Q ∧ b) ≡ₐ (P ⊗ Q) ∧ b` |

The last two rows require a pure boolean `b`. They do not assert that pure
formulas are buffer-free, nor distribute an arbitrary additive conjunction
through separation. They use the fact that every component sees the same
stack. This is how a load's pure register result moves out through its
spatial frame.

## Three adjunctions

Each equivalence below is between derivability statements and contributes
two inference rules. Argument order matches `PersistentRules.v` exactly.

| Constructors | Adjunction |
| --- | --- |
| `AssertSpatialWandIntro`, `AssertSpatialWandElim` | `P * Q ⊢ₐ R` iff `Q ⊢ₐ SpatialWand(P,R)` |
| `AssertTemporalWandLeftIntro`, `AssertTemporalWandLeftElim` | `P ; Q ⊢ₐ R` iff `Q ⊢ₐ TemporalWandLeft(P,R)` |
| `AssertTemporalWandRightIntro`, `AssertTemporalWandRightElim` | `Q ; P ⊢ₐ R` iff `Q ⊢ₐ TemporalWandRight(R,P)` |

Their semantic proofs already exist for the final interpretation. No
pointwise or original-interpretation wand rule is substituted for them.

## Barrier, lock and write rules

| Constructor | Rule and side condition |
| --- | --- |
| `AssertBarrierEmp` | `B(i) ⊢ₐ emp` |
| `AssertBarrierDuplicate` | `B(i) ⊗ B(i) ≡ₐ B(i)` |
| `AssertBarrierDistribute` | `(P ⊗ Q) ; B(i) ≡ₐ (P ; B(i)) ⊗ (Q ; B(i))` |
| `AssertBarrierSpatial` | `P ; B(i) ⊢ₐ P * B(i)` |
| `AssertLockRight` | `P ; L(i) ≡ₐ P * L(i)` |
| `AssertLockLeft` | `L(i) ; P ≡ₐ L(i) * P` |
| `AssertLocksExclusive` | `L(i) * L(j) ⊢ₐ false`, given an active constant processor `k` with `k ≠ i` and `k ≠ j` |
| `AssertWritesExclusive` | `W(a,i,u) * W(a,j,v) ⊢ₐ false` |
| `AssertWritesCollapse` | `(W(a,i,u) ; W(a,i,v)) ; B(i) ≡ₐ W(a,i,v) ; B(i)` |
| `AssertPointsToWrite` | `a ↦ v ⊢ₐ W(a,i,v)`, provided annotation `i` denotes an active processor at every stack |

Except for the constant owners/blocker in `AssertLocksExclusive`, the
displayed arguments are arbitrary expressions. The only processor-domain
conditions are the common blocker for lock exclusion and activity of the
named writer for points-to. Invalid annotations need no premise in the
other rules; the audited atomic interpretations account for them.

Same-owner lock exclusivity under two active processors will be a derived
rule obtained by choosing a distinct active blocker. Exclusion with `;`
follows from `AssertLockLeft`, and exclusion with `⋉` follows from its
spatial projection. There is no unconditional opposite-lock exclusion.

`AssertBarrierSpatial` plus additive introduction gives E9,
`P ⋉ B(i) ≡ₐ P ; B(i)`. E10 is an instance of `AssertLockLeft`.
Barrier-suffix elimination `P ; B(i) ⊢ₐ P` follows from T1, monotonicity
and the temporal unit. These need no extra constructors.

The semantic E8 theorem for `⋉` remains proved but is **not included as a
primitive rule**, and is not being claimed as already derivable in this
basis. No planned container step uses it. The proposal likewise omits the
vacuous mixed small-exchange schemas whose uniform premise forces an empty
processor domain. Completeness is not a goal.

## Two cell rules needed at reacquisition

These are proposed additions to the assertion proof basis, without a
change to assertion semantics or program rules:

```text
AssertCellsSeparate:
  (a ≠ b) ∧ (C(a,u) ; C(b,v))  ≡ₐ  (a ≠ b) ∧ (C(a,u) * C(b,v))

AssertCellOverwrite:
  C(a,u) ; C(a,v)  ⊢ₐ  C(a,v)
```

The disequality is the existing pure boolean `BNot (BEq a b)` and is
retained on both sides. This supports variable addresses known distinct
under an assertion, not just globally distinct constant expressions. For
the container's constant addresses its proof is a boolean calculation.
The overwrite rule is one-way because only that direction is needed.

Their intended semantic proofs use the existing shape theorem for `C`:
each component has a singleton heap, empty buffers, no lock token and a
nonempty set of marks. Distinct addresses give a spatial split; equal
addresses give the later heap value. Neither argument requires giving the
cell a particular processor's mark.

The general proofs have **not** been written. The
[exact-atom search](../scripts/search_cell_algebra.py) checked two active
processors, addresses 1 and 2, values 0 and 1, and every nonempty mark
subset. All compositions were retained: eight distinct-cell instances and
eight overwrite instances, with no counterexample.
[Search output](paper-cell-algebra-search.jsonl).

The following cell rules are intended as **derived proof trees** from this
basis and the existing abbreviations, rather than further constructors:

- Spatial exclusion: `C(a,u) * C(a,v) ⊢ₐ false`.
- A drained write is a cell: `W(a,i,v) ; B(i) ⊢ₐ C(a,v)`.
- Value hiding: `C(a,v) ⊢ₐ ∃x.C(a,x)` with `x ∉ fv(a)`.
- Drained history: `((∃x.C(a,x)) ; W(a,i,v)) ; B(i) ⊢ₐ C(a,v)`,
  choosing `x` fresh for `a,i,v` when moving its binder outward.

The first uses the write-exclusion rule after opening the cells and
discarding their barrier suffixes. The second and third use existential
introduction. The last uses barrier distribution, value-quantifier
distribution and cell overwrite. Capture-avoiding substitution and any
required bound-name conversions must be handled inside these derivations;
they are not semantic entailment premises. If a target cannot be derived,
the missing assertion rule will be reported explicitly.

## How the basis covers the container obligations

The initial 4C target is the same selected-branch one-item program in
`OwnedContainerDerivation.v`, including the pending foreign spatial frame.
The existing retrying version remains checked; its reconstruction can use
the same basis plus the logical/substitution rules. No example is being
reproved semantically in advance of the assertion system.

| Existing recurring obligation | Proposed derivation ingredients |
| --- | --- |
| Rearrange the lock, flag and private tail for loads/stores | Spatial associativity and commutativity |
| Extract a load's register equality through a spatial frame | `AssertPureSeparateRight`, additive projections/introduction |
| Inject the two read results; filter them through `assume` | Disjunction rules and the restricted pure-boolean rule |
| Forget a stored cell's old value | Existential introduction and separation monotonicity |
| Normalize first acquisition | Barrier-suffix elimination, distribution over disjunction, spatial units |
| Normalize second acquisition with the buffered private history | Temporal associativity, barrier distribution, drained-history collapse, lock conversion, the two cell rules |
| Restore the invariant at either unlock | Barrier distribution across `*`, history collapse, value hiding, disjunction injection |
| Add/remove the unrelated foreign frame's `emp` | Spatial units |

The difficult reacquisition step can be expressed without any `⋉`
rebracketing. Starting from

```text
H(x,9) ; ((L(1) * J) ; B(1))
```

associate temporally and distribute the barrier. History collapse and
barrier-suffix elimination give `C(x,9) ; (L(1) * J)`. Lock conversion and
temporal associativity move the lock outside, yielding
`L(1) * (C(x,9) ; J)`. Distribute through the two branches of `J`:

```text
C(x,9) ; C(f,0)                 ⊢ₐ C(f,0) * C(x,9)
C(x,9) ; (C(f,1) * ∃u.C(x,u))  ⊢ₐ C(f,1) * ∃u.C(x,u)
```

The first line uses distinct-cell separation and spatial commutativity.
In the second, open the existential, convert the distinct flag/item pair
to temporal composition, bring the flag past the private cell, collapse
the two cells at `x`, and restore spatial composition. The later branch
may overwrite the old private value; that is the same branch retained by
the existing semantic entailment until the load/assume selects the empty
container case. This is not a claim of unconditional cell preservation
through an overlapping temporal suffix.

## Proof and integration boundary

After this statement checkpoint, the planned sequence is:

1. Prove soundness of the 47 constructors, reusing the audited laws and
   proving the two cell identities. No unrestricted entailment constructor
   may be added to discharge a difficult case.
2. Prove the derived cell/logical rules above and their quantifier plumbing.
3. Give CONS and UNLOCK wrappers whose assertion premises are
   `assertion_derivation` trees. They translate to the current
   `OwnedConsequence` and `OwnedUnlock` using the new soundness theorem;
   their commands, modes and processor/invariant conditions do not change.
4. Reconstruct the one-item container using those wrappers, with no
   manually supplied semantic assertion entailments. Report any remaining
   semantic premise or missing rule at 4C.

The intended wrapper signatures are, schematically:

```text
P ⊢ₐ P'     J ⊢ᵐ {P'} c {Q'}     Q' ⊢ₐ Q
-----------------------------------------
             J ⊢ᵐ {P} c {Q}

A ; B(i) ⊢ₐ J * B
-----------------------------------------
J ⊢ᴰᴶ {L(i) * A} release(i) {B}
```

At this checkpoint only the rule definitions and the independent
original-model counterexample proofs have been implemented. `make check`
passes with 847 audited declarations closed and no axioms or admitted
proofs. This checks the proposed relation's type and its dependencies;
**it does not establish `assertion_derivation_sound`.** That proof and the
4C reconstruction remain ahead.
