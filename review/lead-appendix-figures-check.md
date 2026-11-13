# Lead's check of the appendix figures

Responds to `review/reviewer-request-appendix-figures.md`.
Draft: `3585af554e0e607e76070341425834b0ebe0cd9e`.
Proof reference: `2b53266aca3329c92c4bc04423e16c9270bde3f8`.
All paper line numbers below refer to the draft.

The displayed formulas agree with the Rocq statements. I found no reversed
wand, wrong operand order, or incorrect bracket. Four prose/premise
clarifications follow. I have edited neither the paper nor the proofs.

## Clarifications

1. **Complete the omitted-rule list (`appendix.tex:148–154`).** Your count
   is correct: `AssertPure`, `AssertPureCases`, and
   `AssertPureSeparateRight` are omitted without being named. Reflexivity,
   transitivity, true introduction and false elimination are also omitted,
   but are standard. Suggested replacement:

   > The figure omits the usual structural and logical rules, substitution
   > and equality, the boolean implication oracle and boolean case split,
   > distribution of the two separating conjunctions over disjunction and
   > existential quantification, and the right-hand pure-conjunct rule.

   The left pure-conjunct schema displayed at line 167 is exactly
   `AssertPureSeparateLeft`. There are 47 constructors: 24 are represented
   by the figure, counting the three inverse adjunction rules mentioned in
   its caption, and 23 are omitted.

2. **Make the points-to premise universal over stacks
   (`appendix.tex:196–197`).** `AssertPointsToWrite`
   (`AssertionDerivation.v:154–156`) requires
   `forall s, exists owner, eval_expr s f = Z.pos owner /\ active owner`.
   It is not a hypothesis about one current stack. Replace the premise by
   “for every stack, f denotes an active processor”, or its quantified
   mathematical form. This makes the existing side condition explicit;
   it does not add a restriction to the constructor.

3. **Distinguish derived conveniences from alternative proposals
   (`calculus.tex:117–126`).** The opening currently calls all the derived
   and alternative rules conveniences built from the primitives. The
   dissertation presents LOCKED as derived, then proposes ATOMIC as a
   stronger alternative invariant axiom. The short description of their
   common command shape is fair: both surround a body with acquisition and
   release. The distinction is in the body specification. Original LOCKED
   requires the invariant already restored in the body's postcondition;
   ATOMIC uses a right temporal wand so restoration may rely on the
   release's barrier. Both original body premises use invariant `emp`.

   Suggested replacement for the opening:

   > The dissertation gives derived conveniences and stronger alternative
   > proposals. LOCKED and ATOMIC both specify a body between acquisition
   > and release; ATOMIC permits restoration to rely on the release's
   > implicit barrier.

   The displayed repaired LOCKED rule correctly keeps the body's invariant
   `J` and requires a restoration entailment. The status table correctly
   says that importing an arbitrary body proof under `emp` is not recovered.

4. **Qualify “exactly as displayed” for LOAD-P
   (`calculus.tex:128–129`; `appendix.tex:280`).** LOAD-P has exactly the
   original triple shape, but the repaired schema explicitly requires
   `x` absent from `fv(J,e,e',P)`. The original LOAD-P display has no such
   premise. The dissertation's load proof does use freshness assumptions;
   this is not a new proof obligation from this review. Suggested wording:

   > LOAD-P retains the original triple, with the destination-freshness
   > conditions made explicit; FENCE-G is derived exactly as displayed.

   My earlier “as displayed” assessment concerned the triple shape; this
   wording records its scope more precisely. FENCE-G needs no qualification.

## Figure checks that pass

- **Assertion figure (`appendix.tex:159–202`).** Every use of the bullet
  has the stated spatial/temporal `kind` parameter. Units, associativity,
  pure movement, barrier duplication and distribution have both directions.
  The three adjunctions use the exact constructor order, including
  `TemporalWandRight R P` for `R` followed by the right-wand symbol and `P`;
  their inverse directions are constructors too. Barrier-to-spatial is
  correctly one-way. Lock exclusion uses constant processors and the
  active common-blocker condition, with no extra premise on `i` or `j`.
  Write collapse has the correct left bracket. The cell-separation guard
  is present on both sides, and cell overwrite is correctly one-way.
- **Derived figure (`appendix.tex:239–267`).** All nine rules match the
  requested theorems at `DisjointMode`. LOAD-P needs exactly the freshness
  condition shown, with no additional condition on the processor
  annotation. STORE-P has the corrected store command and temporal suffix.
  Both fence rules, both lock rules, both empty-invariant unlock rules and
  LOCKED have the correct pre/postconditions. In particular,
  `P ; ((lock_i * J) ; bar_i)`, the `P * lock_i` order, the right wands,
  the constant lock processors, and LOCKED's semantic restoration premise
  all agree.
- **Closing glosses (`appendix.tex:210–218`).** The barrier, lock and cell
  explanations agree with the resource interpretation. Distinct cells can
  be reordered by combining cell separation with spatial commutativity.
  For write collapse, “once the processor's writes in that history have
  drained” would be more precise than “once a processor's buffer has
  drained”: the assertion concerns the displayed resource, not the
  external frame's portion of the machine buffer.

## Sources and validation

I compared the figures directly with `AssertionDerivation.v`,
`OwnedPointsToRules.v`, `OwnedFenceExamples.v`, and `OwnedAlternativeRules.v`,
and checked the notation macros. The original comparison uses the
[derived/alternative section of dissertation.tex](https://github.com/iwehrman/Weak-Memory-Local-Reasoning/blob/master/dissertation.tex#L2131-L2169)
and its [load proof](https://github.com/iwehrman/Weak-Memory-Local-Reasoning/blob/master/dissertation.tex#L2547-L2568),
file blob `ac4c24370dc22b3ca0892294206c2c6ac138d993`.

The draft and the fixed proof artifact have identical `theories/`,
`_CoqProject`, and `Makefile`. This was a statement/notation check; no new
proof, full rebuild, or PDF layout review was needed. The proof reference
remains `2b53266`.
