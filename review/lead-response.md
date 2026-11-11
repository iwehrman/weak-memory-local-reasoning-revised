# Development response — checkpoint 1

This responds to [the independent review](independent-review.md) at commit
`0ac73e4`, reviewing the development through `66106f1`. It records the
development direction before any replacement prototype is written.

**I accept both printed-rule counterexamples as faithful. I agree to drop
the separate protected/private assertion positions and the retirement
interpretation from the target design.** There is no disagreement on either
of the two questions identified for this checkpoint.

The existing proofs remain useful evidence under their stated definitions.
They will remain in the repository as earlier experiments; their results
will not be presented as pieces of an already integrated sound calculus.

## 1. Fidelity of the two derivations

I recompiled `Review.v` and `Derivations.v` and independently checked their
proof objects with:

```sh
rocq compile -Q theories WMLR review/Review.v
rocq compile -Q theories WMLR review/Derivations.v
rocq check -silent -Q theories WMLR -Q review '' Review Derivations
```

Both passed. Their five audited declarations reported `Closed under the
global context`. The abstract trilemma remains a conditional theorem: its
frame, consequence, unit, adequacy and execution assumptions are explicit
parameters, not conclusions discharged merely by that audit. The concrete
printed-rule counterexamples supply the stronger application to this logic.

I also compared `printed` in `Derivations.v` with Figures 4.7–4.8 in the
original LaTeX, including the side condition on FRAME-TM. The source checked
was `dissertation.tex`, blob `ac4c24370dc22b3ca0892294206c2c6ac138d993`.
Relevant source: [the concurrent rules](https://github.com/iwehrman/Weak-Memory-Local-Reasoning/blob/master/dissertation.tex#L2094-L2121)
and [the concurrent algebra](https://github.com/iwehrman/Weak-Memory-Local-Reasoning/blob/master/dissertation.tex#L1931-L1955).

### INV's parenthesization

Parsing the premise as `J * (P * lock_i)` is faithful. The original algebra
includes spatial associativity; interpreting the printed text as
`(J * P) * lock_i` gives the same premise up to consequence and that
equivalence. The choice of bracketing does not add an ownership-transfer
permission absent from the printed rule.

### The owner-specific cell

`processor_cell(k,x,v)` expands to `write(k,x,v) ; barrier(k)`, using only
the printed assertion grammar. It is not the dissertation's all-processor
points-to abbreviation, and the review properly distinguishes them.
SKIP, CONS, INV and FRAME-TM range over arbitrary assertions; the checked
instances are therefore legal instances of those rules. They suffice to
refute the printed calculus. Reproducing the examples with the stronger
points-to abbreviation is not necessary for that conclusion, and I do not
label that further variant kernel-checked.

I accept both `printed_calculus_stale_value_unsound` and
`printed_calculus_foreign_barrier_unsound`. My earlier qualification that
the regional example had not been reproduced from the printed rules is
superseded by this work. Retaining these rules, the entailments used in the
derivations and the intended adequacy is impossible; changing the safety
predicate alone does not repair that combination.

## 2. Architecture decisions

### Drop permanent protected/private assertion positions

The target will have one owned local assertion. Acquisition should bring
the protected resources into that owned resource, with only the acquirer's
justified completeness information. Consequence should operate on that
assertion rather than on permanently separate protected/private slots.

A shared pool still belongs in the semantic account of ownership while
the lock is free. That does not require retaining the separate assertion
calculus used by `Separated*`.

The re-marking theorem is a prerequisite, not an assumption I will install
in the new lock proof. It must first be proved for a precisely stated
invariant fragment, or refuted at checkpoint 2.

### Drop the retirement interpretation as the development direction

I accept `retired_later_cell_can_erase_earlier`. The permissive cell atoms
allow hidden retirement at unrelated addresses. That defect is additional
to losing the right-unit law for `emp`, and was missed in my assessment.
I will not extend `Retired*` to pending buffers as the next development step.

The new target preserves `emp` as a two-sided unit. No tombstone atom,
implicit relinquishment inside `emp`, or revised cell entailment will be
introduced without an immediate checkpoint. Explicit tombstones remain
an alternative to compare only if the chosen rule-level repair fails.

### Adopt design D as the candidate, not as an established solution

The candidate replaces printed INV with explicit lock/unlock ownership
rules, uses the writer-existential flushed-cell abbreviation, and initially
restricts FRAME-TM to commands containing no unlock. Spatial and strong
temporal framing are targets for proof, not yet inherited results.

The changed points-to abbreviation is a real contract change. The old
all-processor-complete formula remains expressible; it is not equivalent
to the proposed ordinary cell assertion. Re-marking at a single acquisition
must not claim that unrelated processors have drained.

## 3. Qualifications to the review

These do not change my agreement on the two decisions above.

1. **Removing INV is essential.** Both checked bad programs are `skip`.
   Merely adding "contains no unlock" to FRAME-TM would leave those
   derivations available. The repair is the package of explicit ownership
   boundaries, replacement of INV, and restricted framing. Changing the
   points-to abbreviation alone is likewise insufficient: the review's
   foreign-barrier counterexample already uses an owner-specific cell.

2. **The invariant fragment needs an exact treatment of pure assertions.**
   In the existing interpretation `Pure true` holds on the review's `pend`
   resource, including its pending processor-2 write. I checked this small
   witness in a scratch proof. Thus the proposed fragment with bare pure
   atoms is not automatically buffer-free. This does not refute re-marking
   invariance itself. It separates two obligations that must both be
   examined at checkpoint 2. Guarding pure facts with `emp`, or requiring
   buffer-freeness separately, are possible changes; neither is silently
   adopted here.

3. **The syntactic no-unlock restriction is conservative.** The abstract
   trilemma establishes a conditional incompatibility, not an optimality
   theorem for that particular restriction. A rule permitting frames
   disjoint from the released footprint may ultimately retain more
   expressiveness. We should first test the simpler candidate and keep
   the necessity and sufficiency claims separate.

4. **Discarding old values does not settle every history question.** The
   checked history-invention theorem concerns the specified cell formulas.
   It does not justify declaring arbitrary temporal assertions, other
   processors' completeness information or wands information-free. The
   container proof and more general framing obligations still require
   actual entailments.

## 4. Checkpoints and immediate escalation conditions

### Checkpoint 1 — this response

No replacement prototype, new validity definition or new safety proof has
been written. The response accepts both printed-rule derivations and both
architecture decisions. Any disagreement about those conclusions should be
settled before implementation resumes.

### Checkpoint 2 — invariant fragment, before safety proofs

State the proposed fragment exactly and test whether satisfaction at full
completeness survives replacing the marks by the acquirer's singleton mark.
Report a proof or a counterexample, distinguishing that property from
buffer-freeness and any other requirements of LOCK. Check in before proving
downstream safety rules. Any necessary change to the proposed fragment is
itself an immediate checkpoint.

### Checkpoint 3 — first frame-shape attempt

First state the candidate lemma precisely, with its modes, composition
relations, resource futures, marks and footprint assumptions. Search small
buffers, emphasizing a frame and local resource writing the same address
on the same processor. Report the bounds and outcome of the search before
investing in the general proof. A bounded search with no counterexample is
not a proof. Report the first proof attempt's success or failure as well.

### Stop and report immediately if

- A proposed rule is false, including on a contrived example.
- A proof needs a new side condition, assertion atom or changed entailment.
- The acquire/remove/release/private-use/return container example cannot be
  derived with an unrelated foreign write pending as sketched.
- Implementation would add another validity predicate alongside the
  existing ones.

The last condition also applies to the proposed mode-indexed safety model:
before defining it, I will identify what it replaces and how the
development is being consolidated. I will not evade that checkpoint by
giving another experimental validity predicate a new name. Archived proof
files may remain, but only one candidate soundness target should be active.

The next action after this checkpoint is the invariant-fragment search,
not a buffered retirement port or another safety framework.
