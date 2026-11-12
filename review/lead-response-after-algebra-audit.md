# Lead response after the 4A review

Responds to [reviewer-guidance-after-algebra-audit.md](reviewer-guidance-after-algebra-audit.md)
at `b5c0167`. I accept the review's direction: keep `⋉` as the existing
abbreviation, use the surviving algebra, and state the assertion rules
before proving their soundness. The accepted buffered-load result needs no
new program constructor.

The additional original-semantics checks are complete. The
[4B rule statement](paper-assertion-rules-statement.md) is also ready for
the agreed check-in; its inductive definition type-checks, but its soundness
proof has not been written.

## Qualifications to the three proposed paper findings

1. **Finding 1 needs the premise reading stated.** With the uniform
   connective-inclusion reading, its classification is right: the remaining
   exceptions outside the `⋉` regrouping/exchange cases are E6 and T4.
   Under the literal formula-specific premise, T7 and T8 also fail for
   `(*,;)` and `(;,*)`, although neither connective is `⋉`. The literal
   cases with `⋉` only on the inside fail too. Suggested wording:
   “The unit, spatial/temporal associativity, commutativity, lock-symmetry
   and barrier/write-collapse laws survive. Lock exclusion and the named
   writer entailment need qualifications; exchange needs the separate
   classification below.”
2. **Finding 2 is correct for the enumerated laws:** E3 for `⋉`, T7/T8
   with `⋉` outside, and T9. Both readings of the T7/T8 premise fail in
   these cases. Do not extend that wording to every rearrangement involving
   `⋉`: its unit and barrier-distribution laws, for example, survive.
3. **Finding 3 is correct for the uniform premise.** It forces the active
   processor domain to be empty for the mixed `*`/`;` schemas. With the
   literal premise the general schemas are false on every nonempty domain,
   not “true and unusable.” This does not claim that every individual
   formula instance on a nonempty domain fails.

These are wording qualifications to an accepted table, not changes to the
checked results.

## Requested refutations in the original interpretation

All requested additional refutations transfer, using the same resource
witnesses. They are proved in
[OriginalAlgebraCounterexamples.v](../theories/OriginalAlgebraCounterexamples.v),
whose statements explicitly use `models`.

| Claim | Original-model evidence |
| --- | --- |
| T4 with an invalid or inactive writer annotation, despite an inhabited all-processor cell | `original_points_to_invalid_writer_refuted`; includes annotation 0, negative integers and inactive processor 3 in domain `{1,2}` |
| T7 with `⋉` outside and each of `*`, `;`, `⋉` inside | `original_small_exchange_strong_left_refuted`, indexed by all three choices |
| T8 with `⋉` outside and each of `*`, `;`, `⋉` inside | `original_small_exchange_strong_right_refuted`, indexed by all three choices |
| The other associativity direction, `(P ⋉ Q) ⋉ R` to `P ⋉ (Q ⋉ R)` | `original_strong_associativity_left_model` and `original_strong_associativity_right_not_model` |
| T9 full exchange | `original_full_exchange_left_model`, `original_full_exchange_right_not_model`, `original_full_exchange_refuted` |

Each small-exchange refutation includes the **true uniform inclusion
premise** as a conjunct. Hence the result refutes both readings, rather
than only the weaker displayed premise. The previously checked
right-to-left associativity and opposite-lock witnesses remain in
`AssertionAlgebraCounterexamples.v`.

The transfer is deliberately one-way only for positive witnesses:
wand-free satisfaction in the final interpretation implies original
satisfaction. Every negative statement is proved separately against the
original relations, considering all original decompositions. In these
examples the heap/buffer merge equations, spatial disjointness, lock-bit
disjointness and temporal mark condition already force the contradiction;
the strengthened compatibility condition is not needed.

Thus the paper can classify these as errors in the original printed laws,
not merely differences caused by the repairs. This extension does not claim
an original-model audit of every positive law, nor of the four literal
small-exchange pairs without `⋉` outside. Those are outside this specific
transfer request.

## 4B proposal and verification

[AssertionDerivation.v](../theories/AssertionDerivation.v) gives 47 proposed
constructors, grouped in the statement document. They contain no general
assertion-entailment, satisfaction, safety or validity premise. Boolean
facts and the previously identified processor conditions are explicit.
`⋉` has no constructor or special proof rule.

The only additional cell identities proposed beyond the audited laws are
the two used to normalize reacquisition: distinct flushed cells compose
spatially, and a later flushed cell overwrites an earlier value at the same
address. The first retains an explicit pure disequality guard; the second
is a one-way entailment. A finite exact-atom search found no counterexamples.
Their general proofs belong to the next soundness stage.

`make check` passes with **847 audited declarations closed**, including all
17 new original-model lemmas/theorems. There are no axioms or admitted
proofs. Kernel checking the proposed inductive definition establishes that
it is well-typed, **not** that its rules are sound. The existing assertion
interpretation, 21-constructor program calculus and its soundness theorem
are unchanged.

This is the requested checkpoint after the 4B rule statements and before
their soundness proof. No 4C container reconstruction has been started.
