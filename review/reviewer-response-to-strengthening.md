# Reviewer response to the strengthening batches

Responds to `50f1dbb` and `2b53266`.

## Accepted

- **A.** Both local counterexamples are now stated for `models` and
  `valid_specification`, with the original flushing order transcribed
  separately. The paper cites `original_flushing_closure_false` and
  `original_arbitrary_invariant_unlock_invalid`, and its footnote is gone.
- **B.** Mode elimination holds, and it is an equivalence for derivability.
  The paper's main text now shows one judgment, with FRAME-TM carrying
  "c contains no unlock"; the modes are confined to the semantics section
  and the appendix's mechanized figure.
- **C2, C3, C4.** Accepted and cited. The paper now says that the
  restriction on FRAME-TM, some restriction on the invariant, and the
  two-processor hypothesis are each necessary, and it follows your scope
  note on C3: a restriction is necessary, not this exact fragment.
- **D1.** Accepted and cited in one clause. The premise is vacuous, as you
  say, and the paper does not make more of it than that.

## C1: my statement was wrong; no replacement is requested

Two lock tokens composing into a resource with no admissible environment is
a clean refutation, and it is the same phenomenon the algebra audit found
for lock exclusion. The paper keeps its qualified sentence that the
trilemma does not show the adopted restriction to be the weakest possible.
C2 gives the necessity statement the paper actually needs, so I am not
asking for the repaired form of C1.

## D2: not requested

The paper keeps its prose for FRAME-TM against the original predicate.

## One last check

The paper changed in `sections/calculus.tex`, `results.tex`, `changes.tex`,
`wrong.tex` and `proofs.tex` to use the single judgment and to cite the new
theorems. When convenient, please check those five files against the
proofs as you did before, in particular the new paragraph on the temporal
frame rule and the restated soundness theorem. The paper now cites
`2b53266`.
