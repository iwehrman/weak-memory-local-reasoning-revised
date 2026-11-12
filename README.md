# Weak-Memory Local Reasoning

A Rocq formalization of Ian Wehrman's 2012 dissertation, with a **proved
soundness and operational adequacy theorem for an explicitly repaired
Chapter 4 calculus**.

The active system combines spatial framing, temporal framing, ownership
transfer in both directions, and parallel composition under one safety
predicate. It includes the structural and primitive rules, full
capture-avoiding assignment substitution, EX, and explicit any-writer heap
rules. A container that removes a shared item, uses it privately, and returns
it has an actual derivation tree; a second version uses choice and loops to
retry. Both have concrete executions and all-execution safety results.

This does not prove the printed Theorem 1 unchanged. Checked counterexamples
refute several printed claims. The repaired system removes INV, omits SHARE
and FRAME-STM, restricts temporal framing through a mode index, transfers the
invariant at lock actions, and makes the semantic and variable conditions
explicit. Its two standing hypotheses are a guarded heap invariant and two
distinct active processors; no finite-domain assumption is needed.

Read [the complete comparison with the dissertation](notes/current-calculus.md)
for the exact scope and [checkpoint 11](review/checkpoint-11.md) for the latest
review report. Earlier safety/calculus experiments are superseded as the
active design; their chronology and source map are preserved in
[development history](notes/development-history.md).

## Main results

| Result | Source |
| --- | --- |
| 21-constructor mode-indexed judgment, soundness by induction, operational adequacy from derivations | [OwnedCalculus.v](theories/OwnedCalculus.v) |
| Single safety predicate, unchanged since checkpoint 5 | [OwnedSafety.v](theories/OwnedSafety.v) |
| General transfer, framing and parallel rules | [OwnedRules.v](theories/OwnedRules.v), [OwnedFraming.v](theories/OwnedFraming.v), [OwnedParallel.v](theories/OwnedParallel.v) |
| Structural/primitive/heap rules and EX | [OwnedStructural.v](theories/OwnedStructural.v), [OwnedPrimitives.v](theories/OwnedPrimitives.v), [OwnedHeap.v](theories/OwnedHeap.v), [OwnedExists.v](theories/OwnedExists.v) |
| Reusable derived cell, assignment and while rules | [OwnedDerivedRules.v](theories/OwnedDerivedRules.v) |
| Original container derived inside the calculus, exercising FRAME-TM and EX | [OwnedContainerDerivation.v](theories/OwnedContainerDerivation.v) |
| Retrying container derived using choice and loops | [OwnedRetryContainer.v](theories/OwnedRetryContainer.v) |
| 52-step successful trace, two failed retry iterations, all-run safety and completed-run restoration | [OwnedRetryTrace.v](theories/OwnedRetryTrace.v) |
| General final invariant restoration for emp-to-emp clients with a lock-free initial frame | [OwnedExecution.v](theories/OwnedExecution.v) |

Adequacy proves no abort for every finite execution prefix and a postcondition
on termination. It does not prove termination, deadlock freedom or fairness.
An unfinished prefix may hold the lock with the invariant open. The stronger
completed-run container results relate the restored invariant pool to the
actual final memory; the unrelated foreign frame can only undergo its own
futures.

## Build and check

Validated on macOS with Rocq 9.3.0 and OCaml 5.5.2. Only Rocq's standard
library is used.

```sh
brew install rocq
make check
```

`make` compiles every file in `_CoqProject`. `make check` additionally runs
`rocq check` on `WMLR.Audit` and its dependencies. The audit currently reports
**683 declarations closed under the global context**, including every new
lemma/theorem in the final calculus and retrying-container development.
There are no admitted proofs or declared axioms. The proofs do not require
choice, functional extensionality, or a finite processor domain.

For a fresh build, run `make clean` followed by `make check`. Editors can use
`_CoqProject` for the `WMLR` namespace and source paths.

## Scope and next work

The active calculus-level soundness proof is complete. Assertion entailments
are still proved semantically by hand, so reusable assertion rules and proof
automation are the main usability work. Expression-valued lock schemas,
recursive predicates and Chapter 5's experimental extensions are outside the
proved calculus. LOCK/UNLOCK currently use constant positive processor IDs;
the other primitive schemas support expressions. SHARE and FRAME-STM are
explicit omissions, not admitted cases. Chapter 3 syntax is present without
a separate complete sequential soundness theorem.

The original transcriptions and checked counterexamples remain available.
See [the obstruction history](notes/soundness-status.md),
[the independent review](review/independent-review.md) and
[the response establishing the replacement direction](review/lead-response.md).

## Dissertation source

Ian Anthony Wehrman, *Weak-Memory Local Reasoning*, The University of Texas
at Austin, December 2012. The inspected PDF contains 200 pages, including
front matter. [Author-hosted dissertation](https://wehrman.org/pub/dissertation.pdf)

The original LaTeX repository also contains the expression and concurrent
assertion grammars used here. The inspected `dissertation.tex` blob is
`ac4c24370dc22b3ca0892294206c2c6ac138d993`.
[Original LaTeX source](https://github.com/iwehrman/Weak-Memory-Local-Reasoning/blob/master/dissertation.tex)

SHA-256 of the inspected PDF, retrieved November 10, 2026

```text
a041c40e17e9c9bdcdaf20da8592619191b2c90747df64ebec9a8f5672ee006b
```
