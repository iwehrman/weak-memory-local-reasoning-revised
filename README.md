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
refute several printed claims. The repaired system removes INV, omits
unrestricted SHARE and FRAME-STM, restricts temporal framing through a mode index, transfers the
invariant at lock actions, and makes the semantic and variable conditions
explicit. Its two standing hypotheses are a guarded heap invariant and two
distinct active processors; no finite-domain assumption is needed.

Read [the complete comparison with the dissertation](notes/current-calculus.md)
for the exact scope and [checkpoint 11](review/checkpoint-11.md) for the
accepted calculus checkpoint. Earlier safety/calculus experiments are superseded as the
active design; their chronology and source map are preserved in
[development history](notes/development-history.md).

Paper follow-up: [the first assertion-algebra results](review/paper-units-and-buffered-load.md)
prove the full unit laws, including wands, and derive reading one's own
buffered write using the existing calculus. The
[complete Figures 4.5/4.6 audit](review/paper-algebra-audit.md) classifies
every law and both readings of the small-exchange premise. Spatial and
temporal associativity, lock symmetry and the barrier/write laws survive;
strong-temporal associativity and exchange fail. The assertion
interpretation and proved program calculus are unchanged. The assertion
proof basis now has [checked soundness and derived cell rules](review/paper-assertion-soundness.md)
for all 47 approved constructors. The selected-branch container is now
[reconstructed entirely through assertion proof trees](review/paper-container-assertions.md),
including CONS/UNLOCK and the cell access helpers. The dissertation's
[message-passing example](review/paper-message-passing.md) is also derived
in that system, with its original one-cell execution conclusion, original
points-to postcondition and both outcome traces. [Named spinlocks](review/paper-named-locks.md)
are now derived for finite families, with retry and nested-lock traces.
The [producer/consumer mailbox](review/paper-mailbox.md) transfers a message
of arbitrary length without a producer fence, with a checked 95-step trace
that keeps an unrelated third-processor write pending.
[Restricted SHARE](review/paper-restricted-share.md) is proved in both modes,
with semantic lock-free pre/postconditions and no further side condition.
No constructor was added. The completed batches are collected in the
[review handoff](review/offline-queue-handoff.md). The
[review response](review/lead-response-after-algebra-audit.md) also checks
the requested remaining counterexamples in the original interpretation.
[Independent follow-up](review/paper-independent-results.md) derives the
store-then-fence cell contract, refutes its unfenced version, and proves
exact preservation of the machine's address domain. The next
[batched queue report](review/paper-independent-batch.md) adds audited
original-points-to counterexamples, the derived-rule classification, and
common-split resource framing in both modes, including release. The
[writer's theorem index](notes/paper-theorem-index.md) distinguishes original
errors, repair choices and remaining scope.

## Main results

| Result | Source |
| --- | --- |
| 21-constructor mode-indexed judgment, soundness by induction, operational adequacy from derivations | [OwnedCalculus.v](theories/OwnedCalculus.v) |
| Single safety predicate, unchanged since checkpoint 5 | [OwnedSafety.v](theories/OwnedSafety.v) |
| General transfer, framing and parallel rules | [OwnedRules.v](theories/OwnedRules.v), [OwnedFraming.v](theories/OwnedFraming.v), [OwnedParallel.v](theories/OwnedParallel.v) |
| Structural/primitive/heap rules and EX | [OwnedStructural.v](theories/OwnedStructural.v), [OwnedPrimitives.v](theories/OwnedPrimitives.v), [OwnedHeap.v](theories/OwnedHeap.v), [OwnedExists.v](theories/OwnedExists.v) |
| Reusable derived cell, assignment and while rules | [OwnedDerivedRules.v](theories/OwnedDerivedRules.v) |
| All six conjunction unit laws for arbitrary assertions, including wands | [AssertionUnits.v](theories/AssertionUnits.v) |
| Reading one's own buffered write, with arbitrary history and spatial tail | [OwnedBufferedLoad.v](theories/OwnedBufferedLoad.v) |
| Store/fence cell rule, unfenced counterexample and a complete trace | [OwnedFenceExamples.v](theories/OwnedFenceExamples.v) |
| Arbitrary-length mailbox client, buffered named-lock contracts and foreign pending-write trace | [MailboxDerivation.v](theories/MailboxDerivation.v), [MailboxAdequacy.v](theories/MailboxAdequacy.v), [MailboxTrace.v](theories/MailboxTrace.v) |
| Named spinlocks for finite families, retry and nested-lock traces | [NamedLockRules.v](theories/NamedLockRules.v), [NamedLockTrace.v](theories/NamedLockTrace.v), [NamedLockExamples.v](theories/NamedLockExamples.v) |
| Original message-passing derivation, token-free all-run theorem and both outcome traces | [MessagePassingDerivation.v](theories/MessagePassingDerivation.v), [MessagePassingAdequacy.v](theories/MessagePassingAdequacy.v), [MessagePassingTrace.v](theories/MessagePassingTrace.v) |
| Exact heap-or-buffer address-domain preservation for every execution | [ExecutionDomain.v](theories/ExecutionDomain.v) |
| Exact LOAD-P, corrected STORE-P, and forward/backward fence and lock variants | [OwnedPointsToRules.v](theories/OwnedPointsToRules.v), [OwnedAlternativeRules.v](theories/OwnedAlternativeRules.v) |
| Common-split resource framing and enabled release with pending foreign writes | [OwnedCommonSplit.v](theories/OwnedCommonSplit.v), [OwnedCommonSplitExamples.v](theories/OwnedCommonSplitExamples.v) |
| Original-points-to INV counterexamples and a printed FRAME-STM counterexample | [PrintedPointsToDerivations.v](theories/PrintedPointsToDerivations.v), [PrintedStrongFrame.v](theories/PrintedStrongFrame.v) |
| Restricted SHARE in DJ and OV, with semantic lock-free pre/postconditions | [OwnedShare.v](theories/OwnedShare.v), [OwnedShareOverlap.v](theories/OwnedShareOverlap.v) |
| SHARE and literal STORE-P counterexamples in the final interpretation | [OwnedAlternativeCounterexamples.v](theories/OwnedAlternativeCounterexamples.v) |
| Further assertion laws and checked associativity/lock countermodels | [AssertionAlgebra.v](theories/AssertionAlgebra.v), [AssertionAlgebraCounterexamples.v](theories/AssertionAlgebraCounterexamples.v) |
| Full barrier distribution, lock symmetry and successive-write collapse | [AssertionBarrierAlgebra.v](theories/AssertionBarrierAlgebra.v), [AssertionLockAlgebra.v](theories/AssertionLockAlgebra.v), [AssertionWriteAlgebra.v](theories/AssertionWriteAlgebra.v) |
| Complete small/full-exchange classification, with checked witnesses | [Audit report and theorem map](review/paper-algebra-audit.md) |
| Remaining T4 and strong-temporal exchange refutations in the original interpretation | [OriginalAlgebraCounterexamples.v](theories/OriginalAlgebraCounterexamples.v) |
| Original container derived using assertion proof trees throughout, exercising FRAME-TM and EX | [OwnedContainerDerivation.v](theories/OwnedContainerDerivation.v), [OwnedContainerAssertions.v](theories/OwnedContainerAssertions.v) |
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
**1,316 declarations closed under the global context**, including every new
lemma/theorem in the final calculus, retrying container, paper algebra audit
and paper-strengthening work.
There are no admitted proofs or declared axioms. The proofs do not require
choice, functional extensionality, or a finite processor domain.

For a fresh build, run `make clean` followed by `make check`. Editors can use
`_CoqProject` for the `WMLR` namespace and source paths.

## Scope and next work

The active program and assertion calculi have soundness proofs. The approved
47-constructor assertion basis also derives cell exclusion, drained-write
conversion, value hiding and drained-history collapse. The selected-branch
container now uses these rules for every assertion obligation. The separate
retrying variant remains checked but retains some semantic entailment proofs.
The dissertation's message-passing example now uses that system and has
the original one-cell execution conclusion. Named spinlocks and the
arbitrary-length producer/consumer mailbox are derived too. Restricted SHARE is proved in DJ and OV; the requested queue
is complete and awaits independent review. Completeness and proof automation
are outside the current work queue. Expression-valued lock schemas,
recursive predicates and Chapter 5's experimental extensions are outside the
proved calculus. LOCK/UNLOCK currently use constant positive processor IDs;
the other primitive schemas support expressions. Unrestricted SHARE and
FRAME-STM remain omitted. Restricted SHARE is a semantic theorem, with
corollaries from derivations, rather than a new constructor. Chapter 3 syntax
is present without
a separate complete sequential soundness theorem.

The original transcriptions and checked counterexamples remain available.

The paper-strengthening results are recorded in the
[A/B report](review/paper-strengthening-ab.md) and
[C/D report](review/paper-strengthening-c.md). They include counterexamples
under the original semantics, elimination of the overlap-mode judgment for
unlock-free derivations, and counterexamples establishing the need for the
framing and soundness restrictions. The proposed universal donation
obstruction needs a stronger non-vacuity hypothesis; the isolated original
FRAME-TM counterexample remains optional work. The core semantics and both
calculus definitions are unchanged.
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
