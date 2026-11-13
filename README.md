# Weak-Memory Local Reasoning, Revised

A Rocq mechanization of the program logic from Ian Wehrman's 2012
dissertation, [*Weak-Memory Local Reasoning*][dissertation], together with
a short report on what it found.

The dissertation proposed a separation logic for concurrent programs on an
x86-like, total-store-order (TSO) memory model, and left its soundness
proof unfinished. This repository finishes the job, with one caveat: the
logic as originally stated is not sound. The mechanization shows where it
fails, repairs it, and proves the repaired logic sound.

**Start with the report: [paper/main.pdf](paper/main.pdf).** It recalls
the original logic, explains what was wrong and what changed, and walks
through example proofs. It is written for a reader who knew the
dissertation but has forgotten the details.

## Findings

- **The original calculus is inconsistent.** Four of its rules together
  derive false specifications, for example that `skip` changes the
  contents of a memory cell. Several supporting claims are also false,
  each with a checked counterexample.
- **A repaired calculus is sound.** It has 21 rules. It keeps the
  assertion language, `emp` as a unit, the temporal frame rule (for
  commands that do not release the lock) and the original load and store
  axioms. It replaces the invariant rule with lock and unlock rules that
  transfer ownership of the invariant.
- **Adequacy.** A derivable specification guarantees that no execution of
  the machine aborts, and that the postcondition holds on termination.
- **A proof system for assertions.** 47 rules, proved sound. Completeness
  is not claimed.
- **Worked examples**, all derived in the calculus: a store followed by a
  fence, reading one's own buffered write, a shared container, the
  dissertation's own message-passing example, named locks built on the
  machine's single global lock, and a producer/consumer mailbox.

The results are about partial correctness. They say nothing about
termination, fairness or deadlock.

## Building and checking

Requires [Rocq](https://rocq-prover.org) 9.3 and nothing beyond its
standard library. Validated on macOS with Rocq 9.3.0 and OCaml 5.5.2.

```sh
brew install rocq
make check
```

`make` compiles everything listed in `_CoqProject`. `make check` also runs
the independent kernel checker over [`theories/Audit.v`](theories/Audit.v),
which prints the assumptions of 1,316 theorems. Every one is reported as
closed under the global context: there are no axioms and no admitted
proofs.

The report is built with [Tectonic](https://tectonic-typesetting.github.io):

```sh
tectonic paper/main.tex
```

## Where to look

| Path | Contents |
| --- | --- |
| [`paper/`](paper) | The report, in LaTeX, with a built PDF. |
| [`theories/`](theories) | The Rocq development: 196 files, about 30,000 lines. |
| [`notes/`](notes) | Design notes. [`current-calculus.md`](notes/current-calculus.md) compares the repaired calculus with the dissertation rule by rule, and [`paper-theorem-index.md`](notes/paper-theorem-index.md) maps the report's claims to theorems. |
| [`review/`](review) | The working record: checkpoint reports, review requests and responses, kept as written. |
| [`scripts/`](scripts) | Bounded searches that were used to look for counterexamples before attempting general proofs. |

Some entry points into `theories/`:

| Result | File |
| --- | --- |
| The safety predicate and validity | [`OwnedSafety.v`](theories/OwnedSafety.v) |
| The calculus, soundness and adequacy | [`OwnedCalculus.v`](theories/OwnedCalculus.v) |
| The assertion proof system and its soundness | [`AssertionDerivation.v`](theories/AssertionDerivation.v), [`AssertionSoundness.v`](theories/AssertionSoundness.v) |
| Inconsistency of the original calculus | [`OriginalPointsToDerivations.v`](theories/OriginalPointsToDerivations.v), [`OriginalStrongFrame.v`](theories/OriginalStrongFrame.v) |
| Other counterexamples to original claims | [`OriginalLocalCounterexamples.v`](theories/OriginalLocalCounterexamples.v) |
| Why the side conditions are needed | [`OwnedNecessity.v`](theories/OwnedNecessity.v) |
| The shared container | [`OwnedContainerDerivation.v`](theories/OwnedContainerDerivation.v) |
| The dissertation's message-passing example | [`MessagePassingDerivation.v`](theories/MessagePassingDerivation.v), [`MessagePassingAdequacy.v`](theories/MessagePassingAdequacy.v) |
| Named locks and the mailbox | [`NamedLockRules.v`](theories/NamedLockRules.v), [`MailboxDerivation.v`](theories/MailboxDerivation.v), [`MailboxAdequacy.v`](theories/MailboxAdequacy.v) |

## Scope

The development covers Chapter 4 of the dissertation, the concurrent
logic. Not covered:

- unlocked access to shared state (the dissertation's "daring" rules, and
  so algorithms such as Dekker's);
- the strong temporal frame rule, which is unsound as stated and is
  omitted;
- allocation, recursive predicates, permissions and the other extensions
  of Chapter 5;
- a soundness proof for the sequential logic of Chapter 3.

The soundness theorem assumes that the invariant comes from a restricted
fragment and that there are at least two processors. The report explains
both assumptions and shows that neither can simply be dropped.

## How this was made

The proofs and the report were written with AI assistance, using Claude
Fable and ChatGPT Astra. One model led the proof development and the other
reviewed it independently and wrote the report; each checked the other's
work against the Rocq sources. The `review/` directory is the record of
that exchange. Every theorem cited in the report is checked by the Rocq
kernel.

## Source

Ian Anthony Wehrman, *Weak-Memory Local Reasoning*, PhD dissertation, The
University of Texas at Austin, December 2012.
[PDF][dissertation] · [LaTeX source][latex]

The definitions were transcribed from the LaTeX source at blob
`ac4c24370dc22b3ca0892294206c2c6ac138d993`.

## License

[MIT](LICENSE).

[dissertation]: https://wehrman.org/pub/dissertation.pdf
[latex]: https://github.com/iwehrman/Weak-Memory-Local-Reasoning
