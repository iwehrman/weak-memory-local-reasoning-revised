# Weak-Memory Local Reasoning

A Rocq formalization of Ian Wehrman's 2012 dissertation, beginning with the
languages and their foundational metatheory. The eventual target is Theorem 1,
soundness of the concurrent specification logic relative to its operational
semantics, with explicit corrections where required.

The current development defines the syntax of both chapters' commands,
assertions, and specifications. It proves expression and assertion independence
from irrelevant stack variables, expression substitution correctness, and
properties of the syntax. Concrete memory semantics and Theorem 1 remain open.

## Build and check

Validated on macOS with Rocq 9.3.0, OCaml 5.5.2, and the standard library bundled
by Homebrew. The project uses only Rocq's standard library.

```sh
brew install rocq
make check
```

`make` compiles every file listed in `_CoqProject`. `make check` additionally
runs `rocq check` on `WMLR.Audit` and its dependencies to check the compiled proof
objects. `theories/Audit.v` prints the assumptions of the principal theorems
when compiled. Each currently reports `Closed under the global context`.
All current proofs end with `Qed` and use no admitted facts or declared axioms.

For a fresh build, run `make clean` followed by `make check`. Editors can use
`_CoqProject` for the `WMLR` namespace and source paths.

## Source correspondence

Page numbers below are the dissertation's printed page numbers.

| Rocq file | Content | Dissertation |
| --- | --- | --- |
| `theories/Expressions.v` | Integer expressions, booleans, stacks, free variables, substitution, fresh names | §3.2, pp. 39–41 |
| `theories/Languages.v` | Sequential and concurrent primitives and commands, variable sets, command abbreviations, processor annotation | §3.3, pp. 41–48 and §4.2, pp. 88–98 |
| `theories/Assertions.v` | Both assertion grammars, named quantifiers, spatial and temporal connectives, all three wands, points-to abbreviations | §3.5, pp. 60–69 and §4.4, pp. 113–119 |
| `theories/AssertionSemantics.v` | Interpretation of the concurrent assertion grammar over a supplied resource model | Figure 4.4, p. 115 |
| `theories/Specifications.v` | Specification records, variable side conditions, invariant-preservation lemma | §3.6, §4.5, Figure 4.8 |
| `theories/Examples.v` | Message-passing syntax, quantifier examples, points-to freshness, assignment-invariant example | Figure 1.1 and §4.4 |
| `theories/Audit.v` | Assumption reports for the principal proved results | Formalization audit |

`AssertionSemantics.interpretation` takes a resource type, atomic predicates,
and spatial and temporal composition relations as explicit inputs. The
assertion theorem quantifies over every such interpretation. Instantiating
this interface with the dissertation's generalized multiprocessor memory
systems is a remaining obligation. The interface assumes no algebraic laws.

## Proved results

- `eval_expr_agrees` and `eval_bexpr_agrees` establish Lemma 1. Evaluation
  depends only on free variables.
- `eval_subst_expr` and `eval_subst_bexpr` equate syntactic substitution with
  stack update using the replacement's value in the original stack.
- `sequential_mod_in_fv` and `concurrent_mod_in_fv` show every modified variable
  occurs free in the command.
- `embedding_preserves_modifies` and `embedding_fv` characterize the variable
  sets after annotating a sequential command with a processor expression.
- `ConcurrentAssertion.points_to_fv` shows the points-to abbreviation has
  exactly the free variables of its address and contents.
- `satisfies_agrees` proves the concurrent analogue of Lemma 3 for the full
  assertion grammar, including quantifiers and separating implications.
- `assignment_preserves_invariant` proves that updating a variable absent
  from an invariant preserves its truth at a fixed resource.

The message-passing examples check syntax and variable side conditions.
Their operational correctness remains open. The assignment example proves
that a pure invariant `x = 0` becomes false after updating `x` to `1`, for any
resource interpretation. Relating that fact to the printed proof rule and
the complete `safe_n` predicate is also pending.

## Representation choices

- Identifiers are natural-number names and values are arbitrary integers.
  Boolean evaluation uses Rocq's `bool`, corresponding to the dissertation's
  values `0` and `1`.
- Arithmetic and boolean syntax implements the operators explicitly listed
  in §3.2. The ellipses can be extended as examples require.
- Free and modified variable sets are represented by lists, interpreted
  through membership. Duplicates and list order carry no semantic meaning.
- Quantifiers retain named binders and remove the bound name from the free
  variables. General capture-avoiding assertion substitution is pending.
  The concurrent points-to abbreviation already chooses a provably fresh
  processor name automatically.
- Concurrent primitives keep expression-valued processor annotations.
  Valid processor and location domains will be specified with the memory
  model. The sequential grammar omits the stray processor subscript on
  p. 44, following that chapter's uniprocessor semantics.
- `Concurrent.of_sequential` annotates a command tree. Its current theorems
  concern syntax. The semantic relationship between the two machines is a
  separate obligation.
- Temporal wand constructors follow Figure 4.4's operand order.
  `TemporalWandRight conclusion future` models `conclusion ◁− future`.

## Remaining proof work

1. Implement capture-avoiding assertion substitution and prove its semantic
   substitution lemma, including shadowing and variable capture cases.
2. Define heaps, FIFO write buffers, processor arrays, blocked processors,
   buffer-completeness sets, and the concrete transition relations. Prove
   the three operational properties of Lemma 2.
3. Define the spatial, temporal, and spatiotemporal separation relations and
   instantiate the assertion interpretation. Prove the required algebra
   and flushing closure properties.
4. Encode `safe_n`, semantic validity, and the specification inference rules.
   Check the printed assignment axiom against the invariant-preservation
   condition. Record any adopted correction with its motivating example.
5. Formalize the overlapping-heap example for Conjecture 1 on p. 174 and
   develop the decomposition-preservation lemma needed by the spatial frame
   proof. Establish the frame, concurrency, and invariant rules.
6. Complete soundness by induction on derivations and prove the message-passing
   example against the resulting semantics.

The dissertation identifies its soundness proof as incomplete on pp. 9–10.
The present project starts with the core grammars and Figures 4.7–4.8 as the
intended specification calculus. Chapter 5's experimental extensions and
the additional "daring" rules require separate investigation.

## Dissertation source

Ian Anthony Wehrman, *Weak-Memory Local Reasoning*, The University of Texas
at Austin, December 2012. The inspected PDF contains 200 pages, including
front matter. [Author-hosted dissertation](https://wehrman.org/pub/dissertation.pdf)

SHA-256 of the inspected PDF, retrieved November 10, 2026

```text
a041c40e17e9c9bdcdaf20da8592619191b2c90747df64ebec9a8f5672ee006b
```
