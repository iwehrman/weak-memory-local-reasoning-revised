# Weak-Memory Local Reasoning

A Rocq formalization of Ian Wehrman's 2012 dissertation, covering the
languages, concurrent execution and assertion semantics, and foundational
metatheory.
The eventual target is Theorem 1,
soundness of the concurrent specification logic relative to its operational
semantics, with explicit corrections where required.

The current development defines both chapters' command, assertion, and
specification syntax, and implements Chapter 4's multiprocessor memory model
and operational semantics. Generalized memories, all three separation relations,
and the concrete assertion interpretation are now defined. The development
proves Lemma 2, complete execution examples, foundational separation properties,
and an operational replacement for the invalid Conjecture 1. Integration of
that replacement into the safety predicate and Theorem 1 remain open.

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
| `theories/Machine.v` | Heaps, FIFO write buffers, blocked sets, processor domains, flushing, memory well-formedness | Definition 4 and §4.2, pp. 90–95 |
| `theories/BufferRelations.v` | Order-preserving interleavings, list overriding, domain and lookup lemmas | Section 2.1.3, pp. 14-15 |
| `theories/Separation.v` | Generalized-memory validity, spatial/temporal/spatiotemporal separation, unit properties, commutativity and inclusions | Definition 5 and Section 4.3, pp. 99-113 |
| `theories/FrameDecomposition.v` | Preservation of memory domains and operational replacement frame-decomposition lemmas | Repair work for Conjecture 1 and Lemma 21, pp. 174-176 |
| `theories/OperationalSemantics.v` | Primitive and command steps, aborts, successful execution closure, Lemma 2 and preservation proofs | Figures 4.1–4.2, pp. 93–96 and Lemma 2, p. 48 |
| `theories/ExecutionExamples.v` | Complete store-buffering, fence, and lock/unlock traces, blocked operations and faults | Concrete checks of §4.2's execution rules |
| `theories/Assertions.v` | Both assertion grammars, named quantifiers, spatial and temporal connectives, all three wands, points-to abbreviations | §3.5, pp. 60–69 and §4.4, pp. 113–119 |
| `theories/AssertionSemantics.v` | Interpretation of the concurrent assertion grammar over a supplied resource model | Figure 4.4, p. 115 |
| `theories/ConcreteAssertions.v` | Figure 4.4 instantiated over valid generalized memories; points-to denotes a flushed cell | Sections 4.4.1-4.4.2, pp. 114-119 |
| `theories/SeparationExamples.v` | Concrete assertion witnesses, completeness checks, and a checked refutation of Conjecture 1 | Sections 4.3-4.4 and p. 174 |
| `theories/Specifications.v` | Specification records, variable side conditions, invariant-preservation lemma | §3.6, §4.5, Figure 4.8 |
| `theories/Examples.v` | Message-passing syntax, quantifier examples, points-to freshness, assignment-invariant example | Figure 1.1 and §4.4 |
| `theories/Audit.v` | Assumption reports for the principal proved results | Formalization audit |

`AssertionSemantics.interpretation` takes a resource type, atomic predicates,
and spatial and temporal composition relations as explicit inputs. The
assertion theorem quantifies over every such interpretation. `ConcreteAssertions`
instantiates it with the subtype of well-formed generalized multiprocessor
memories, including for the resources quantified by separating implications.
The interface assumes no algebraic laws.

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
- `lemma2` proves that a successful concurrent step shrinks the free and
  modified variable sets and preserves every variable outside the original
  modified set. Each property also holds for successful finite executions.
- `steps_preserve_well_formed` and `steps_preserve_lock_complete` establish
  preservation of processor-domain membership and lock completeness.
- `buffer_lookup_newest`, `enqueue_read_own_write`, and
  `enqueue_other_processor_read` establish most-recent-write forwarding and
  the immediate visibility of an enqueued write to its own processor.
- `store_buffering_zero_zero` proves a full execution in which both loads
  read zero, both stores subsequently reach shared memory with value one,
  and all buffers finish empty. Result registers initially contain minus one.
- `store_fence_trace` and `lock_store_unlock_trace` check complete executions
  that flush the local buffer before a fence or unlock proceeds.
- `spatial_well_formed`, `temporal_well_formed`, and
  `spatiotemporal_well_formed` show that composition preserves Definition 5,
  including its empty-completeness-set heap condition and processor domains.
- `spatial_comm` proves spatial commutativity. All three operations have the
  empty generalized memory as a unit, with uniqueness up to pointwise
  equivalence. `temporal_functional` proves uniqueness of temporal results.
- `spatial_in_spatiotemporal` and `temporal_in_spatiotemporal` prove the two
  inclusions used by the specification logic.
- `points_to_requires_flushed` proves that the fresh-binder abbreviation
  describes a single flushed heap cell, empty buffers, no blocked processors,
  and completeness of every active processor. `concrete_points_to_cell`
  supplies an actual satisfying model; pending writes cannot satisfy it.
- `printed_conjecture1_false` refutes the printed conjecture with a successful
  assume step and an overlapping one-cell decomposition.
- `steps_domain_subset` proves that successful executions introduce no new
  memory locations. `spatial_frame_recombination_sets` uses this fact to prove
  equality of spatial and spatiotemporal recombinations when the frame flushes
  and the local residual comes from actual execution.
- `spatial_frame_recombination_region` permits the local residual to occupy
  a subregion of an executed ownership region, allowing that region to include
  shared state. Connecting this premise to global safety is still required.

The earlier message-passing examples in `Examples.v` check syntax and variable
side conditions. Their general operational correctness remains open. The
assignment example proves
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
  The sequential grammar omits the stray processor subscript on
  p. 44, following that chapter's uniprocessor semantics.
- `Concurrent.of_sequential` annotates a command tree. Its current theorems
  concern syntax. The semantic relationship between the two machines is a
  separate obligation.
- Temporal wand constructors follow Figure 4.4's operand order.
  `TemporalWandRight conclusion future` models `conclusion ◁− future`.

## Execution model

Locations are positive integers. An arbitrary predicate on positive integers
specifies the active processor domain. The execution examples use processors
1 and 2; the assertion examples also exercise a domain containing every positive
processor identifier. Primitive execution requires an active processor.
Nonpositive and inactive processor annotations have no primitive transition.
Addresses outside the current heap and local-buffer domains, including zero
and negative addresses, produce the load/store aborts in Figure 4.1 when the
operation is enabled.

Buffers append writes at the tail and flush from the head. Loads use the newest
matching local write, falling back to shared memory. Blocked processors can
still assign registers and enqueue stores. Loads and flushing require an
unblocked processor. Fences, lock acquisition, and lock release require an
empty local buffer. A false assumption waits, while a false assertion aborts.

The language retains the dissertation's partial blocked sets for future
separation reasoning. `memory_well_formed` requires blocked processors and
nonempty buffers to belong to the active domain. `lock_complete` expresses
the stronger property that the lock is free or has a single owner. Execution
preserves each property when it holds initially. Set comparisons use pointwise
logical equivalence, so these results require no extensionality axioms.

Figure 4.2 uses an unannotated terminal `skip`. Generated terminal skips in
this encoding use the constant annotation 1, which is ignored for termination.
Every annotated skip is treated as terminal, including when removing it from
a sequence or parallel composition. Silent flushes can continue after the
program reaches skip, as permitted by the figure's `c-tau` rule.

`step` represents a successful transition and `abort` a transition to the
terminal fault outcome. `steps` is the reflexive-transitive closure of
successful transitions. A faulting execution has a successful prefix followed
by an abort. The semantics imposes no fairness or termination assumption.

The implemented machine is Chapter 4's concurrent machine. A separate
Chapter 3 machine and a semantic comparison with `Concurrent.of_sequential`
remain future work.

## Separation and assertion model

A generalized memory adds a completeness set to the operational memory.
`generalized_well_formed` requires completeness and blocking to stay within
active processors, inactive buffers to be empty, and the heap to be empty
when the completeness set is empty. The concrete assertion universe is the
subtype of tuples satisfying these requirements. Pointwise equality avoids
functional extensionality and proof irrelevance axioms.

Spatial separation interleaves buffers and requires disjoint memory domains
and blocked sets. Temporal separation concatenates buffers, uses right-biased
heap overriding, and imposes the compatibility and completeness conditions
on pp. 104-105. Spatiotemporal separation uses list overriding and temporal
compatibility, without temporal separation's additional completeness condition.
All operations union the blocked and completeness sets.

The list-override equation on p. 14 only displays lookup equality, although
its preceding sentence explicitly restricts the result to interleavings.
`buffer_overrides` makes both requirements explicit. Lookup equality alone
would allow arbitrary deletion or duplication of writes, contradicting the
stated interleaving restriction and Proposition 2(5).

The atomic assertion predicates follow Figure 4.4. In particular, `emp`
does not fix the completeness set, and a barrier on an inactive or nonpositive
processor has the same models as `emp`. A pending write may block only its own
processor; a flushed write blocks none and requires its originating processor
to be complete. The proved unit properties concern the empty generalized
memory (empty completeness set), not every model of the assertion `emp`.

## Frame proof repair

The printed Conjecture 1 permits an arbitrary post-step decomposition. Even
an unchanged one-cell heap can then be assigned both to a frame and to a local
residual by heap overriding. Such a decomposition cannot be spatial.

The proved replacement tracks which locations a residual may own through
actual execution. It establishes the recombination equality needed by the
spatial-frame argument under that additional, operationally justified
hypothesis. The region variant permits transfers inside a larger region,
such as the combined invariant and private state.

This does **not** yet establish the full spatial frame rule: the printed safety
predicate does not supply these execution-backed witnesses automatically.
The exact integration obligation and possible repair are recorded in
[notes/frame-decomposition.md](notes/frame-decomposition.md). No change to
`safe_n` or the specification rules has been silently adopted.

## Remaining proof work

1. Implement capture-avoiding assertion substitution and its semantic lemma.
2. Prove or repair the remaining algebraic claims, including associativity
   in Propositions 5-7, and generalized flushing closure (Proposition 9).
   These are not assumed by the concrete interpretation.
3. Encode `safe_n`, semantic validity, and the specification inference rules.
   Check the assignment axiom's invariant-preservation side condition.
4. Connect the replacement frame-decomposition lemma to safety witnesses,
   including shared-invariant ownership transfers and preservation of the
   local postcondition. Derive witness normalization if possible; otherwise
   explicitly revise the safety semantics and recheck the primitive rules.
5. Establish the full frame, concurrency, and invariant rules, then complete
   soundness by induction on derivations and the message-passing example.

The dissertation identifies its soundness proof as incomplete on pp. 9–10.
The present project starts with the core grammars and Figures 4.7–4.8 as the
intended specification calculus. Chapter 5's experimental extensions and
the additional "daring" rules require separate investigation.

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
