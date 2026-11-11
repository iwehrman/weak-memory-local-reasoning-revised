# Soundness: checked obstructions and repairs

The revised full soundness theorem is **not proved**. The current development
contains checked negative results about the printed claims and a separate
repaired model. The repaired model has associative generalized-memory
operations, actual flushing decomposition, ownership-aware safety, operational
adequacy, and derivation soundness for a bounded calculus. The latest
future-aware wand interpretation has full assertion flushing closure and
base heap/lock rules, with a restricted release rule. The subsequent ownership
protocol proves protected-memory transfer with private resources, and a first
parallel theorem composes two threads under explicit variable-interference
conditions, including private loads into registers. General frame and
concurrency rules remain open. See [the semantic changes](persistent-semantics.md)
and [the parallel theorem's exact premises](parallel-ownership.md).

## The assignment axiom fails against full safety

`Safety.v` encodes `safe_n` and specification validity from pp. 131-132.
`SafetyExamples.v` gives this instance of the printed assignment axiom:

```text
invariant: x = 0
precondition: true
command: x := 1 on processor 1
postcondition: true
```

Substitution into the pure postcondition leaves `true`, so the printed axiom
derives this specification. Start with all registers zero, empty memories,
and no held lock. After the assignment the invariant is false for every
possible shared-memory component. The global lock is still free. Consequently
the post-step invariant-or-locked obligation fails already at safety index 1.

`printed_assignment_invalid` proves this specification invalid.
`printed_assignment_soundness_false` proves that even the pure-postcondition
subset of the printed assignment axiom cannot be sound. Any calculus
containing that unrestricted axiom therefore cannot satisfy Theorem 1 as
printed. This argument does not depend on the frame conjecture or the
associativity problems below.

The checked repair `assignment_preserves_environment` requires the assigned
variable to be absent from the invariant's free variables.
`repaired_assignment_action` additionally checks the concrete assignment
transition and substituted pure precondition/postcondition. It covers the
non-silent action in the printed model.

The separate `repaired_pure_assignment_valid` now proves full validity in the
repaired model when the invariant is pure and does not mention the assigned
variable. It covers every safety index, admissible frame, and silent flush,
using proved flushing closure of pure assertions. General spatial/temporal
invariants require their own flushing-closure theorem in that pointwise model.
The newer `persistent_assignment_valid` uses the proved full closure theorem
for future-aware assertions and permits an arbitrary invariant, with the same
free-variable side condition and a pure postcondition.

## Lookup-only list overriding is not associative

Let `a`, `b`, and `c` be singleton buffers writing values 1, 2, and 3,
respectively, to the same address. The list `[2, 1, 3]` is admitted by
`a override (b override c)`: it is an interleaving and its last lookup is 3.
It is not admitted by `(a override b) override c`: the inner result must
place 1 before 2, and interleaving with 3 cannot reverse that order.

`printed_buffer_override_not_associative` checks this counterexample to
Proposition 2(2), including the interleaving requirement from the preceding
prose. Thus the failure is not caused by omitting that requirement.

`ordered_overrides` is a conservative candidate repair. A write from the
future input can be selected only after all writes to its address in the
past input have been selected. The following are proved:

- It implies the printed override relation and preserves every write.
- It includes concatenation and, for disjoint domains, all interleavings.
- It is associative, constructively, in both directions.
- Its output head comes from a real component head; a future-origin head
  cannot bypass a conflicting past write.

`memory_ordered` lifts this repair to memory systems, retaining the printed
compatibility relation. It includes both spatial and temporal compositions.
`ordered_flush_split` and `ordered_flushes_split` prove replacements for the
one-step and finite flushing-decomposition claims used in frame reasoning:
the component residuals arise from actual flush transitions.

## Blocking facts also obstruct memory associativity

There is a second, independent problem. Take:

- `a`: a pending write to address 1 on processor 1;
- `b`: a flushed write to address 1;
- `c`: an empty memory contributing the fact that processor 1 is blocked.

The compatibility guard admits `a` composed with `(b composed with c)`,
because processor 1 is blocked in that grouping. It rejects composing `a`
with `b` first, where the blocking fact is absent.
`printed_spatiotemporal_not_associative` checks this for the original
memory separator. `printed_memory_compatibility_not_associative` shows that
replacing only list overriding by the ordered version does not fix it.

`stable_compatible` is a separate conservative candidate: conflicts are
checked regardless of whether a processor is currently blocked. It implies
the printed compatibility relation. `stable_compatibility_associative`
proves its definedness conditions are invariant under temporal regrouping;
`temporal_join_associative` proves equality of the resulting temporal tuples
up to pointwise equivalence. The combined generalized-memory results are
described below.

The stronger guard excludes some compositions permitted by the dissertation.
That is an explicit change to expressiveness, not a transcription correction.
It is now used in the explicitly separate repaired assertion interpretation
and safety model. The printed definitions remain unchanged.

## Combined repair and constructive associativity

`RepairedSeparation.v` combines stable compatibility and ordered overriding
in `memory_repaired`, and lifts it to `repaired_spatiotemporal`.
`repaired_temporal` combines stable compatibility with the original temporal
completeness side condition. The following are checked:

- Associativity for both operations on generalized memories and on the
  well-formed resource subtype used by assertions. Intermediate witnesses
  are themselves valid resources.
- Inclusion of spatial and repaired temporal composition in repaired
  spatiotemporal composition; inclusion of the repaired relations in their
  printed counterparts; well-formedness and spatiotemporal unit properties.
- Actual one-step and finite flushing decomposition preserving the stronger
  compatibility guard, plus spatial flushing decomposition.
- Temporal assertion associativity in `repaired_interpretation`; a nonempty
  points-to model still exists and still describes a flushed cell.

`BufferSelections.v` enumerates the finite ordered merges of two finite
buffers and selects a valid intermediate merge. This makes the intermediate
buffer array a function, avoiding a choice axiom when lifting buffer
associativity to arbitrary processor domains. No processor-finiteness,
functional-extensionality, or proof-irrelevance assumption is used. The
enumeration constructs proof witnesses; it is not an efficient execution engine.

The compatibility repair changes expressiveness. Restricting the framing
relation reduces the environments quantified by safety, so repaired validity
does not automatically imply printed validity. Repaired adequacy is proved
directly against the original operational steps. Locked-update specifications
remain an important test of the stronger guard.

## What the safety adequacy results establish

`safe_execution_residual` follows any finite concrete execution from a state
covered by `safe_n`, maintaining a valid shared/frame/local decomposition
and a real flushing history for the external frame.
`safe_execution_no_abort` excludes a fault at the resulting state.
`safe_execution_post` establishes the local postcondition if execution has
reached an annotated skip. The shared invariant holds whenever the global
lock is not held, as required by the environment predicate.

The development also proves index and postcondition monotonicity, and the
consequence and disjunction rules for specification validity. These results
assume safety where stated; they do not assume the intended derivation
soundness theorem, any separation-algebra law, or assertion flushing closure.

## Ownership-aware safety and the proved calculus fragment

`RepairedSafety.v` defines an explicit alternative to `safe`. Besides the
combined framing relation, it requires each post-step private and shared
domain to stay within the union of the previous private and shared domains.
The external frame must still evolve by actual flushes. This permits ownership
transfer through the invariant while excluding acquisition from an unrelated
spatial frame. It does not require a private residual to stay private throughout.

`repaired_environment_flush` constructs such witnesses for silent transitions,
assuming flushing closure of the invariant. `repaired_skip_safe` covers all
indices for flush-closed invariant and postcondition predicates. These closure
premises are discharged for pure assertions, giving full corrected assignment
validity. `owned_spatial_recombination` proves the connection between the new
witness requirement and the replacement frame lemma; the frame inference rule
itself remains open.

`RepairedRules.v` proves consequence, disjunction, and sequencing for repaired
validity. It also defines `pure_derivation`, containing skip, assignment with
invariant freshness, sequencing, and pure consequence, and proves
`pure_fragment_sound` by induction on derivations. No rule has a safety or
program-validity premise. The logical implications in consequence concern
only expression evaluation.

`repaired_safe_execution_no_abort` and `repaired_safe_execution_post` reprove
operational adequacy. `RepairedExamples.v` derives `x := 1; x := x + 1` under
the invariant `y = 0`, constructs an initial environment containing allocated
heap cells and a pending write, and exhibits a run flushing that write between
assignments. The derivation and adequacy theorem establish `x = 2` for every
terminating execution from that initial state, independently of flush scheduling.

## What still prevents a full positive soundness claim

The pointwise temporal wand is not flushing closed: a two-processor example
becomes false when flushing enables a composition with a barrier. The newer
future-aware interpretation repairs this, proves closure for all formulas,
preserves wand-free meanings, and satisfies all three wand adjunctions.
`persistent_calculus_sound` now covers the base rules documented in
[persistent-semantics.md](persistent-semantics.md).

General release is a separate obstruction. Safety permits a false invariant
while locked, but the printed unlock contract does not restore it. A concrete
two-processor instance is invalid. The proved release rule requires the truth
of a pure invariant in the precondition. A separate ownership protocol now
proves acquisition/release for arbitrary assertions and a heap-restoring
critical-section example, with spatial external frames and no separate private
payload at the closed boundary. Its assertion syntax and interpretation are
unchanged. This is a checked bounded design, not the full general invariant
rule. See [ownership-protocol.md](ownership-protocol.md).

The subsequent `private_valid` semantics carries an explicit private component
through the closed boundary. Acquisition/release accept arbitrary invariant
and private assertions; framed cell operations and buffered release preserve
private resources. A derived whole-critical-section rule and a checked
two-cell example restore shared memory and read the retained private cell
after release. Spatial external frames remain a restriction. See
[private-ownership.md](private-ownership.md).

`private_parallel_rule` now composes two closed-to-closed derivations for
distinct processors satisfying the existing mutual variable-interference
condition. The earlier blanket register-preservation premise is removed;
its theorem remains a corollary. A single shared ownership
decision gives both processors consistent views through acquisition, flushing,
and release. The proof also retains a terminated thread's private postcondition
as a frame after the operational semantics erases the parallel node. It covers
all ordinary executions of the pair, proving no abort and, on termination,
one restored invariant and the spatial conjunction of both private posts.
The three-cell example has competing writers, checked traces in both orders,
and a reachable state with a temporarily violated invariant and a blocked
contender. A further example performs post-release private loads into distinct
variables and proves both register results for every terminating execution.
Variable-support bounds protect intermediate assertions and a finished
thread's postcondition. A checked negative example uses the same destination
twice and loses the first result, demonstrating the interference condition's
role. The full concurrency and frame rules remain open. See
[parallel-ownership.md](parallel-ownership.md).

Capture-avoiding assertion substitution, general expression/framed heap
axioms, choice/loop, general parallel, invariant, and frame rules remain open.
The ownership condition is a requirement that each proof must construct; it
does not establish suitable witnesses for every printed specification.
Further rearrangement laws may be needed. See [frame-decomposition.md](frame-decomposition.md).
