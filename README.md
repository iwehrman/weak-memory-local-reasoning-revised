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
and operational replacements for several problematic auxiliary claims.

The printed safety predicate is now formalized, with proofs of its operational
adequacy. A checked assignment instance refutes the unrestricted assignment
axiom against that full semantics, so **Theorem 1 cannot hold as printed**.
There are also checked counterexamples to two claimed associativity properties.
The combined repair now has generalized-memory associativity, flushing
decomposition, a separate assertion interpretation, and an ownership-aware
safety predicate with operational adequacy. A future-aware interpretation of
wands now has flushing closure for the full assertion grammar. A bounded
calculus including base load/store, fence, acquisition, and a restricted
release rule has checked soundness. **Full corrected soundness remains open.**
The arbitrary-invariant unlock contract has a checked counterexample. A separate
ownership protocol now proves general invariant transfer at acquire/release,
soundness of a small calculus, and a heap-restoring critical section for all
executions. It keeps assertion syntax and interpretation unchanged, but uses
open/closed judgment indices and spatial external frames. Its private-resource
extension now carries arbitrary private assertions through acquisition/release
and proves a post-release private load. A parallel rule now composes two
threads under explicit variable-interference conditions, with consistent
shared ownership and retained private postconditions. Competing protected
writes followed by private loads check for all interleavings. A general semantic
spatial frame rule now holds at closed entry, including frames with pending
writes. A subsequent generalized ownership model proves acquire/release,
flushing, bounded calculus soundness, and temporal history framing around the
whole shared/private region. A checked counterexample shows that its
unrestricted private temporal frame rule fails even for a derivable
closed-to-closed specification: invariant transfer can export another
processor's completeness mark. The replacement boundary rule and examples
check, but the general frame/concurrency integration and full soundness remain
open. A subsequent model recovers the original private temporal frame rule
with only its variable condition by keeping protected assertions separate
from private assertions while the lock is held. It checks protected updates,
private fences and loads, a bounded calculus with FRAME-TM, and operational
adequacy, including genuinely pending frames. It rejects foreign-barrier
import. Withdrawal of protected cells into private ownership now checks at
an owner fence or unlock, returning an owner-specific flushed-cell assertion;
FRAME-TM survives the relaxed footprint bound. Donation back to the protected
pool still conflicts with overlapping private heap history, even after
draining buffers. A positive reassembly lemma covers disjoint histories.
A separate retirement experiment now resolves the overlapping-heap case
in a **buffer-free fragment**: `emp` can record relinquished ownership,
so older framed values need not remain live cells. Both transfer directions,
FRAME-TM, a small calculus and all-execution examples check. A flush-simulation
lemma supports extending this design to buffered histories, but that combined
model and integration with spatial framing/concurrency remain open.
The independent review subsequently proves two unsound specifications from
the printed rules and identifies an additional cell-erasure defect in the
retirement interpretation. The subsequent target preserves `emp`'s unit laws,
drops permanent protected/private assertion slots and retirement, and uses
explicit ownership rules with restricted temporal framing. Full calculus
soundness is not yet proved. Checkpoint 2 now proves that invariants with heap-guarded pure
assertions survive re-marking to the acquiring processor alone, have empty
buffers, and cannot absorb pending writes at release. Checkpoint 3 proves
the temporal-only resource lemma but refutes the proposed generalization
to external `#`, including an acquisition case. Checkpoint 4 proves that a
fixed frame determines the local buffers and that actual machine flushes
can be attributed to one component with the other and the pool unchanged.
Checkpoint 5's approved single safety target, `owned_safe` / `owned_valid`,
is now implemented. It has closure under the full generalized-future
relation, empty-frame operational adequacy, and mode inclusion. All three
fixed acceptance tests pass: disjoint-only donation, rejected foreign-barrier
import, and a safe private store while another thread holds the lock.
Additional checked regressions cover double acquisition, split-token
contexts, and a local flush blocked by an external token. The approved scope
requires two distinct active processors for lock-specific reasoning and the
client adequacy theorem; it does not require finiteness. General LOCK and
UNLOCK are now proved for arbitrary fragment invariants. A checked
counterexample refutes the proposed unrestricted FRAME-STM rule in disjoint
mode: its spatial and temporal conjuncts can use different resource splits,
and donation need not preserve both. FRAME-STM is now omitted from the
active target while its assertion abbreviation remains unchanged.
**General FRAME-SP in both modes and semantic FRAME-TM from overlap-mode
validity are now proved**, after bounded searches found no counterexamples.
They add no lock-free-frame or no-unlock condition and need no processor-count
assumption. FRAME-TM uses the existing invariant fragment. The safety and
assertion definitions are unchanged. **General parallel composition now
holds in both modes**, including register updates and either thread
finishing first. Its only addition to the printed interference condition is
that neither command modifies variables free in the shared invariant.
Checked examples include acquisition followed by a sibling store while
blocked and two threads updating distinct registers. The requested routine
rules now check, including assignment with capture-avoiding substitution
for arbitrary assertions. **The printed strong-temporal LOAD/STORE forms
and explicit any-writer cell extensions are proved in both modes.** Their
proofs preserve the existing conjunction abbreviation for `⋉`; LOAD makes
destination and invariant freshness explicit. Checked examples include
buffer forwarding behind duplicate older writes and cross-processor cell
access without gaining new completeness marks. No further safety or assertion
change was needed. Full corrected soundness remains open.
See [the routine and heap-rule checkpoint](review/checkpoint-9.md),
[the parallel checkpoint](review/checkpoint-8.md),
[the general framing checkpoint](review/checkpoint-7.md),
[the lock rules and FRAME-STM counterexample](review/checkpoint-6.md),
[the implementation checkpoint](review/checkpoint-5-implementation.md),
[the definition proposal](review/checkpoint-5.md),
[its acceptance tests](review/checkpoint-5-acceptance.md),
[the fixed-frame and flush checkpoint](review/checkpoint-4.md),
[the frame-shape checkpoint](review/checkpoint-3.md),
[the invariant-fragment checkpoint](review/checkpoint-2.md),
[the response and development checkpoints](review/lead-response.md),
[the independent review](review/independent-review.md),
[retirement: earlier experiment and its limits](notes/retired-ownership.md),
[the preceding transfer results and obstruction](notes/ownership-transfer.md),
[the recovered FRAME-TM and its ownership discipline](notes/separated-temporal-framing.md),
[the preceding regional result and obstruction](notes/regional-ownership.md),
[the preceding framing work](notes/framing-status.md),
[the parallel rule](notes/parallel-ownership.md),
[the private-resource extension](notes/private-ownership.md), and
[the soundness status](notes/soundness-status.md) for exact claims and limits.

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
The proofs use no admitted facts or declared axioms. Constructive witness
functions do not require choice, extensionality, or a finite processor domain.

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
| `theories/OrderedBuffers.v` | Candidate event-ordering repair; associativity, conservativity, head origin; printed associativity counterexample | Repair work for Proposition 2, pp. 14-15 |
| `theories/BufferSelections.v` | Finite enumeration and constructive selection of intermediate buffers without choice | Lifting repaired buffer associativity to arbitrary processor arrays |
| `theories/Separation.v` | Generalized-memory validity, spatial/temporal/spatiotemporal separation, unit properties, commutativity and inclusions | Definition 5 and Section 4.3, pp. 99-113 |
| `theories/OrderedSeparation.v` | Candidate repaired separator and one-step/finite flushing decomposition | Repair work for Lemmas 4 and 7 |
| `theories/StableCompatibility.v` | Conservative compatibility repair; temporal definedness associativity; blocking-based counterexample | Repair work for Sections 4.3.2-4.3.3 |
| `theories/RepairedSeparation.v` | Combined repair; temporal/spatiotemporal associativity on valid generalized resources, inclusions and units | Explicit alternative to Section 4.3 |
| `theories/RepairedFlushing.v` | Actual component flushes preserving the combined repair; spatial flushing decomposition | Replacements for the flushing lemmas used in soundness |
| `theories/FrameDecomposition.v` | Preservation of memory domains and operational replacement frame-decomposition lemmas | Repair work for Conjecture 1 and Lemma 21, pp. 174-176 |
| `theories/OperationalSemantics.v` | Primitive and command steps, aborts, successful execution closure, Lemma 2 and preservation proofs | Figures 4.1–4.2, pp. 93–96 and Lemma 2, p. 48 |
| `theories/ExecutionExamples.v` | Complete store-buffering, fence, and lock/unlock traces, blocked operations and faults | Concrete checks of §4.2's execution rules |
| `theories/Assertions.v` | Both assertion grammars, named quantifiers, spatial and temporal connectives, all three wands, points-to abbreviations | §3.5, pp. 60–69 and §4.4, pp. 113–119 |
| `theories/AssertionSemantics.v` | Interpretation of the concurrent assertion grammar over a supplied resource model | Figure 4.4, p. 115 |
| `theories/AssertionSubstitution.v` | Total capture-avoiding simultaneous substitution and its semantic theorem, including quantifiers and wands | General ASSIGN support without a capture side condition |
| `theories/ConcreteAssertions.v` | Figure 4.4 instantiated over valid generalized memories; points-to denotes a flushed cell | Sections 4.4.1-4.4.2, pp. 114-119 |
| `theories/RepairedAssertions.v` | Separate interpretation using stable temporal composition; temporal assertion associativity and pure flushing closure | Candidate corrected assertion semantics |
| `theories/Safety.v` | Printed safety and validity, index/postcondition monotonicity, consequence/disjunction rules, operational adequacy, assignment-action repair | Section 4.5.2, pp. 131-132 |
| `theories/RepairedSafety.v` | Ownership-aware safety, flushing witnesses, full pure-assignment validity, operational adequacy, frame-recombination bridge | Explicit alternative to Section 4.5.2 |
| `theories/RepairedRules.v` | Consequence, disjunction and sequencing; soundness of a pure assertion derivation fragment | Checked subset of a corrected calculus |
| `theories/RepairedExamples.v` | Points-to witness, derived register program, nonempty initial environment and execution with an intervening flush | Nonvacuity and operational checks of the repair |
| `theories/GeneralizedFlushing.v` | Indexed component flushing, completeness growth, decomposition on valid generalized resources | Definition 6 and flushing-closure proof obligations |
| `theories/AssertionFlushing.v` | Flushing preservation for all atomic assertions | Proposition 9 ingredients |
| `theories/FlushingCounterexample.v` | Two-processor failure of pointwise temporal-wand closure | Obstruction to Proposition 9 under pointwise wands |
| `theories/PersistentAssertions.v` | Future-aware wands, full assertion flushing closure, free-variable theorem, equivalence for wand-free assertions | Explicit additional semantic repair |
| `theories/PersistentRules.v` | General invariant closure in primitive proofs, structural rules, and all three wand adjunctions | Corrected rule ingredients |
| `theories/HeapRules.v` | Full validity of constant-cell load/store rules with arbitrary invariants | Checked base forms of heap axioms |
| `theories/LockRules.v` | Fence and acquisition for arbitrary invariants; release with an explicit pure-invariant precondition | Checked lock rules and restricted release repair |
| `theories/OwnershipProtocol.v` | Open/closed ownership safety with spatial external frames and flushing preservation | Separate repair of protected-resource ownership |
| `theories/OwnershipRules.v` | Arbitrary-invariant acquisition/release, sequencing, and operational adequacy | Checked transfer protocol without new assertions |
| `theories/OwnershipHeap.v` | Owned cell stores, fences, and release using its implicit buffer drain | Heap operations in the ownership protocol |
| `theories/OwnershipCalculus.v` | Phase-indexed derivations and their soundness | Bounded ownership calculus |
| `theories/OwnershipExamples.v` | All-execution heap restoration, concrete buffered traces, rejected unrestored release | Two-processor protocol checks |
| `theories/PrivateOwnership.v` | Separate private/shared components and flushing preservation | Ownership protocol extended with private resources |
| `theories/PrivateRules.v` | Arbitrary private-resource transfer, sequencing, and operational adequacy | Acquisition/release with private pre/postconditions |
| `theories/PrivateHeap.v` | Framed stores/fences, buffered release, and post-release private loads | Checked spatial primitive framing |
| `theories/PrivateCalculus.v` | Bounded sound calculus and derived whole-critical-section rule | Phase-indexed proof rules |
| `theories/PrivateExamples.v` | Two-cell all-execution restoration and private load, concrete trace, rejected aliasing | Private resource preservation and accessibility |
| `theories/SpatialExchange.v` | Constructive spatial associativity and exchange of closed ownership views | Resource rearrangement for concurrency |
| `theories/PrivateFraming.v` | General semantic spatial frame rule at closed entry, real component flushing and register agreement | Checked spatial framing for private validity |
| `theories/SpatialFramingExamples.v` | Critical section and private load with an additional pending-write frame | All-execution results and a 14-step trace |
| `theories/TemporalFrameCounterexample.v` | Full local completeness invalidates the general semantic temporal frame rule | Lost-marking obstruction, including the usual variable condition |
| `theories/TemporalSafety.v` | Marked resources, temporal-prefix safety, general temporal frame rule, and adequacy | Separate prototype; not yet integrated with ownership |
| `theories/TemporalFence.v` | Fence introduces guarded completeness; arbitrary past temporal framing | Checked fence rule without requiring initially drained history |
| `theories/TemporalFramingExamples.v` | Rejected spurious barrier, pending-write fence example, all-execution safety/post and concrete trace | Nonvacuity of the marked prototype |
| `theories/TemporalTransfer.v` | Mark-preserving invariant extraction and enabled unlock behind unchanged temporal history | Transfer lemma for history outside the ownership region |
| `theories/TemporalOwnershipObstruction.v` | Restored-invariant release fails with a spatial pool outside temporal history; alternative arrangement recomposes | Checked integration obstruction and positive repair witness |
| `theories/RegionalResources.v` | Generalized shared/private regions, marked acquisition, temporal history, and flush preservation | History placed before the combined ownership region |
| `theories/RegionalSafety.v` | All-index acquire/release, skip, consequence, sequence and operational adequacy | Checked regional ownership semantics |
| `theories/RegionalCalculus.v` | Derivations and soundness for the regional lock/sequence/consequence fragment | No frame or heap/concurrency constructors yet |
| `theories/RegionalFraming.v` | Operational history frame rule around `J * P` and `J * Q` | Checked boundary rule, not the private frame rule under hidden `J` |
| `theories/InvariantCompleteness.v` | Points-to completeness can be assigned to an empty spatial sibling; derived foreign-processor barrier | Completeness import obstruction |
| `theories/RegionalExamples.v` | Pending-write round trip, overlapping past/shared cell, all-run boundary theorem, rejected private temporal frame | Concrete nonvacuity and closed-to-closed counterexample |
| `theories/SeparatedSafety.v` | Separate protected/private judgments, actual flushing, general private FRAME-TM and operational adequacy | Recovered frame shape with the original variable condition |
| `theories/SeparatedRules.v` | Protected proof lifting, acquisition/release, sequence, componentwise consequence and private fence | Completeness remains confined to its assertion compartment |
| `theories/SeparatedHeap.v` | Private loads with invariant/protected-assertion freshness | Register changes and temporal heap history |
| `theories/SeparatedCalculus.v` | Sound bounded calculus including FRAME-TM | No safety or validity premises in constructors |
| `theories/SeparatedExamples.v` | Pending-frame protected restoration, real fence, rejected foreign-barrier import and overlapping private history | All-execution results and concrete operational traces |
| `theories/TransferredCells.v` | Owner-specific flushed-cell abbreviation, shape and private-mark construction | Existing assertion grammar with a weaker synchronization contract |
| `theories/InvariantFragment.v` | Guarded invariant fragment, arbitrary nonempty re-marking, empty-buffer shape, and retained-write release obligation | Checkpoint 2; assertion results without a new safety model |
| `theories/InvariantFragmentExamples.v` | Bare-pure release counterexample, nonempty cell with a pending foreign write, rejected foreign-barrier import, and container fragment | Concrete checkpoint-2 assertion checks |
| `theories/FrameShape.v` | Temporal-only residual splitting and reassociation | Checkpoint-3 baseline; resource theorem without a new safety predicate |
| `theories/FrameShapeCounterexample.v` | Failed `#` residual reconstruction under a footprint bound, for assume and acquisition | Checked auxiliary-lemma counterexamples, not proof-rule counterexamples |
| `theories/ResidualUniqueness.v` | Fixed-frame buffer cancellation, forced duplicate-head origin, and incompatible premature local flush | Checkpoint-4 residual and duplicate-write results |
| `theories/FlushAttribution.v` | A machine flush belongs to the frame or local resource, with precise marks and the buffer-free pool fixed | Checkpoint-4 attribution for arbitrary resources and invariant pools |
| `theories/FixedFrameExamples.v` | The unchanged frame excludes checkpoint 3's bad assume and acquisition residuals | Direct checks of the proposed repair |
| `theories/LockRepresentation.v` | Singleton free/held ambiguity and complete locks assembled from partial blocked sets | Checked diagnostics for the checkpoint-5 definition proposal |
| `theories/ProgramSteps.v` | Non-flush action labels, erasure, and classification of every existing machine step | Approved fixed-frame program-step semantics |
| `theories/OwnedSafety.v` | The single owned-resource safety target, full future closure, mark budget, and two frame modes | Active replacement for the separated development path |
| `theories/OwnedAdequacy.v` | Actual flush attribution, exact empty-frame execution, and operational adequacy | Partial correctness without mode-specific client premises |
| `theories/OwnedResources.v` | Local updates, donation reassembly, disjointness preservation, and mode inclusion | Resource lemmas for the active target |
| `theories/OwnedRules.v` | General LOCK in both modes and UNLOCK in disjoint mode, for arbitrary fragment invariants | Checked explicit ownership-transfer rules |
| `theories/OwnedFraming.v` | General FRAME-SP in both modes; FRAME-TM from overlap validity; exact-frame reconstruction and mark preservation | Checked semantic frame rules for the active target |
| `theories/OwnedInterference.v` | Program, abort, environment and full owned-safety transport between agreeing stacks | General support for private register changes |
| `theories/OwnedParallel.v` | Same-index parallel safety and semantic parallel validity in both modes; finished-thread spatial framing | Printed interference plus invariant-variable freshness |
| `theories/OwnedStructural.v` | Skip, consequence, disjunction, sequence, choice and loop for the active predicate | General rules in both modes |
| `theories/OwnedPrimitives.v` | Full-assertion assignment, assume, assert, small and general fence | Invariant freshness for assignment; actual fence earns its own mark |
| `theories/OwnedHeapResources.v` | Preserved local reads and enqueueing with a pending or flushed allocation witness | Exact external frame and pool; whole-resource temporal store post |
| `theories/OwnedHeap.v` | Printed strong-temporal LOAD/STORE and explicit any-writer cell forms, with expression arguments | Existing `⋉` semantics; explicit destination freshness |
| `theories/OwnedAcceptance.v` | All three fixed acceptance tests, double acquisition, split-token fault, and externally blocked local future | Checked checkpoint-5 implementation regressions |
| `theories/StrongTemporalCounterexample.v` | Valid unframed release and invalid strong-temporally framed instance, with independent spatial/temporal witnesses | Counterexample to unrestricted FRAME-STM in disjoint mode |
| `theories/OwnedFramingExamples.v` | Spatially framed donation and private store; temporal acquisition with a genuine foreign pending write | Applications of the proved frame rules |
| `theories/OwnedParallelExamples.v` | Acquire then blocked sibling store, either finished branch, and distinct register assignments | General-rule applications with concrete enabled starts |
| `theories/OwnedRoutineExamples.v` | Variable-capture regression and a pending-write fence that waits for an actual flush | Assignment and fence nonvacuity |
| `theories/OwnedHeapExamples.v` | Foreign-writer cell access without new marks, buffered load/store behind duplicates, and independently witnessed strong conjunction | Heap-rule applications with inhabited environments and traces |
| `theories/OwnershipTransfer.v` | Protected-to-private withdrawal at fence/unlock; disjoint-history donation reassembly | Checked transfer rules and a restricted boundary lemma |
| `theories/OwnershipTransferLimits.v` | Scoped cell versus ordinary points-to; general retained-history donation obstruction | Concrete invalid donation and positive disjoint-history instance |
| `theories/TransferExamples.v` | Known-present withdrawal, release, private load and retained foreign write | All-run proofs, concrete traces, rejected all-processor transfer postcondition |
| `theories/RetiredHeaps.v` | Experimental live/retired heap resources; spatial/temporal associativity; changed temporal-emp entailment | Buffer-free candidate repair for donation |
| `theories/RetiredSafety.v` | Separate buffer-free validity, general FRAME-TM, ownership exclusivity and execution adequacy | Actual machine semantics with explicit empty-buffer environments |
| `theories/RetiredTransfer.v` | Donation and withdrawal with arbitrary overlapping heap history, including at unlock | Checked bidirectional transfer in the experiment |
| `theories/RetiredRules.v` | Acquire/release/load/sequence, bounded calculus and soundness | No safety premise hidden in constructors |
| `theories/RetiredExamples.v` | Return at unlock and return/withdraw/read with old value 5 and current value 7 | All-execution proofs and terminating traces |
| `theories/RetirementFlushing.v` | Masked-history flush simulation; compatibility supplies the required no-pending-write condition | Bridge toward buffered retirement, not a complete buffered model |
| `theories/VariableSupport.v` | Bounds on assertion variables, invariant freshness, and static thread interfaces | Existing variable-interference condition supplies compatibility |
| `theories/ThreadProgress.v` | Residual derivations with variable bounds, relevant-register agreement, and waiting-thread steps | Thread obligations for the parallel rule |
| `theories/SharedViews.v` | One shared ownership decision, symmetric views, flushing and step preservation | Concurrent owner/non-owner agreement |
| `theories/ParallelOwnership.v` | All-execution parallel safety and recombination of private postconditions | Two distinct processors under mutual variable noninterference |
| `theories/ParallelExamples.v` | Competing writers with separate private cells, both execution orders, and a blocked contender | Nonempty concurrent checks |
| `theories/ParallelLoads.v` | Post-release private loads, all-execution heap/register results, and a same-destination counterexample | Register interference and preservation of a finished thread's result |
| `theories/UnlockCounterexample.v` | Two-processor failure of arbitrary-invariant unlock | Release-restoration obstruction |
| `theories/PersistentCalculus.v` | Bounded derivation system and checked soundness | Partial corrected version of Theorem 1 |
| `theories/PersistentExamples.v` | Store postcondition through flushing, wand repair, and derived lock round trip | Concrete checks of the current semantics and rules |
| `theories/SafetyExamples.v` | Refutation of a printed assignment-axiom instance against full safety | Figure 4.7, p. 124 |
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

`PersistentAssertions` uses the same atoms and repaired composition relations,
but makes each wand quantify over future resources. Its atomic and composition
closure laws are proved. [Exact changes and side conditions](notes/persistent-semantics.md)
distinguishes this interpretation from both earlier models.

## Proved results

- `owned_load_valid` and `owned_store_valid` prove the printed
  strong-temporal heap forms. `owned_load_any_writer_valid` and
  `owned_store_any_writer_valid` add the required forms for writer-existential
  flushed cells. All hold in both modes with the existing `⋉` abbreviation.
- `owned_assignment_valid` uses `persistent_assertion_subst` to support
  arbitrary postconditions, including quantifiers and wands. General
  sequence, consequence, disjunction, choice, loop and fence rules now hold
  for the same active predicate.
- `owned_parallel_valid` proves the general semantic parallel rule for
  `owned_safe` in both modes, with the printed interference condition and
  invariant-variable freshness. `owned_safe_parallel` supplies the same-index
  theorem; `owned_safe_stack_agrees` permits private register updates.
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
- `safe_execution_no_abort` and `safe_execution_post` show that the printed
  safety predicate guarantees fault freedom along finite executions and its
  postcondition on the residual local state at termination. The proof also
  tracks the shared invariant and the external frame's flushing.
- `consequence_valid` and `disjunction_valid` establish these two inference
  rules directly for the printed validity definition.
- `printed_assignment_soundness_false` refutes the pure-postcondition subset
  of the unrestricted assignment axiom. `assignment_preserves_environment`
  and `repaired_assignment_action` check the repair for the non-silent action
  when the assigned variable is absent from the shared invariant.
- `ordered_associative` proves associativity of a stricter list-override
  relation that preserves the origin order of conflicting writes.
  `ordered_is_override` shows it is a restriction of the printed operation.
- `ordered_flush_split` and `ordered_flushes_split` give actual one-step and
  finite component flush sequences under the candidate repaired separator.
  It still includes spatial and temporal compositions.
- `stable_compatibility_associative` proves that a conservative compatibility
  condition is invariant under temporal regrouping. This is a definedness
  theorem; the combined repair is established by the following results.
- `repaired_resource_associative` and
  `repaired_temporal_resource_associative` prove associativity for the combined
  operations on valid generalized memories, including temporal completeness
  side conditions. `repaired_temporal_assertion_associative` lifts that result
  to assertion satisfaction.
- `repaired_flush_split` and `repaired_flushes_split` prove actual component
  flushing while preserving stable compatibility. `spatial_flush_split`
  additionally preserves disjoint ownership.
- `repaired_environment_flush` constructs shared, private, and external-frame
  residuals for a silent step, given flushing closure of the invariant.
  Pure assertions have this closure proved in `repaired_full_pure_flushes`.
- `owned_spatial_recombination` derives spatial recombination from the new
  ownership witness requirement, allowing private/shared transfers. It does
  not establish the full frame inference rule.
- `repaired_pure_assignment_valid` proves full validity with a pure invariant
  that does not mention the assigned variable, including all intervening
  flushes. `pure_fragment_sound` proves derivation soundness for pure
  assertions, skip, assignment, sequence, and consequence.
- `repaired_safe_execution_no_abort` and `repaired_safe_execution_post`
  re-establish operational adequacy for the revised safety predicate.
  `register_program_all_terminating_runs` uses a derivation and a concrete
  nonempty initial environment to prove the result of every terminating
  execution of `x := 1; x := x + 1`; a checked run flushes a pending write
  between the assignments.
- `persistent_assertion_flushing_closed` proves generalized flushing closure
  for the whole assertion grammar under future-aware wands. The pointwise
  temporal wand has a checked two-processor counterexample, and
  `persistent_wand_free_unchanged` proves that wand-free formulas keep their
  previous meaning. All three wand adjunctions are proved.
- `persistent_calculus_sound` extends the checked calculus with arbitrary
  invariants, assume/assert, base constant-cell load/store, fence, lock
  acquisition, and release for a pure invariant explicitly asserted in the
  precondition. That earlier calculus retains its pure-assignment and
  constant-cell scope; the newer general rules target `owned_valid`.
  `persistent_derivation_no_abort` connects its derivations to execution.
- `arbitrary_invariant_unlock_invalid` shows why release needs a restoration
  obligation. A checked lock/unlock round trip and store postcondition after
  flushing exercise the positive rules. See the current repair notes.
- `ownership_calculus_sound` proves the separate ownership protocol's bounded
  calculus. `restore_program_all_terminating_runs` restores a heap invariant
  temporarily violated inside the critical section, for every terminating
  execution and admissible spatial frame. `unrestored_release_invalid`
  rejects release with a wrong protected value. No assertion constructor or
  interpretation changes were needed; the specification has phase indices.
- `private_calculus_sound` extends this design with genuine private local
  resources on both sides of the closed boundary. `private_critical_section_rule`
  is derived from body proofs. `private_restore_all_terminating_runs` proves
  restoration of the shared cell and preservation/readback of a separate
  private cell for every terminating run. `private_alias_rejected` excludes
  duplicate shared/private ownership of one cell.
- `private_spatial_frame_valid` proves general semantic spatial framing with
  closed entry, arbitrary final phase and frame assertion, and the usual
  variable condition. A pending-write example preserves the frame through a
  critical section and private load.
- `prefix_temporal_frame_valid` proves temporal framing in a separate semantics
  retaining local completeness. Fence and operational adequacy are checked.
  Two counterexamples isolate lost completeness and incompatible placement of
  shared ownership. `temporal_history_release_transfer` checks the alternative
  release decomposition with history outside the ownership region. These
  results are not yet a combined spatial/temporal/parallel calculus.
- `regional_calculus_sound` proves the generalized acquire/release,
  skip/sequence/consequence fragment. `regional_history_frame_rule` proves
  `{R ; (J * P)} c {R ; (J * Q)}` as an all-execution boundary theorem.
  An overlapping-history/pending-private-write example checks.
  `regional_temporal_frame_counterexample` refutes the unrestricted private
  temporal rule for an actually derivable closed-to-closed specification.

The earlier message-passing examples in `Examples.v` check syntax and variable
side conditions. Their general operational correctness remains open. The
assignment example proves
that a pure invariant `x = 0` becomes false after updating `x` to `1`, for any
resource interpretation. `SafetyExamples.v` now lifts that observation to
an invalid specification under the complete `safe_n` predicate.

## Representation choices

- Identifiers are natural-number names and values are arbitrary integers.
  Boolean evaluation uses Rocq's `bool`, corresponding to the dissertation's
  values `0` and `1`.
- Arithmetic and boolean syntax implements the operators explicitly listed
  in §3.2. The ellipses can be extended as examples require.
- Free and modified variable sets are represented by lists, interpreted
  through membership. Duplicates and list order carry no semantic meaning.
- Quantifiers retain named binders and remove the bound name from the free
  variables. General assertion substitution freshens binders automatically,
  with a semantic theorem covering the complete grammar. Both points-to
  abbreviations also choose a provably fresh processor name automatically.
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

That recombination lemma alone does **not** establish a frame rule for the original
`safe` predicate, which is unchanged. The separate `repaired_safe` predicate now
requires post-step private and shared domains to remain within their prior
combined region. `owned_spatial_recombination` connects those witnesses to
the needed spatial result, and the proved primitive fragment supplies them.
Other inference rules must still establish compatible witnesses and recursive
safety. The later `private_spatial_frame_valid` completes semantic spatial
framing for `private_valid` at closed entry. See
[notes/frame-decomposition.md](notes/frame-decomposition.md) and
[the subsequent temporal work](notes/framing-status.md).

## Safety and candidate algebra repairs

`Safety.v` transcribes the three safety clauses, including existential
post-step decompositions, buffer-complete assertion interpretation, the
shared-invariant obligation while unlocked, and external-frame flushing.
Well-formedness is explicit because the raw Rocq memory type also contains
tuples outside the dissertation's processor universe. Terminality recognizes
every annotated skip, consistently with the operational encoding.

The positive adequacy results start from an assumed `safe_n` fact and follow
actual executions. They do not establish that every specification derivable
in the printed calculus is safe. The assignment counterexample shows why
that additional claim needs corrections.

The candidate repairs are kept separate from the transcription. Ordered
overriding prevents selecting a future write while a past write to the same
address remains. It repairs list associativity and enables checked memory
flushing decomposition. Independently, the printed compatibility condition
can change when a third component supplies blocking facts; a conservative
condition without that exception has checked temporal definedness
associativity. `RepairedSeparation.v` combines these changes and proves
associativity at the generalized-resource level. `repaired_interpretation`
and `repaired_safe` use the changes explicitly; `concrete_interpretation` and
`safe` retain the printed definitions.

The stronger guard excludes some old compositions and therefore restricts
the environments quantified by safety. Relation inclusion does **not** imply
that repaired validity entails printed validity. Operational adequacy has
been reproved independently. Whether the stronger guard preserves the
general framed load/store/lock specifications remains an open expressiveness
check. Base heap operations, fence, and acquisition now check; unrestricted
release fails because it does not establish the invariant on unlocking.

The earlier future-aware repair uses `persistent_models` and `persistent_valid`.
Only wand interpretation changes from the previous repaired model; ordinary
machine steps and the ownership-aware safety predicate are reused. Full
assertion closure and the bounded calculus soundness theorem are proved.
Here `persistent` means preserved by generalized flushing, not duplicable.
See [the precise rule comparison and release problem](notes/persistent-semantics.md).
The active `owned_valid` target retains that assertion interpretation but uses
the approved single-resource ownership semantics described above.

## Remaining proof work

1. Derive the container example with acquisition, removal, release, private
   use and return, while a foreign write is pending.
2. Justify any additional printed rules included in the eventual calculus.
   EX and SHARE are not established for `owned_valid`; INV remains removed
   and FRAME-STM remains omitted.
3. Define a calculus that tracks overlap-mode validity for FRAME-TM, then
   prove soundness by induction on derivations and apply operational
   adequacy. Continue the [review checkpoints](review/lead-response.md);
   [checkpoint 9](review/checkpoint-9.md) records the current exact scope.

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
