# Repairing the spatial frame argument

> **Historical checkpoint.** This report describes an earlier development
> stage. Its alternative safety/calculus design is superseded by
> `OwnedSafety.v` and `OwnedCalculus.v`; any statements about remaining
> soundness work belong to that stage. Reused resource lemmas and checked
> counterexamples retain their meanings. See the
> [current calculus and complete comparison](current-calculus.md).

The target is Lemma 21 (pp. 174-176), a step toward Theorem 1. The immediate
problem is the use of Conjecture 1 to turn a spatiotemporal post-step
decomposition into a spatial one.

**Current status:** `private_spatial_frame_valid` now proves the semantic
spatial frame rule for the later private ownership model at closed entry.
The arguments below explain its ownership-domain foundation and why the
printed predicate alone is insufficient. Subsequent temporal counterexamples,
the marked-resource frame theorem, and an alternative invariant-transfer
lemma are documented in [framing-status.md](framing-status.md).

## Checked obstruction

`printed_conjecture1_false` formalizes the conjecture and its refutation.
Initially, the frame owns the cell `1 -> 7` and the local memory is empty.
The whole memory is their spatial composition. An `assume true` step on
processor 1 leaves the whole memory unchanged, and the frame takes zero
flushes. Nevertheless, the post-step whole can be decomposed
spatiotemporally into two copies of the same cell: heap overriding hides
the overlap. Those two components cannot be spatially composed.

This is a counterexample to the conjecture's universal statement. It does
not by itself prove that the spatial frame rule or Theorem 1 is false.

## Checked replacement

`steps_domain_subset` proves that a successful execution can only retain
locations already present in its initial memory domain (heap or any buffer).
Stores have an allocated-address premise, so enqueuing a write does not
introduce a location. Flushing only moves a location from a buffer to the
heap. The theorem covers the full current command language, including locks,
parallel commands, nondeterministic choice, loops, and silent flushing.

`spatial_frame_recombination_sets` proves the following. If:

1. `frame` and `local` initially compose spatially;
2. `frame'` is obtained from `frame` by zero or more flushes; and
3. `local'` is obtained from `local` by a successful finite execution;

then, for every output memory, composing `frame'` and `local'`
spatiotemporally is equivalent to composing them spatially. This is equality
of result sets, not a guarantee that the sets are nonempty; the safety proof
must still supply the post-step spatiotemporal composition witness.

The proof first derives that both residual domains remain within their
initial, disjoint domains. A spatiotemporal result already guarantees
disjoint blocked sets and that its buffers interleave the two inputs.
Together these facts meet all spatial-composition requirements. Conversely,
spatial composition is always included in spatiotemporal composition.

The replacement does not assume the desired post-step separation, and its
footprint premises follow from actual execution. In particular,
`empty_execution_cannot_acquire_cell` proves that the fabricated residual
in the counterexample cannot meet the new execution premise.

`spatial_frame_recombination_region` generalizes the third premise. An
ownership region disjoint from the frame may execute, and the local residual
may occupy any subset of that region's final domain. This permits ownership
to move between shared and private parts *within* the region. It does not
require every residual private location to have been private initially.

## Remaining connection to soundness

The printed safety predicate (pp. 131-132), now transcribed in `Safety.v`, provides post-step resources
existentially. It constrains the external frame to flush, but does not say
that the chosen local resource follows an execution of the original local
state or stays within a tracked ownership region. A global transition alone
does not supply this missing condition, as the counterexample demonstrates.

The next proof obligation is to construct a post-step witness that both:

- stays within the original private-plus-invariant ownership region; and
- preserves the required invariant and recursive safety/postcondition facts.

One possible approach is a witness-normalization theorem for the printed
safety semantics. No such theorem is established. Merely deleting overlapping
cells is insufficient:
assertion satisfaction and recursive safety of the resulting resource must
also be proved. In particular, lock steps can transfer ownership from the
shared invariant, so restricting all residuals to the original private
footprint would be too strong.

The development now explores the explicit alternative in `RepairedSafety.v`.
Its `ownership_preserved` condition requires both residual private and shared
domains to lie within the union of the old private and shared domains. The
external frame still evolves by actual flushing. `repaired_safe` includes
this requirement at each recursive step, and uses the combined repaired
separator. The printed `safe` definition is retained unchanged.

`ownership_frame_disjoint` proves that a spatial frame initially disjoint from
both private and shared regions remains disjoint from both residuals when it
flushes and `ownership_preserved` holds. `owned_spatial_recombination` then
turns a repaired spatiotemporal result into a spatial result. This is a checked
bridge from the new witness condition to the replacement lemma.

Actual silent steps construct these witnesses in `repaired_environment_flush`.
The corrected assignment rule and the skip/sequence/consequence fragment
supply them and have full validity proofs; adequacy is reproved for the revised
predicate. This earlier `repaired_safe` fragment does not itself supply the
general spatial frame rule. The later private ownership model supplies lock
transfer and recursive safety, and `PrivateFraming.v` completes its semantic
spatial frame rule with closed entry. No normalization theorem from printed
safety is claimed.

`OrderedSeparation.v` now proves one-step and finite flushing decomposition
for a candidate separator using ordered buffer overriding. The transcription
remains unchanged. Two separate associativity obstructions and their candidate
repairs are detailed in [soundness-status.md](soundness-status.md).
`RepairedSeparation.v` and `RepairedFlushing.v` now combine the repairs, prove
temporal and spatiotemporal associativity on valid generalized resources, and
preserve the stronger guard under actual component flushing.
`GeneralizedFlushing.v` now handles the completeness sets and valid resource
witnesses. Full assertion flushing closure is proved in the future-aware
interpretation. The later temporal frame theorem retains completeness instead
of promoting each component to full. Combining it with shared/private transfer
still requires a different placement of temporal history; see
[framing-status.md](framing-status.md).
None of these laws is postulated as an axiom to make the replacement lemma compile.
