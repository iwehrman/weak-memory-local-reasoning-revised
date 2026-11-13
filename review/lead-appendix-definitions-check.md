# Lead's check of the definition and program appendices

Responds to `review/reviewer-request-appendix-definitions.md`.
Draft: `4c5d06b` (line numbers below refer to this draft).
Proof sources: `2b53266`, mechanically renamed at
`1c66a282af874690ed3ef3bd45d9d1789d7b14e8`.

The example programs and specifications agree with the sources. The
definition prose needs the qualifications below, including one incorrect
quantifier grouping in temporal compatibility. These are paper corrections;
no new proof work or semantic change is needed. I have not edited the paper.

## Corrections and suggested wording

1. **State the active-processor conditions explicitly
   (`appendix.tex:94–104,117–120,130–135`).** A memory is well formed when
   its blocked set is a subset of the active processors and every inactive
   processor has an empty buffer (`Machine.v:94–96`). The remaining two
   resource conditions are correctly stated. A flush requires an **active**
   processor unblocked in the resource's own memory
   (`GeneralizedFlushing.v:8–11`); it does not inspect an external frame.
   For a precise held-lock definition, write
   `i ∈ Proc` and `K = Proc \ {i}`, where `Proc` is the active domain
   (`Machine.v:85–87`). Use this both for the environment's whole memory
   and for the local memories in acquire/release updates. “Blocks none”
   correctly means that the entire blocked set is empty.

   Suggested additions: “All memories here have blocked sets contained in
   the active domain and empty buffers at inactive processors”; “some
   active processor i unblocked in μ”; and “i is active and the blocked
   set is precisely Proc minus i”. The flush's activity also follows from
   the well-formed target marks as written, but stating it directly matches
   the actual step definition.

2. **Updates are labeled by actions, not necessarily primitive commands
   (`appendix.tex:124–127`).** `ProgramSteps.v:20–54` includes choice,
   loop unfolding, completed-prefix removal, and parallel completion as
   program steps. These perform no primitive; their label is
   `OrdinaryAction`. Replace the opening by:

   > A non-flush program step has an action label: ordinary, fence by i,
   > acquire by i, or release by i. Structural steps have the ordinary
   > label. Let such a step take the local resource, pool and phase to
   > their primed successors.

   With that reading of α, the transfer clauses, footprint inclusion and
   mark budget match `OwnedSafety.v:43–68`. In particular, mark preservation
   is not required: the budget is the subset condition already displayed.

3. **Separate the two compatibility quantifiers
   (`appendix.tex:180–186`).** The current “for processors i ≠ j” phrase
   incorrectly makes the heap-conflict condition depend on a second
   processor. `Separation.v:31–37` imposes that condition for **each single**
   jointly unblocked active processor i, even if there is no distinct
   jointly unblocked j. Only the cross-buffer condition requires i ≠ j.

   Suggested replacement:

   > The blocked sets must be disjoint. For each active processor i
   > unblocked in both memories, B₀(i) must write to no address in h₁.
   > For each pair of distinct active processors i,j unblocked in both
   > memories, B₀(i) and B₁(j) must write to disjoint sets of addresses.
   > The repaired relation drops the unblocked qualifications in these
   > two clauses.

   This is exactly `temporal_compatible` and `stable_compatible`; it adds
   no condition to either relation.

4. **Qualify the blanket “more restrictive” claim and make wand recursion
   explicit (`appendix.tex:166–168,188–193`).** The inclusion statements
   are established for buffer overriding and compatibility. For a wand,
   adding future tests strengthens the clause when its operand predicates
   and composition are fixed. It does not establish that every repaired
   assertion has fewer models than its original interpretation: the
   operands are recursively reinterpreted, wand antecedents are
   contravariant, and the temporal composition relation also changes.

   Replace the blanket sentence by:

   > Buffer overriding and compatibility admit fewer compositions.
   > Implications additionally require their extension test to hold at
   > every future of the current resource.

   Then add that this clause applies **at every implication occurrence,
   including nested ones**, with both operands interpreted recursively in
   the repaired semantics. `future_satisfies` (`PersistentAssertions.v:8–32`)
   quantifies over futures of the current resource only, at the same stack,
   and then over compatible extensions. It does not independently advance
   the extension before testing it. The resulting full interpretation is
   proved future-closed; no global inclusion of arbitrary assertions in
   the original interpretation is claimed.

5. **Make the flush explanation refer to the attribution argument
   (`appendix.tex:158–161`).** The sentence is pointing in the right
   direction, but a flush does not need to wait for a recursive program
   step to obtain a fresh frame. Suggested replacement:

   > Machine flushes are not program steps. Under the guarded-invariant
   > hypothesis the pool is buffer-free; flush attribution assigns each
   > flush to the local resource or the frame. Local flushes are handled
   > by future closure, and frame flushes by re-instantiating the
   > universally quantified environment, at the same safety index.

   This follows the statement of `pooled_resource_flush_attribution`
   (`FlushAttribution.v:55–71`) and the quantifiers of `owned_safe`.

6. **Retain the frame-future premise in the short Conjecture 1 description
   (`wrong.tex:47–48`).** The full description in
   `original.tex:208–211` retains it correctly. The table should say, for
   example:

   > Conjecture 1: a post-step spatiotemporal split of an initially
   > spatially split memory is spatial when its first component is a
   > flushed descendant of the original first component.

   For literal correspondence, the conjecture's conclusion is equality of
   the two sets of compositions for that resulting pair of components,
   not just a claim about one chosen output. The full prose's “again a
   spatial split” is a fair summary; the source and the renamed
   `original_conjecture1` in `SeparationExamples.v:154–161` state the
   equality explicitly.

## Checks that pass, with scope notes

- **Environment well-formedness fields.** Omitting their repetition is
  harmless with the resource/satisfaction conventions above. A free pool
  satisfying J at full completeness is well formed
  (`persistent_full_well_formed`); a held pool is empty. The combined
  resource is well formed by its type, and spatial composition preserves
  memory well-formedness (`raw_spatial_well_formed`). Thus the two explicit
  record fields follow from the other conditions as described.
- **Safety recursion.** The quantifier order, successor stack s′, exact
  retained frame, update from the future local resource ν₁, and decrement
  of the index all match. “Has terminated” means syntactically `skip_i`
  (`Safety.v:15`), not merely unable to step; adding that parenthesis would
  make the standalone definition precise. Validity quantifies over all
  stacks, satisfying resources, and indices.
- **Buffer overriding.** Both descriptions and the per-address occurrence
  order agree with `buffer_overrides` and `ordered_overrides`.
- **Retrying container.** Both branches, the done-register assignments,
  the corresponding put variant, and the foreign-write specification
  match `OwnedRetryContainer.v`. Here r is source register 0 and g is 1.
- **Message passing.** All three specifications and the two branches of
  `mp_received r 2` match `MessagePassingSyntax.v:21–29` and
  `MessagePassingDerivation.v:8,67,78`.
- **Named locks.** Acquire, release and the invariant family match
  `NamedLockSyntax.v`. The exit value x=0 follows under the binary-flag
  invariant; it is not a fact about this loop on arbitrary malformed
  flags. “Under this invariant the loop exits with x=0” would clarify
  `appendix.tex:469–470`. The referenced release rule still has its
  exclusivity premise from Section 8, as well as acquire's scratch
  freshness condition.
- **Mailbox.** The producer, consumer, invariant and three specifications
  match. The register renaming is 0→z, 1→y, 2→w; reusing y as acquire
  scratch and mailbox-flag register is correct. The region operations
  access the list in the displayed order. Use the conventional empty
  product `A(()) = emp` and empty store/load sequence `skip` for K=0.
- **Daring-rule sentence.** `open.tex:8–11` accurately summarizes the basic
  DARING-LOAD and DARING-STORE premises: the single command is specified
  under invariant emp with J as a spatial part of both endpoints. For precision, call these the
  **basic** daring rules: the separately proposed DARING-STORE-2 only
  promises restoration after a barrier, and is not covered by “gives J
  back”. The original text leaves the soundness exploration open.
- **Figures 4.5 and 4.6.** “One of equivalences and one of entailments” is
  correct; the original captions say exactly those categories.

## Source and validation scope

The original-source comparisons use
[Conjecture 1](https://github.com/iwehrman/Weak-Memory-Local-Reasoning/blob/master/dissertation.tex#L2741-L2745),
[the daring rules](https://github.com/iwehrman/Weak-Memory-Local-Reasoning/blob/master/dissertation.tex#L2171-L2178),
and the two figure captions at lines 1952 and 1974 of the same file,
blob `ac4c24370dc22b3ca0892294206c2c6ac138d993`.

All appendix Rocq citations resolve. The requested rename is independently
reported in `review/lead-rename-original.md`; it preserves every statement
and proof, and its clean build and kernel check passed. This appendix check
adds no theorem or test and is not a PDF layout review.
