# Restricted SHARE: proved in both modes

**The approved restricted SHARE rule holds in DJ and in OV.** The OV
counterexample conjectured in the latest guidance does not materialize.
Both theorems use the unchanged `owned_safe` / `owned_valid`; neither
adds an invariant-variable condition or another semantic restriction.

This report follows the [statement before implementation](paper-restricted-share-statement.md).
The results await independent review. The paper, queue and reviewer guidance
have not been edited.

## Exact rule and scope

For either mode M separately:

```text
J valid_M {P} c {Q}
every model of P is lock-free
every model of Q is lock-free
---------------------------------
emp valid_M {J * P} c {J * Q}
```

The standing hypotheses are the existing `invariant_fragment J` and
`two_active_processors active`. Pre/post lock-freeness quantifies over
all stacks and all well-formed resources. There is no finiteness assumption,
command restriction, additional freshness condition, or restriction to
derivable source triples.

The principal declarations are:

- `owned_share_valid` in [OwnedShare.v](../theories/OwnedShare.v): DJ to DJ.
- `owned_share_overlap_valid` in
  [OwnedShareOverlap.v](../theories/OwnedShareOverlap.v): OV to OV.
- `owned_share_derivation_valid` and
  `owned_share_overlap_derivation_valid`: the corresponding corollaries
  from actual derivation trees.

These do **not** claim DJ-to-OV strengthening. The overlap theorem has an
OV-valid premise. Unrestricted SHARE and the merely syntactic reading of
lock-freeness remain refuted by the existing checked counterexamples.

The program system still has 21 constructors, and the assertion basis still
has 47. SHARE is a proved semantic rule and a theorem from derivations;
there is no new `owned_derivation` constructor. Consequently an internal
proof tree using SHARE is not silently accepted by the old judgment. Adding
such a constructor, if wanted for presentation or nested uses, is a separate
review decision now backed by the theorem.

## Why the proof works

The source specification treats J as a shared pool. The conclusion owns
that same resource privately. The induction records a resource decomposition:
while the source local is lock-free, the target owns `j * local` with
`j` satisfying J; while the source local holds the lock, target and source
local resources coincide. This relation is a proof witness between two uses
of `owned_safe`, not another safety predicate or a compartment added to the
semantics.

Acquisition moves the pool into the source local, while the target already
owned those cells. Release restores the source pool and folds its cells back
into the target local. The restored J component is marked only for the
releasing processor, so the target obeys the existing mark budget. No foreign
barrier is gained. Generalized futures are handled by the existing spatial
future-splitting theorem, including mark-only futures.

An externally held lock is also covered. In that case the proof temporarily
puts the retained J component into the source's external frame. The source
frame stays fixed during the action; the target frame stays fixed too.
Frames and pool states remain re-quantified at every recursive safety call.

The subtle issue is a command changing the stack while another thread holds
the lock. Source safety also has to handle an environment with the blocked
bits cleared and the same J placed in the free pool. Every already enabled
non-lock action remains enabled there. Its successor must preserve that
exact pool and establish J on the new stack. `owned_share_preserves_invariant`
and its OV counterpart use this fact. The constructive mark-restoration
lemmas cover empty heaps and nonempty heaps without excluded middle or an
extra mark assumption. This is why no new `mod(c)`/`fv(J)` premise is needed
for this semantic rule.

## The OV result and the stale-frame conjecture

OV permits an external frame to contain a hidden heap copy at an address
owned by J. Such a frame cannot be put spatially beside the source's free
pool. The proof projects only those hidden heap entries out of the **source
environment's** frame. Its buffers, blocked bits and marks are unchanged.
The target always uses the original frame.

This projection changes neither the physical heap seen by the command nor
its enabled transition: the owned J cells override the removed entries.
After an ordinary action the retained J still overrides them. After
acquisition the source local must contain those heap entries: program steps
do not change the shared heap, and the projected frame contains no replacement
copy. Restoring the original frame therefore preserves the same physical
successor. Source safety at the successor already quantifies over fresh
frames, so the proof is not committed to the projected frame in later steps.

On release the source-validity premise already ensures that the returned
pool is spatially disjoint from its actual source frame. Folding that pool
into the target local works in either mode. This differs from the failed
FRAME-STM and unrestricted temporal donation examples: here the target does
not give the retained invariant footprint away to a new nonempty pool.

The lemmas in
[OwnedShareOverlapResources.v](../theories/OwnedShareOverlapResources.v)
check projection, restoration, both regroupings and unchanged program-step
heaps. `share_stale_external_environment` exhibits an admissible target with
owned value 7 and a hidden external value 5 at the same address;
`share_stale_frame_requires_projection` proves that the same unprojected
frame cannot be used beside the source pool. This pins down the actual gap
in the naive proof and its repair.

## Operational result and examples

`owned_share_all_runs` and `owned_share_derivation_all_runs` in
[OwnedShareAdequacy.v](../theories/OwnedShareAdequacy.v) state the direct
operational consequence for either source mode. Starting with a resource
satisfying `J * P`, every finite execution is non-aborting; termination has
a free lock and the actual final memory satisfies `J * Q` at full completeness.
The full marking is an adequacy-level interpretation of the final memory,
not a program-step mark award. This result does not claim termination,
fairness, or restoration at every intermediate prefix.

[OwnedShareExamples.v](../theories/OwnedShareExamples.v) applies DJ SHARE to
the already derived container, giving `emp valid_DJ {J} container {J}`, and
then spatially frames the foreign write around it. It checks an inhabited
initial J. The existing concrete container trace is unchanged.

[OwnedShareOverlapExamples.v](../theories/OwnedShareOverlapExamples.v) also
applies OV SHARE to the general store-then-fence cell derivation, with arbitrary
fragment invariant, address, values and active acting processor. The existing
negative SHARE examples are retained unchanged.

## Search, audit and remaining decisions

`scripts/search_restricted_share.py` records its output in
[paper-restricted-share-search.jsonl](paper-restricted-share-search.jsonl).
The DJ family covers two processors, three addresses, values 0/1, all mark
choices, initial buffers of length at most one per component, and local,
external and free token placements. It screens all enabled program actions
and bounded source residuals in that family. A separate seeded OV search
uses 12,000 draws, buffers up to length two per component, overlapping heap
copies and same-processor writes. Neither found a failed resource simulation.
These are bounded step checks, not semantic validity proofs; the Rocq
induction is the general result.

The eleven new theory files contain **1,131 physical lines and 52 audited
declarations**. The complete development now has **193 theory files,
30,052 physical lines and 1,284 audited declarations**. `make check` passes
in the working tree and a fresh source export; all audited declarations are
closed, and both independent `rocq check` runs succeed. Validation is also
recorded in the consolidated [offline queue handoff](offline-queue-handoff.md).

The requested work queue is complete. Independent review should decide how
to present restricted SHARE in the paper, particularly whether to leave it
as a semantic theorem or add an explicit calculus constructor. The proof does
not require a design change. DJ-to-OV strengthening, assertion completeness
and automation remain outside the established result.
