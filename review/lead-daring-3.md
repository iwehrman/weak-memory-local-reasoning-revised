# Buffered-pool proof checkpoint: through Dekker

Response to `reviewer-guidance-daring-3.md` at `b0fe13f`.

**Proof commit: `88106e8184b8c1c440142321791409db665a91f4`.**

The requested step-3 checkpoint is reached. The general atomic rule, SEQ,
CONS, CONC and adequacy are proved for the approved definition. All six
Dekker premises are proved, their composition is valid, and the final
machine theorem erases the ghost cells. No definition or proposed rule
statement had to change.

## Scope and validation

All changes are new files. `BufferedPoolCandidate.v`, the main `_CoqProject`,
`owned_safe`, `owned_derivation`, existing statements and `paper/` are
unchanged. The earlier counterexamples to the original daring rules still
stand. These new results concern the separately proposed, lock-free,
disjoint-mode buffered-pool judgment; they do not establish those original
rules or combine this judgment with the lock-transfer calculus.

The new build entry point is:

```sh
make -f Makefile.buffered -j4 check
```

It builds the established development, compiles the candidate definitions
and new proofs, and kernel-checks both `WMLR.Audit` and
`WMLR.BufferedPoolAudit`. The latter audits 108 new proof declarations;
together with the existing 1,341 that is 1,449. No axioms, admitted proofs,
functional extensionality or unchecked computation are used. The six finite
certificate calculations close by `eq_refl` after the certificate checker
has been proved sound.

A fresh clone of the proof commit passed that command with exit 0 under
Rocq 9.3.0. Its build printed **1,449 declarations closed under the global
context**, and both audits passed kernel checking. The clone had no
preexisting compiled proof artifacts. A source scan of the added files
found no axioms, parameters, hypotheses, admits or aborted proofs.

## 1. Foundations

`theories/BufferedPoolResources.v` proves:

- `buffered_pool_flush`: a real pool flush preserves its assertion at full
  marks. This works for arbitrary assertions, using the existing flushing
  closure; it does not assume mark insensitivity or a buffer-free pool.
- `buffered_environment_flush`: every machine flush has a successor of
  exactly one of the three forms in `buffered_flush_update`. The other two
  components remain fixed, and the successor is an admissible environment.
  The returned private resource is also a future of the original one.
- `buffered_joint_buffers_unique`: with the external frame and output
  fixed, the joint pool/private buffers are unique. The pool/private split
  itself may change. This is buffer cancellation, not a claim that private
  buffers remain unique across a transfer.
- Environment regrouping and `buffered_update_frame`, including joint
  footprint and private mark-budget preservation.

The regrouping proof reuses the established resource algebra through an
equivalence between the new environment and an old **free-pool environment**.
It does not reuse old safety or its pool-preserving action clause.

`theories/BufferedPoolExtension.v` proves
`buffered_atomic_extension` for arbitrary common primitives. It projects
an actual framed step to the pool/private union, invokes the frameless
premise, and reattaches the exact frame. A framed-enabled fence implies a
frameless-enabled fence; the converse is never needed. A store appends
after the actor's entire buffer, and the spatial enqueue lemma preserves
the original interleaving with the frame.

## 2. General rules and adequacy

The principal statements are direct inhabitants of the propositions in
`BufferedPoolCandidate.v`:

| Theorem | Location |
| --- | --- |
| `buffered_atomic_valid` | `BufferedPoolRules.v` |
| `buffered_sequence_valid` | `BufferedPoolRules.v` |
| `buffered_consequence_valid` | `BufferedPoolRules.v` |
| `buffered_parallel_valid` | `BufferedPoolParallel.v` |
| `buffered_valid_adequacy` | `BufferedPoolAdequacy.v` |

SKIP and FRAME-SP are also proved (`buffered_skip_valid` and
`buffered_spatial_frame_valid`). Same-index spatial framing was needed for
CONC's finished-thread cases, so it belongs on the shortest route.

CONC retains precisely the approved interference and invariant-variable
conditions. It has no processor-count or finiteness assumption, no extra
fragment premise, and no register-preservation premise. The acting thread
may redistribute the pool and its private resource. The sibling retains
its exact resource, and fresh environment quantification plus stack
agreement handles the changed pool and frame on its next step.

The explicit flush clause and closure under **all** local futures remain
unchanged. The framing and concurrency proofs split a local future into
component futures; they do not narrow closure to machine-enabled flushes.

Adequacy instantiates the empty frame internally. A flush of that frame is
impossible, so every finite concrete execution retains an empty external
frame. Its terminal decomposition satisfies the same full pool invariant
and the private postcondition. There is no residual mode/frame premise.

## 3. Dekker: six premises to a machine theorem

`theories/BufferedDekkerProof.v` proves the six exact candidate propositions:

```text
buffered_dekker_store0_premise   : BufferedDekker.store0_premise
buffered_dekker_store1_premise   : BufferedDekker.store1_premise
buffered_dekker_fence0_premise   : BufferedDekker.fence0_premise
buffered_dekker_fence1_premise   : BufferedDekker.fence1_premise
buffered_dekker_load0_premise    : BufferedDekker.load0_premise
buffered_dekker_load1_premise    : BufferedDekker.load1_premise
```

This goes beyond the earlier bounded search. `BD.models_image` proves that
every lock-free model of the fixed invariant has one of the 24 enumerated
memory shapes. `BD.image_models` proves the converse for canonical full-mark
resources. These facts include both pending and drained history models.
Private marks and incoming stacks are not enumerated or bounded.

`BDV.certificate_sound` turns a successful finite calculation into the
**universally quantified atomic premise**. It proves non-abort, projects
every actual primitive result, constructs the returned full pool and
private postcondition, and checks exact memory recomposition. Successor
private resources retain the original private marks. The footprint bound
comes from the actual machine step and the two spatial decompositions.

`buffered_dekker_valid` composes the six results using the proved atomic,
sequence and parallel rules. It is a proof by composition of semantic
rules, not a new inductive derivation-system definition. The two-load
postcondition excludes `(0,0)`: each zero branch would own the same prize
cell, contradicting spatial disjointness.

`theories/BufferedDekkerAdequacy.v` gives the requested machine statement:

```text
dekker_fenced_all_runs:
  execution two_processors n dekker_fenced s initial_memory last t final ->
  ~ abort two_processors last (State t final) /\
  (terminal last -> ~ (t 0 = 0 /\ t 1 = 0)).
```

Here `initial_memory` has precisely the two flags initialized to zero,
empty buffers and a free lock. The initial stack `s` is arbitrary.
`dekker_fenced` is defined in `DekkerSyntax.v`, which imports only machine
syntax and examples. The theorem statement contains no candidate validity,
invariant, resource, mark or ghost-cell definition.

The proof lifts an arbitrary real execution to one with eleven untouched
ghost cells, applies the composed specification and adequacy, and erases
the cells. `HeapExtensionFootprint.v` generalizes the existing erasure
helper from one address expression to a finite list; the old helper and
machine semantics are unchanged.

Two execution witnesses complement the universal theorem:

- `dekker_unfenced_zero_zero`: a terminating unfenced execution reads
  `(0,0)` and has empty final buffers, reusing the checked store-buffering
  trace.
- `dekker_fenced_terminates`: a checked 13-step fenced execution reads
  `(0,1)`.

These are finite-execution safety results, not fairness or total-correctness
claims. This is the fenced two-flag litmus, not the full retrying mutual
exclusion algorithm.

## Full marks and the requested limitation

`theories/BufferedPoolLimitations.v` settles the reviewer's reading of a
drained history. `buffered_full_pool_drained_history` proves, for an active
named writer `i` and a drained `i` buffer:

```text
pool |=full (x ↣ u ; x ⇝_i v)  iff  pool |=full x ↣ v.
```

The resource-level theorem is slightly stronger: containing every active
mark is enough. The active-writer premise is explicit. This does not extend
to arbitrary re-marking of pending histories.

The limitation is also checked, not just described:

- `buffered_unmarked_ordinary_no_heap`: an ordinary successor of a private
  resource with no marks has an empty heap.
- `buffered_empty_ordinary_cannot_own_cell`: starting with unmarked `emp`,
  no ordinary update can yield a private `writer_points_to` cell.
- `buffered_emp_load_withdrawal_premise_invalid`: with
  `J = emp ∨ x ↣ 0`, the proposed atomic premise
  `{emp} r := [x]_1 {x ↣ 0}` fails. The counterexample uses the **nonempty**
  one-cell pool, empty private marks, and an enabled load returning zero.
  Returning the cell to the private side would require a mark the load
  cannot earn. The proof does not exploit the empty-pool branch instead.

Dekker avoids this limitation because each thread starts with ghost cells,
which force a nonempty private mark set. No fix or additional condition was
introduced.

## Checkpoint and remaining work

I am stopping at the requested step-3 review point. No statement failed and
there is no unresolved proof obligation in the files submitted here.

Step 4 remains: general DISJ, CHOICE, LOOP and EX, plus the private
load/store/fence, assignment, assume and assert rules. SKIP and FRAME-SP
are already done. The overlay build can be integrated into the main
manifest after review; the withdrawn `DaringCandidate.v` is still present
and unchanged. No paper edits or claims of a complete new calculus were
made.
