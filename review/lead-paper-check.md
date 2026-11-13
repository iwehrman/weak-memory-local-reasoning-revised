# Lead's paper-to-proof check

Responds to `review/reviewer-acceptance-of-offline-queue.md`.

**Draft checked:** `67b469bf9b9f6354e5181870f4a62431b5f3675a`.
**Proof artifact checked:** `99b4052d76238e6d3d89e27255a3d6d00e27a562`.
There is no difference in `theories/`, `_CoqProject`, or `Makefile` between
these commits. All paper line references below refer to the draft commit.

The principal soundness and adequacy statements match the proofs. All 35
explicit Rocq references in `paper/sections/*.tex` resolve to declarations
in the build. The figures are correct. I found several places where the
prose goes beyond the theorem, omits a hypothesis, or loses a distinction
from the earlier reports. These are paper corrections, not a request to
reopen the proof queue. I have changed neither the paper nor the proofs.

I read all twelve section files, checked the cited statements and relevant
definitions, reran `make check`, and separately evaluated `Audit.v` to
check its assumption reports. This was a statement/definition audit, not a
new line-by-line proof review or an independent literature survey. In
particular, the historical and novelty assessments in `related.tex` are
outside the Rocq correspondence check.

## Corrections to technical claims

### 1. The trilemma does not prove that every overlapping frame fails

**Locations:** `wrong.tex:191–194`; also `intro.tex:38–43`.

`ReviewObstructions.trilemma` requires a particular execution whose initial
state satisfies `R ; P` and whose final state does **not** satisfy `R`.
The proposition displayed at `wrong.tex:157–165` includes that condition
correctly. Its later conclusion that the restriction "cannot be weakened"
and that "every frame that overlaps a released cell yields a false
specification" does not follow. No optimality theorem about every
overlapping frame was proved.

The introduction similarly omits the bad-execution hypothesis and replaces
it with non-cancellativity in general. Non-cancellativity by itself is not
the hypothesis of the checked theorem.

**Suggested correction:** unrestricted framing is incompatible with a
transfer-out specification *when an admissible temporal history can become
false after that transfer*. The checked stale-value examples supply such
histories. The modes give a sufficient repair; the theorem does not show
that every weaker restriction fails.

### 2. Emp-to-emp restoration needs an initially lock-free external frame

**Location:** `results.tex:39–42`.

`OwnedExecution.owned_emp_derivation_restores` explicitly assumes
`lock_free (resource_memory active frame)`, as well as an admissible initial
environment. The paper drops the lock-free-frame assumption while talking
about a general environment frame.

The assumption matters: `skip` has an emp-to-emp specification even when
another thread's external frame holds the lock. That execution does not
release the other thread's lock. This is an explanation of the missing
hypothesis, not a newly added regression theorem.

**Suggested correction:** say "with an initially lock-free external
frame", or restrict the paragraph to the free-lock, empty-frame starts of
the preceding adequacy theorem. The conclusion about the final frame is
also precise: it is a `resource_future` of the initial frame, not an
arbitrary replacement.

### 3. Small exchange has two premise readings, with different results

**Locations:** `appendix.tex:124–125,133–136`; `intro.tex:58–61`.

The table says exchange between `*` and `;` is vacuous because its premise
forces an empty processor set. That is correct for the **uniform** premise
comparing the two connectives on *all* assertions. It is not correct for
the literal displayed premise about the particular `P,Q`.

`AssertionExchange.assertion_literal_exchange_spatial_refuted` and
`assertion_literal_exchange_temporal_refuted` refute the literal versions
on any nonempty processor domain. The uniform versions are covered by
`assertion_uniform_incomparable_empty` and
`assertion_uniform_incomparable_exchange`. This distinction is recorded
in `review/paper-algebra-audit.md`.

**Suggested correction:** label the row "uniform premise: vacuous;
literal premise: refuted". Qualify "everything else survives" and the
introduction's "one family of exceptions" accordingly. Even under the
uniform reading these exchanges are unusable on the nonempty domains of
the calculus; they are not useful surviving laws.

### 4. Two cited counterexamples use intermediate interpretations

**Locations:** `wrong.tex:4–7,41–52`; `mechanization.tex:12–14`.

The blanket statement that every counterexample in this section is checked
against the unmodified printed definitions is too strong:

- `FlushingCounterexample.pointwise_temporal_wand_not_flush_closed` uses
  `repaired_models`, which retains pointwise wands but uses the repaired
  temporal separator (`RepairedAssertions.v:10–21`).
- `UnlockCounterexample.arbitrary_invariant_unlock_invalid` refutes
  `persistent_valid`, the earlier repaired safety interpretation, rather
  than `valid_specification`, the transcription of printed validity.

The local counterexample arguments explain defects that also concern the
printed design. But these two theorem statements do not literally assert
what the opening and mechanization paragraphs promise. The later checked
stale-value, foreign-barrier, and strong-frame derivations **do** use the
printed calculus and `valid_specification`.

**Suggested correction:** identify these two intermediate targets and
separate the paper explanation of the printed defect from the exact
checked statement. The source separation is real; the claim that every
cited theorem uses the original interpretation is not. This report adds no
new original-interpretation proof.

### 5. A command can establish all-processor points-to on a finite domain

**Location:** `changes.tex:60–64`.

The mark budget limits what **one action** can add; it does not say that
every mark in a postcondition must already occur in the precondition.
Thus "can therefore never be established by a command, only inherited"
is too strong.

For example, on the domain `{1,2}`, start with a flushed writer-existential
cell and execute `fence_1; fence_2`. The two fences can establish both
marks. `OwnedFenceExamples.owned_derive_fence_after` supplies the barrier
suffixes, and `OwnedPointsToRules.alternative_writer_complete_points_to`
identifies a writer cell carrying all active marks with the printed
points-to assertion. This is a composition of existing results, not a new
named proof added by this audit.

**Suggested correction:** acquisition by processor `i` alone cannot
manufacture the foreign processors' marks, so the *general acquire rule*
cannot promise all-processor points-to. That is the reason for the weaker
cell, and it is enough for the argument.

### 6. Distinguish program-step mark budgets from generalized futures

**Location:** `model.tex:11–15`.

"Nothing else does" omits `GeneralizedMark` in
`GeneralizedFlushing.v:19–26`. The future relation permits monotone mark
growth with no machine flush; its flush constructor can also add marks
beyond the flushing processor. `OwnedSafety.owned_safe` deliberately
quantifies over this full relation, including mark-only futures.

The program-step statement is narrower and correct:
`OwnedSafety.action_earns` permits a new mark only for the acting processor
of a fence, acquire, or release, and `owned_mark_budget` enforces that
bound. The attribution theorem chooses a particular flush future that adds
only the flushing processor's mark.

**Suggested correction:** state the program-step budget separately from
the additional abstract futures included for closure. These marks concern
local temporal composition; a local flush does not certify that an entire
concrete processor buffer, including an external frame, has drained.

### 7. Re-marking has a nonempty-target-mark premise

**Location:** `model.tex:83–87`.

`InvariantFragment.invariant_fragment_remark` assumes that source and
target have the same underlying memory **and that the target has at least
one completeness mark**. "Regardless of which processors are marked"
should retain that qualification. The singleton-acquirer case satisfies
it. The fragment-shape theorem separately supplies empty buffers and no
lock token.

**Suggested correction:** "the same memory with any nonempty admissible
mark set satisfies the same fragment invariant". This does not impose a
new condition on the proved acquisition rule.

### 8. The displayed buffered-load derivation omits freshness

**Location:** `proofs.tex:31–37`.

The displayed application of FRAME-TM needs `r` absent from `fv(R)`.
Otherwise the load can change the stack fact being framed. The cited
`OwnedBufferedLoad.owned_derive_load_after_history` also explicitly
requires the destination to be absent from the invariant, address,
processor annotation, and value expression. Those are present in the
general rules elsewhere in the paper but absent from this display.

**Suggested correction:** put `r` absent from `fv(J,R,x,i,v)` beside the
example, with `x,i,v` understood as the expressions in the displayed rule.
The theorem's postcondition moves the pure equality outside the temporal
conjunction; the displayed inside form is the intermediate FRAME-TM result
and is fine once freshness is stated.

### 9. The mailbox payload drains before the acquire, not at the later release

**Location:** `proofs.tex:171–175`.

The producer fills the payload before `nl_acquire`. That acquire contains
a physical global acquire, whose machine guard requires the producer's
buffer to be empty. The payload writes must therefore have drained before
that physical acquire can run. The concrete trace makes this explicit:
`MailboxTrace.mb_acquire_after_fill_trace` flushes both payload writes
before `named_lock_acquire_success_trace`.

The later full-flag write drains before the physical acquire inside
`nl_release`, as witnessed by `mb_publish_release_trace`.

**Suggested correction:** keep the useful "no explicit fence" claim, but
attribute the payload's draining to acquisition. A subsequent release does
not provide the first draining point for those writes.

### 10. The assertion-system paragraph needs two scope corrections

**Locations:** `intro.tex:63–67`; `proofs.tex:102–114`.

First, `AssertionSoundness.assertion_derivation_sound` proves soundness;
there is no incompleteness theorem. "It is not complete" is stronger than
the established result and conflicts with the accurate "No completeness
is claimed" in `calculus.tex:103` and the open question in `open.tex:24–27`.

Second, the promised caveat about the **older retrying container** is
missing. `OwnedRetryContainer.v` still discharges some CONS and UNLOCK
premises semantically, for example at lines 176, 182–185, and 216–218.
Its derivation remains valid. It just has not been migrated to assertion
proof trees throughout.

**Suggested correction:** say completeness is unestablished; scope the
claim about eliminating semantic entailments to the migrated one-item
container, message-passing, named-lock, and mailbox derivations. Add an
explicit sentence that the older retrying-container variant retains
semantic entailments, as the acceptance note requests. Make clear that the
sixteen-entailment count refers to the one-item derivation, not that variant.

## Smaller qualifications

- **Compatibility and daring rules (`wrong.tex:60–64`).** The claim that
  rejected compositions arise *only* under the unadopted daring rules is
  not established by the algebraic counterexample in
  `StableCompatibility.v`. That theorem is about resource compositions,
  not the reachable states or derivations of a specified subcalculus.
  Remove "only", or label this as an unproved claim about the intended
  ownership discipline. The soundness proof does not need it.
- **Available derived rules (`wrong.tex:204–208`).** Qualify "ATOMIC,
  SHARE ... are not available" as the *printed/unrestricted forms*.
  The same-J atomic wrapper and restricted semantic SHARE are now
  available, as the later sections correctly say.
- **Pending-write atom (`original.tex:83–85`).** "A single pending write
  ... and nothing else" hides the allowed blocked-writer bit.
  `ConcreteAssertions.pending_atom` permits `K` to be any subset of
  `{i}`; completeness marks are not fixed by the atom. Its heap is empty
  and its only buffered occurrence is the named write. The flushed case
  additionally has empty buffers and `K` empty. This distinction matters
  to blocked-store examples and some algebraic countermodels.
- **Concrete mailbox start (`proofs.tex:178–180`).** When stating the
  all-runs result, make the ordinary address-distinctness assumption
  explicit: `MailboxAdequacy.mailbox_all_runs` requires
  `NoDup (1 :: 2 :: foreign :: map fst items)`. The abstract derivation is
  for any list, including the empty list; the concrete inhabited start
  additionally separates its lock flag, mailbox flag, payload addresses,
  and foreign address. The named-lock display also needs a scratch
  register fresh for the whole global pool, as the acquire theorem states.
- **Container evidence (`proofs.tex:95–100`).** The cited
  `owned_container_foreign_pending_throughout` checks the pending write
  on the listed concrete memories. Also cite `owned_container_trace` for
  the 24-step execution and `OwnedRetryTrace.owned_container_completed_restores`
  for unconditional restoration on completion. Both already exist; the
  latter is stronger than the free-or-held conclusion of basic adequacy.

## Final figures and hypotheses

| Quantity | Confirmed value | Counting convention |
| --- | ---: | --- |
| Theory files | 193 | All `.v` files listed in `_CoqProject`; also exactly all `theories/*.v` files |
| Physical theory lines | 30,052 | All lines in those files, including comments, blanks, historical experiments, and `Audit.v` |
| Audited declarations | 1,284 | 1,284 distinct `Print Assumptions` entries; all 1,284 report `Closed under the global context` |
| Program-calculus constructors | 21 | Constructors of `OwnedCalculus.owned_derivation` |
| Assertion-calculus constructors | 47 | Constructors of `AssertionDerivation.assertion_derivation`; parameterized equivalence/direction schemas are counted once |
| Prover | Rocq 9.3.0 | Built with OCaml 5.5.2 |

`make check` passed on the checked draft, including the independent
`rocq check` of `WMLR.Audit`. A separate batch evaluation of `Audit.v`
produced exactly 1,284 closed-context lines and no other output. A scan
found no axiom/parameter declarations or admitted proofs in the theory
sources. There are no new proof declarations in this report.

The standing hypotheses of `owned_calculus_sound` and
`owned_derivation_adequacy` are exactly:

1. `invariant_fragment invariant`;
2. `two_active_processors active`, meaning two distinct active processors
   exist, **not** that the domain is finite or has exactly two elements.

Soundness also takes the derivation being interpreted. Adequacy adds the
specified concrete start: a resource satisfying `P`, a pool satisfying `J`
at full completeness, their spatial composition, and a free whole lock.
It quantifies over finite executions, with the postcondition conditional
on termination. The empty external frame is supplied internally; there is
no extra mode premise for the client.

`assertion_derivation_sound` has no standing fragment, processor-count,
finiteness, mode, or wand-free assumption. Its constructor-specific
conditions, including the boolean-only oracle and the qualified atomic
rules, remain part of its derivations.

Restricted SHARE has the same two standing hypotheses plus semantic
lock-freedom of **every** model of each endpoint assertion. It is a theorem
in either mode, not a 22nd program rule. Emp-to-emp restoration has the
initial lock-free-frame hypothesis described in correction 2. None of the
top-level results asserts termination, fairness, or deadlock freedom.

## Fixed reference for the paper

Cite **`99b4052d76238e6d3d89e27255a3d6d00e27a562`** as the fixed proof
artifact: it is the completed queue accepted and clean-built by the
reviewer, and it contains every formal result cited in this draft.

Artifact URL:
<https://github.com/iwehrman/weak-memory-local-reasoning-rocq/tree/99b4052d76238e6d3d89e27255a3d6d00e27a562>

The later draft commit `67b469bf9b9f6354e5181870f4a62431b5f3675a` is the
reference for this **paper audit**, not a different proof result. The
private repository's access status is unchanged. Paper-only corrections
do not require moving the proof citation; if any formal source changes,
the new artifact should instead be checked and pinned explicitly.

## Rocq reference map

All 35 explicit names resolve uniquely. No cited name needs to be renamed
or replaced because it is missing. Locations are in the unchanged theory
sources at the fixed proof commit. A citation resolving does not by itself
settle the scope issues above.

| Cited name | Definition or statement |
| --- | --- |
| `owned_derivation` | `theories/OwnedCalculus.v:12` |
| `assertion_derivation_sound` | `theories/AssertionSoundness.v:14` |
| `overlap_frame_shape_counterexample` | `theories/FrameShapeCounterexample.v:228` |
| `pooled_resource_flush_attribution` | `theories/FlushAttribution.v:55` |
| `ordered_residual_unique` | `theories/ResidualUniqueness.v:11` |
| `invariant_fragment_remark` | `theories/InvariantFragment.v:123` |
| `owned_safe_common_frame` | `theories/OwnedCommonSplit.v:68` |
| `owned_derive_store_fence_cell` | `theories/OwnedFenceExamples.v:26` |
| `owned_plain_store_cell_invalid` | `theories/OwnedFenceExamples.v:71` |
| `owned_derive_load_after_history` | `theories/OwnedBufferedLoad.v:44` |
| `owned_container_derived` | `theories/OwnedContainerDerivation.v:129` |
| `owned_container_foreign_pending_throughout` | `theories/OwnedContainerTrace.v:170` |
| `owned_retrying_container_derived` | `theories/OwnedRetryContainer.v:213` |
| `message_passing_all_runs` | `theories/MessagePassingAdequacy.v:107` |
| `message_passing_points_to` | `theories/MessagePassingAdequacy.v:146` |
| `named_lock_acquire_family` | `theories/NamedLockRules.v:109` |
| `named_lock_release_family` | `theories/NamedLockRules.v:117` |
| `mailbox_parallel_derived` | `theories/MailboxDerivation.v:97` |
| `mailbox_all_runs` | `theories/MailboxAdequacy.v:122` |
| `owned_calculus_sound` | `theories/OwnedCalculus.v:95` |
| `owned_derivation_adequacy` | `theories/OwnedCalculus.v:126` |
| `owned_printed_share_lock_counterexample` | `theories/OwnedAlternativeCounterexamples.v:84` |
| `owned_share_valid` | `theories/OwnedShare.v:162` |
| `owned_share_overlap_valid` | `theories/OwnedShareOverlap.v:146` |
| `owned_emp_derivation_restores` | `theories/OwnedExecution.v:71` |
| `printed_assignment_invalid` | `theories/SafetyExamples.v:41` |
| `printed_buffer_override_not_associative` | `theories/OrderedBuffers.v:116` |
| `printed_spatiotemporal_not_associative` | `theories/StableCompatibility.v:164` |
| `pointwise_temporal_wand_not_flush_closed` | `theories/FlushingCounterexample.v:92` |
| `printed_conjecture1_false` | `theories/SeparationExamples.v:163` |
| `arbitrary_invariant_unlock_invalid` | `theories/UnlockCounterexample.v:30` |
| `printed_points_stale_value_unsound` | `theories/PrintedPointsToDerivations.v:280` |
| `printed_points_foreign_barrier_unsound` | `theories/PrintedPointsToDerivations.v:295` |
| `printed_strong_frame_counterexample` | `theories/PrintedStrongFrame.v:60` |
| `trilemma` | `theories/ReviewObstructions.v:28` |
