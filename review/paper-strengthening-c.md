# Strengthening C, and optional D1

The A/B results are in `paper-strengthening-ab.md`, committed at `50f1dbb`.
The targets for this batch were stated in `paper-strengthening-c-statement.md`.
No existing safety definition, assertion interpretation, invariant fragment,
or calculus constructor changes in this batch. Paper edits remain with the
reviewer.

| Request | Result | Principal theorem |
| --- | --- | --- |
| C1: every nonempty invariant makes release overlap-invalid from a satisfiable precondition | **False as stated** | `owned_universal_donation_obstruction_refuted` |
| C2: FRAME-TM cannot accept an arbitrary DJ-valid premise | **Proved counterexample** | `owned_disjoint_temporal_frame_counterexample` |
| C3: omit the fragment hypothesis from calculus soundness | **Proved counterexample**, both modes | `owned_soundness_without_fragment_refuted` |
| C4: omit the two-processor hypothesis from calculus soundness | **Proved counterexample**, both modes | `owned_soundness_without_two_processors_refuted` |
| D1: INV alone under printed validity | **Proved counterexample** | `original_inv_alone_counterexample` |
| D2: FRAME-TM alone under printed validity | **Deferred optional work** | No new claim |

C's results are in `theories/OwnedNecessity.v`; D1 is in
`theories/OriginalLocalCounterexamples.v`. Every new theorem and helper is
included in `Audit.v`.

## C1: a satisfiable assertion need not have an environment

Take exactly processors 1 and 2, `J = C(2,7)`, `A = lock(2)`, and
`B = false`. The resource assertion

```text
lock(1) * lock(2)
```

is satisfiable. The first token blocks `{2}`, the second blocks `{1}`,
and these blocked sets are disjoint. Their spatial union has empty heap
and buffers, and blocks both processors. It is a well-formed generalized
resource. `two_locks_inhabited` gives its concrete model.

No admissible environment can contain it. A whole memory containing the
resource still blocks both processors. It is neither free nor held by any
active processor, because a held lock leaves its owner unblocked.
`all_blocked_has_no_owned_environment` proves this directly from
`owned_pool_status`. The same holds of every local future.

Consequently the nonterminal release specification

```text
{lock(1) * lock(2)} unlock(1) {false}
```

is valid in **both** modes: its environment obligations are empty.
`owned_inhabited_but_environmentless_unlock_valid` proves the more general
fact for every invariant and postcondition. The principal counterexample
also proves the other requested hypotheses: two active processors, a
fragment invariant, and a heap cell in every model of that invariant.

This does not provide a safe example of an actual overlapping donation.
It refutes the proposed theorem's stated non-vacuity condition. Any
replacement must at least require an admissible environment in which a
release really is enabled, rather than merely a model of the precondition.
For example, one could require witnesses for the precondition, an
`owned_environment`, and a `program_step` with `ReleaseAction i` at the
same stack and whole memory. I have **not** proved that this replacement
hypothesis is sufficient for the desired universal obstruction. That is
the statement to settle next if the paper needs the general necessity
claim. Existing concrete overlap-donation failures remain valid.

This is also why the lock-exclusivity law in the algebra audit required
an active processor blocked by *both* tokens. Two different tokens need
not conflict as resources on a two-processor domain.

## C2: temporal framing really needs a stronger premise

The counterexample reuses the one-cell invariant, buffered histories, and
enabled release from the FRAME-STM diagnostic. Only the temporal
conjunct is used now:

```text
valid DJ J P release Q
mod(release) ∩ fv(R) = ∅
not valid DJ J (R ; P) release (R ; Q)
```

`J = C(3,0)`, and `R` chooses between a write to location 2 and that
same cell at location 3. The initial local resource has the lock, the
location-3 cell, and processor 2's pending writes to locations 1 then 2.
The temporal precondition uses the overlapping cell branch of `R`.

Release must return location 3 to the pool. The fixed-frame argument
forces the residual to have an empty heap and those same two buffered
writes. It cannot satisfy `R ; Q`: the cell branch has no heap cell left,
and the write-to-2 branch cannot be the temporal prefix of a buffer that
starts with the write to location 1.

The proof uses the concrete `stm_initial_environment` and
`stm_release_step`, so this failure is not due to an empty set of
environments or a stuck release. It rules out every successor admitted by
the fixed safety definition. It does not use strong temporal conjunction
in the specification being refuted.

## C3: the all-processor invariant breaks the transferring LOCK rule

Let `J` be the original printed `2 ↦ 7`. `OwnedLock` derives, in either
mode,

```text
J ⊢ {emp} lock(1) {(lock(1) * J) ; bar(1)}.
```

Start with the lock free, a one-cell pool satisfying `J`, an empty local
resource with no marks, and an empty external frame.
`all_processor_initial_environment` establishes this concrete admissible
start. The acquire is enabled.

Every model of the postcondition contains processor 2's completeness
mark. Every permitted successor is bounded by the empty input mark set
plus the acting processor's mark, here only processor 1. Thus no safe
successor can meet the postcondition. The proof does not choose one
unhelpful residual; it rules out all of them using `owned_mark_budget`.

One acquire already suffices, so there is no need to build the longer
acquire/release example suggested in the request. The result pairs the
derivation with invalidity and keeps two distinct active processors. It
therefore is literally a counterexample to `owned_calculus_sound` with
the fragment hypothesis removed.

**Scope for the paper:** some restriction on invariants is necessary for
the unchanged transferring rule. In particular, a general acquisition
cannot return the printed all-processor points-to assertion. This does
not prove that our *exact* fragment or cell abbreviation is the unique
repair among alternative rule designs. The old points-to can still be
used in preconditions and postconditions; the issue is promising it from
this acquisition.

## C4: the two-processor assumption is needed by soundness

Take the singleton domain `{1}` and the fragment invariant `C(2,7)`.
The first acquisition has the usual postcondition

```text
L = (lock(1) * C(2,7)) ; bar(1).
```

Spatially frame that first result around a second `OwnedLock`. Sequencing
then derives

```text
{emp} lock(1); lock(1) {L * L}.
```

`owned_singleton_double_acquire_derived` is an actual derivation in each
mode, using the existing unit entailment, spatial frame, and sequencing
rules. No soundness assumption is used to construct it.

`single_initial_environment` supplies a free-lock start with the nonempty
one-cell pool. `single_double_acquire_execution` proves a complete
three-step machine execution, including the sequence transition: both
acquires run because the singleton held encoding has no blocked bits.

`owned_singleton_double_acquire_invalid` refutes validity from that start,
even for an arbitrary postcondition. The first successful acquire forces
the pool phase to held. The intermediate sequence step preserves it. The
second acquire is physically enabled but requires the input phase to be
free. No choice of residuals can reconcile those requirements.

The principal theorem pairs the derivation and invalidity while retaining
the invariant-fragment hypothesis. This is a counterexample to calculus
soundness with only the two-processor hypothesis removed, rather than just
an observation that the lock encoding is ambiguous.

## D1: INV alone

Use `J = false`, `P = emp`, `Q = false`, and `c = skip`. The exact printed
INV premise is

```text
emp ⊨ {false * (emp * lock(1))} skip {false * (false * lock(1))}.
```

It is valid because its precondition has no models. The proposed INV
conclusion is

```text
false ⊨ {emp * lock(1)} skip {false * lock(1)},
```

which is invalid: the precondition has a concrete full-completeness
held-lock model, and the terminal clause requires an impossible
postcondition immediately. `original_inv_alone_counterexample` proves
both halves using `valid_specification`. No temporal-frame rule is used.
The valid premise is deliberately vacuous; this is a minimal logical
counterexample, not an inhabited execution of that premise.

## D2 and the next reviewer decision

The existing private-validity counterexample does not supply the printed
premise. The natural original target is still
`{emp} skip {bar(1)}`, framed by a pending processor-1 write. Proving its
premise under printed validity must handle arbitrary machine flushes and
reconstruct the printed environment at every index. There is no general
printed skip-validity theorem in the current library to instantiate.
I stopped after this feasibility check rather than adding that
infrastructure in the optional batch. No isolated printed FRAME-TM result
is claimed here; the existing combined printed-rule refutations remain.

The mandatory requests are now either proved or, for C1, refuted in their
stated form. The reviewer can revise C1's non-vacuity hypothesis, retain
the paper's qualified necessity claim, or request the optional D2 proof.
No failure of an accepted positive rule or change to the core semantics
has been found.

## Validation

`make check` passes. A second `make check` from a fresh source-only export,
with no compiled files copied, also passes. Both audits print exactly
**1,316** closed-context reports, with no errors, and both complete the
independent kernel check of `WMLR.Audit`. The fresh export was compared
with the final theory sources and build inputs before committing.

The source counts are **196 theory files**, **30,574 physical lines**, and
**1,316 audited declarations**. The program and assertion constructor
counts remain **21** and **47**. The final strengthening commit should
replace `99b4052` as the paper's fixed proof reference; it contains A, B,
C2–C4, the C1 refutation, and D1. Earlier reports' counts describe their
own checkpoints.
