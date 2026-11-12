# Current calculus: soundness and differences from the dissertation

The repaired Chapter 4 calculus is now sound by induction on derivations,
with operational adequacy for the dissertation's concurrent machine.
`owned_derivation` in [`OwnedCalculus.v`](../theories/OwnedCalculus.v) is the
active judgment; `owned_safe` / `owned_valid` remain the single safety target
introduced at checkpoint 5. No safety definition changed at checkpoint 11.

This is a soundness theorem for an explicitly repaired calculus. It is not
a proof of Theorem 1 with the printed rules and assertion interpretation
unchanged. Checked counterexamples rule out that claim. This document is the
consolidated comparison; earlier reports record historical checkpoints.

## Judgment, standing hypotheses, and theorem

Write `J ⊢ᵐ {P} c {Q}` for `owned_derivation active J m P c Q`.

| Mode | Environments admitted by validity | Rules specific to the mode |
| --- | --- | --- |
| Overlap (`OV`) | Compatible external frames, including overlapping histories | FRAME-TM |
| Disjoint (`DJ`) | External frame and local resource have disjoint address domains | UNLOCK |

Overlap validity is the stronger obligation. The explicit weakening rule
goes **OV → DJ**, never the other way. All other constructors are available
at both modes. Mode is a proof index, not a runtime state or a new assertion.

The soundness theorem has two standing hypotheses:

1. `invariant_fragment J`.
2. `two_active_processors active`: two distinct active processors exist.

Under these hypotheses, `owned_calculus_sound` proves every derivation
semantically valid. `owned_derivation_adequacy` takes a derivation directly
and proves no abort for every finite execution from a concrete free-lock
start with a local resource satisfying `P` and a disjoint pool satisfying
`J`. On termination it supplies `Q` and the final ownership decomposition.
It instantiates the empty external frame internally; no mode-specific
environment premise remains. Neither theorem assumes a safety or validity
certificate for the command.

This is partial correctness, not termination, deadlock freedom, fairness, or
progress. A prefix can stop inside a critical section with the invariant
open. Even a terminating specification may explicitly retain the lock.
For clients derived from `emp` to `emp`, with an initially lock-free external
frame, `owned_emp_derivation_restores` proves more: every completed execution
has a free lock, and its final memory splits into an actual invariant pool
and a future of that frame. Both container programs instantiate this result.

No finiteness hypothesis on the processor domain is used. The two-processor
condition is required by the original blocked-set encoding of the lock:
with one active processor, a held lock and a free lock coincide. We kept the
machine encoding instead of adding an owner field.

## Rule comparison

`C(a,v)` below is `writer_points_to a v`; `bar(i)` and `lock(i)` are the
existing atoms. `P ⋉ Q` still abbreviates `(P * Q) ∧ (P ; Q)`, with potentially
different witnesses for the two conjuncts.

| Printed rule or family | Current checked treatment |
| --- | --- |
| SKIP, ASSUME, ASSERT | Same forms, either mode. A false assumption waits; a false assertion aborts. |
| CONS, DISJ, SEQ, CHOICE, LOOP | Same forms, either mode. CONS keeps semantic entailment premises. Sequence, choice, and parallel premises use a common mode; weakening can align them. |
| ASSIGN | Full capture-avoiding substitution over the whole assertion grammar. Requires the destination absent from `fv(J)`, to preserve the shared invariant when the lock is free. |
| LOAD | Printed strong-temporal form is proved. The destination must be absent from the address, processor annotation, asserted value, retained assertion, and invariant. The appendix's freshness qualifications are explicit; they are not inferred from the unqualified figure. |
| STORE | Printed strong-temporal form is proved, without a new variable side condition. |
| LOAD-ANY, STORE-ANY | Added rules accessing `C(a,v)` regardless of its existential writer. Needed for cells transferred from the pool. These rules do not grant the acting processor a completeness mark. LOAD-ANY requires destination freshness for the address, asserted value, retained assertion, and `J`; it does not need annotation freshness because that annotation is absent from the preserved cell assertion. |
| FENCE | The printed small form `{emp} fence_i {bar(i)}` is a constructor at either mode. The more general `{P} fence_i {P ; bar(i)}` is also semantically proved; it is not an extra calculus constructor. |
| LOCK | Replaced by explicit acquisition: `{emp} acquire(i) {(lock(i) * J) ; bar(i)}`, either mode. The invariant's cells become local ownership, with no imported foreign-processor marks. |
| UNLOCK | Replaced by explicit restoration/donation: from `A ; bar(i) ⊨ J * B`, derive `{lock(i) * A} release(i) {B}` in DJ only. `A` and `B` are arbitrary assertions. The machine's existing release guard supplies the actor's drain; there is no extra fence instruction. |
| INV | Removed. Invariant transfer occurs at the actual acquire/release actions. Retaining INV would reintroduce the checked stale-value and foreign-barrier derivations. |
| FRAME-SP | Same assertion form and usual variable condition, either mode. No lock-free-frame or register-preservation condition. |
| FRAME-TM | Original assertion form and variable condition, restricted to an OV premise and conclusion. There is no syntactic “no unlock” premise. DJ validity alone is insufficient. |
| FRAME-STM | Omitted. A checked DJ counterexample exploits independent witnesses in the two conjuncts of `⋉`. The connective itself is retained unchanged and works in LOAD/STORE. No common-witness constructor was added. Soundness or failure of this frame rule in OV is not claimed. |
| CONC | Printed mutual variable-interference condition, plus neither command modifies a free variable of `J`. Supports arbitrary commands, nested parallel composition, and disjoint register updates. |
| EX | Printed freshness in command and postcondition, plus freshness in `J`. `owned_exists_valid` proves the rule in both modes by stack-agreement transport. |
| SHARE | Deliberately omitted. The top-level adequacy theorem starts directly with a concrete pool satisfying `J`; the current one-global-lock setting needs no nested invariant discharge. Omission is not a claim that SHARE has been refuted. |
| Mode weakening | New explicit OV → DJ rule. It packages the proved inclusion of semantic validities. |

There are 21 constructors. None contains `owned_safe`, `owned_valid`, or an
operational correctness assumption as a premise. Assertion entailments in
CONS and UNLOCK still require semantic proofs; there is no complete assertion
proof calculus or automation layer.

One formalization scope limit is explicit: the LOCK and UNLOCK schemas use
constant positive processor identifiers, matching the semantic transfer
theorems proved so far. The command grammar permits expression-valued
annotations, and the other primitive schemas support expressions. General
expression-valued lock schemas have not been proved here. This restriction
predates the derivation system; the new judgment does not silently generalize
those theorems.

## Assertion and resource semantics

These repairs preceded the final derivation system. They matter when
comparing meanings and entailments with the dissertation, even for rules
whose displayed syntax is unchanged.

| Area | Difference and reason |
| --- | --- |
| Temporal compatibility | Conflicts are checked for all active processors, including blocked ones. The printed blocking exception allows regrouping to change whether a composition is defined. `StableCompatibility.v` proves the repair and its conservativity. |
| Spatiotemporal buffer merge (`#`) | Uses event-ordered overriding, retaining write occurrences and requiring earlier-component writes to precede later-component writes to the same address. The printed interleaving-plus-lookup condition loses occurrence information. The repaired operation has constructive associativity and actual flush decomposition. |
| Separating implications | All three wands quantify over resource futures before testing extensions. The printed pointwise temporal wand is not flushing closed. The repaired semantics has closure for the whole assertion grammar and proved wand adjunctions. Wand-free formulas agree with the earlier repaired interpretation, not necessarily with the original compatibility relation. |
| Atomic assertions and grammar | No new atom or constructor. `emp`, write, lock, and barrier atoms keep their pre-retirement meanings. There are no tombstones or retirement marks. The original all-processor `A.points_to` abbreviation remains available unchanged under its own name. |
| Weakened cell abbreviation | `C(a,v) = ∃k. (a ↦ₖ v ; bar(k))`, with a fresh binder. It describes a flushed cell with some writer's mark, rather than marks for every active processor. This is an abbreviation in the existing grammar. |
| Shared invariants | Syntactic fragment: `emp`, `C(a,v)`, spatial conjunction, disjunction, existential quantification, and guards `b ∧ H` with `H` itself in the fragment. Bare pure assertions are excluded because they can absorb pending buffers. Arbitrary assertions, including wands, remain allowed in specifications and frames. |
| Completeness marks | A mark on a local resource constrains earlier history when that resource is composed temporally. A local flush does not claim that the whole machine buffer is empty. Fence/acquire/release additionally have whole-buffer guards in the machine; their proof updates may earn only the acting processor's mark. Acquisition re-marks the invariant for the acquirer alone. |

Every fragment invariant is buffer-free and token-free and survives any
nonempty re-marking of the same memory. Thus representing the free pool with
full completeness is a convention, not a permission to export every mark.
At release the invariant part cannot absorb a pending foreign write.
At acquisition the proof re-establishes the chosen mode, including disjoint
ownership of all acquired cells when working in DJ.

The paper algebra audit proves `emp` is a two-sided unit for `*`, `;`
and `⋉` for the entire assertion grammar, including wands, on every
processor domain. `AssertionUnits.v` removes the wand-free limitation of
earlier unit helpers; no semantic definition changes. The completed audit
also proves spatial/temporal associativity, lock symmetry, full barrier
distribution and successive-write collapse. It refutes strong-temporal
associativity in both directions, the small-exchange cases with `⋉`
outside, full exchange, and unrestricted lock multiplication. One
associativity countermodel and the lock countermodel are additionally
checked in the original interpretation. The lock witness has no admissible
machine environment; same-owner lock exclusivity still holds under the
standing two-processor assumption. The all-processor points-to/write law
needs an active annotation; for the weaker cell the exact condition is
presence of that processor's mark. See the
[complete audit](../review/paper-algebra-audit.md) for all instances,
including both readings of the small-exchange premise. The interpretation
and program rules remain unchanged; no assertion rule set has yet been
selected.

The grammar has no recursive predicates. The invariant fragment therefore
does not describe an unbounded linked container. That expressiveness limit
is inherited from the formalized grammar; it is not a finiteness assumption
on machine heaps or processors.

## Safety definition and machine

The concurrent operational machine is unchanged by the ownership repair:
stores enqueue, loads can forward, flushes update shared memory, and
acquire/release wait for the acting processor's buffer to be empty. The
formalization separates program steps from flush steps explicitly and
accounts for assignment actions in safety.

The replacement safety predicate has one local owned resource and an
external invariant pool. When free, the pool satisfies `J`; when held, the
pool is empty and the token and its cells can belong to the current thread,
another thread's frame, or a split compatible context. Only release requires
the complete token locally. There are no permanent protected/private
assertion compartments or open/closed indices in the judgment.

Each program step fixes its input frame exactly. Each recursive safety
obligation quantifies environments afresh, allowing other threads to act
between the thread's steps. Pool transfer is tied to the actual lock action;
the footprint bound prevents acquiring unrelated cells, and the mark budget
prevents inventing foreign barriers. Machine flushes are attributed to the
frame or local component with the other fixed, not handled by arbitrary
repartitioning. Safety is closed under all generalized local futures,
including mark-only futures and local flushes blocked in a particular
external environment. That stronger closure survived the general proofs.

## Derived examples and practical cost

Both the original selected-branch container and a retrying version have
actual derivation trees in the new judgment. The original uses FRAME-TM at
reacquisition. The retrying version uses a done register, CHOICE and LOOP;
an unsuccessful take releases the lock before retrying. Retaining spatial
ownership of its private item excludes a full pool that owns the same item,
so the return operation's failure branch is unreachable. Its acquisition is
proved using FRAME-SP instead. This is a stronger precondition already
available from the preceding private store, not a new side condition.

A 52-step successful trace starts with the free, nonempty pool and keeps an
unrelated processor's write pending. A second concrete trace executes two
failed take iterations (30 steps) from an admissible empty-container pool,
releasing the lock and returning to the loop each time. Neither trace is a
claim of termination for every schedule. The language's guarded-choice
encoding can also choose a false assumption and wait.

The practical proof work remains assertion entailment. The original example
had 16 named obligations (28 expanded instances); its derivation trees reuse
that algebra and replace manual existential opening with EX. Derived rules
now package cell-only LOAD/STORE, assignment from an entailment about the
updated stack, while loops, and unreachable release. The retrying proof adds
two ownership entailments: spatially retained item history excludes the full
pool, and release's barrier completes both histories for donation. Guards
and stack-update assertions are still discharged semantically. No new
FRAME-STM, invariant fragment, validity predicate, or extra fence was needed.

`OwnedBufferedLoad.v` also derives loading one's own latest write from
`(R ; W(a,i,v)) * T`, with arbitrary history `R` and spatial tail `T` and
the usual destination freshness conditions. It uses the existing LOAD,
FRAME-TM, FRAME-SP and mode weakening rules; no LOAD constructor is added.
Concrete tests cover a still-pending write, its flushed future, and another
processor reading the older heap value. See the
[early paper report](../review/paper-units-and-buffered-load.md).

## Superseded experiments and remaining scope

`OwnedCalculus.v` is the active proof system. `RepairedSafety`/`RepairedRules`,
`PersistentCalculus`, `OwnershipProtocol`/`OwnershipCalculus`,
`PrivateOwnership`/`PrivateCalculus`, `TemporalSafety`'s alternative safety,
`RegionalSafety`/`RegionalCalculus`, `SeparatedSafety`/`SeparatedCalculus`, and
the `Retired*` safety/calculus development are historical alternatives, not
additional validity layers required by the current judgment. Some files also
contain resource utilities reused by the active proof. They are retained
with their original theorem meanings, rather than relabelled as proofs of
the new predicate. The retirement interpretation is abandoned.

The assertion grammar, original machine/transcription, repaired algebra,
future-aware assertion interpretation, invariant-fragment proofs, and
`Owned*` rule modules are active foundations. Checked counterexamples remain
regressions and evidence explaining the repairs. See the
[historical index](development-history.md) and
[obstruction notes](soundness-status.md) for that chronology.

The main Chapter 4 repair now has calculus-level soundness and adequacy.
Remaining extensions include assertion proof automation, expression-valued
lock schemas, recursive predicates, and the dissertation's Chapter 5
experiments. FRAME-STM and SHARE are deliberate omissions from this target,
not unfinished cases hidden inside its soundness proof. Sequential Chapter 3
syntax is present, but no separate complete sequential soundness theorem is
claimed.
