# Work queue for the follow-up paper

From the reviewer, after checkpoint 11 (`0e1ae5f`). The lead continues to own
the proofs; the reviewer owns the writing. This queue lists proof work that
the paper needs. The same rules as before apply: state the target before
proving it, search before a general proof where a search is cheap, and stop
and report if a rule fails or a new side condition, atom or validity
predicate is needed.

## Checkpoint 11: accepted

I rebuilt `0e1ae5f` from a clean clone. `make check` passes with 683 audited
declarations closed and no axioms or admitted proofs. I read
`owned_derivation` in full: 21 constructors, none with a safety or validity
premise, UNLOCK at disjoint mode only, FRAME-TM at overlap mode only, and
weakening from overlap to disjoint. `owned_calculus_sound` is a direct
induction over those constructors. The clarification that no-abort does not
mean every prefix restores the invariant is correct, and
`owned_emp_derivation_restores` is the right stronger statement.

## The paper and its reader

The paper is for a small audience who know the dissertation and have
forgotten its details. It is chronological: the original model and calculus,
what was wrong, what changed, the new model and calculus, the results, and a
short comparison with later work. Differences from the dissertation are in
the foreground. So the most valuable proof work is whatever lets the paper
make an exact statement about the original, in the original's own terms.

## Priority 1: the dissertation's own example (Section 4.1)

The dissertation's worked concurrent example is a message-passing program:

```text
c_s = lock_0; [d] := 1_0; unlock_0
c_r = lock_1; x := [d]_1; unlock_1; if x = 1 then ([d] := 2_1; fence_1)

emp ⊢ {x = 0 ∧ d ↦ 0}  c_s || c_r  {d ↦ x + 1}
```

Its proof uses an auxiliary assignment `s := 1` in the sender and the
invariant

```text
I = (x = 0 ∧ (s = 0 ∨ s = 1) ∧ d ↦ s) ∨ (x = 1 ∧ s = 1 ∧ emp)
```

`I` mentions `x` and `s`, which the threads modify. The repaired calculus
forbids that. A reader who remembers one proof from the dissertation will
remember this one, so the paper has to say what happens to it.

Targets:

1. **Status of the original proof.** State precisely which steps of the
   dissertation's derivation the repaired calculus rejects, and why. If the
   printed derivation relies on an instance that is itself unsound, exhibit
   it; if it is merely no longer derivable, say that instead.
2. **A repaired derivation of the same program.** No auxiliary code if
   possible. My suggestion, which is unchecked: replace the auxiliary
   registers by ownership tokens, which are allocated cells that are never
   read or written. The sender starts with a token `t`, the receiver with a
   token `r`, and

   ```text
   J = C(d,0) ∨ (C(d,1) * C(t,_)) ∨ (C(t,_) * C(r,_))
   ```

   The sender holding `t` excludes the last two branches when it acquires;
   the receiver holding `r` excludes the last branch. The receiver keeps `d`
   and donates `r` when it reads 1.
3. **The original conclusion.** Recover `d = x + 1` on termination for every
   execution. With tokens this may need a domain-preservation argument at
   the adequacy level, or the restricted SHARE of priority 3. Report which.
4. **Non-vacuity.** Traces for both outcomes (`x = 0` and `x = 1`), with the
   receiver's private store buffered at some point.

Report the design before the proof. If tokens do not work, that is a finding
the paper needs, not a failure to hide.

## Priority 2: one ambitious derivation

The paper should include a derivation of something more substantial than the
dissertation could attempt. The constraints are the current language: no
allocation, no recursive predicates, constant or expression addresses.
Assertion families defined by a Rocq function over a size parameter are
allowed and encouraged.

My proposal has two parts. The lead may propose something better, but should
report the design and the intended theorem statements first.

**Part A: named locks as derived rules.** The machine has one global lock.
Build a test-and-set spinlock on a flag cell `l`, with acquisition as a
retry loop under the global lock and release under the global lock, and
prove derived rules for an arbitrary lock invariant `I_l`:

```text
J ⊢ {emp} acquire(l) {I_l}
J ⊢ {I_l} release(l) {emp}

J = product over locks l of ((C(l,0) * I_l) ∨ C(l,1))
```

for any finite family of locks with fragment invariants. I expect release to
need `I_l` to be exclusive (`I_l * I_l` unsatisfiable) so that holding `I_l`
excludes the unlocked branch. State whatever condition is needed. This
recovers the multi-lock rules of concurrent separation logic inside the
single-lock TSO calculus, which is a result about the calculus and not only
an example.

**Part B: a client.** A producer and a consumer in parallel, passing a
message of `K` cells through a mailbox protected by a spinlock from part A,
for arbitrary `K`:

- The producer fills the cells privately with ordinary stores, with no
  fence, and donates them by acquiring and releasing.
- The consumer retries until the mailbox is full, withdraws the cells, and
  reads them privately.
- The specification says the consumer ends up owning cells holding the
  values the producer wrote.
- A third processor's unrelated write stays pending in a checked trace.

This scales the dissertation's message-passing theme up to a data structure
with ownership transfer of a region, a derived lock abstraction, and
concurrency, and it relies on the TSO-specific point that the release drains
the producer's buffer.

If part A fails or needs a condition that makes it unusable, stop and
report. If part B at arbitrary `K` is too heavy, a fixed small `K` with the
parametric statement left open is acceptable, stated as such.

## Priority 3: small results that make the exposition exact

Each of these is a table row or a sentence in the paper. They are
independent and can be done in any order.

1. **SHARE.**
   - Check the counterexample to the printed SHARE under the new LOCK:
     apply it to `owned_lock_valid` with a one-cell invariant; the
     postcondition requires two disjoint copies of the cell.
   - Attempt a restricted SHARE: the precondition and postcondition are
     lock-free, disjoint mode. Report whether it holds, and whether it fails
     in overlap mode.
2. **What survived.** A checked list, with theorem names, of the
   dissertation's assertion laws that hold in the final interpretation:
   both unit laws for `emp`, associativity of `*` and `;`, commutativity of
   `*`, the three wand adjunctions, and flushing closure.
3. **The dissertation's derived rules.** For each rule in its "Derived and
   Alternative Axioms" paragraph (LOAD-P, STORE-P, the strengthened LOCK and
   UNLOCK, FENCE-G, LOCK-G, UNLOCK-G, the backward variants, LOCKED, ATOMIC),
   report one of: derived in `owned_derivation`, derivable in modified form,
   or not available, with a reason. The "daring" rules are expected to be
   unavailable; one sentence saying why is enough.
4. **Printed counterexamples in the dissertation's own abbreviation.** Redo
   the two derivations of `review/Derivations.v` with the all-processor
   points-to, so the claim about the original uses its own definitions.
5. **Move the review proofs into the build.** `review/Review.v` and
   `review/Derivations.v` are outside `_CoqProject`. Put them, or
   equivalents, under `theories/` and in `Audit.v` so the paper can cite
   audited declarations.
6. **Dekker with fences.** The introduction motivates the work with a fenced
   Dekker's algorithm. It reads the other thread's flag without the lock, so
   I expect it to be out of reach. Confirm that in one paragraph, identifying
   the missing rule. No proof is needed unless it turns out to be derivable.
7. **Index for the writer.** One file mapping each rule, each repair and each
   counterexample to its theorem name and source file, plus the figures the
   mechanization section needs: lines of Rocq, audited declarations, and the
   standing hypotheses. `notes/current-calculus.md` is close; it needs the
   theorem names made uniform and the errors separated from the design
   choices.

## Priority 4: a proof system for assertions

Approved by Ian. The dissertation's "Contributions and Status" section names
two major components left unfinished: a proof system for the assertion
language, and the soundness proof. The second is done. This is the first.

It has three parts. Part A is independent and may start at any time. Parts B
and C come after priorities 1 and 2, because those derivations show which
laws recur.

**Part A: audit the dissertation's algebra.** Figures 4.5 and 4.6 (the
"Concurrent Algebra" subsection) list about twenty equivalences and
entailments, several stated schematically over all three conjunctions. For
each instance, in the final interpretation (`persistent_models`), report one
of: proved, refuted with a checked countermodel, or holds in a stated
modified form. Do not assume any of them. I expect at least the full
exchange law for `*` and `⋉` to be doubtful, given the FRAME-STM
counterexample, and the laws mentioning points-to need both the printed
all-processor abbreviation and `writer_points_to`. The result is a table for
the paper.

**Part B: a sound rule set.** An inductive entailment-derivation type whose
rules are:

- the laws that survive part A;
- ordinary first-order rules for the connectives and quantifiers;
- the three wand adjunctions;
- the laws the container proofs needed repeatedly: barrier distribution over
  spatial conjunction, collapse of a drained history to its current cell,
  cell exclusivity, and existential introduction for cell values;
- whatever priorities 1 and 2 show to be recurring.

Pure boolean and arithmetic facts stay as semantic side conditions. Prove
soundness with respect to `persistent_entails`. State the rules before
proving them, as with every earlier checkpoint.

**Part C: use it.** Give CONS and UNLOCK variants whose premises are
entailment derivations, and re-derive the one-item container with no
semantic entailment premises. If a step cannot be derived, report the
missing law; that is the measure of whether the rule set is adequate. Then
do the same for as much of priorities 1 and 2 as is practical, and say what
was left semantic.

**Out of scope.** Completeness, decision procedures and proof automation.
The dissertation itself observes that no complete rule set exists, because
the language includes arithmetic. Do not change the assertion grammar or
interpretation; a law that needs such a change is a stop-and-report.

## Check-in points

- After the design for priority 1, and again after its result.
- After the design and theorem statements for priority 2, before part A's
  proof; then after part A; then after part B.
- After priority 4 part A's table; after the rule statements for part B,
  before their soundness proof; and after part C.
- Priority 3 items need no individual check-in. Report them together, and
  immediately if any contradicts something the calculus currently claims.
