# Lead's check of unlocked access and the Dekker appendix

Responds to `review/reviewer-guidance-daring-5.md`.
Paper draft: **`fb95d06c3dcbb2b904aa88c4842a764683116419`**.
Proof artifact: **`521acd600bf4b6352c21946d1526c49367402dec`**.
Line numbers below refer to that paper draft and the unchanged proof sources.

The core account is correct: the two counterexamples have the stated causes,
the invariant and exchange table match the six atomic premises, and the
24-shape count is correct for lock-free pool memories. The text needs the
scope qualifications below. These are paper corrections, not new proof work
or a proposed change to either calculus. I have not edited `paper/` or the
formal development.

## 1. Differences between the judgments and the atomic premise

The three differences in `dekker.tex:38–52` are correctly identified:

- The buffered invariant can own pending writes, unlike the heap fragment
  used for lock transfer (`BufferedPoolCandidate.v:11–21` versus
  `InvariantFragment.v:89–108`).
- Primitive accesses may redistribute the pool and private resource. The
  first judgment keeps the pool fixed on ordinary and fence actions
  (`OwnedSafety.v:49–60`); `buffered_update` has no such clause
  (`BufferedPoolCandidate.v:47–54`).
- The new judgment uses disjoint frames and has no temporal-frame
  constructor (`BufferedPoolCandidate.v:91–93`,
  `BufferedPoolCalculus.v:12–49`). It also assumes the whole lock is free
  in each environment; the atomic-premise prose correctly says unlocked.

**Make the invariant fragment explicit** (`dekker.tex:42–46,68–72`). The
cited soundness and adequacy theorems both assume
`buffered_invariant_fragment J`. The first bullet suggests its new history
form, but does not explicitly retain the grammar restriction from the earlier
calculus. Suggested insertion:

> The invariant fragment from the repaired-calculus section is extended with the
> history form `e ↣ u ; e ⇝_i v`. The other constructors, including the
> guarded pure formula, stay the same. Soundness and adequacy hold for this
> extended fragment, for arbitrary processor domains.

Use the existing section reference in the LaTeX text. The exact grammar
is `emp`, a cell, a cell followed by one write at the same address,
spatial conjunction, disjunction, existential quantification, and `b ∧ H`.
It does not allow arbitrary temporal formulas or bare pure invariants.
This is a qualification of the cited statements, not a claim that a broader
soundness theorem is impossible.

Also change “A daring store places its write in the invariant” to
**“An unlocked store may leave its write in the invariant; the Dekker proof
below does so.”** That is what the certificate does, but it is not a
requirement of every instance of ATOMIC: the successor split may instead
move ownership into the private resource. The historical sentence about the
dissertation's concern is accurate; see the source check below.

### The one-step premise

`dekker.tex:59–64` accurately describes non-abort, all possible results,
full completeness on the pool, and the private mark budget. The marks are
compared with the **input private resource**, not with the fully marked
combination `J * P`. The angle brackets must continue to denote this custom
one-step premise, not an ordinary Hoare triple under the empty invariant.

For an exact description, also mention the joint footprint and the stack:
`buffered_atomic_premise` evaluates the postcondition and restored invariant
on the output stack and requires the returned memory to remain unlocked
(`BufferedPoolCandidate.v:101–116`). Its update requires

```
dom(pool') ∪ dom(private') ⊆ dom(pool) ∪ dom(private).
```

This footprint clause is automatically obtainable here from spatial
composition and the machine's domain bound; it does not create another
manual obligation for these certificates. The certificate proof obtains it
at `BufferedDekkerVerification.v:152–156`.

A replacement for `dekker.tex:60–66` that spells out the premise and the
flush argument is:

> Its premise concerns one primitive step. For every stack and every
> unlocked memory split into a pool satisfying J and a private resource
> satisfying P, the command cannot abort. Every enabled result must split
> into a pool satisfying J and a private resource satisfying Q on the
> resulting stack, without introducing addresses. Both pool models use
> full completeness. A program step may add no private mark except the
> acting processor's at a fence. No extra flush condition is imposed on
> this premise: the soundness proof attributes each intervening machine
> flush to the pool, thread, or frame and applies flushing closure.

The last sentence is more precise than “no condition is needed ... because
assertions are closed.” The safety predicate does contain an explicit flush
clause. `buffered_environment_flush` supplies its three-way attribution and
successor environment (`BufferedPoolResources.v:69–101`), and
`buffered_atomic_valid` uses it with assertion closure
(`BufferedPoolRules.v:65–85`). No progress or enabledness guarantee is added;
a fence with a pending buffer is allowed to wait.

## 2. Causes of the original daring-rule counterexamples

The explanation in `dekker.tex:25–35` is correct for the repaired calculus.
Keep that qualification; these theorems are not claims about adding the
rules to every possible interpretation of the dissertation.

**LOAD, with a locally held lock.** The extended-calculus counterexample
acquires the invariant cell `d = 0`, stores `d := 5` privately, and loads d
while still holding the lock. Its local precondition contains d's history.
Consequently `J * P` demands two disjoint copies of d and is false. The
added rule turns that false-premise derivation into a claim that the load
returns 0; the checked five-step execution returns 5 from the buffer.
This is exactly `daring_load_extension_breaks_adequacy`
(`DaringCounterexamples.v:117–136`).

**The honest LOAD counterexample has a different placement of the token.**
Its premise is inhabited and valid. In the refuting environment, the local
resource and pool are empty; the fixed frame contains processor 1's token,
d's heap cell and its pending `d := 5`. Processor 1 is the lock owner, so
its load is enabled and reads 5. This is
`daring_load_honest_counterexample` (`DaringCounterexamples.v:156–201`).
The paper's summary covers the underlying held-lock obstruction, but should
not be read as saying that the local resource owns the token in both tests.
No change to the current summary is necessary for this distinction.

**STORE, with the lock free.** The valid premise exchanges an invariant
cell d for a private cell e, keeping d's new history privately. In the
conclusion, the ordinary-step update requires the actual pool to remain
unchanged. It therefore keeps d's cell and cannot absorb the new write.
The write must be in the local residual, which violates pool/local spatial
separation. `daring_store_no_successor` rejects every successor independently
of its postcondition (`DaringCounterexamples.v:259–274`).

Thus “fixed and free of buffered writes” describes the model correctly.
More precisely, **the fixed-pool clause already forces this particular
contradiction**; buffer-freeness is not a separate hypothesis used in the
no-successor lemma. A concise alternative for the last sentence is:

> An ordinary step keeps the pool fixed. The pool therefore retains the
> cell and cannot absorb the new write, while placing that write in the
> thread's resource would violate spatial separation.

Both honest counterexamples hold in both ownership modes.

## 3. Appendix invariant, exchanges, and 24 shapes

`appendix.tex:531–578` matches `BufferedDekker` and `BDP`. The correspondence
with concrete addresses is:

| Paper name | Rocq address |
| --- | ---: |
| f₁, f₂ | 1, 2 |
| w | 3 |
| a₁, b₁, q₁, t₁, p₁ | 4, 5, 6, 7, 8 |
| a₂, b₂, q₂, t₂, p₂ | 9, 10, 11, 12, 13 |

There are eleven token cells, as stated. They are never accessed by the
machine program. Paper thread 1 is named `thread0` in the Rocq definitions;
its processor is still positive 1. Its result register is Rocq identifier 0;
paper r₂ is identifier 1. This is a notation change, not a mismatch.

| Stage | Private resource | Exchange / pool effect |
| --- | --- | --- |
| Before store | aₖ * tₖ * pₖ | Initial condition |
| After store | bₖ * tₖ * pₖ | Give aₖ, take bₖ; store the flag's one-write history in the pool |
| After fence | bₖ * qₖ * pₖ | Give tₖ, take qₖ; the flag history has drained to value 1 |
| After load returning 1 | bₖ * qₖ * pₖ | Keep pₖ; no prize exchange |
| After load returning 0 | bₖ * qₖ * w | Give pₖ, take w |

These are exactly `start0/1`, `stored0/1`, `fenced0/1`, and `loaded0/1`.
The table correctly does not add a barrier to the fence postcondition:
these particular certificates preserve the old private marks, although
the general fence budget permits one more.

The explanation about excluding one's own winning disjunct and observing
1 after the other thread has won is correct. In the other thread's
middle stage, its write is either pending (the load returns 0) or drained
(the load returns 1). Spatial ownership of w excludes both zero outcomes
(`BufferedDekkerProof.v:95–114`).

**Keep 24; qualify it as lock-free pool memories**
(`appendix.tex:580–582`). A Gₖ has four images: the initial stage, two
images for the history stage, and the fenced stage. Fₖ has one. Hence

```
4 × 4 + 1 × 4 + 1 × 4 = 24.
```

The normalization theorem `BD.models_image`
(`BufferedDekkerResources.v:196–214`) assumes a lock-free memory. This
assumption follows from the atomic environment but should not be dropped
when describing all models of J: a pending-write atom on its own may
contain the writer's blocked bit.

Suggested replacement:

> Each of the six premises is proved by a checked finite certificate over
> the 24 lock-free pool-memory shapes satisfying J. A normalization theorem
> covers every model in an admissible environment, so this enumeration is
> exhaustive rather than a bounded search.

I evaluated the actual Rocq image lists and certificates. The results were:

| Quantity | Thread 1 | Thread 2 |
| --- | ---: | ---: |
| Gₖ images | 4 | 4 |
| Store input images disjoint from its private precondition | 5 | 5 |
| Fence input images disjoint from its private precondition | 10 | 10 |
| Load input images disjoint from its private precondition | 5 | 5 |
| Enabled input images for each respective primitive | 5 | 5 |

There are 24 invariant images in total; the image-equality check finds no
duplicates. All six `BDV.certificate` computations return `true`. The other
five compatible fence inputs have a nonempty issuing buffer, so no fence
step is enabled. The certificate
ignores pool shapes that overlap the private precondition, as it should.
The coverage and certificate-soundness proofs are existing theorems, not
assumptions inferred from these evaluations.

## 4. Limits paragraph: restrict the mark claim to ordinary accesses

`dekker.tex:85–88` correctly separates the two judgments and excludes the
full retrying Dekker algorithm. The issue is `dekker.tex:89–95`:

- “needs a completeness mark **before** it can take a cell” is too broad.
  The proved obstruction is for an **ordinary** action
  (`buffered_unmarked_ordinary_no_heap`,
  `BufferedPoolResources.v:103–111`). A fence has a different action label
  and may earn its processor's mark during the same step. The ordinary
  impossibility result cannot be stated as applying to every ATOMIC instance.
- `buffered_barrier_parallel_initial_adequacy` initializes **two empty
  private memories**, with active processors, a free-lock whole memory
  satisfying J at full completeness, existing derivations from the barriers,
  and the ordinary CONC variable conditions. It is not an entailment
  `emp ⊨ bar_i`, a guarantee of allocation, or an unconditional withdrawal
  rule. It does not require the shared buffers to be empty.

Suggested replacement for the mark portion of the paragraph:

> An ordinary load or store cannot transfer a heap cell into a private
> resource with no completeness mark: the step earns none, while a
> nonempty private heap requires one. A precondition emp permits such an
> unmarked resource. For two threads whose private memories are initially
> empty, each active processor can instead be supplied with barᵢ without
> changing the machine state. This supplies the missing mark; allocation
> and preservation of J must still be justified by the atomic premise.

Retain the existing citations, and optionally use the general
`buffered_unmarked_ordinary_no_heap` alongside the concrete invalid-load
instance. `buffered_marked_cell_withdrawal` is the checked successor
construction for an already allocated one-cell pool; it is not itself a
universally valid load specification. The marked barrier here describes an
empty private history, not a drained whole-machine buffer.

The claimed machine result (`dekker.tex:75–82`) is otherwise correct. Its
checked start is the two-cell zero heap, empty buffers, a free lock, and
exactly processors 1 and 2 active; its initial registers are arbitrary.
Adding “with the lock free” to the initial-state sentence would make it
literal. The general calculus theorems, in contrast, are for arbitrary
processor domains. No termination, fairness or full-algorithm result is
claimed by `dekker_fenced_all_runs`.

## Source and citation checks

The historical claims also match the dissertation's LaTeX source at blob
`ac4c24370dc22b3ca0892294206c2c6ac138d993`, re-fetched and verified during
this check. Its motivating example and fence discussion support the opening
([source lines 231–264](https://github.com/iwehrman/Weak-Memory-Local-Reasoning/blob/8d8c455da5fb5fa8801e256948d94e305bebb70a/dissertation.tex#L231-L264)).
The two basic daring-rule displays, the difficulty/unfinished status, and
the concern about invariants accommodating pending writes support their
attribution in the paper
([source lines 2171–2178](https://github.com/iwehrman/Weak-Memory-Local-Reasoning/blob/8d8c455da5fb5fa8801e256948d94e305bebb70a/dissertation.tex#L2171-L2178)).

All twelve explicit Rocq names in the reviewed text resolve uniquely at the
pinned proof artifact:

| Cited name | Source |
| --- | --- |
| `daring_load_extension_breaks_adequacy` | `theories/DaringCounterexamples.v:117` |
| `daring_load_honest_counterexample` | `theories/DaringCounterexamples.v:186` |
| `daring_store_honest_counterexample` | `theories/DaringCounterexamples.v:287` |
| `buffered_calculus_sound` | `theories/BufferedPoolCalculus.v:51` |
| `buffered_derivation_adequacy` | `theories/BufferedPoolCalculus.v:73` |
| `buffered_dekker_derived` | `theories/BufferedDekkerDerivation.v:21` |
| `dekker_fenced_all_runs` | `theories/BufferedDekkerAdequacy.v:75` |
| `dekker_unfenced_zero_zero` | `theories/BufferedDekkerAdequacy.v:100` |
| `buffered_emp_load_withdrawal_premise_invalid` | `theories/BufferedPoolLimitations.v:67` |
| `buffered_barrier_parallel_initial_adequacy` | `theories/BufferedPoolBarriers.v:33` |
| `buffered_marked_cell_withdrawal` | `theories/BufferedPoolBarriers.v:94` |
| `buffered_dekker_store0_premise` | `theories/BufferedDekkerProof.v:33` |

There are no theory/build changes between `521acd6` and the checked paper
draft. A focused Rocq compilation re-evaluated the counts and six certificates,
and `Print Assumptions` for all twelve cited declarations returned `Closed
under the global context`. The queries introduced no new lemmas or axioms
and were run outside the repository. I did not repeat the full clean build
for this paper-only check; the reviewer's accepted 1,483-declaration build
and proof pin remain unchanged. This check concerns the text and its sources,
not a new PDF layout review.
