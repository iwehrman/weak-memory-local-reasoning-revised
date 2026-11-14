# Lead response: basic daring rules and the lock-free candidate

Stage 1 passes: all three requested negative results are proved in Rocq.
Stage 2 does **not** pass as proposed. Its definitions are stated and its
bounded searches find failures in invariant access, store admissibility,
and the ghost-token argument. No general Stage 2 proof or derivation
system has been built.

This follows the revised request aimed at fenced Dekker, committed as
`0a3e724`. The artifact to review is **`94776a492d38c4aded86e8c87591c79431b873e7`**.
Only new files were added. The active `owned_safe`, `owned_derivation`,
existing theorems, `_CoqProject`, baseline `Audit.v`, and `paper/` are
unchanged.

## Stage 1: checked results

All results below are in `theories/DaringCounterexamples.v`, with the
extension in `theories/DaringExtension.v`.

### N1: adding DARING-LOAD breaks adequacy

`daring_load_extension` has the existing 21 rule schemas plus
DARING-LOAD. Its invariant is an index, allowing the new constructor's
premise to use `emp`. `daring_load_embeds_owned` embeds every existing
proof tree without strengthening or weakening any old rule.

- `daring_load_extended_bad_derivation mode` derives
  `{emp} acquire(1); store_1(d,5); load_1(x,d) {x=0}` under `J = d ↣ 0`.
- `daring_load_extended_trace` gives the complete **five-step** execution
  ending at `halt` with `x=5`. There is no flush: the load forwards the
  pending store. The lock remains held, which adequacy permits.
- `daring_load_extension_breaks_adequacy mode` packages the derivation,
  fragment invariant, two processors, inhabited precondition, nonempty
  initial free pool, initial spatial decomposition, terminating trace,
  final register value, and the impossibility of *any* local resource
  satisfying the promised postcondition.

The intermediate assertion is `lock_1 * ((d ↣ 0) ; d ⇝_1 5)`. It is
obtained by the existing acquisition and framed store rules, dropping the
unneeded barrier assertion by consequence. `J * P` is false because
both spatial operands own address d. The load premise under `emp` is an
ordinary derivation framed by false, followed by consequence. Thus the
reviewer's proposed argument works, including its false-premise step.

### N2: an honest LOAD premise still has an invalid conclusion

`daring_load_honest_counterexample mode` gives all of:

- an ordinary proof tree under `emp` of
  `{(d ↣ 0) * emp} load_1(x,d) {(d ↣ 0) * (x=0)}`;
- its semantic validity and an inhabited precondition;
- invalidity under J of `{emp} load_1(x,d) {x=0}`.

It holds for **both modes**. The premise has exactly the `J * P` and
`J * Q` shapes, not just the equivalent informal cell-and-pure version.
The refuting environment has empty pool, empty local resource, and a
frame holding processor 1's token, heap `d=0`, and buffered `d:=5` on
processor 1. The load is enabled and returns 5. Every possible successor
fails the pure postcondition.

The environment and step are exposed as
`daring_load_held_environment` and `daring_load_held_step`.

### N3: an honest STORE premise fails even with the lock free

`daring_store_honest_counterexample mode` uses distinct addresses d and e:

    J = (d ↣ 0) ∨ (e ↣ 0)
    P = e ↣ 0
    Q = (d ↣ 0) ; d ⇝_1 5.

Under the empty invariant, `{J * P} store_1(d,5) {J * Q}` has an ordinary
proof tree and is valid. The precondition is inhabited. Its spatial
separation forces J to choose d initially; after the store, e supplies J
and the thread retains d's history as Q.

But `{P} store_1(d,5) {Q}` under J is invalid in **both modes**. Start with
J's d cell in the free pool, e local, and the external frame empty. The
machine can enqueue `d:=5`. An ordinary owned step keeps the pool fixed,
so the pending write must go in the local residual. That violates the
pool/local spatial separation. `daring_store_no_successor` rules out
**every** successor, independently of the requested postcondition.

This is a two-cell honest refutation; I do not claim a proved minimality
result. The naive single-cell store-to-pool example needs care: with a
fixed cell invariant it does not itself supply an honest restoring
premise. The disjunction permits the necessary ownership swap.

## Stage 2: definition and what was tested

The statement fixed before the search is
`review/daring-lock-free-candidate.md`. The compiled, standalone
`theories/DaringCandidate.v` defines the candidate environment, updates,
safety, validity, rule propositions and adequacy proposition.
**These propositions have no soundness proofs.** They do not extend the
active calculus.

Choices that the request left open are explicit:

- pool-before-frame/local uses memory-level temporal composition;
- the whole memory is lock free, with no lock/unlock commands;
- program steps fix the exact frame, retain the existing footprint and
  mark budgets, and may re-split the pool except at a store;
- physical flushes update an existing pool cell and flush exactly one
  component, leaving the other fixed;
- full local-future closure is retained, and a separate physical-flush
  clause is added because the pool may now change;
- invariant access uses overlap-mode validity under `emp` as its premise;
- store stability quantifies over every stack and full model of J,
  requires the target address to exist, and preserves J when its heap
  value is updated;
- no pending-write admissibility, processor-ownership or ghost-address
  condition has been silently added.

The search is `scripts/search_daring_rules.py`; its reproducible output
is `review/daring-search-results.jsonl`. It reuses the repository's
ordered composition and generalized-future implementation. The search
is finite evidence, not a Rocq proof of a Stage 2 claim.

## Stage 2 failures

### Invariant access does not account for the external frame

A direct load witness uses pool `d=0`, local `emp`, and external frame
`[d:=1]_1`. The pool-first environment permits this state. Processor 1's
load returns 1, while the private premise for `{J ; emp} load {J ; x=0}`
reads 0. This witness also points to the need to constrain which writes
an external frame may contain.

There is a second access obstruction that does **not** rely on an
invariant-changing pending write. Use `J = d ↣ 0`, a local empty resource
already marked for both processors, and external frame `[d:=0]_2`.
Take Q to be `d ↣ 0`. On a private cell resource, both `J ; emp` and
`J ; J` hold; a load, assignment to an unrelated register, true assume,
true assert, or fence preserves that resource. In the candidate's shared
conclusion, every local resource satisfying Q contains a heap cell at d.
That is incompatible with the fixed frame's pending write at d. The
search exhausts the residual decompositions for each of these five
steps and finds none satisfying Q. The pending value is 0, so requiring
this write to preserve J does not resolve the obstruction.

Skip presents an additional, simpler problem: it is already terminal.
The same cell-copy premise cannot make a bare empty local resource
satisfy Q. There is no machine step at which to transfer ownership.
Ordinary `{P} skip {P}` should be kept separate from invariant access.

### Store stability is insufficient

Take `J = (d ↣ 0) ∨ (d ↣ 1)`, `P = emp`, and a frame with `[d:=1]_2`.
Every model of J has d, and setting d to 1 preserves J. Processor 1 can
nonetheless issue another `d:=1`. With the frame fixed and the pool
buffer-free, this second write has to be local. The compatibility
relation forbids pending writes to the same address in different
processors **across these two components**. No successor exists.

Compatibility is a restriction on admissible decompositions, not a
permission system preventing the machine from issuing such stores. It
also does not impose a global single-writer condition inside one raw
resource. A writer-ownership discipline is still missing.

### External flushes need an admissibility condition

With `J = d ↣ 0`, a frame may currently contain `[d:=1]_1`. Its flush
changes the pool to `d=1`, violating J. Consequently even ordinary SKIP
fails the candidate's physical-flush obligation in this environment.
The per-store stability premise governs the thread's own issuance; it
does not constrain an arbitrary quantified frame. This is an actual
failure of the stated SKIP proposition, not an argument against the old
`owned_skip_valid`.

### The Dekker token-exclusion argument fails with temporal overlap

The proposed ghost invariant has **15 heap models**. It contains both
flag addresses in every model, and all **30** checks of setting either
flag to 1 preserve it. Those parts of the sketch pass.

But all 15 models can coexist temporally with thread 0's `t0 * p0` and
its pending flag write. Holding `t0` does not rule out a pool that also
has `t0`. In **seven** models, q0 is absent from the entire pool/private
footprint after the write drains. The fence postcondition `q0 * p0`
cannot then be obtained by any permitted re-split.

For example, let the pool hold `w, t0, f0=1, q1, f1=0`, and let the
thread hold `t0, p0` followed by `f0:=1`. This is a permitted temporal
overlap. After flushing, there is still no q0 anywhere. The fence cannot
create that address. This refutes a claimed entailment in the proposed
derivation, independently of any hoped-for proof of the access rule.

## What survived bounded checking

| Check | Actual bound / count | Result |
|---|---|---|
| Buffer cancellation | 2 processors, 2 addresses, values 0/1, each component buffer length 0–2 on one processor, 5 pools; 8,650 composed worlds | No failure |
| Physical flush attribution | 8,640 flushes in that family; 1,560 duplicate-head cases | No failure; duplicates attributed to the frame |
| Additional heap/foreign-processor attribution | 396 worlds and 396 enabled flushes from the focused heap/pending-atom family | No failure |
| Spatial-frame/parallel reconstruction | 3,144 environments, 10,100 non-store successors, 4,198 store successors; 1,644 successors with a pending frame write to a pool address | Sufficient reconstruction lemmas fail |
| Structural validity implications | 26 initial resources, 8 frames, 9 stacks, empty and Boolean-cell invariants, indices 2 and 4; 28 inhabited base triples | 396 implications tested; no failure in this limited fragment |
| Ghost invariant | 15 heap models, 30 stability checks | Stability passes; proposed token exclusion fails |
| Fenced physical program | Exhaustive finite model, 31 reachable states | No abort; final read pairs 01, 10, 11 |
| Unfenced physical program | Exhaustive finite model, 34 reachable states | 00 reachable, as well as 01, 10, 11 |

The structural counts are: SEQ 60, CONS 56, DISJ 28, CHOICE 52, LOOP 24,
EX 28, FRAME-SP 52, CONC 96. Eight additional uninhabited framed/parallel
preconditions were skipped, not credited as passing tests. These tests
use skip, true assume, assignment, and fence; assertions use emp, true,
one register equality and a cell, with the displayed connectives. The
CONC subset uses register-preserving commands. It is deliberately much
smaller than arbitrary commands or assertions, and EX uses a finite
value domain. No general structural rule is established by these counts.

A reconstruction failure is **not by itself a refutation of FRAME-SP or
CONC validity**: the selected local successor might not belong to a
universally valid specification. The smallest found obligation failure
has a retained cell d overlapping the pool, an empty acting resource,
and a store that produces a local pending write at d. The retained cell
and new pending write cannot be reassembled spatially. Thus the old
frame-proof route cannot be copied without another argument or a
restriction on shared-cell overlaps.

The physical program enumeration is a Python finite-state check, not
the requested eventual Rocq mutual-exclusion theorem. Its unfenced trace
is `store 0; load 0; store 1; load 1`, with both writes pending. Processor
indices 0/1 in the script correspond to Rocq processors 1/2.

## Suggested direction for the next review

I agree with the request's reason for separating this development: a
pool cell cannot remain spatially owned by the old invariant while a
private resource holds a buffered write to that address. A different
shared-access model is needed for this proof route.

I would not discard temporal pool composition solely on these results.
Buffer cancellation and flush attribution still look viable. The
missing structure concerns permissions and what ownership may overlap:

1. Make external pending writes admissible only when their possible
   flushes preserve the invariant. Per-store stability alone is not an
   environment guarantee.
2. Give shared flags an explicit writer discipline, covering same-thread
   histories in frames as well as foreign writers. The invariant-access
   premise must account for those permitted frames; private `J ; P`
   validity alone is too weak an interface.
3. Preserve spatial exclusivity for ghost/private addresses. One possible
   design distinguishes the shared flag addresses from ghost addresses:
   allow temporal overlap at the former, while requiring a spatial split
   at the latter. This would restore the token-exclusion argument that
   the current all-temporal composition loses.
4. Retain ordinary SKIP, rather than treating it as a transfer step.
   Shared-cell extraction also needs a condition ensuring that pending
   frame writes cannot invalidate the resulting private ownership.

These are proposed changes, **not implemented repairs**, and they may
require more than a convenient side condition. I have not established
that this is the smallest or best design, nor that it admits the full
Dekker derivation. The useful next checkpoint is agreement on the
permission/overlap interface and another small search, before any general
safety or concurrency proof.

## Reproduction and audit

Because the request says new files only, `Makefile.daring` is a standalone
overlay. It runs the unchanged baseline check, then compiles the new
modules and kernel-checks `DaringAudit`:

```sh
make -f Makefile.daring check
python3 scripts/search_daring_rules.py
```

The baseline `make check` covers **1,316** audited declarations.
`DaringAudit.v` adds **25 proved declarations**, for **1,341 combined**.
The Stage 2 proposition definitions are not counted as proved rules.
The overlay check passes, and every new audited declaration is closed
under the global context, with no added axioms or admitted proofs.

A fresh local clone of `94776a492d38c4aded86e8c87591c79431b873e7`
completed the entire overlay build and both kernel checks successfully.
Its build printed exactly **1,341** closed declarations. Running the
search from that clone reproduced the committed JSONL output byte for
byte. The report itself is committed separately so it can name the exact
validated artifact.
