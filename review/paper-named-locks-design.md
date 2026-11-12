# Priority 2 design: named locks and a region mailbox

Priority 1 is complete at `b012e32`; its
[report](paper-message-passing.md) is ready for review. Ian has authorized
continuing without waiting for routine checkpoints. This states the next
target before implementation. A false proposed rule, a new semantic
restriction or a change to the assertion language/safety definition remains
a stop-and-report point.

## Part A: finite families of derived spinlocks

For a finite list of pairs `(l,I_l)`, define the assertion family by an
ordinary Rocq fold, with spatial unit `emp`:

```text
F(l,I) = (C(l,0) * I) ∨ C(l,1)
J     = spatial product of F(l,I_l)
```

Every `I_l` is in the approved invariant fragment. Lock flag addresses are
constant positive addresses. An inhabited concrete configuration will use
distinct flags disjoint from protected cells; the generic derivations need
not assume that every arbitrary family is inhabited.

For active actor `i`, flag `l` and scratch register `x`, the intended code is:

```text
attempt(l,i,x):
  acquire(i); x := [l]_i;
  if x=0 then ([l] := 1_i; release(i)) else release(i)

acquire_named(l,i,x):
  x := 1;
  while x=1 do attempt(l,i,x)

release_named(l,i):
  acquire(i); [l] := 0_i; release(i)
```

The two uses of `release(i)` return the **physical** global lock. The
derived lock remains logically held while its flag is 1. There is no new
machine lock instruction, assertion atom, held-lock ghost state or
validity predicate. Acquisition has a real retry branch; it does not
replace that branch with an assumed successful read.

The target derivations, at disjoint mode, are:

```text
J ⊢ {emp} acquire_named(l,i,x) {I_l}
J ⊢ {I_l} release_named(l,i) {emp}
```

Conditions are made explicit from the start:

- `x` is absent from the free variables of the family invariant. The
  acquire implementation modifies this scratch register; clients must
  respect the existing frame/parallel variable conditions.
- Release receives an **assertion derivation**
  `I_l * I_l ⊢ₐ false`. Its semantic content is the exclusivity condition
  anticipated in the queue. Requiring a proof certificate keeps every
  consequence/donation obligation inside the assertion system; it does
  not claim completeness for arbitrary semantically exclusive formulas.
  Acquisition does not need exclusivity.
- Soundness/adequacy use the existing standing hypotheses: fragment
  invariant and two distinct active processors. The derived rules do not
  introduce a new processor-count or finiteness hypothesis. The family of
  named locks is finite because its assertion is a finite fold.

The finite-family proof should expose the chosen component and regroup the
remaining components using assertion associativity/commutativity. The
physical acquire transfers the whole global pool temporarily; the named
operation restores all other components on release. When the chosen flag
is zero, acquisition retains `I_l` and returns flag 1; when it is one, the
failed attempt returns the entire pool and retries. On named release,
retained `I_l` excludes the zero-flag branch by the supplied exclusivity
proof; it is donated with the new zero flag.

Before general proofs, screen these acquisition/release assertions for one
and two named components, both actors, all mark sets, and pending/flushed
flag writes. This finite search does not replace the all-frame soundness
result. After the derivations, include a nonempty concrete two-lock
instance and successful/failed-attempt traces if the design survives.

## Part B: arbitrary-length mailbox client

Use a named lock whose protected invariant owns a mailbox flag and either
no message or a spatial product of `K` message cells. `K` and the list of
values are Rocq parameters, so no recursive assertion constructor or
allocation operation is required. The mailbox flag makes this invariant
exclusive even when `K=0`.

The producer starts with the message cells, fills them using ordinary
stores with no fence, acquires the named lock, and donates the message in
the full-mailbox branch. The consumer retries until full, withdraws the
message, releases the named lock, and reads the cells privately. The
intended final assertion records the producer's value vector and consumer
ownership. All generated flag/message addresses must be distinct; this is
an ordinary condition on the inhabited concrete client layout.

The capstone must include an unrelated third processor's pending write in
a checked trace. It should show the pending producer writes before the
physical acquisition drains them and the consumer's private accesses
after ownership transfer. There is no promise of fairness or termination;
the target remains partial correctness with explicit successful and retry
executions.

This is a design target, not a completed proof. Any semantic entailment
that cannot be reconstructed as an assertion derivation will be named,
and any genuinely stronger condition than those above will be reported
before extending the proof around it. Restricted SHARE remains the next
item after this client in the latest queue order.
