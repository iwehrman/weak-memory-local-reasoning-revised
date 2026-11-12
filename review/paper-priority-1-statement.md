# Priority 1: resumed statement after assertion reconstruction

The [deferred design](paper-priority-1-design.md) is resumed after 4C at
`cd1121d`. Its token invariant, thread specifications and execution
extension/erasure route were accepted in
[the review after the audit statement](reviewer-guidance-after-audit-statement.md).
Ian has authorized continuing through the queue while the reviewer is
offline, stopping when a substantive decision needs review.

The target remains the dissertation's original message-passing program,
with no auxiliary assignment or token accesses. Register 1 holds the data
address and register 0 receives the load. Processors 1 and 2 represent the
printed 0 and 1. Two ordinary, untouched token cells are used in the
derivation and removed from the final execution theorem.

```text
T = C(t,0), U = C(r,0)
J = C(d,0) ∨ ((C(d,1) * T) ∨ (T * U))

sender   = acquire(1); [d] := 1₁; release(1)
receiver = acquire(2); x := [d]₂; release(2);
           if x=1 then ([d] := 2₂; fence₂) else skip

J ⊢ᴰᴶ {T} sender {emp}
J ⊢ᴰᴶ {U} receiver {(U ∧ x=0) ∨ (C(d,2) ∧ x=1)}
```

The receiver target drops its unnecessary initial `x=0` requirement:
it overwrites `x` before testing it. Consequence recovers the originally
proposed precondition if needed. Tokens have constant positive addresses;
the data address remains the read-only expression `EVar 1`. Fresh token
addresses will be chosen when proving the original-heap result.

All program assertion obligations must be assertion derivations. The
completed basis already supplies cell exclusion, history completion,
spatial rearrangement, pure guards and barrier distribution. Additional
reusable proof trees may be derived without adding constructors. No
assertion-language, interpretation, safety or program-rule change is planned.

The final theorem must cover the original one-cell heap: every finite
execution is non-aborting, and every terminal execution has `x=0` or `x=1`,
data value `x+1`, empty buffers and a free lock. An assertion corollary
should recover the original all-processor points-to at full completeness.
The extra tokens must not remain hypotheses of that theorem.

The general exact-domain-preservation theorem requested in the old design
is now proved in `ExecutionDomain.v`. The remaining operational work is
terminal-state extraction and extension/erasure of untouched cells. The
original derivation's rejected steps remain as classified in the deferred
design; no new unsoundness claim about its specific triple is made.

Before the general proofs, screen the token branch exclusions, donation
entailments, drained-store completion and terminal pool cases over two
processors, three addresses, all mark subsets and pending/flushed writes.
Then prove the derivations and operational theorem, and exhibit complete
traces for both load outcomes, including a pending private store in the
`x=1` trace. This statement records targets, not completed results.
