# Completed offline queue: consolidated reviewer handoff

The requested queue is complete. The lead continued under Ian's explicit
instruction to batch independent work while the reviewer was unavailable.
No paper text, reviewer guidance or queue document was edited. These results
are checked locally but await independent review; prior accepted checkpoints
are not being relabelled as approval of these batches.

## Results in queue order

| Batch | Commit / source | Result |
| --- | --- | --- |
| 4B assertion system | `b196efd`; [report](paper-assertion-soundness.md) | All 47 assertion constructors sound, with derived cell rules and CONS/UNLOCK interfaces |
| 4C selected-branch container | `cd1121d`; [report](paper-container-assertions.md) | Every assertion obligation reconstructed as a proof tree |
| Priority 1 message passing | `b012e32`; [report](paper-message-passing.md) | Original program derived; proof tokens erased from actual one-cell executions; original points-to conclusion and both outcome traces |
| Priority 2A named locks | `853f731`; [report](paper-named-locks.md) | Arbitrary finite invariant families; retrying acquire, release, and nested two-lock witness |
| Priority 2B mailbox | `85a0e14`; [report](paper-mailbox.md) | Arbitrary finite message length, including zero; buffered producer without a fence, retrying consumer and private reads; 95-step complete trace and 41-step failed iteration |
| Restricted SHARE | Current batch; [report](paper-restricted-share.md) | General semantic theorem in DJ **and** OV, with precisely the approved lock-free pre/postconditions |

Each report links its statements, principal declarations, scope limitations
and bounded searches. The [writer's index](../notes/paper-theorem-index.md)
provides a consolidated source map. The design statements for message
passing, named locks, buffered interfaces and SHARE were recorded before
implementation; they are not independent approvals.

## Recommended reading order

1. **SHARE statements and proof route.** `owned_share_valid` and
   `owned_share_overlap_valid` are the last general rules. OV does not fail:
   the proof removes hidden heap entries only from the source environment's
   frame and restores the exact target frame. See the explicit stale-frame
   witnesses. No DJ-to-OV strengthening is claimed.
2. **Named-lock interfaces.** Check family membership, scratch freshness,
   and the explicit assertion proof `I_l * I_l ⊢ false` used for release.
   The retained-resource acquire and buffered-release interfaces are derived
   for the same implementations, without a new fence or rule.
3. **Mailbox statement and non-vacuity.** The proof and actual-initial-memory
   adequacy are list-parametric; the concrete trace has two message cells.
   The foreign write stays pending in the witness trace, not necessarily in
   every run. Private loads reuse one destination register.
4. **Message-passing conclusion.** Inspect `message_passing_all_runs` and
   `message_passing_points_to`: the result is about actual one-cell memories,
   not a memory left padded with proof-token cells. The printed derivation
   itself is not claimed unchanged.
5. **4B/4C**, if not already inspected: assertion soundness, derived cell
   rules, and the client proof trees which the larger examples reuse.

## Validation and unchanged foundations

`make check` passes both at the completed working tree and in a fresh source
export with no prior compiled artifacts: all **1,284 audited declarations are
closed under the global context**, and the independent `rocq check` completes
successfully in both builds. All 193 theory sources, `_CoqProject` and
`Makefile` in the clean build match the completed working tree byte for byte. No axioms or admitted proofs were added.
The development has 193 theory files and 30,052 physical lines listed in
`_CoqProject`, including the historical experiments and audit.

The active safety definition, machine, assertion interpretation and invariant
fragment are unchanged. The program judgment still has 21 constructors and
the assertion proof basis 47. The standing hypotheses remain a fragment
invariant and two distinct active processors, without finiteness.

SHARE's `assertion_lock_free` is the approved property of assertions.
`share_resource_decomposition` is only a resource witness inside its
induction. Neither is a new command-safety or command-validity predicate.
The rule needs no extra invariant-variable premise, even at the semantic
level: safety in the alternate free-pool environment supplies preservation.

## Decisions for independent review

- Accept or challenge the theorem statements and operational scope of these
  batches before integrating them into the paper.
- Correct the provisional expectation that restricted SHARE fails in OV.
  The counterexamples to unrestricted SHARE and syntactic lock-freeness
  remain valid and should stay in the account.
- Decide whether the paper presents restricted SHARE as a semantic theorem
  or whether an additional program-calculus constructor is useful. The lead
  has not added one; the existing derivation corollaries already support the
  stated top-level use.

There is no failed rule or new semantic restriction waiting for a repair
decision. The next work is independent review and paper integration, not
another already-requested proof batch. The old retrying-container module
still has some semantic entailment proofs; the selected-branch container and
the new retrying mailbox use assertion proof trees throughout. Assertion
completeness/automation, expression-valued lock schemas, recursive predicates,
DJ-to-OV SHARE strengthening and Chapter 5 remain outside this completed queue.
