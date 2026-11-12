# Reviewer guidance after the audit statement

Responds to `16f5f85` (the 4A audit statement and the parked Section 4.1
design). The queue in `work-queue-for-paper.md` is current as of `382ac5c`.

## The audit statement: approved

Proceed with part 4A as stated in `paper-algebra-audit-statement.md`. The
inventory (E1 to E12, T1 to T9, each over the three conjunctions), the
distinctions that can change a law's truth, and the search-then-prove
procedure are what was asked for. Three additions:

1. **T7 and T8.** You plan to test both the literal side condition
   `P • Q ⊨ P ○ Q` and the uniform one. Also report which reading the
   dissertation's prose intends, since the paper must say whether a failure
   is of the printed law or of one transcription of it.
2. **Unit laws with wands.** `container_spatial_emp_elim` has a wand-free
   premise. If E1 or E2 fails for an assertion containing a wand, that is a
   headline finding: `emp` as a two-sided unit is one of the properties the
   project set out to preserve. Report it as soon as it is known, in either
   direction, without waiting for the full table.
3. **Result format.** For each instance give one of: proved, refuted,
   holds in a stated modified form. Give the theorem name, and for a
   refutation the smallest countermodel in words as well as in Rocq. The
   table goes into the paper nearly verbatim.

No rule set for 4B should be chosen until the 4A table is reported.

## One new item to run alongside the audit

Priority 5 item 1 (reading your own buffered write) was added at `382ac5c`
and should be settled early, because its answer may add a load rule that the
later derivations will want. It asks first whether
`{(∃u. C(x,u)) ; W_i(x,v)} r := [x]_i {... ∧ r = v}` is derivable today.
Check in with the answer before adding any constructor.

Priority 5 items 2 to 4 can wait and be reported together.

## The parked Section 4.1 design

Your correction to my queue entry is right and I accept it. The original
proof is not rejected at the sender's `s := 1`, which is proved under `emp`
inside ATOMIC's premise. It is rejected at the composition: ATOMIC is not
available, the parallel rule's invariant-variable conditions fail for `s`
and `x`, and SHARE and AUX are absent. Keep the distinction you drew
between "does not port" and "is false"; the paper will use that wording.

On the repaired design, when you return to it:

- **The token invariant and the two thread specifications** look right.
  Exclusion of branches by a spatially retained token is the same mechanism
  the retrying container used for its unreachable branch.
- **The `x = 0` outcome.** Exact preservation of the memory domain along
  executions is the right lemma, and it is a property of the machine, not of
  the calculus. Prove it once, generally, since priority 2 may need it too.
- **Erasing the tokens.** The extension and erasure argument is acceptable
  and I prefer it to making this example depend on SHARE. State the final
  theorem for the original program and the original one-cell heap, as you
  propose. If the erasure argument generalizes cheaply to "cells the
  command never mentions", state it that way; if not, the specific version
  is enough.
- **The restricted SHARE** (priority 3 item 1) stays an independent item.
  If it is proved, note in the report whether it would have given the
  original triple directly, but do not restructure priority 1 around it.

## Check-ins, unchanged

After the 4A table; after the 4B rule statements and before their soundness
proof; after 4C. For priority 5 item 1, as above. Immediately for anything
that contradicts a current checked claim or would need a change to the
assertion grammar or interpretation.
