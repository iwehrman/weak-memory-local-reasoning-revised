# Request: check three new appendix sections and three small statements

**Draft to check:** the commit that adds this file (paper only). This is
separate from, and lower priority than, the rename in
`reviewer-request-rename-printed.md`. No new proof work is requested, and
please do not edit the paper.

Ian asked that the reader not need the Rocq files to see what the safety
predicate, the repaired definitions and the example programs actually are.
I transcribed the following by hand. Each is a place where a wrong
quantifier or a dropped condition would be easy to miss.

## 1. Appendix "The safety predicate in full" (`app:safety`)

Source: `OwnedSafety.v`, `GeneralizedFlushing.v`, `Separation.v`.

- **Resources.** I state `generalized_well_formed` as: well-formed memory,
  marks are active processors, heap empty if there are no marks.
- **Futures.** Two kinds of step, from `generalized_step`: add marks; or
  flush the oldest write of a processor `i` not blocked in the resource's
  own memory, with `Γ ∪ {i} ⊆ Γ'`. Is "not blocked in μ" the right reading
  of `flush_at active i m m'`, and does it also need `i` active?
- **Environments.** Four numbered conditions from `owned_environment` and
  `pool_status`. I dropped the two well-formedness fields. I describe
  `lock_free whole` as "no processor is blocked in μ0" and
  `lock_held active whole i` as "the processors blocked in μ0 are exactly
  those other than i". Check both against `LockRepresentation.v`, in
  particular whether "other than i" should be restricted to active
  processors.
- **Updates.** `action_transfer`, `owned_footprint`, `owned_mark_budget`.
  I use the same "blocks exactly the processors other than i" phrase for
  `lock_held` on the local resource, and "blocks none" for `lock_free`.
- **Safety.** The displayed recursion, including "if c has terminated"
  for `terminal command`, and the frame `ν_F` and stack handling in the
  successor environment.
- The closing remark: "Flushes by the machine are not program steps. They
  are accounted for by the quantification over futures of the local
  resource, and by the fresh choice of frame at each level."

## 2. Appendix "The repaired definitions" (`app:definitions`)

- **Buffer overriding.** Original (`buffer_overrides`): interleavings whose
  lookup agrees with the overriding of the two lookups. Repaired
  (`ordered_overrides`): a write to `ℓ` is taken from the later buffer only
  when no write to `ℓ` remains in the earlier one. I conclude "all of b's
  writes to an address precede all of b''s".
- **Temporal compatibility.** Original (`temporal_compatible`) versus
  `stable_compatible`: the same two conditions, for all active processors
  instead of jointly unblocked ones.
- **Implications.** I say the repaired reading requires the original
  condition "of every future of ν". Please check this against
  `future_satisfies`: is the quantification over futures of the current
  resource only, and is it applied at each implication (nested ones too)?
- The opening claim: "Each replacement is more restrictive than the
  original." True for overriding and compatibility; is it a fair statement
  for the implications?

## 3. Appendix "The programs of Section 8" (`app:examples`)

Sources: `OwnedRetryContainer.v`, `MessagePassingSyntax.v`,
`MessagePassingDerivation.v`, `NamedLockSyntax.v`, `NamedLockRules.v`,
`MailboxSyntax.v`, `MailboxDerivation.v`, `RegionRules.v`.

- **Retrying container:** `take` and `put` as while loops with a done
  register `g`, and the final specification with `R = y ⇝_2 17`.
- **Message passing:** the three specifications, with the postcondition
  `(r ↣ 0 ∧ x = 0) ∨ (d ↣ 2 ∧ x = 1)` for `mp_received r 2`.
- **Named locks:** `acquire_i(l, x)` and `release_i(l)`, the remark that
  the loop exits with `x = 0`, and `J` as the spatial product of
  `(l_k ↣ 0 * I_k) ∨ l_k ↣ 1`.
- **Mailbox:** lock flag `l`, mailbox flag `m`, message cells; the lock's
  invariant `m ↣ 0 ∨ (m ↣ 1 * A(v))`; producer and consumer programs; the
  three specifications with `A(0)` as the producer's precondition. I
  renamed registers (`z` for the producer's scratch, `y` for the consumer's
  flag register and scratch, `w` for the read target) and omitted processor
  annotations with a sentence saying so. In the source the consumer uses
  one register both as the acquire scratch and as the loaded flag; I kept
  that.

## 4. Three sentences in the main text

- `original.tex`: Conjecture 1 stated as "if a memory splits spatially
  into μ_b and μ_c and takes a step, then any spatiotemporal split of the
  result into a flushed descendant of μ_b and some μ'_c is again a spatial
  split". Table 1 has a shorter version of the same.
- `open.tex`: the daring rules "would let a thread load from or store to
  the invariant's cells without the lock, provided that the single
  command, specified with J in hand, gives J back".
- `appendix.tex`: Figures 4.5 and 4.6 described as "one of equivalences
  and one of entailments".

## Report

A short file in `review/` listing each discrepancy with its location and a
suggested replacement.
