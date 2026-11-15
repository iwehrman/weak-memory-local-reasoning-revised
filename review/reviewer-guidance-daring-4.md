# Reviewer response: the Dekker checkpoint is accepted

Responds to `review/lead-daring-3.md` at `3ee5b3b` (proofs at `88106e8`).

## Verified

- A clean clone of `3ee5b3b` passes `make check` (1,341) and
  `make -f Makefile.buffered check` (1,449 closed declarations, exit 0, no
  axioms reported).
- No `Admitted`, `Axiom` or `Parameter` in the added files.
- I read the statements of `buffered_atomic_valid`,
  `buffered_parallel_valid`, `buffered_valid_adequacy`,
  `buffered_dekker_valid`, `buffered_dekker_post_excludes_zero_zero`,
  `dekker_fenced_all_runs`, `dekker_unfenced_zero_zero`,
  `dekker_fenced_terminates`, `buffered_full_mark_drained_history` and the
  limitation theorems. Each says what the report says.
- `dekker_fenced` is `store_buffering` with a fence after each store, on
  the same `initial_memory`, and its statement mentions no candidate
  definition. That is the theorem I asked for.

Accepted, with no changes requested to what is proved. The rules are
direct inhabitants of the propositions approved before the proof, and
nothing had to be weakened. Thank you also for proving the limitation and
the drained-history equivalence instead of only describing them.

## What the paper will and will not say

So that we agree on the claim before I write it:

- A separate judgment for lock-free commands, with disjoint frames and an
  invariant that may own buffered writes, has a sound rule for atomic
  access to the invariant at a single primitive, together with SKIP, SEQ,
  CONS, FRAME-SP and CONC, and is adequate for the machine.
- With it, the fenced store-buffering test is proved never to end with
  both registers zero, and the unfenced one can.
- It is a restricted replacement for the basic daring rules. The original
  rules stay refuted.
- Not claimed: the full retrying Dekker algorithm, a combination with the
  lock calculus, an inductive derivation system, or the remaining rules
  until step 4 is done.

Tell me if any of that overstates the result.

## Next

1. **Integrate into the main build.** Add the new files to `_CoqProject`
   and their audited declarations to `Audit.v`, so `make check` covers
   them and the paper can cite one commit and one count. Delete the
   withdrawn `DaringCandidate.v`, `DaringAudit.v` and `Makefile.daring`;
   `Makefile.buffered` can go once the main build includes its files.
   Keep `BufferedPoolCandidate.v`: its propositions are now the rule
   statements.
2. **Step 4**: DISJ, CHOICE, LOOP, EX, and the private load, store, fence,
   assignment, assume and assert rules. Report any that fail.
3. **A derivation system.** Once step 4 is in, package the proved rules as
   an inductive `buffered_derivation` with a soundness theorem into
   `buffered_valid`, as `owned_derivation` does, and restate the Dekker
   proof as a derivation. The atomic rule's premise stays semantic. This
   is what lets the paper say "derived in the calculus" in the same sense
   as the other examples.
4. **Update `notes/paper-theorem-index.md`** with the new entry points and
   remove the line saying fenced Dekker lacks a shared-access rule.

One question, no work requested yet: is there an obstacle you can already
see to embedding this judgment in the lock calculus, so that a lock-free
block could run inside a program that also takes the lock? A paragraph of
opinion is enough. I want to know whether to describe that as open or as
blocked.

Check in after items 1 to 4.

## Addendum: the withdrawal limitation

Ian asked how the limitation proved in `BufferedPoolLimitations.v` could be
lifted. Two candidates, in order. Add these after items 1 to 4; they do
not block them.

5. **Start the thread with a barrier.** The limitation is about a thread
   with no mark, and `emp` is just the usual way to have none. Test
   whether a precondition `bar_i` is enough:
   - the atomic premise `{bar_1} r := [x]_1 {bar_1 * x ↣ 0}` (or the
     nearest true form) with `J = emp ∨ x ↣ 0`, the instance that fails
     for `emp`;
   - adequacy from an initial state with empty buffers, where each thread
     is given its own barrier at no cost;
   - CONC with `bar_1 * bar_2` split between two threads.

   If all three hold, the limitation becomes a remark about how to write
   preconditions, and no rule changes. Small theorems are enough.

6. **Only if 5 fails: let a withdrawal earn a mark.** Loosen
   `buffered_mark_budget` so that a thread receiving a heap cell from the
   pool may gain a mark for a processor on which its private resource has
   no pending write. Statement and bounded search first, against FRAME-SP
   and CONC reconstruction in particular. No general proof without a
   check-in; this would reopen the soundness proofs.
