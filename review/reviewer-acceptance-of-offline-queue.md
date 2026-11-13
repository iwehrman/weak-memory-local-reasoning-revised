# Reviewer response to the completed offline queue

Responds to `b196efd` through `99b4052` and `offline-queue-handoff.md`.
I read all six reports and the statements of the principal theorems, and
rebuilt `99b4052` from a clean clone. I did not read the proofs line by
line; the kernel did.

## Accepted

All six batches are accepted as stated.

- **Assertion system.** `assertion_derivation_sound` is proved for the 47
  approved constructors with none added, and I confirmed that no constructor
  mentions a semantic relation. The four cell rules are derived.
- **Container.** Every CONS and UNLOCK premise is a proof tree, including
  those inside the cell-access helpers. Zero semantic resource entailments
  remain.
- **Section 4.1.** `message_passing_all_runs` is about the original program
  and the original one-cell heap, with no token in the statement, and
  `message_passing_points_to` recovers the dissertation's all-processor
  conclusion. The distinction between "does not port" and "is false" is
  kept.
- **Named locks.** Acquire and release are derived for a finite family, with
  exclusivity required only at release and supplied as an assertion proof.
  The 59-step trace with both named flags set while the global lock is free
  answers the question I would have asked.
- **Mailbox.** Derived for an arbitrary list of cells, the empty list
  included, with no fence, and adequacy from an actual initial memory with a
  third processor's write pending.
- **Restricted SHARE.** Proved in both modes. My expectation that overlap
  mode would fail was wrong, and your explanation of why it differs from the
  donation and FRAME-STM failures is the right one: the target never gives
  the invariant's footprint to a new pool.

## Decisions

1. **SHARE stays a semantic theorem.** Do not add a constructor. The
   calculus is 21 rules, and the paper will state restricted SHARE next to
   adequacy.
2. **The retrying container may stay as it is.** The one-item container and
   the mailbox cover the assertion system. The paper will say that the
   retrying container still has semantic entailments.
3. **No further proof work is requested for the paper.** The queue is
   closed.

## Three small requests, none blocking

1. **Check the paper against the proofs.** `paper/` now has a full draft.
   Please read `paper/sections/*.tex` and report any technical claim that is
   stronger than, or different from, the theorem it cites, and any Rocq name
   that does not exist or has moved. Report in `review/`; do not edit the
   paper. This reverses our usual roles and is the most useful thing left.
2. **Final figures.** Confirm in one place the numbers the paper prints:
   theory files, physical lines, audited declarations, constructor counts,
   and the standing hypotheses of the top-level theorems.
3. **A fixed reference point.** When the paper check is done, say which
   commit the paper should cite.
