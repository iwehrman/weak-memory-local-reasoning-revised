# Reviewer response: the buffered-pool candidate is approved for proof

Responds to `review/lead-daring-2.md`,
`review/buffered-pool-candidate-statement.md` and
`theories/BufferedPoolCandidate.v` at `9e1ab1c`.

## Verified

- A clean clone of `9e1ab1c` passes `make check`: 1,341 closed
  declarations, exit 0, no axioms. `DaringExtension.v` and
  `DaringCounterexamples.v` are in `_CoqProject`.
- `python3 scripts/search_buffered_pool.py` reproduces
  `review/buffered-pool-search-results.jsonl` byte for byte.
- I read `BufferedPoolCandidate.v` in full. The definitions say what the
  statement file says.

Stage 1 is closed. I am updating the paper to cite the three theorems.

## The two design choices: both accepted

**DJ throughout.** Accepted. Your `J = d ↣ 0 ∨ e ↣ 0` example is the same
obstruction that confines release to disjoint mode in the active logic,
and here every atomic step can transfer. Overlap mode existed to support
the temporal frame rule, which this judgment does not have, so nothing is
lost.

**The pool is read at full marks, and that has content.** Accepted, and
thank you for not papering over the failed re-marking. My reading of why
it is sound, for you to confirm or refute in the proof: at full marks a
drained history `e ↣ u ; e ⇝_i v` says no more than `e ↣ v`, so a thread
that deposits a drained cell cannot plant a false fact in the pool, and a
thread that withdraws one reads it under its own marks and its own budget.
The only direction information could leak is pool to thread, and the
budget closes it.

## One limitation to record

A resource with no marks cannot own a heap cell, and a load or store earns
no mark. So a thread whose precondition is `emp` at empty marks can never
withdraw a cell from the pool with the atomic rule. Dekker is unaffected
because each thread starts with tokens. Please state this in the eventual
report with the smallest example, so the paper can say plainly what the
rule cannot do. I am not asking for a fix.

## Proof order

Go ahead with the general proof. I would like the shortest path to the
Dekker theorem first, and the rest of the rule set after.

1. **Foundations**: the full-pool flush lemma, three-way flush
   attribution, joint pool/local cancellation, primitive extension to a
   disjoint frame.
2. **Soundness of the rules Dekker uses**: the atomic rule, SEQ, CONS and
   CONC. Then adequacy.
3. **Dekker**: the six premises, the derivation of the composed program,
   and a machine-level theorem with no candidate definitions in its
   statement:

   - from a heap with `f0 = f1 = 0` and empty buffers, no execution of the
     fenced program aborts, and no terminating execution ends with
     `r0 = 0` and `r1 = 0`;
   - the unfenced program has a terminating execution with
     `r0 = r1 = 0`.

   The ghost cells are erased as in `message_passing_all_runs`.
4. **The remaining rules**: SKIP, DISJ, CHOICE, LOOP, EX, FRAME-SP and the
   private axioms. If any of these fails, report it and keep going; it
   does not block step 3.

Check in after step 3, or earlier if a statement has to change.

## Things I expect the proof to stress

These passed the bounded search. I list them because they are where I
would look first if a proof gets stuck.

- **CONC with a sibling that changes the pool.** From one thread's view
  the sibling's step replaces both the pool and the frame. The definition
  handles this by quantifying environments afresh at each index. The
  footprint bound, with frames disjoint, is what stops the sibling's
  repartition from reaching this thread's cells.
- **A waiting fence.** The premise gives no obligation for a disabled
  fence. The lifted step must use the fact that an enabled framed fence is
  also enabled frameless, and never the converse.
- **Stores and buffer order.** The new write is last on the actor's whole
  buffer. The frameless post-split has to extend to every interleaving
  that the frame's own writes by that actor allow.
- **Stack variables.** The atomic premise checks `J` at the successor
  stack, so the rule itself needs no side condition on `fv(J)`. CONC does,
  and your statement has it.

## Scope reminders

- New files only. `owned_safe`, `owned_derivation` and existing statements
  stay as they are.
- Do not edit `paper/`.
- Keep `BufferedPoolCandidate.v` as the statement of record. If a
  definition must change, change it there and say so in the report.
- The withdrawn `DaringCandidate.v` can be deleted once the new
  development is in the main build; the search results in `review/` are
  record enough.
