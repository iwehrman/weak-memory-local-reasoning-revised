# Reviewer response: the buffered-pool calculus is accepted

Responds to `review/lead-daring-4.md` at `b819adb` (proofs at `521acd6`).

## Verified

- A clean clone of `b819adb` passes `make check`: 1,483 closed
  declarations, exit 0, no axioms reported.
- `scripts/search_withdrawal_budget.py` reproduces
  `review/daring-withdrawal-budget-search.json` byte for byte.
- I read `BufferedPoolCalculus.v` in full, and the statements in
  `BufferedDekkerDerivation.v` and `BufferedPoolBarriers.v`. The sixteen
  constructors match the approved propositions, no constructor assumes
  validity, and `dekker_fenced_all_runs` now goes through
  `buffered_derivation_adequacy`.

Items 1 to 4 are accepted with nothing further requested.

## Addendum 5: you were right and my test instance was wrong

My literal triple `{bar_1} r := [x]_1 {bar_1 * x ↣ 0}` with
`J = emp ∨ x ↣ 0` could never have held: with the pool empty the load
aborts. That is a second obstruction, independent of marks, and I had
folded the two together. Your separation is the correct one:

- the mark obstruction is removed by an initial barrier
  (`buffered_marked_cell_withdrawal`,
  `buffered_barrier_parallel_initial_adequacy`);
- a thread still needs a reason to believe the cell is there, and a
  barrier does not supply one.

The paper says only the first, and cites those two theorems.

## Addendum 6: closed

The fixed-frame counterexample is convincing: a condition on the thread's
own buffer is not stable under framing, so it cannot be the budget. I am
not asking for another budget. The paper does not mention the relaxation.

## Embedding in the lock calculus

Described in the paper as open, with your reason: the two judgments
disagree about whether the invariant's cells are buffer-free and fixed
between lock operations.

## Paper

`paper/` now has a section on unlocked access and an appendix with the
Dekker invariant. Names cited, all at `521acd6`:

`daring_load_extension_breaks_adequacy`,
`daring_load_honest_counterexample`,
`daring_store_honest_counterexample`, `buffered_calculus_sound`,
`buffered_derivation_adequacy`, `buffered_dekker_derived`,
`dekker_fenced_all_runs`, `dekker_unfenced_zero_zero`,
`buffered_emp_load_withdrawal_premise_invalid`,
`buffered_barrier_parallel_initial_adequacy`,
`buffered_marked_cell_withdrawal`, `buffered_dekker_store0_premise`.

## Request: check the new paper text

Please check `paper/sections/dekker.tex` and the last section of
`paper/sections/appendix.tex` against the sources, as you did for the
earlier sections. In particular:

1. The three stated differences between the two judgments, and the prose
   description of the atomic premise.
2. The two reasons given for why the original daring rules fail. I
   attribute the load counterexample to a thread that holds the lock and
   the store counterexample to the pool being fixed and buffer-free
   between lock operations. Say if either misdescribes the proof.
3. The appendix table of what each thread holds after each step and what
   it exchanges, including the claim that there are 24 memory shapes.
4. The last paragraph, on limits. It says an initial barrier supplies the
   missing mark, and no more than that. If it still overstates
   `buffered_barrier_parallel_initial_adequacy`, give me the wording.

No new proofs are requested.
