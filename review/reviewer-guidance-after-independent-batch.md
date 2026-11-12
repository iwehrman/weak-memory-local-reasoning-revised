# Reviewer guidance after the 4B statement and the independent batch

Responds to `33bcab0`, `26af676` and `9333c80`. I rebuilt `9333c80` from a
clean clone: `make check` passes with 947 audited declarations closed.

## Decisions

1. **The 47-constructor assertion system is approved. Proceed to its
   soundness proof**, then the derived cell rules, the CONS and UNLOCK
   wrappers, and 4C.
2. **Restricted SHARE uses the semantic premises you proposed**: every model
   of the precondition and of the postcondition is lock-free. The syntactic
   reading is refuted and should be reported as such.
3. **No common-split connective and no new program rule.** The resource
   theorem is enough for the paper.

## The assertion rule set

I read the statement rule by rule and have no objection to any rule. What I
checked specifically:

- No constructor takes a semantic entailment, satisfaction, safety or
  validity premise. The pure rule is confined to boolean expressions.
- `⋉` has no rules of its own.
- The contextual forms of disjunction and existential elimination carry an
  additive context with the right freshness condition.
- The two pure-through-separation rules rely only on both components seeing
  the same stack, and say nothing about pure formulas being buffer-free.
  That is the right way round, given the earlier bare-pure finding.
- The two new cell rules are plausible from the shape theorem: both sides
  are buffer-free, so the temporal mark condition is vacuous, and overwrite
  is stated in the one direction that is true. They still need their general
  proofs.

Two requests for the soundness report:

- For each constructor give the semantic lemma that discharges it, in the
  same form as the program-rule table in `notes/paper-theorem-index.md`.
- When the derived cell rules are done, say which of them needed
  bound-variable renaming, and whether any rule had to be added to the 47.
  A final count of constructors with a one-line reason for each addition is
  what the paper will print.

If a constructor turns out to be unsound, that is a stop-and-report with
the countermodel, as usual. Do not weaken it silently.

## The independent batch: accepted

- **Printed derivations with the dissertation's own points-to**, under the
  original interpretation. The paper now presents both derivations with
  `↦` and cites `printed_points_stale_value_unsound` and
  `printed_points_foreign_barrier_unsound`.
- **The printed FRAME-STM counterexample.** Accepted, and used in the paper
  as a third derivation. Your caution is right and the paper follows it:
  the derivation also uses INV, so this shows that FRAME-STM does not escape
  the problem, not that it is an independent source of unsoundness.
- **Common-split framing**, in both modes and across release. This settles
  what the dissertation's strong temporal frame rule needed. The paper will
  say that the rule is sound for one common split and unsound for the
  conjunction of two.
- **Derived-rule table.** Accepted as the paper's table. I will present the
  two literal mismatches (STORE-P's displayed command and suffix, FENCE-B's
  displayed command) as transcription slips in the dissertation, with the
  corrected forms derived, which is how you classified them.
- **Fenced store and its unfenced twin**, **domain preservation**, the
  **SHARE counterexamples**, the **Dekker paragraph** and the **writer's
  index**: accepted.

On your three wording qualifications to my proposed findings: all accepted.
The paper will use your suggested sentence for the first, restrict the
second to the enumerated laws, and state the third only for the uniform
premise.

## Restricted SHARE: where it sits

Attempt it after 4C and priority 1, not before. Priority 1 was designed not
to need it. State the overlap-mode question separately; I expect it to
fail, because an overlapping frame may hold a stale copy of a cell that
moves into the pool, but that is the kind of expectation that has been
wrong before. If the disjoint-mode theorem needs a further premise, report
the premise and the countermodel that forces it.

## Order from here

1. Soundness of the assertion system and the derived cell rules.
2. 4C: the one-item container with no semantic entailment premises.
3. Priority 1: the Section 4.1 example, in the system.
4. Priority 2: named locks and the producer/consumer client, in the system.
5. Restricted SHARE.

Check in after 1, after 2, after the result of 3, and at the design and
each part of 4, as before.
