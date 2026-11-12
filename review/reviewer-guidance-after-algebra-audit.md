# Reviewer guidance after the algebra audit (4A)

Responds to `ae16e60`. I rebuilt it from a clean clone: `make check` passes
with 830 audited declarations closed.

## 4A and the two early items: accepted

- **Units.** `emp` is a two-sided unit for all three conjunctions over the
  full grammar, wands included. This was the result I asked to hear first,
  and it is the best possible answer.
- **Reading your own buffered write.** It is derivable today, and my reading
  was wrong. The old cell is the temporal frame and the newest write is
  LOAD's owned resource. I am glad to be wrong here: the derivation is the
  clearest use of FRAME-TM in the whole development, and the paper will use
  it as the motivating example for keeping that rule. No constructor is to
  be added. Priority 5 item 1 is closed.
- **The audit table.** Accepted as the paper's table. The classification,
  the both-readings treatment of T7 and T8, and the countermodels in words
  are what was asked for.

Three findings I will state prominently in the paper, so please tell me if
any is overstated:

1. Every printed law that does not mention `⋉` on the outside survives,
   apart from two that need a qualification (E6 on lock exclusion and T4 on
   the writer annotation).
2. Every printed law that rebrackets or exchanges through `⋉` fails:
   associativity in both directions, small exchange with `⋉` outermost
   under either reading of the premise, and full exchange.
3. The small-exchange laws between `*` and `;` hold only under a premise
   that forces the processor domain to be empty, so they are true and
   unusable.

## One request on scope of the negative results

The report says the `⋉` associativity countermodel and the opposite-lock
countermodel were also checked in the original `models` interpretation, and
the other negative results were not. For the paper's "what was wrong"
section the distinction matters: a law refuted only in the repaired
interpretation is a difference, not an error in the dissertation. Please
check the remaining refutations (T4 as printed, T7 and T8 with `⋉`
outermost, T9) against `models` as well, or say which cannot be transferred
and why. This is small and can be done alongside 4B.

## Guidance for 4B, the rule set

State the rules before proving them, as planned. My suggestions:

1. **Treat `⋉` as the abbreviation it is.** Give it no rules of its own
   beyond what follows from `∧`, `*` and `;`: T5, T6 and introduction from
   both conjuncts. No rebracketing, no exchange. The unit laws for `⋉` then
   follow and need not be primitive.
2. **Structural laws:** units, associativity and monotonicity for `*` and
   `;`; commutativity of `*`; the three adjunctions.
3. **Barrier laws:** T1, E7, E8, E9, E10.
4. **Lock laws:** E5 in its stronger form (`P ; L(i) ≡ P * L(i)` and the
   mirror), and the qualified E6. Say which standing hypothesis each needs.
5. **Write and cell laws:** E11, E12, the qualified T4, and the laws the
   container needed for `C`: exclusivity of two cells at one address, a
   drained write is a cell, collapse of a drained history onto its last
   write, and existential introduction for the value.
6. **Logic:** the usual rules for `∧`, `∨`, `∃`, `∀` and `false`,
   distribution of `*` and `;` over `∨` and `∃`, and a rule admitting a pure
   boolean entailment as a side condition.

Keep it small. A law that no derivation uses can be left out and listed in
the report as proved but not included. Completeness is not a goal.

## Check-ins, unchanged

After the 4B rule statements and before their soundness proof; after 4C.
