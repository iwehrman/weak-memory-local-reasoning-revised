# Restricted SHARE: statement before the proof attempt

The remaining queue item is the following semantic rule, with the existing
meaning of validity and the empty invariant in the conclusion:

```text
J valid_DJ {P} c {Q}
every model of P is lock-free
every model of Q is lock-free
---------------------------------
emp valid_DJ {J * P} c {J * Q}
```

The standing hypotheses are that `J` belongs to the approved invariant
fragment and two distinct active processors exist. "Every model" quantifies
over every stack and every well-formed resource. It does not mean absence
of a lock atom in the syntax. The latter was already refuted.

The overlap question is stated separately: replace DJ by OV in both the
premise and conclusion above. DJ-to-OV would be a third, stronger question;
a counterexample to it would not refute the same-mode OV statement.

First screen the resource simulation with two processors, small heaps,
pending writes, all mark choices and each possible token placement. The
target owns the invariant's cells privately while the source lock is free.
On acquire those cells become part of the source local resource; on release
they return to the source pool but remain inside the target local resource.
An externally held lock must also be covered, since environments are
re-quantified at every step.

The proposed target is a theorem about the existing safety predicate, not
a new predicate or constructor. No invariant-variable premise is silently
added: although existing derivations already preserve the invariant's free
variables, the displayed semantic statement has no such premise. If that
generality fails, report the countermodel before selecting a repair.

This is a statement of work, not a completed theorem. The assertion and
program systems remain unchanged.

The completed results are recorded in [the SHARE report](paper-restricted-share.md).
