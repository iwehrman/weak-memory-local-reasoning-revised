# Soundness: checked obstructions and repairs

The revised full soundness theorem is **not proved**. The current development
contains checked negative results about the printed claims, positive repairs
of several ingredients, and an operational adequacy theorem for the printed
safety predicate. These are distinct results.

## The assignment axiom fails against full safety

`Safety.v` encodes `safe_n` and specification validity from pp. 131-132.
`SafetyExamples.v` gives this instance of the printed assignment axiom:

```text
invariant: x = 0
precondition: true
command: x := 1 on processor 1
postcondition: true
```

Substitution into the pure postcondition leaves `true`, so the printed axiom
derives this specification. Start with all registers zero, empty memories,
and no held lock. After the assignment the invariant is false for every
possible shared-memory component. The global lock is still free. Consequently
the post-step invariant-or-locked obligation fails already at safety index 1.

`printed_assignment_invalid` proves this specification invalid.
`printed_assignment_soundness_false` proves that even the pure-postcondition
subset of the printed assignment axiom cannot be sound. Any calculus
containing that unrestricted axiom therefore cannot satisfy Theorem 1 as
printed. This argument does not depend on the frame conjecture or the
associativity problems below.

The checked repair `assignment_preserves_environment` requires the assigned
variable to be absent from the invariant's free variables.
`repaired_assignment_action` additionally checks the concrete assignment
transition and substituted pure precondition/postcondition. It covers the
non-silent action; full axiom validity also needs intervening-flush closure.

## Lookup-only list overriding is not associative

Let `a`, `b`, and `c` be singleton buffers writing values 1, 2, and 3,
respectively, to the same address. The list `[2, 1, 3]` is admitted by
`a override (b override c)`: it is an interleaving and its last lookup is 3.
It is not admitted by `(a override b) override c`: the inner result must
place 1 before 2, and interleaving with 3 cannot reverse that order.

`printed_buffer_override_not_associative` checks this counterexample to
Proposition 2(2), including the interleaving requirement from the preceding
prose. Thus the failure is not caused by omitting that requirement.

`ordered_overrides` is a conservative candidate repair. A write from the
future input can be selected only after all writes to its address in the
past input have been selected. The following are proved:

- It implies the printed override relation and preserves every write.
- It includes concatenation and, for disjoint domains, all interleavings.
- It is associative, constructively, in both directions.
- Its output head comes from a real component head; a future-origin head
  cannot bypass a conflicting past write.

`memory_ordered` lifts this repair to memory systems, retaining the printed
compatibility relation. It includes both spatial and temporal compositions.
`ordered_flush_split` and `ordered_flushes_split` prove replacements for the
one-step and finite flushing-decomposition claims used in frame reasoning:
the component residuals arise from actual flush transitions.

## Blocking facts also obstruct memory associativity

There is a second, independent problem. Take:

- `a`: a pending write to address 1 on processor 1;
- `b`: a flushed write to address 1;
- `c`: an empty memory contributing the fact that processor 1 is blocked.

The compatibility guard admits `a` composed with `(b composed with c)`,
because processor 1 is blocked in that grouping. It rejects composing `a`
with `b` first, where the blocking fact is absent.
`printed_spatiotemporal_not_associative` checks this for the original
memory separator. `printed_memory_compatibility_not_associative` shows that
replacing only list overriding by the ordered version does not fix it.

`stable_compatible` is a separate conservative candidate: conflicts are
checked regardless of whether a processor is currently blocked. It implies
the printed compatibility relation. `stable_compatibility_associative`
proves its definedness conditions are invariant under temporal regrouping;
`temporal_join_associative` proves equality of the resulting temporal tuples
up to pointwise equivalence. These are not yet a proof of the full
spatiotemporal algebra or of its generalized completeness-set version.

The stronger guard excludes some compositions permitted by the dissertation.
That is an explicit change to expressiveness, not a transcription correction.
It has not been installed into the assertion interpretation or safety model.

## What the safety adequacy results establish

`safe_execution_residual` follows any finite concrete execution from a state
covered by `safe_n`, maintaining a valid shared/frame/local decomposition
and a real flushing history for the external frame.
`safe_execution_no_abort` excludes a fault at the resulting state.
`safe_execution_post` establishes the local postcondition if execution has
reached an annotated skip. The shared invariant holds whenever the global
lock is not held, as required by the environment predicate.

The development also proves index and postcondition monotonicity, and the
consequence and disjunction rules for specification validity. These results
assume safety where stated; they do not assume the intended derivation
soundness theorem, any separation-algebra law, or assertion flushing closure.

## What still prevents a full positive soundness claim

The candidate algebra repairs need to be combined and checked with generalized
memories and assertion closure. The corrected derivation system must then be
encoded and its primitive, structural, concurrency, invariant, and frame
rules proved against a compatible safety semantics.

The earlier replacement frame lemma still needs a proof that safety supplies
ownership-respecting residual witnesses, including transfers from shared
invariants. See [frame-decomposition.md](frame-decomposition.md). Strengthening
safety to carry these witnesses is a candidate design, not an established
theorem. No semantic-validity premise has been inserted into an axiom merely
to make a soundness induction succeed.
