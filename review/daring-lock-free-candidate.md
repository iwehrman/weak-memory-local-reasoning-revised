# Daring rules: Stage 2 statement before search

Target request: `reviewer-request-daring-rules.md`, revised for fenced
Dekker (`0a3e724`). Stage 1 is in `DaringExtension.v` and
`DaringCounterexamples.v`. This file fixes the Stage 2 candidate before
running its search. None of the following is an accepted replacement for
the active calculus. No general proof is attempted.

The precise definitions and rule propositions are in
`theories/DaringCandidate.v`. In particular a `Definition ... : Prop` in
that file is a **question**, not a proved rule.

## Environment and updates

Only commands with no lock or unlock are admitted. Every environment has
an unblocked whole memory and a buffer-free, unblocked pool satisfying
fragment invariant J at full completeness. It factors as

    whole ∈ pool ; (frame # local).

The outer operation is the memory-level temporal operation: pool marks
are not added to the private resource. The inner operation is the
existing repaired, ordered spatiotemporal operation. There is no
additional heap-disjointness or processor-ownership condition. In
particular the candidate permits a pool cell to overlap a component heap
or a buffered write. This is the proposal being tested, not an assumption
that such overlaps are sound.

Within a program step the external frame is exactly fixed. Pool and local
resource may be re-split on non-store steps. Stores keep the pool exactly.
The union of pool and local footprints cannot grow, and local marks may
only be retained or gained for the processor executing a fence. There
are no acquire/release actions in this language.

A machine flush of `(address,value)` changes the pool's cell at that
address if one exists, and otherwise leaves the pool unchanged. Exactly
one of frame and local takes its ordinary generalized flush, adding only
the flushing processor's mark; the other is fixed. The resulting pool
must satisfy J. The flushed component keeps the heap entry that the
existing resource-flush semantics gives it. We do not silently change
what a write atom means after a flush.

## Safety and validity

`daring_safe 0` is true. At index `n+1`, quantify over every existing
resource future of the local resource, including mark-only futures. A
terminal command must satisfy its postcondition on that future resource.
Then quantify afresh over every pool and frame forming an environment:

- the command cannot abort;
- every program step has a successor with the same frame, the update
  conditions above, and safety at index n;
- every enabled machine flush has the exact attribution described above
  and safety at index n for the unchanged command.

`daring_valid` requires lock-free syntax and safety at every index from
every model of the precondition. The explicit machine-flush clause is a
departure from simply copying `owned_safe`: its old closure argument
cannot account for a changing pool. Local-future closure is retained,
conservatively, rather than assumed adequate on its own.

No pending-write restriction has yet been added to environments. Whether
one is necessary is part of the search. In particular, stability of the
value of *one issued store* does not automatically constrain the writes
in an arbitrary external frame.

## Rule questions

- Invariant access: the request's `J ; P` / `J ; Q` premise, at
  **overlap-mode** `owned_valid` under `emp`. Try load, fence, assignment,
  assume, assert and skip separately. Overlap mode is the stronger of the
  existing validity notions. Skip remains terminal, with no invented
  machine transition to perform a transfer.
- Store: for every stack and every full model of J, the evaluated address
  exists, and updating its heap value to the evaluated right-hand side
  again satisfies J. The pool is otherwise unchanged. Ask whether this
  suffices for `{P} store_i {P ; write_i}`.
- Ordinary SKIP, SEQ, CONS, DISJ, CHOICE, LOOP, EX, FRAME-SP and CONC are
  separate propositions. EX retains freshness for J, command and post;
  CONC retains the existing interference and invariant-variable
  conditions. All other side conditions are the existing ones.
- FRAME-TM is not a target of this request. Locks and mixed-judgment
  concurrency are not in scope.

Adequacy asks that validity, a fragment invariant, two active processors,
an initial precondition, and an empty-frame environment imply no abort
on every finite execution; on termination an empty-frame decomposition
satisfying the invariant and postcondition must exist. The initial
composition is temporal, as proposed. This is stated, not proved.

## Search plan and limits

Use the existing finite implementation of ordered composition and resource
futures (`search_frame_shape.py`). Two processors, values 0/1 and three
addresses suffice for the small witnesses; a separate finite state model
uses nine distinct addresses for the proposed Dekker ghost invariant.

1. Test the access primitives and store on focused inhabited assertion
   families, explicitly searching successor decompositions rather than
   rejecting a single chosen successor. Separate actual bounded rule
   failures from failures of a sufficient frame-reconstruction lemma.
2. Check basic structural implications at small safety indices, with
   closure, fresh environments, physical flushes and fixed frames. Record
   exactly which instances and indices were tested. Failed premises do
   not count as successful tests of a rule.
3. Search residual-buffer uniqueness and physical-flush attribution with
   a fixed buffer-free pool, including duplicate writes. Test invariant
   preservation separately from the algebraic attribution question.
4. Check spatial-frame/parallel regrouping with a pending frame write to
   a pool address, and with pool ownership re-splitting. Do not describe
   a failed regrouping obligation alone as a refuted validity rule.
5. Enumerate the ghost invariant's heap models to check the proposed
   store-stability and token-exclusion arguments. Explore the small
   fenced and unfenced machine programs as an independent target check.

These are bounded tests, not a decision procedure for the Rocq predicates
or a soundness proof. The follow-up report will contain the actual bounds,
counts, witnesses, incomplete items and proposed changes. Any repair is
for reviewer discussion before general proofs or a new calculus.
