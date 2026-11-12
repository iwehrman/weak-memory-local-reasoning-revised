# Checkpoint 5 — reviewed safety definition proposal

**Status update:** the user approved this definition with two distinct
active processors. It is now implemented, with closure, adequacy, mode
inclusion, and all fixed acceptance tests checked. See the
[implementation checkpoint](checkpoint-5-implementation.md). The text below
records the original proposal and the decisions presented for review.

**Original status:** this is a definition proposal, not a completed checkpoint or a soundness
result. No replacement safety predicate or proof rule has been implemented.
The three requested [acceptance tests](checkpoint-5-acceptance.md) are fixed
before rule proofs. The proposal below addresses changing environments,
completeness marks, disjointness, and empty-frame adequacy.

There is one new decision before implementation: the blocked-set encoding
does not distinguish a free lock from a held lock on a singleton processor
domain. This is now checked in [LockRepresentation.v](../theories/LockRepresentation.v).
Finiteness alone does not remove the ambiguity. The proposed definition is
conditional on resolving it; no processor assumption has been installed.

## 1. One development target

This would replace **`separated_safe` / `separated_valid` as the active
development path**. It has one owned generalized resource and one shared
invariant pool, with a mode parameter `ov` or `dj`. It has no permanent
protected/private assertion positions and no retirement interpretation.
Earlier predicates and their proved theorems retain their historical meanings;
they are not automatically results about this replacement.

Assertions remain `persistent_models`. The ordinary cell abbreviation is
`writer_points_to`; invariants use the accepted guarded fragment from
checkpoint 2. No new assertion atom, changed entailment, or additional
semantic validity family is proposed here. In particular, `emp` keeps its
unit laws. The known variable-interference requirements remain proof
obligations for the eventual rules.

## 2. Two facts about the existing lock representation

### Singleton domains need a decision

The machine records a held lock by blocking every active processor except
its owner. For `active = {i}`, that blocked set is empty. The checked facts are:

- `singleton_emp_lock_equivalent`: `lock(i)` and `emp` have the same atom
  interpretation, for every generalized memory and every choice of marks.
- `singleton_acquire_still_free`: acquisition still produces a memory
  satisfying `lock_free`.
- `singleton_empty_acquire_enabled`: acquisition from the physically empty
  singleton machine is an actual enabled operation.
- `free_held_characterization`: a free memory is also held by `i` precisely
  when `i` is active and every active processor equals `i`.
- `two_processors_separate_free_held`: two distinct active processors
  suffice to make free and held mutually exclusive.

This matters for the proposed universal environment quantification. With a
singleton domain, an empty local resource and empty frame could be admitted
as a held state with an empty pool. The machine would nevertheless allow an
acquisition there. A nonempty invariant cannot then be supplied to its
postcondition. Merely naming the cases with different tags does not fix
this: both tags still admit the same resources and machine operation.

My recommended small scope condition for retaining the current machine and
assertion interpretation is **at least two distinct active processors**.
This does not require both to execute instructions. Representing a
single-processor program using an otherwise unused extra processor is a
possible way to recover that case, but no embedding theorem is claimed.
The alternative is an explicit owner/token representation, which would
change the existing singleton `emp`/`lock` equivalence and require reviewing
the machine, resource operations, and lock atom together. Neither alternative
is silently adopted by this proposal.

### Partial blocking information must remain admissible

The existing resource universe permits partial blocked sets. A checked
three-processor witness has a local resource blocking only processor 2 and
a frame blocking only processor 3. Both are well formed, have empty heaps
and buffers, and compose spatially to a whole memory held by processor 1.
Neither component is individually free or a complete held lock.

`SplitLockWitness.fragments_well_formed`, `fragments_compose`, `whole_held`,
and `parts_incomplete` check those facts. `failing_assert_enabled` checks
that `assert false` on processor 1 faults in that whole memory.

Consequently, the environment should not demand that the complete blocked
set always reside entirely on one side of `#`. Such a demand would exclude
this real context and leave the local nonterminal safety obligations
vacuous. This is a checked resource-level warning, not a proved counterexample
to a new safety predicate, since none has been defined.

The proposal admits split blocking information. The permission to **release**
still requires the complete token in the local resource. This preserves the
existing resource universe instead of adding a new well-formedness filter.

## 3. The environment and the three ordinary ownership situations

Write `mem(r)` and `marks(r)` for a generalized resource's memory and
completeness set, and `D(m)` for `memory_domain m` (heap and buffer addresses).
Resources `nu`, `F`, and `C` have the existing well-formed subtype. The pool
`H` and the whole machine `M` are raw memories. All memory equalities below
can be expressed fieldwise; no extensionality axiom is intended.

The candidate environment relation is:

```text
Env(k, J, s, nu; F, H, C, M, phase)

    F # nu = C                         repaired_spatiotemporal
    H spatially composed with mem(C) = M
    H and M are memory-well-formed
    if k = dj: D(mem(F)) is disjoint from D(mem(nu))

    phase = Free:
        lock_free(M)
        persistent_full_satisfies(active, s, H, J)

    phase = Held(i):
        lock_held(active, M, i)
        H = empty_memory
```

The invariant-fragment theorem makes `H` buffer-free and lock-free in the
free case; the empty pool has both properties in the held case. The pool's
full marks are only a convention for interpreting its invariant. They are
not part of the mark union in `F # nu`.

This includes all three requested ordinary situations:

| Situation | Pool | Local resource | Frame |
| --- | --- | --- | --- |
| Free | Satisfies `J` | Lock-free | Lock-free |
| Held locally by `i` | Empty | Contains the complete token for `i` | Lock-free |
| Held externally by `i` | Empty | Lock-free | Contains the complete token for `i` |

It also admits the partial-token compositions described above. `Held(i)`
records the global machine status; whether release is permitted locally is
tested separately. This is deliberately more inclusive than a disjunction
requiring either the local resource or the frame to contain a complete token.

When another thread holds the lock, its owned resources are in the frame,
including the cells it is manipulating inside the critical section. **The
frame need not currently satisfy `J`.** The holder may be restoring it, and
ownership transfer can change its footprint. Requiring `J` during that
interval would prohibit the intended critical sections. There is no second
copy of the invariant's cells left in the pool while held.

Neither the phase nor the pool is a persistent parameter of safety. They
are universally quantified environment witnesses at each recursive step.

## 4. Program steps, transfers, and marks

Introduce a proof-level classification of **non-flush program steps** with
their actual action: ordinary instruction, fence on `i`, acquire on `i`,
release on `i`, or structural command step. Sequence and parallel contexts
propagate the action. Structural steps include sequence completion, choice,
and loop unfolding. They do not earn a mark.

This classification must be shown to erase to `OperationalSemantics.step`.
Conversely, every existing step must classify either as a machine flush
with command and stack unchanged, or as one of these program steps. In
particular, a flush under a sequence or parallel constructor remains a
flush. We must not classify a step just by comparing its input/output
memories: an assumption or fence can also leave memory unchanged.

For each actual program step from an admissible environment, the successor
must recompose to that actual resulting machine with **the exact same `F`**,
including its marks. The pool and local blocking information obey:

| Action | Pool and phase | Local blocking information |
| --- | --- | --- |
| Ordinary, structural, fence | Same pool, same phase | Unchanged |
| Acquire `i` | `Free` to `Held(i)`; pool becomes empty | Complete token for `i` |
| Release `i` | `Held(i)` to `Free`; returned pool satisfies `J` | Complete local token for `i` required before; lock-free after |

All successors additionally obey the footprint bound:

```text
D(H') union D(mem(nu'))  subset  D(H) union D(mem(nu))
```

The unchanged-pool clauses matter: an assumption cannot silently transfer
cells into or out of the invariant. Acquisition consumes the old pool;
release alone may choose a new invariant pool. Recomposition with the
actual machine and fixed frame is still mandatory. Buffer residual
uniqueness is supplied by checkpoint 4; the corresponding heap and frame
reconstruction arguments remain to be proved.

There must also be an explicit upper bound on successor marks:

```text
marks(nu') subset marks(nu) union earned(action)

earned(fence i) = earned(acquire i) = earned(release i) = {i}
earned(ordinary or structural action) = empty
```

All three listed synchronization operations require the **whole** processor
buffer `i` to be empty in the existing machine. Forgetting marks is allowed,
subject to resource well-formedness. Importing the pool's other marks is
not allowed. At acquisition, checkpoint 2 supplies an interpretation of the
acquired invariant with exactly the actor's singleton mark. A returned pool
may again be interpreted with full marks, without giving those marks to the
retained local resource.

The mark bound is a proposed semantic clause, not a new assertion entailment
or a checked theorem about the not-yet-written predicate. Without a bound,
memory recomposition and a footprint bound alone do not constrain the marks
of an existentially chosen successor.

## 5. A well-founded safety definition and fresh frames

Here is the proposed recursion, in mathematical pseudocode. `future` is the
existing `resource_future`; `models` means `persistent_models`.

```text
Safe(k, 0, J, c, s, nu, Q) = True

Safe(k, n+1, J, c, s, nu, Q) =
  for every nu_f with future(nu, nu_f):
    (if c is terminal, models(s, nu_f, Q))
    and
    for every F, H, C, M, phase with
      Env(k, J, s, nu_f; F, H, C, M, phase):
        c does not abort in (s, M)
        and
        for every labeled program step (c,s,M) --action--> (c',s',M'):
          there exist nu', H', C', phase' such that
            Env(k, J, s', nu'; F, H', C', M', phase')
            and the action, footprint, and mark clauses of section 4 hold
                relative to nu_f and the input environment
            and Safe(k, n, J, c', s', nu', Q)

Valid(k, J, P, c, Q) =
  for every n, s, nu: models(s, nu, P) implies Safe(k,n,J,c,s,nu,Q)
```

The terminal assertion is outside the environment implication. It cannot
be discharged just because a resource has no admissible context. Initial
and final marks are real local marks, not uniformly promoted to full marks
inside this definition.

The outer universal quantification over futures gives same-index local
closure by transitivity, without an ill-founded recursive call at the same
index. This preorder also includes mark-only extensions. Those express
logical monotonicity; they are not machine synchronization steps. The
definition must handle **every** future, including the reflexive one. It
cannot choose an extra mark in order to escape an obligation. A program
successor has the separate mark budget above.

On a real machine flush, checkpoint 4 fixes the pool and attributes the
flush to one component. A frame flush leaves `nu` unchanged; universal
environment quantification admits the resulting frame. A local flush is
handled by same-index closure. The affected resource can be chosen to gain
exactly the flushing processor's mark. No arbitrary repartition follows a
flush.

The frame is fixed **within one program step**. The recursive `Safe` call
quantifies over new frames, pools, and phases. Another thread may acquire,
change its owned cells, or release between this thread's steps. The
definition imposes no future relation between those successive external
frames. This universal quantification is an obligation on the proof, not
permission to invent additional concrete machine transitions.

Re-quantifying resources does not by itself handle changes to the shared
register stack. The concurrency proof must still use the accepted
variable-interference conditions to transport the other thread's safety
to the changed stack. The third acceptance test avoids registers so it
tests the ownership issue directly.

## 6. What a completeness mark means

A mark on a generalized resource does **not** mean its entire current
buffer is empty. The existing `GeneralizedFlush` removes one head write,
adds its processor's mark, and may leave a nonempty tail. A mark records a
completed boundary before the remaining history represented by that resource.

`bar(i)` is more specific: its own heap and buffers are empty, it is
lock-free, and it has mark `i` when `i` is active. In a composition
`R ; bar(i)`, the temporal relation therefore requires `R`'s buffer for
`i` to be empty. It does not inspect an unrelated external `#` frame.
Conversely, `bar(i) ; write_i(x,v)` may have a pending write after the barrier.

Fence/acquire/release have the stronger physical guard that the whole
machine buffer for the actor is empty. That justifies adding the actor's
mark, while a flush justifies a prefix boundary. These uses are compatible;
they do not give `bar(i)` two different assertion interpretations.

FRAME-TM needs the prefix-relative temporal condition. When its local suffix
earns a mark from a program synchronization step, the physical guard drains
the framed prefix on that processor too. When the mark comes from an actual
flush of the suffix, FIFO attribution must establish that the preceding
prefix on that processor is already empty. The unchanged-frame clause and
mark budget prevent an unrelated mark appearing in the suffix instead.
These are the intended proof obligations for the unlock-free FRAME-TM
theorem; the complete theorem is not yet proved.

## 7. Disjoint mode and adequacy

Disjointness is an assumption on **each input environment** in `dj` mode,
and it must be established in each actual successor environment. It is not
a permanent promise about one fixed frame.

Acquisition does not require a new disjointness side condition on assertions.
The old pool is spatially disjoint from `F # nu`, hence disjoint from both
components. The successor footprint bound therefore keeps the enlarged
local resource disjoint from the unchanged `F`. For ordinary steps the pool
is fixed and cannot be appropriated; for release the new pool and retained
local footprint lie inside the old local footprint. Actual flushes introduce
no new addresses outside the flushing component's old domain. These are
proof arguments to formalize, not additional input assumptions.

The intended top-level adequacy theorem starts from a concrete admissible
initial memory using `F = empty_resource`. The `#` unit law and empty domain
discharge the frame/mode conditions in **both** modes. Under the proposed
nondegenerate lock-domain choice, a complete externally held token cannot
be hidden in that empty frame.

Validity should then imply: every finite actual execution avoids abort, and
every terminal execution has a final owned resource satisfying `Q` and a
pool/ownership decomposition of the actual final memory. If the lock is
free, the pool satisfies `J`; if it is held locally, the pool is empty.
In particular, a free final state has the usual spatial `J`/`Q` account.
The conclusion is about the owned resource inside the machine, not a claim
that `Q` alone describes a nonempty free pool as well.

The index counts program steps; real flushes use closure. Any finite run is
covered by choosing a sufficiently large index. This is partial correctness,
without fairness or termination claims. The top-level statement must expose
the initial invariant and the eventual processor-domain decision, but must
leave **no mode-specific frame premise** to the client.

## 8. Review boundary and next work

The mandatory tests are recorded separately, with both positive validity
targets and explicit nonvacuous machine witnesses. They are requirements for
the eventual predicate; none is being reported as proved against it now.
The split-token and singleton diagnostics are already checked against the
existing machine and resource definitions.

Before coding the replacement, resolve the singleton-domain choice and
review the inclusive held-state clause, action-specific transfers, and mark
budget. After that, implement one predicate and its operational step
classification; prove closure and adequacy; then prove the three acceptance
results **before** calculus rules. Any failed test is a definition checkpoint,
not a reason to weaken its expected result silently. General framing,
concurrency, and the container derivation remain later obligations.

## Validation

`make check` passed, including the independent proof-object check. All
**411** audited declarations reported `Closed under the global context`.
The ten newly audited declarations concern only the existing lock/resource
representation. They introduce no axioms, admitted proofs, new safety
predicate, or ambient processor-domain assumption. The mathematical
definition and acceptance targets in these documents have not been compiled
as a new framework and are not included in that theorem count.
