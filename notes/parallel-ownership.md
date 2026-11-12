# Two threads sharing one protected invariant

> **Historical checkpoint.** This report describes an earlier development
> stage. Its alternative safety/calculus design is superseded by
> `OwnedSafety.v` and `OwnedCalculus.v`; any statements about remaining
> soundness work belong to that stage. Reused resource lemmas and checked
> counterexamples retain their meanings. See the
> [current calculus and complete comparison](current-calculus.md).

`private_parallel_rule` proves concurrent composition for two threads in the
private-resource calculus, including register updates from private loads.
It covers every finite execution of the ordinary
`Concurrent.Parallel` command, including all permitted flush schedules. It
establishes absence of aborts and, on termination, a restored shared invariant
and the spatial combination of the two private postconditions.

This extends the [private-resource protocol](private-ownership.md). There is
no new assertion constructor and no further change to `persistent_models`
or the machine semantics. Full corrected soundness remains open.

## Rule and its exact premises

The schematic rule is:

```
J |- {Closed; P} c_i {Closed; Q}
J |- {Closed; R} d_j {Closed; S}
i != j
modifies(c_i) disjoint from FV(R, d_j, S)
modifies(d_j) disjoint from FV(P, c_i, Q)
----------------------------------------------------
{J * P * R} c_i || d_j {J * (Q * S)}
```

The two premises are derivations in `private_derivation`, not arbitrary
assumed Hoare-validity facts. That bounded calculus contains skip, sequencing,
acquisition/release, the owned constant-cell store/fence rules, and private
loads into registers. `parallel_variable_condition`, already defined in
`Specifications.v`, supplies exactly the displayed mutual condition. The
earlier register-free theorem follows as `private_parallel_memory_only_rule`.

The initial whole memory must have the well-formed, unlocked decomposition
required by `private_environment`: one shared pool satisfying `J`, the left
private component satisfying `P`, and a spatially separate right private
component satisfying `R`. Each private assertion is interpreted with the
usual full processor-completeness marks. There are not two copies of `J`.
`J`, `P`, `Q`, `R`, and `S` can use the full existing assertion grammar.

Each thread may modify variables that the other's specification and code do
not depend on. The private load rule already requires its destination to be
absent from `FV(J)`. `private_derivation_modifies_invariant` proves that every
derivation in this calculus respects that requirement; it is not a further
unproved premise of the parallel theorem. The owner identifiers are fixed
and distinct. The processor domain itself can be arbitrary and is not
required to be finite.

## Register interference through intermediate assertions

`private_derivation_support` proves that the output assertion's free variables
are contained in those of the invariant, input assertion, and command. The
strengthened `private_derivation_step` constructs a residual derivation whose
new input assertion obeys the same bound. This accounts for intermediate
assertions hidden by sequencing, not just the initial and final assertions.

`thread_interface` records a fixed variable set and write set for each thread.
`specification_interface` computes them from the ordinary specification:
`FV(J) ++ FV(P, c, Q)` and `modifies(c)`. They are proof bookkeeping; clients
do not supply extra assertion syntax or per-step interference proofs.
`specification_interfaces_compatible` derives the required compatibility from
the existing mutual variable condition and the invariant-freshness theorem.

At each step, the residual command's modified variables stay within its
original write set. `thread_step_agrees` therefore establishes agreement on
the other thread's variable set, and `thread_spec_transport` preserves its
current assertion using `persistent_full_agrees` plus flushing closure.
Register equality outside that set is unnecessary. The same bound protects
a finished thread's postcondition while its sibling continues to execute.

## How the ownership views agree

`joint_state` has exactly three cases:

- **Closed:** the pool satisfies `J`, and each thread has its private memory.
- **Left owns the lock:** the left thread has the pool plus its private
  memory. The right thread retains its private assertion and a closed-phase
  continuation.
- **Right owns the lock:** the symmetric case.

`memory_spatial_associative` and `spatial_exchange` construct the decomposition
needed to switch the active viewpoint. This is constructive, using the
existing finite-buffer witness machinery rather than a choice axiom.

When one processor owns the lock, a different processor cannot acquire it
or perform a load. `waiting_derivation_step` nevertheless allows structural
steps and ordinary global flushes; the proof does not assume that a waiting
thread takes no steps. The owner preserves the waiting thread's private
assertion because its external frame evolves by actual flushes and every
assertion is flushing closed. Agreement on the waiting thread's relevant
variables supplies the remaining assertion-preservation obligation.

`joint_left_step` and `joint_right_step` maintain the shared ownership
decision after every step. When one side reaches skip, the machine can erase
the parallel node. `parallel_certificate` then retains that side's proved
postcondition as a spatial frame for the surviving thread. This handles both
early termination and subsequent flushes, rather than reasoning only about
executions that retain a parallel syntax node throughout.

`parallel_certificate_execution` follows any finite execution.
`parallel_certificate_no_abort` excludes a fault at every resulting state.
`parallel_certificate_post` returns, on termination, a free lock and one
shared pool satisfying `J`, spatially separated from a private memory
satisfying `Q * S`. The theorem proves partial correctness; it does not
assert fairness or termination of all schedules.

## A checked competing-writers example

The initial memory has protected cell `1 |-> 7`, left private cell `2 |-> 11`,
and right private cell `3 |-> 13`. Both threads use the same lock and invariant:

```
left, processor 1:                 right, processor 2:
lock;                             lock;
[1] := 9; fence;                  [1] := 5; fence;
[1] := 7; unlock                  [1] := 7; unlock
```

Each thread is derived independently with its own private pre/postcondition.
`competing_restorers_no_abort` covers all executions.
`competing_restorers_all_terminating_runs` proves that every terminating
execution leaves the lock free and all three cells at 7, 11, and 13.

Two concrete 23-step traces execute the critical sections in opposite orders.
Both flush the temporary value into shared memory before restoring it. A
separate five-step prefix reaches a shared value of 9 with processor 2 blocked;
`contended_waiter_cannot_acquire` checks that processor 2 cannot acquire in
that state. Thus the universal theorem is instantiated with real ownership
handoff and a temporarily broken invariant, not just empty lock round trips.

## Post-release loads and the need for the side condition

`ParallelLoads.v` appends `x := [2]` to the left critical section and
`y := [3]` to the right critical section, using different program variables
(identifiers 0 and 1). Both commands modify registers and thus fail the old
`memory_only` requirement. They satisfy the mutual variable condition.

`competing_readers_no_abort` proves safety for all execution prefixes.
`competing_readers_all_terminating_runs` proves, for every terminating run,
that the lock is free, all three cells remain 7, 11, and 13, and the registers
hold `x = 11` and `y = 13`. Two concrete 27-step traces cover opposite orders:
the first thread has finished before the other writes its result. This checks
preservation of the retired thread's postcondition as well as active views.

`same_destination_rejected` proves that choosing `x` for both destinations
violates the interference condition. `same_destination_loses_left_result`
constructs a successful 27-step run ending with `x = 13`, contradicting the
left thread's earlier `x = 11`. Thus unrestricted register interference cannot
be admitted by simply dropping the condition.

All principal results are imported by `Audit.v`. They use no admitted lemmas,
declared axioms, classical choice, extensionality, or processor-finiteness
assumption.

## Remaining work

Nested parallel derivations, arbitrary numbers of threads, choice and loops,
integration of framing into parallel derivations, temporal external frames, and the full invariant rule remain
outside this theorem. The current pair consumes the whole initial spatial
decomposition; a further arbitrary external frame needs its own composition
proof. The generic heap rules and complete corrected Theorem 1 remain open.

The subsequent [framing work](framing-status.md) proves spatial framing for
ordinary private semantic validity, plus temporal framing in a separate
marked-resource prototype. Neither result adds a frame constructor to
`private_derivation`, and the temporal prototype does not replace the semantics
of this parallel theorem. The newer [regional model](regional-ownership.md)
handles overlapping history and acquire/release, but exposes a further
completeness-import counterexample to unrestricted private temporal framing.
That rule-design issue should be resolved before porting the parallel theorem.

Ordinary arithmetic assignments and general expression-based loads/stores
still need integration into the private calculus. Removing `memory_only`
does not add those derivation constructors. Extending the calculus also
requires extending its variable-support proof; general consequence rules
with additional intermediate variables need particular care.
