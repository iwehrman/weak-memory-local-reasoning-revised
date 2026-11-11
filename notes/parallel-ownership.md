# Two threads sharing one protected invariant

`private_parallel_rule` proves a first concurrent composition rule for the
private-resource calculus. It covers every finite execution of the ordinary
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
i != j       modifies(c_i) = modifies(d_j) = empty
----------------------------------------------------
{J * P * R} c_i || d_j {J * (Q * S)}
```

The two premises are derivations in `private_derivation`, not arbitrary
assumed Hoare-validity facts. That bounded calculus contains skip, sequencing,
acquisition/release, and the owned constant-cell store/fence rules. It also
contains private loads, but loads modify a register and thus do not satisfy
this first parallel rule's `memory_only` premise.

The initial whole memory must have the well-formed, unlocked decomposition
required by `private_environment`: one shared pool satisfying `J`, the left
private component satisfying `P`, and a spatially separate right private
component satisfying `R`. Each private assertion is interpreted with the
usual full processor-completeness marks. There are not two copies of `J`.
`J`, `P`, `Q`, `R`, and `S` can use the full existing assertion grammar.

The register restriction prevents either thread from changing variables in
the invariant or the other thread's assertions. Replacing it with conventional
free-variable interference conditions requires additional proofs; the
present result does not silently assume those proofs. The owner identifiers
are fixed and distinct. The processor domain itself can be arbitrary and is
not required to be finite.

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
assertion is flushing closed. Pointwise register preservation supplies the
remaining assertion-preservation obligation.

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

All principal results are imported by `Audit.v`. They use no admitted lemmas,
declared axioms, classical choice, extensionality, or processor-finiteness
assumption.

## Remaining work

The next concurrency step is to permit register updates under explicit
interference conditions, including private loads after release. Nested
parallel derivations, arbitrary numbers of threads, choice and loops, general
frame rules, temporal external frames, and the full invariant rule remain
outside this theorem. The current pair consumes the whole initial spatial
decomposition; a further arbitrary external frame needs its own composition
proof. The generic heap rules and complete corrected Theorem 1 remain open.
