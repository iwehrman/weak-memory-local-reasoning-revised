# Private resources through a critical section

This extends the checked ownership protocol with a private local component
that survives acquisition and release. The original prototype remains in
`OwnershipProtocol.v`; the new semantics is `private_valid` and `private_safe`.
The assertion grammar, `persistent_models`, and ordinary machine execution
are unchanged.

## Resource accounting and rules

In the closed phase, the combined owned region is spatially split into:

- a shared pool satisfying `J`, and
- the command's private local memory, described by its pre/postcondition.

In the open phase, the whole combined region is local to the lock owner.
There is no separate unconstrained shared pool. A spatial external frame
remains outside the combined region in both phases. Residual region domains
cannot grow, and the external frame can change only by actual flushes.

The proved transfer rules are:

```
J |- {Closed; P}                  lock_i    {Open; lock_i * (J * P)}
J |- {Open; lock_i * (J * Q)}      unlock_i  {Closed; Q}
```

`J`, `P`, and `Q` range over the full existing assertion grammar, including
future-aware wands. There are no additional purity, precision, or finite
processor premises on these rules. Their state-space conditions, including
spatial separation, lock ownership, and well-formedness, are explicit in the
environment definition.

Acquisition combines the two valid assertion witnesses without losing their
spatial separation. Release extracts the restored `J` and retained `Q`
witnesses from the owned region. `private_execution_closed_post` returns
both witnesses separately, together with their spatial composition and the
external frame. It does not establish only the combined assertion `J * Q`.

`private_environment_flush` handles flushing in the external frame, the
shared pool, or the local memory. Assertion closure supplies preservation
where necessary; private writes are not required to have empty buffers in
the transfer rules.

## Program rules and adequacy

The bounded calculus additionally proves:

- Stores and fences on a protected cell while preserving arbitrary private
  `P`. These are checked framed primitive rules, not an assumed general
  frame inference rule.
- Buffered single-cell release while retaining `P`, using unlock's ordinary
  empty-buffer execution condition instead of requiring an extra final fence.
- Loading a private cell after release. The destination must be absent from
  the free variables of `J`, matching the invariant-preservation condition
  already identified for loads.
- Skip and sequencing across ownership phases.

`private_calculus_sound` is proved by induction on derivations. No derivation
constructor contains a safety or program-validity premise. The internal
`private_lift_open_primitive` theorem reuses checked primitive proofs from the
earlier protocol where their open views agree; it does not assert that the
two validity definitions coincide in general.

`private_critical_section_rule` derives a whole critical section from a body
derivation:

```
J |- {Open; lock_i * (J * P)} body {Open; lock_i * (J * Q)}
----------------------------------------------------------------
J |- {Closed; P} lock_i; body; unlock_i {Closed; Q}
```

The body must restore `J`. This rule is for the new phase-indexed calculus;
the dissertation's original invariant rule is not thereby proved.

`private_execution_no_abort` and `private_execution_closed_post` quantify
over ordinary machine executions, including every permitted flush schedule.
They establish partial correctness, without a termination or fairness premise.

## Concrete checks

The example uses processors 1 and 2, protected cell `1 |-> 7`, and private
cell `2 |-> 11`:

```
lock_1;
[1] := 9; fence_1;
[1] := 7; unlock_1;
x := [2]_1
```

The restoring write can still be pending when unlock is reached.
`private_restore_trace` exhibits a 13-step execution with both buffered writes
flushed and the post-release load performed. `private_initial_environment`
constructs the nonempty shared/private starting decomposition.

`private_restore_no_abort` covers every execution from every admitted initial
spatial external frame. `private_restore_all_terminating_runs` establishes
that every terminating execution leaves the lock free, the protected cell
equal to 7, the private cell equal to 11, and `x` equal to 11. Thus the private
cell remains usable after the shared resource has been returned.

`private_alias_rejected` proves that the same heap cell cannot simultaneously
serve as the protected invariant and the private resource, regardless of the
chosen combined region. All new principal results are included in `Audit.v`.

## Remaining boundaries

The protocol uses spatial external frames. A subsequent
[two-thread composition theorem](parallel-ownership.md) now proves agreement
between owner and non-owner views, preserves both private postconditions, and
handles competing heap-restoring critical sections. It now permits register
updates under the existing mutual variable-interference condition, including
post-release private loads into distinct variables. General semantic spatial
framing is now proved at closed entry in `PrivateFraming.v`, with arbitrary
frame assertions and the usual variable condition. A separate marked-resource
prototype proves temporal framing and fence, but integrating temporal external
frames with these ownership rules remains open. See
[the exact results and transfer obstruction](framing-status.md).

The newer [regional model](regional-ownership.md) now proves generalized
acquire/release and a history rule around the entire shared/private region.
Its derivable closed-to-closed counterexample shows that the original private
temporal frame rule cannot be recovered merely by retaining completeness.
These results do not reinterpret the private or parallel theorems above.

The transfer rules accept arbitrary private assertions; the current checked
heap rules are constant-cell rules. The example preserves its private cell;
arbitrary private-state transformations, general expressions, substitution,
and general register/heap framing require further rules and proofs.
There is no new assertion constructor, finite-processor assumption, classical
axiom, or extensionality axiom. Full corrected soundness remains open.
