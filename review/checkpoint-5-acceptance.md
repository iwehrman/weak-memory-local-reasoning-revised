# Checkpoint 5 — fixed acceptance tests

These are theorem targets for the [proposed single safety definition](checkpoint-5.md),
recorded before implementing that predicate or proving its rules. They are
**not yet checked validity results**. `C(x,v)` abbreviates `writer_points_to`,
and `W_i(x,v)` abbreviates the original `LeadsTo` atom. All examples use
constant addresses/values and processor annotations. No register condition
is being hidden in them.

## 1. Donation: invalid with overlap, valid with disjoint external frames

Use two active processors, owner 1, and

```text
J = emp or C(x,7)
P = lock(1) * C(x,7)
c = release(1)
Q = emp
```

Required results:

```text
not Valid(ov, J, P, c, Q)
    Valid(dj, J, P, c, Q)
```

The negative witness must start in an admissible held state: the pool is
empty, the local resource owns `x = 7` and the complete token for processor
1, and the fixed external frame is a flushed `x = 5` cell. Both buffers are
empty. Local and frame cell marks may both be exactly `{1}`. The `#` heap
override gives the actual whole cell value 7, and release is enabled.

Release leaves that physical value unchanged. A local `emp` successor
cannot supply the cell. If the returned pool is empty, the fixed frame
would make the whole value 5. If the pool contains `x = 7`, it is not
spatially disjoint from the frame. Neither invariant disjunct can recompose
to the actual successor. This witness is excluded by `dj` precisely because
the external frame overlaps the local cell.

The positive target quantifies over **all** admissible disjoint frames,
including pending writes elsewhere. It transfers `x = 7` to the pool and
retains `emp`, with the external frame unchanged. It is not enough to show
one successful unframed execution.

The wording "valid in disjoint mode" applies to this ordinary donation
contract. It does **not** mean the forged conclusion that release changes
`x = 7` into a stale owned `x = 5` becomes valid. The old overlapping history
must be folded into the donated owned assertion, not preserved as an
external frame across release.

## 2. Foreign completeness: invalid in both modes

Use active processors 1 and 2, distinct addresses `x` and `y`, and

```text
J = C(x,7)
P = emp
c = acquire(1); release(1)
Q = bar(2)
```

Required results:

```text
not Valid(ov, J, P, c, Q)
not Valid(dj, J, P, c, Q)
```

Fix the initial local resource to physically empty memory with **no marks**.
It satisfies `emp`. The free pool contains `x = 7`; the external frame has
one pending processor-2 write `y := 17`, no heap, no blocked bits, and no
marks. This is an admissible environment in both modes. Processor 1's whole
buffer is empty, so its acquire and subsequent release can occur while
the foreign write remains pending.

Use the actual no-flush execution, including the structural sequence step.
At each safety obligation choose the reflexive local future. The program
mark budget permits only mark 1 to be added. Pool marks cannot be imported,
and the structural step earns no mark. Thus no allowed local successor can
satisfy the active processor-2 barrier at termination.

The invalidity result must rule out every allowed successor witness for
this finite execution, not merely exhibit one badly chosen re-marking.
The acceptance theorem concerns semantic validity, which is stronger than
failure to derive the specification from a particular set of rules.

## 3. A private store while another thread holds the lock

Use two active processors, distinct addresses `x` and `z`, and `J = C(x,7)`.
The shared pool is empty because processor 1 holds the lock. Choose the
two owned resources to satisfy:

```text
P1 = lock(1) * C(x,7)
P2 = C(z,3)

c1 = skip
Q1 = P1

c2 = [z] := 9 on processor 2
Q2 = C(z,3) ; W_2(z,9)
```

Required positive targets are the two component specifications in `dj`
mode, plus a **common concrete machine witness** for their simultaneous
views. The first resource may have marks `{1}` and the second `{2}`.
They compose spatially, with empty buffers and whole blocked set `{2}`.
In the owner's view, the token is local. In the storing thread's view,
the same token and protected cell are external. Neither view has a free
invariant pool.

The witness must include the actual enabled processor-2 store, which
appends `(z,9)` to its buffer and leaves the lock held by processor 1.
`PrimitiveStore` permits issue while the processor is blocked. The owner
resource stays exactly fixed, the storing resource satisfies `Q2`, and
both successor views must be admissible. A proof based only on the storing
thread having no admissible environment fails this test.

The component validity targets require safety for every index, including
local flushing closure, not just the immediate postcondition. The owner
uses `skip` to isolate the held-by-another case without introducing a
release/restoration obligation. A parallel-composition rule and an
all-execution theorem for a larger critical section are later results;
this test must not presuppose that rule.

## Additional definition checks

Two diagnostics are already kernel-checked in
[LockRepresentation.v](../theories/LockRepresentation.v):

- **Singleton ambiguity:** free and held overlap, and the lock atom is
  equivalent to `emp`. A processor-domain or representation decision must
  be explicit before the predicate is implemented.
- **Split-token contexts:** on processors `{1,2,3}`, empty-memory resources
  blocking `{2}` and `{3}` are individually well formed and compose to a
  whole lock held by 1. Neither part is lock-complete. An actual
  `assert false` on 1 aborts in the whole state. The proposed environment
  must admit this context, so the local safety obligation can see the fault.

The second check adds a regression requirement without changing the three
requested targets: an incomplete local token is not a reason to exclude all
contexts, and it is not enough permission to release the complete lock.
These diagnostics do not define another validity predicate.
