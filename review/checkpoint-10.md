# Checkpoint 10 — container derivation and complete trace

**The container example is proved for the unchanged `owned_valid`.** It
acquires the invariant, removes its item, releases, writes the item
privately, reacquires, and returns the item. A checked 24-step execution
starts with a free lock and a nonempty invariant pool and keeps processor
2's foreign write pending throughout.

No FRAME-STM, new side condition, extra fence instruction, invariant-fragment
change, assertion-interpretation change, or new safety/validity predicate
was needed. The general EX and SHARE rules remain unproved. This is the
requested check-in after the container, before the derivation system.

## Exact example and result

Use the existing writer-existential cell `C(a,v) = writer_points_to a v`.
The example has two processors, three distinct constant addresses
`f = 1`, `x = 2`, `y = 3`, and one destination register `r = 0`.

```text
X = ∃v. C(x,v)
J = C(f,0) ∨ (C(f,1) * X)
R = y ↦₂ 17

acquire(1);
r := [f]₁; assume(r = 1);
[f] := 0₁;
release(1);
[x] := 9₁;
acquire(1);
r := [f]₁; assume(r = 0);
[f] := 1₁;
release(1)
```

[`owned_container_valid`](../theories/OwnedContainer.v) proves
`validᵈʲ J {R} container_program {R}` for **all** satisfying stacks and
resources, all safety indices, and every admissible environment. The core
theorem is `container_core_valid : validᵈʲ J {emp} c {emp}`.

This formalizes the selected branches of the review's one-item container
example. A false `assume` waits; this is a safety/partial-correctness result,
not a terminating implementation of a retrying container API. The concrete
execution below takes both assumptions successfully. The invariant uses
the unchanged fragment, including its original existential over the item's
value. It is nonempty in both the empty and full branches, because the flag
cell remains allocated.

## The foreign frame is cheaper than anticipated

The review predicted that `R` would need to appear by hand in every unlock
premise because temporal framing cannot cross release. In this example,
**one application of FRAME-SP frames the entire core program**, including
both releases:

```text
{emp} c {emp}
---------------- FRAME-SP
{R * emp} c {R * emp}
```

The spatial unit entailments give `{R} c {R}`. `R` has no free register, so
the usual frame-variable condition is immediate. Its disjointness from the
pool is supplied by the existing environment definition; this is not a new
Hoare-rule condition. The initial witness shows that this framing accepts
the intended pending write at `y`.

Thus there is no repeated manual threading of the foreign write. This does
not recover temporal framing across release, or retain overlapping foreign
history: it uses the spatial rule precisely because this write is unrelated
to the container's cells.

## Where temporal framing is essential to this derivation

Let `H(a,v) = (∃u. C(a,u)) ; (a ↦₁ v)`. The private store produces
`H(x,9)`, which permits its write to remain buffered. On the second
acquisition, FRAME-TM gives

```text
H(x,9) ; ((lock₁ * J) ; bar(1)).
```

The general LOCK rule and this framed acquisition are valid in overlap
mode; the established mode-weakening theorem then supplies disjoint-mode
validity for sequencing with releases. No temporal frame is applied across
a release.

`container_reacquire_entails` uses the actual acquisition barrier to drain
the private history and obtain the two flag cases needed by the load. In
the selected `f = 0` case, the thread retains `C(x,9)`. The other case is
kept until the load/assume eliminates it; the proof does not silently assume
that branch impossible.

This is the longest example-specific entailment, about 50 lines. It
reconstructs the spatial cell split from the finite heap shape. It earns no
foreign mark. The checked regression `owned_container_reacquire_waits`
also shows that the lock instruction cannot execute while the private write
is still buffered.

## Ownership and release obligations

These are the main core assertions, with the outer spatial frame `R`
omitted for readability:

| Point | Assertion |
| --- | --- |
| Initial | `emp` |
| First load and successful `assume(r=1)` | `lock₁ * (C(f,1) * X)` |
| Store `f := 0` | `lock₁ * (H(f,0) * X)` |
| First release | `X` |
| Private store `x := 9` | `H(x,9)` |
| Second load and successful `assume(r=0)` | `lock₁ * (C(f,0) * C(x,9))` |
| Store `f := 1` | `lock₁ * (H(f,1) * C(x,9))` |
| Final release | `emp` |

The two UNLOCK premises are proved as entailments:

```text
(H(f,0) * X) ; bar(1)       ⊨ J * X
(H(f,1) * C(x,9)) ; bar(1)  ⊨ J * emp
```

`container_barrier_spatial` distributes the earned barrier across spatial
components. `container_history_complete` reduces a drained history to its
current cell. The other component is retained at the first release and
donated at the second. The helper for removing a barrier suffix reuses the
existing wand-free result; every assertion used here is wand-free. This
does not restrict any previously proved rule.

The heap instructions use the checkpoint-9 any-writer cell rules plus
spatial framing and consequence. `container_store_some_valid` handles the
unknown old private value by unpacking its existential satisfaction witness
and applying the already proved constant-value rule for that value. It
does not assume or add a general EX rule.

## Entailment cost and recurring patterns

Counting **nonidentity entailments at rule premises**, the factored source
has **16 obligations**: 14 premises at its ten CONSEQUENCE applications,
plus two UNLOCK premises. Six other CONSEQUENCE premises are identities.
These counts exclude the internal resource-algebra rewrites used to prove
an entailment.

Expanding the reused helpers for this particular program gives **28
nonidentity entailment instances**:

| Application | Uses | Nonidentity premises per use | Instances |
| --- | ---: | ---: | ---: |
| Read a flag cell with a lock and spatial tail | 4 | 2 | 8 |
| Inject each load result into the branch disjunction | 4 | 1 | 4 |
| Filter the disjunction through an assumption | 2 | 1 | 2 |
| Forget the old cell value in a store history | 3 | 1 | 3 |
| Spatially frame each flag store, then reassociate | 2 | 2 | 4 |
| Normalize the first acquisition | 1 | 1 | 1 |
| Introduce the temporal unit and normalize reacquisition | 1 | 2 | 2 |
| Introduce and eliminate the outer spatial unit | 1 | 2 | 2 |
| Restore the invariant at release | 2 | 1 | 2 |
| **Total** | | | **28** |

The main candidates for reusable derived rules are:

- **Framed cell access:** spatial rearrangement recurs at both flag reads
  and both flag stores; extracting the pure result recurs at the reads.
- **Load-and-select:** the same two-case load proof serves both assumptions.
- **History completion at release:** barrier distribution and history
  collapse serve both unlock premises; drained-history normalization also
  serves reacquisition.
- **Routine assertion algebra:** spatial units, associativity, commutativity,
  connective monotonicity, and existential introduction need not be reproved
  in later clients.

The explicit proof cost is real, mostly in semantic assertion reasoning.
The missing FRAME-STM does not require a new program instruction or a
stronger precondition in this example. Spatial framing removes the predicted
cost of threading the unrelated foreign write.

## Nonvacuity, execution, and verification

[`OwnedContainerTrace.v`](../theories/OwnedContainerTrace.v) establishes:

- `owned_container_initial`: an inhabited precondition, an admissible empty
  external frame, a free lock, and a fully marked invariant pool containing
  `f = 1` and `x = 7`. The local buffer of processor 2 contains `y := 17`.
- `owned_container_trace`: a **24-step** complete execution. Only processor
  1 flushes: first `f := 0`, then the private `x := 9` before reacquisition,
  and finally `f := 1` before the last release. There is no fence instruction.
- `owned_container_foreign_pending_throughout`: processor 2's buffer is
  `[(y,17)]` in every named memory state of that trace. Intermediate load,
  assume and sequencing steps leave memory unchanged.
- `owned_container_final_contents`: final heap `f = 1`, `x = 9`; processor
  1's buffer empty; processor 2's write still pending; lock free.
- `owned_container_all_runs_safe`: the general validity theorem instantiated
  through adequacy for every finite execution from this concrete start.
  Other executions may flush the foreign write; the unchanged write atom
  allows that. The pending-throughout result is an existence result for the
  displayed execution, not a claim about every schedule.

`make check` passes with **626** audited declarations closed under the global
context, including 46 new declarations. No axioms or admitted proofs were
added. The three new modules contain the reusable entailments, the rule-based
derivation, and the initial/trace/adequacy checks separately.

## Next boundary

The example is complete. The remaining work is to settle the intended scope
of EX and SHARE, define the mode-tracking derivation system, and prove
soundness by induction followed by adequacy. No general EX or SHARE result
and no calculus-level soundness theorem is claimed at this checkpoint.
