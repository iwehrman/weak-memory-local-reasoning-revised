# Checkpoint 3 — statements before the search

This checkpoint tests resource lemmas, without introducing a safety predicate.
Write `T(a,b,c)` for `repaired_temporal active a b c`, and `O(a,b,c)` for
`repaired_spatiotemporal active a b c` (the repaired `#`). All resources are
well-formed generalized memories, including their completeness marks.
`a ->* b` means the existing `resource_future`: marks may grow and buffers
may undergo finitely many enabled FIFO flushes. It is not a program step.

## Temporal-only baseline

The initial regrouping is ordinary temporal associativity:

```text
T(R,P,RP) and T(F,RP,W)
  implies exists G, T(F,R,G) and T(G,P,W).
```

The proposed residual lemma is:

```text
T(F,R,G), G ->* G', T(G',P',W')
  implies exists F',R',RP',
    F ->* F' and R ->* R'
    and T(F',R',G') and T(R',P',RP') and T(F',RP',W').
```

This quantifies over one owned resource `P'`, not protected/private assertion
slots. No footprint or program-step premise is needed for this algebraic
baseline. It is the decomposition-and-reassociation part of the existing
`separated_safe_temporal_frame` proof, not a claim that its full safety
theorem transfers unchanged. In particular, it does not justify framing
over ownership release.

## First generalization: external `#`, internal `;`

Test the analogous claim with `O` outside and `T` inside:

```text
T(R,P,RP), O(F,RP,W), O(F,R,G), O(G,P,W),
G ->* G', O(G',P',W')
  implies exists F',R',RP',
    F ->* F' and R ->* R'
    and O(F',R',G') and T(R',P',RP') and O(F',RP',W').
```

For the operational search, also require:

- an actual assume-true, store, FIFO flush, or acquire step of the whole
  machine from the initial to final underlying memory;
- an initially buffer-free, lock-free shared pool spatially disjoint from
  `W`; the pool is empty except in acquisition cases, where it is one fresh
  cell and is transferred into the owned resource;
- the final local/pool footprint is included in the initial local/pool
  footprint, excluding the retained frame `R` and external frame `F`;
- lock acquisition requires the acquiring processor's whole buffer empty,
  returns the lock token in `P'`, and gives `P'` only its old marks plus that
  processor's mark. Other tested local marks do not gain unrelated marks.

This is the overlap-permitting (`ov`) case needed for temporal framing;
there is no extra `dom(F) disjoint dom(P)` premise. The `dj` case would impose
that disjointness. No new mode-indexed validity definition is being made.

The key quantifier is **every residual decomposition satisfying these
premises**, not merely the residual constructed by a particular primitive
proof. The search must not silently replace that claim by the weaker one.
The internal spatial/strong-temporal cases are later obligations; passing
the temporal baseline alone does not establish them.

## Scope of the bounded search

Use two active processors and two addresses for the overlapping-buffer
family, with a third fresh address for the acquisition pool. Values are 0
and 1. Initially `F`, `R`, and `P` each have one pending write on the same
processor; `F` and `P` target `x`, and `R` targets distinct `y`. `F` also has
one heap cell at `x`. Vary the values and well-formed marks. Both choices of
processor and both address orders are included.

Enumerate every composition and finite generalized future in this family.
For each actual step, enumerate all residual local heaps that can yield the
final heap and all residual buffers obtained as subsequences of the final
buffers, subject to the footprint and local-mark restrictions above. Check
all possible future splits in the conclusion. This is a bounded family,
not exhaustive enumeration of all small machines or a proof of a rule.

Acquisition uses the other processor, whose buffer is empty, and a pool
cell disjoint from both frames. The largest whole buffer has four writes
(after a store); acquiring changes the local footprint without flushing the
other processor's buffer. A search failure must be reproduced against the
Rocq definitions before being called a checked counterexample.

## Checkpoint-2 review qualifications

The pool's full mark set is a convention **for fragment satisfaction among
nonempty mark sets**. Completeness still affects temporal composition with
other resources; the re-marking theorem does not erase that role. Also, the
fragment has no recursive predicates: the container test describes a fixed
number of cells, not an arbitrarily large heap container. The previous
foreign-barrier rejection was a concrete example, not a stated general
theorem.
