# Independent queue 5.3: a common spatial/temporal split

This states the target before the bounded search and general proof. It does
not propose an assertion constructor or reinstate FRAME-STM.

Given the **same three resources** `retained`, `local`, `big`, assume both
`spatial retained local big` and `repaired_temporal retained local big`.
The target is a same-index framing lemma for `owned_safe`, in either mode:

```text
invariant_fragment J
owned_safe mode J n c s local Q
mod(c) ∩ fv(R) = ∅
retained ⊨ R
spatial retained local big
repaired_temporal retained local big
----------------------------------------------------
owned_safe mode J n c s big (R ⋉ Q)
```

The proof must maintain a common split at each successor, not merely prove
the two postcondition conjuncts with unrelated witnesses. A separate
reconstruction lemma will expose this guarantee. Future closure must also
split every generalized future using common witnesses, including mark-only
futures and local flushes. The principal requested case is disjoint mode
across release; the intended statement does not syntactically exclude any
command. The fragment assumption is already the hypothesis of temporal
reconstruction. No processor-count assumption is expected here.

The precondition is a resource-level hypothesis. An assertion `R ⋉ P`
alone does **not** provide it, because its conjuncts can have different
witnesses. Thus this result would not contradict the checked FRAME-STM
counterexample or by itself add a usable assertion-level frame rule.

Before the proof, run `scripts/search_common_split.py`: two processors,
three addresses, values 0/1, the existing empty/one-cell pool family,
all mark combinations in focused families, 4,000 seeded samples, and a
focused held-lock/release family with retained and local foreign writes.
Check common future splitting, unframing, and reconstruction after every
bounded admissible successor. Include assume, store, fence, acquisition
and release; report action counts and any counterexample. As elsewhere,
the finite search is screening; Rocq is authoritative.

## Result

The search found no counterexample. The general theorem and enabled release
example are now proved; see [the batched results](paper-independent-batch.md#3-common-split-framing-succeeds-including-release).
The stated resource-level scope and assertion grammar are unchanged.
