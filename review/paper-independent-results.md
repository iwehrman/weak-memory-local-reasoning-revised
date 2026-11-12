# Independent work alongside the 4B statement checkpoint

This records the batch at `26af676`. The later [independent batch](paper-independent-batch.md)
updates the remaining-queue statuses below and adds the writer's index.

The work queue permits priority 3 and priority 5 items 2–4 independently of
the assertion-system work. This batch completes **priority 5.2**, the
store/fence comparison, and the general domain-preservation lemma requested
in the earlier guidance for the Section 4.1 example. Neither depends on the
proposed 47-constructor assertion system or changes its pending statement.

## Fenced store: derived; unfenced flushed-cell contract: invalid

[OwnedFenceExamples.v](../theories/OwnedFenceExamples.v) proves

```text
J ⊢ᵐ {C(a,u)} [a] := v_i; fence_i {C(a,v)}
```

for either ownership mode, any invariant, any positive constant address,
any integer old/new values, and any active issuing processor. The theorem
is `owned_derive_store_fence_cell`, an actual `owned_derivation` tree.
`owned_store_fence_cell_valid` applies the existing soundness theorem under
its usual guarded-invariant and two-active-processors hypotheses.

The derivation uses the existing any-writer store rule, temporal framing of
FENCE, and the already checked drained-history entailment. A reusable helper,
`owned_derive_fence_after`, gives

```text
J ⊢ᵐ {P} fence_i {P ; B(i)}
```

for arbitrary assertions and annotations, in either mode. The disjoint
case follows by the existing mode-weakening rule. No constructor is added
to either proof system.

The same cell-to-cell specification **without** the fence is invalid in
both modes. `owned_plain_store_cell_invalid` proves this for every positive
constant address and every pair of integer values on the two-processor
domain, with invariant `emp`. `owned_plain_store_cell_not_derivable` then
rules out a derivation in the current program calculus.

This is failure of the flushed-cell postcondition, not an assertion that
ordinary stores are unsafe. The valid store postcondition retains a write
history. For the failed specification, start with a flushed cell, empty
pool and empty frame. A successful store can terminate with its write still
pending. The fixed empty frame and unchanged empty pool force that pending
write into any successor local resource; `C(a,v)` requires empty buffers,
so no alternative residual can satisfy it. This argument still works when
the stored value equals the old value.

`owned_store_fence_cell_witness` supplies an inhabited precondition and an
admissible free-lock environment in both modes, plus a complete four-step
execution: issue the write, finish the sequence prefix, flush the write,
then execute the fence. It checks that the write is pending after issue
and the final heap contains the new value with the issuing buffer empty.
This is an existence trace alongside general validity, not a termination
or fairness theorem. The result establishes the requested store rule, not
an embedding of all ordinary separation logic.

## Exact preservation of the machine's address domain

[ExecutionDomain.v](../theories/ExecutionDomain.v) strengthens the existing
subset results to equality:

```text
execution active n command s initial next t final
  → ∀a. memory_domain final a ↔ memory_domain initial a
```

`execution_preserves_domain` is the exact-length execution result;
`steps_preserve_domain` is the reflexive-transitive version. Supporting
theorems cover a single instruction, machine step and flush. They have no
assertion, invariant, safety, well-formedness, finiteness or processor-count
hypothesis.

Here the domain is the union of heap addresses and addresses in every
buffer. It is not a claim that the heap's domain alone is fixed: flushing
may move an address from a buffer into the heap. Stores can append only at
an address already readable by their processor; flushes retain an address
by installing the buffered write in the heap. The other transitions change
registers, control flow or lock bits without changing this domain.

This is the machine-level prerequisite requested for proving that the
message-passing example cannot lose its original data cell. It does not
yet prove the example, token erasure or a general extra-cell erasure result.

## Remaining queue and review boundary

| Work | Current status / dependency |
| --- | --- |
| 4A algebra audit; units; own-buffered-write load; original-model refutations requested after 4A | Complete |
| 4B assertion rules | Statement and type checked; its soundness proof is next after the statement check-in |
| 4C one-item container using assertion derivations for all entailments | Follows 4B soundness |
| Priority 1: original message-passing example | Design recorded; domain-preservation prerequisite now proved; program derivation and token erasure remain after 4C |
| Priority 2: derived named locks and producer/consumer mailbox | Design and theorem checkpoint still required; follows the assertion system and earlier example |
| Priority 3.1: printed SHARE counterexample and restricted SHARE | Independent; open |
| Priority 3.2: surviving assertion laws | Covered by the accepted audit and existing adjunction/flushing-closure proofs |
| Priority 3.3: dissertation's derived/alternative program rules | Independent classification still open |
| Priority 3.4–5: original-abbreviation review counterexamples in the audited build | Independent; open |
| Priority 3.6–7: fenced Dekker scope and consolidated theorem/repair index | Independent; open |
| Priority 5.2: store/fence comparison | Complete in this batch |
| Priority 5.3: frame property with one common spatial/temporal split | Independent investigation; state and search the lemma before proving it |
| Priority 5.4: transfer the FRAME-STM counterexample to the printed calculus | Independent; open |

The independent items can proceed without selecting different assertion
rules or changing semantics. SHARE and common-split framing remain
substantive proof investigations; their placement in this column is not a
prediction that their proposed statements hold. A failed rule or a repair
requiring new semantic assumptions still gets reported at once.

The useful next independent batch is to classify the original derived
program rules and bring the review's original-abbreviation counterexamples
into the checked build. The index can then record their final theorem
names. The main 4B/4C sequence remains at its agreed statement checkpoint.

## Verification

`make check` passes with **863 audited declarations closed**, including all
16 new lemmas/theorems in these two files. No axioms or admitted proofs were
added. The existing assertion interpretation, program rules, safety
predicate, standing hypotheses and pending 4B proposal are unchanged.
