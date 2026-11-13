# Proof work that would simplify and strengthen the paper

From the reviewer, after `review/lead-paper-check.md`, whose corrections are
all applied in `8fd1497`. Ian approved reopening the queue for the first
item and asked me to reread the paper for others. Each item below removes a
hedge from the paper or lets a section be stated more simply. They are
independent. State each target before proving it, as before, and report a
refutation as readily as a proof: several are my expectations, and those
have been wrong before.

The proof artifact the paper cites is `99b4052`. If these land, the paper
will cite the new commit.

## A. The two local errors, against the printed definitions

Table 1 of the paper marks two rows as checked only against an intermediate
interpretation. Re-prove both against the dissertation's own definitions.

1. **Flushing closure.** `pointwise_temporal_wand_not_flush_closed` uses
   `repaired_models`. State and prove the same failure for `models`, with
   the printed temporal composition and the printed flushing order of
   Definition 6. The argument turns on the completeness condition of
   temporal composition, which the repair did not change.
2. **Unlock.** `arbitrary_invariant_unlock_invalid` refutes
   `persistent_valid`. State and prove that
   `{lock_i} unlock_i {emp}` under invariant `false` is invalid for
   `valid_specification`.

## B. A mode-free presentation of the calculus

The paper has to introduce two modes to state two rules. I believe the
judgment can be presented with one mode and the original side condition.

1. **Mode elimination.** For a command containing no `unlock`, every
   disjoint-mode derivation can be replayed in overlap mode:

   ```text
   owned_derivation DJ P c Q  →  unlock_free c  →  owned_derivation OV P c Q
   ```

   by induction on the derivation, since UNLOCK cannot occur in it and
   every other rule exists at both modes.
2. **The original frame rule, derived.**

   ```text
   J ⊢ᴰᴶ {P} c {Q}     unlock_free c     mod(c) ∩ fv(R) = ∅
   ---------------------------------------------------------
   J ⊢ᴰᴶ {R ; P} c {R ; Q}
   ```

If both hold, the paper's main text will present a single judgment with
FRAME-TM carrying "c contains no unlock", which is the dissertation's rule
plus one side condition, and move the modes to the semantics section where
they explain why. Say whether `unlock_free` needs to look inside loops,
choices and parallel compositions in the obvious way, and whether anything
weaker suffices.

## C. Necessity of the restrictions

The paper currently says the repairs are sufficient. Four small results
would let it say which are necessary.

1. **UNLOCK cannot be overlap-valid when it donates.** If every model of
   `J` owns at least one cell, then no specification
   `{lock_i * A} unlock_i {B}` with a satisfiable precondition is valid in
   overlap mode. State the hypothesis on `J` however is cleanest. This
   replaces the paper's hedge that the trilemma "does not show that the
   particular restriction adopted is the weakest possible" with a theorem
   about this calculus.
2. **FRAME-TM cannot take a disjoint-mode premise.** A concrete instance:
   a disjoint-mode-valid specification and a frame `R` satisfying the
   variable condition, whose temporally framed conclusion is invalid in
   disjoint mode. The stale-value donation should supply it.
3. **LOCK is unsound for an all-processor invariant.** With `J` the printed
   `x ↦ 7`, which is outside the fragment, exhibit a derivation in
   `owned_derivation` whose conclusion is invalid, for example
   `{emp} lock_1; unlock_1 {bar(2)}`. This would show that soundness needs
   some restriction on `J`, and it turns the paper's "choice" label on the
   weakened cell into "forced".
4. **LOCK is unsound on one processor.** On a singleton domain with a
   one-cell invariant, exhibit a derivation whose conclusion is invalid;
   `lock_i; lock_i` is the obvious candidate. The existing singleton lemmas
   show the encoding is ambiguous; this would show the hypothesis is needed
   by the theorem, not only convenient for the proof.

For 3 and 4, an invalid `owned_valid` conclusion from an `owned_derivation`
is what is wanted, so that each is literally a counterexample to
`owned_calculus_sound` with one hypothesis dropped.

## D. Optional: each printed rule on its own

The paper says in prose that the printed safety predicate forgets the
invariant at acquisition, so INV cannot be justified from it, and that it
reads local states at full completeness, so FRAME-TM cannot either. Two
theorems would replace that prose, each a valid premise with an invalid
conclusion under the printed `valid_specification`:

1. INV alone.
2. FRAME-TM alone. The existing `private_temporal_frame_counterexample`
   has the right shape but is stated for `private_valid`.

These need premise validity for the printed predicate, which may be
awkward given the printed composition's failures. If either is costly, say
so and skip it; the paper can keep its prose.

## Order and check-ins

A and B first: A was promised, and B changes how the paper presents the
calculus. Then C. D only if cheap. Report A and B together, then C, and
stop to report at once if B fails, since the paper's structure depends on
it.
