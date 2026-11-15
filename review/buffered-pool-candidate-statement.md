# Second daring candidate: statement before search

Response to `reviewer-guidance-daring-2.md` at `dca2000`.
`theories/BufferedPoolCandidate.v` is the precise statement. Its rule and
adequacy definitions are propositions to test, not proved theorems.
No general proof is part of this checkpoint.

## Decisions and departures

The pool owns both shared heap cells and their pending writes. It remains
spatially separate from frame and local resources, including their buffer
address domains. The whole memory is lock free. Commands contain no lock
or unlock. Nothing changes in `owned_safe` or `owned_derivation`.

The intended new judgment uses **DisjointMode**: the frame and local
resource have disjoint address domains. Their composition is still the
existing repaired `#` relation, with the existing DJ condition. This is
an explicit choice where the guidance did not specify the mode. All
primitive steps may transfer ownership; an unframed premise alone might
not protect an overlapping external history from donation. The search
will also test the OV variant and report any concrete obstruction.
FRAME-TM is not proposed for this judgment.

The invariant fragment extends the existing guarded fragment with
`(e ↣ u) ; e ⇝_i v`, one write on a cell. The usual spatial, disjunctive,
existential and guarded-pure constructors remain. No new assertion atom
or new resource composition is introduced. This small fragment is enough
for the proposed Dekker invariant. Longer histories are deferred.

**The pool is always interpreted at full completeness.** Its buffers need
not be empty. No marks-insensitivity lemma is assumed. The search will
compare full, writer-only and foreign-only marks for pending and flushed
histories. If marks-insensitivity fails, that rejects such a lemma, not
this explicit full-mark interpretation. There is no implicit loan of the
pool's marks to the private resource.

A pending write atom can carry blocked bits in the existing semantics.
Thus membership in the extended fragment is not itself a proof of lock
freedom. Lock freedom is required of each whole environment and each
frameless input; spatial composition then forces every part to be
unblocked. This does not redefine the write atom.

## Updates, safety and adequacy

Program steps fix the exact external frame. Pool and local resource may
be repartitioned, including at a store. Their combined footprint cannot
grow. Local successor marks must come from the original **local** marks,
plus the acting processor at a fence. Full pool marks do not enter that
budget. The successor pool again satisfies J at full completeness.

A physical flush is attributed to exactly one component: pool, frame or
local. It takes an actual indexed flush of that component, fixing the
other two. A pool flush preserves its full mark set. A local or frame
flush adds only the flushing processor's mark. Successor decomposition
and J are checked again. Future-closure of assertions, not a separately
postulated stability condition on issued writes, is the proposed route
to preservation of J.

`buffered_safe` uses the old step-index pattern, including closure over
all local futures and fresh quantification of environments at each
recursive call. It additionally contains the explicit three-way
physical-flush clause. The terminal postcondition holds on the private
resource, independent of whether an environment exists.

Validity quantifies over all indices and all precondition models, and
requires lock-free syntax. Adequacy starts with `pool * local`, J and P,
and a lock-free whole memory. It concludes no abort on every finite
execution and a final `pool' * local'` satisfying J and Q on termination.
There is no leftover mode or external-frame premise. No two-processor
assumption is needed in the statement of this lock-free adequacy target;
that old assumption was about the lock encoding. The Dekker test itself
has two processors.

## The atomic premise and rules

`buffered_atomic_premise` quantifies over every stack, private model of P,
and full pool model of J, and every lock-free spatial composition of
them. The primitive cannot abort. Every actual program result must split
spatially into a full model of J and a private model of Q, respecting the
original local mark budget and the joint footprint bound. A disabled
fence has no result obligation; it is not treated as having executed.

This is a direct semantic premise. It is neither `owned_valid` nor an
existential witness for one chosen input split. It applies to store,
load, fence, assignment, assume and assert, excluding terminal skip.
The target atomic rule is from this premise to DJ validity.

Ordinary SKIP, SEQ, CONS, DISJ, CHOICE, LOOP, EX, FRAME-SP and CONC are
stated. EX retains freshness for J, command and post; CONC retains the
existing interference and invariant-variable conditions. Private cell
load/store, fence, substitution assignment, assume and assert are also
stated. Nothing here claims these propositions are established.

## Search plan

The new script will reuse the finite memory/ordered-buffer implementation,
without altering the withdrawn candidate's script or its results.

1. **Marks:** enumerate marked cell histories and their futures. Try
   non-store and fence attempts to export an unearned foreign mark from
   a full pool. Test the budget against the original local resource.
2. **Fences and foreign loads:** test own pending pool writes before and
   after a flush, and another processor's pending write with reads before
   and after flushing. Check that disabling a fence is distinct from
   aborting or proving its postcondition prematurely.
3. **Frame and parallel reconstruction:** enumerate framed environments,
   pool-changing successors, and both views after a sibling step. Compare
   DJ with OV. Separate failed sufficient lemmas from refuted rules.
4. **Buffers:** search cancellation with the frame and pool both fixed;
   separately test the joint pool/local residual with only the frame
   fixed. Do not claim local-buffer uniqueness across an ownership
   transfer. Search all three origins of a physical flush, including
   duplicate writes inside one owning component.
5. **Dekker:** use the 13 distinct addresses (two flags, ten per-thread
   tokens, one prize) and the exact three-stage G and winner branches in
   the guidance. Enumerate every full pool memory model, every nonempty
   private mark set, and each of the six primitive preconditions. For
   every enabled step, search all postcondition models and verify actual
   memory recomposition, J, footprint and mark budgets. Also check pool
   futures and the spatial exclusivity of the prize.

The small algebra tests use two processors, values 0/1, three addresses,
and component buffers of length at most two; the exact focused families,
counts and any stronger bounds will be recorded in the output/report.
The Dekker enumeration fixes all named ghost-cell values to 0 and checks
all flag/history shapes of those formulas. Stack variation is sampled
from -1/0/1; the guards, addresses and values do not depend on the incoming
registers. These are bounded tests, not proofs of the Rocq propositions.
