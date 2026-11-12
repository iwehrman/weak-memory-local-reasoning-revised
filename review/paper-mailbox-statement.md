# Priority 2B: buffered contracts before the region client

Part A is checked at `853f731`. The plain named-lock contracts deliberately
forget draining information. Before the arbitrary-length client, prove
the following stronger *derived* contracts for the same implementations:

```text
J ⊢ᴰᴶ {R} acquire_named(l,i,x) {I_l * (R ; bar(i))}

A ; bar(i) ⊢ₐ I_l       I_l * I_l ⊢ₐ false
------------------------------------------------
J ⊢ᴰᴶ {A} release_named(l,i) {emp}
```

The acquire scratch variable is fresh for `J` and `R`; the selected lock
belongs to the finite family. These are assertion-proof premises and
existing variable conditions, not new semantic validity assumptions.
Soundness continues to use the same two standing hypotheses.

The intended proof keeps `R` inside the physical release premise. That
premise is `payload ; bar(i)`, so barrier distribution completes the acting
processor's retained writes. A failed acquire attempt can forget the new
barrier and retry with `R`; the successful attempt retains it in the
postcondition. This does not temporally frame an entire command containing
a release. For buffered named release, complete `A` in the physical release
premise, then use the existing exclusivity certificate to reject the
already-free named-lock branch.

Screen these contracts on both actors, pending/flushed retained writes,
foreign pending writes, and the two flag branches before general proofs.
If they fail or require a genuinely stronger condition, stop and report.

The client target remains the part-B design: arbitrary-length message
cells, producer ordinary stores without a fence, retrying consumer,
consumer ownership and loaded values, and an unrelated third-processor
write pending in a checked trace. The message cell product and its buffered
history are finite Rocq families. The mailbox invariant always owns its
flag, giving the exclusivity certificate even for length zero.

Producer use: fill the message, acquire with its history as `R`, complete
that history using the stronger postcondition, set the mailbox full, and
use buffered named release. Consumer use: acquire and inspect the mailbox,
retry if empty; otherwise retain the message spatially, set the mailbox
empty, use buffered named release, and read the message privately. No
additional fence or physical-lock callback is planned.

These are targets, not completed results. The assertion and program
constructor counts remain 47 and 21 unless a separately proved assertion
rule is needed and reported, as permitted by the queue.
