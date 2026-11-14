#!/usr/bin/env python3
"""Stage-2 bounded tests of DaringCandidate.v, not a proof of its rules.

Read review/daring-lock-free-candidate.md for the statement fixed before
this search. Reuses the project's ordered composition and future model.
Expected counterexamples are results; a malformed search raises an error.
"""
from collections import Counter, deque
from dataclasses import asdict, replace
from functools import lru_cache
from itertools import product
import json

from search_frame_shape import Resource, EMPTY, compose, flushed, futures, stable, shuffles
from search_owned_frames import physical, residual_buffer


def cell(address, value, marks=3, size=3):
    return Resource(tuple(value if a == address else None for a in range(1, size + 1)), ((), ()), marks=marks)


def pending(actor, address, value, marks=0, size=3, copies=1):
    buffers = [(), ()]
    buffers[actor] = ((address, value),) * copies
    return Resource((None,) * size, tuple(buffers), marks=marks)


@lru_cache(None)
def worlds(pool, frame, local):
    if pool.blocked or frame.blocked or local.blocked or any(pool.buffers):
        return ()
    return tuple(w for c in compose("ov", frame, local) for w in compose("tm", pool, c))


@lru_cache(None)
def matches(pool, frame, local, whole):
    return any(physical(w) == physical(whole) for w in worlds(pool, frame, local))


@lru_cache(None)
def pool_flush(pool, actor, whole):
    address, value = whole.buffers[actor][0]
    if pool.heap[address - 1] is None:
        return pool
    heap = list(pool.heap)
    heap[address - 1] = value
    return replace(pool, heap=tuple(heap))


def update_ok(local, pool, successor, returned, kind, actor):
    earned = 1 << actor if kind == "fence" else 0
    return (not successor.marks & ~(local.marks | earned)
            and (successor.domain() | returned.domain()) <= (local.domain() | pool.domain())
            and (kind != "store" or returned == pool))


def _successors(pools, frame, local, pool, after, kind, actor):
    """All fixed-frame residuals within the old pool/local footprint.

    Buffer cancellation is exact, including duplicates. A new local heap
    can only contain the corresponding value of the physical final heap,
    since local is the last overriding component. Pool choices are the
    complete models of the explicitly chosen finite invariant.
    """
    buffers = tuple(residual_buffer(f, w) for f, w in zip(frame.buffers, after.buffers))
    if None in buffers:
        return
    allowed = local.domain() | pool.domain()
    heaps = tuple((None, value) if value is not None and a + 1 in allowed else (None,)
                  for a, value in enumerate(after.heap))
    earned = 1 << actor if kind == "fence" else 0
    for heap, marks, returned in product(product(*heaps), range(4), pools):
        if marks & ~(local.marks | earned):
            continue
        successor = Resource(heap, buffers, marks=marks)
        if (successor.well_formed() and update_ok(local, pool, successor, returned, kind, actor)
                and matches(returned, frame, successor, after)):
            yield successor, returned


def _flush_successors(pools, frame, local, pool, whole, actor):
    after = flushed(whole, actor)
    if after is None:
        return
    returned = pool_flush(pool, actor, whole)
    if returned not in pools:
        return
    ff = flushed(frame, actor)
    ll = flushed(local, actor)
    if ff is not None and matches(returned, ff, local, after):
        yield "frame", local, ff, returned
    if ll is not None and matches(returned, frame, ll, after):
        yield "local", ll, frame, returned


@lru_cache(None)
def successors(pools, frame, local, pool, after, kind, actor):
    return tuple(_successors(pools, frame, local, pool, after, kind, actor))

@lru_cache(None)
def flush_successors(pools, frame, local, pool, whole, actor):
    return tuple(_flush_successors(pools, frame, local, pool, whole, actor))


def read(whole, actor, address):
    for loc, value in reversed(whole.buffers[actor]):
        if loc == address:
            return value
    return whole.heap[address - 1]


def enqueue(whole, actor, address, value):
    buffers = list(whole.buffers)
    buffers[actor] += ((address, value),)
    return replace(whole, buffers=tuple(buffers))


# The small structural checker evaluates the stated step-indexed predicate.
# Stacks have registers 0,1. Formula tuples below use only emp, pure, cells,
# writes, conjunction, disjunction, spatial separation, and finite EX.
@lru_cache(None)
def spatial_factors(r):
    addresses = sorted(r.domain())
    answers = []
    for sides in product((0, 1), repeat=len(addresses)):
        own = dict(zip(addresses, sides))
        heaps = [tuple(v if own.get(a + 1) == side else None for a, v in enumerate(r.heap)) for side in (0, 1)]
        bufs = [tuple(tuple(w for w in b if own[w[0]] == side) for b in r.buffers) for side in (0, 1)]
        for lm, rm in product(range(4), repeat=2):
            if lm | rm != r.marks:
                continue
            left, right = Resource(heaps[0], bufs[0], marks=lm), Resource(heaps[1], bufs[1], marks=rm)
            if left.well_formed() and right.well_formed() and r in compose("sp", left, right):
                answers.append((left, right))
    return tuple(answers)


@lru_cache(None)
def holds(formula, stack, r):
    tag, *args = formula
    if tag == "emp":
        return not r.domain() and not r.blocked
    if tag == "true":
        return True
    if tag == "false":
        return False
    if tag == "eq":
        return stack[args[0]] == args[1]
    if tag == "cell":
        return r == cell(*args, marks=r.marks) and r.marks != 0
    if tag == "write":
        actor, address, value = args
        return (r == pending(actor, address, value, marks=r.marks)
                or (bool(r.marks & (1 << actor)) and r == cell(address, value, marks=r.marks)))
    if tag == "and":
        return all(holds(f, stack, r) for f in args)
    if tag == "or":
        return any(holds(f, stack, r) for f in args)
    if tag == "sp":
        return any(holds(args[0], stack, left) and holds(args[1], stack, right)
                   for left, right in spatial_factors(r))
    if tag == "exists":
        variable, body = args
        return any(holds(body, tuple(value if i == variable else v for i, v in enumerate(stack)), r)
                   for value in (-1, 0, 1))
    raise ValueError(formula)


HALT = ("skip",)


@lru_cache(None)
def events(command, stack, whole):
    """Return (aborts, ((kind, actor, next, stack_after, memory_after),...))."""
    tag, *args = command
    if tag == "skip":
        return False, ()
    if tag in ("seq", "par"):
        left, right = args
        if tag == "seq" and left == HALT:
            return False, (("ordinary", 0, right, stack, whole),)
        ab, es = events(left, stack, whole)
        out = [(k, a, (tag, nxt, right), st, w) for k, a, nxt, st, w in es]
        if tag == "par":
            if left == HALT:
                out.append(("ordinary", 0, right, stack, whole))
            if right == HALT:
                out.append(("ordinary", 0, left, stack, whole))
            ab2, es2 = events(right, stack, whole)
            ab |= ab2
            out += [(k, a, (tag, left, nxt), st, w) for k, a, nxt, st, w in es2]
        return ab, tuple(out)
    if tag == "choice":
        return False, tuple(("ordinary", 0, c, stack, whole) for c in args)
    if tag == "loop":
        return False, (("ordinary", 0, ("choice", HALT, ("seq", args[0], command)), stack, whole),)
    actor = args[0]
    result, after = stack, whole
    if tag in ("assume", "assert"):
        okay = args[1] is True or (args[1] is not False and stack[args[1][0]] == args[1][1])
        if not okay:
            return tag == "assert", ()
    elif tag == "assign":
        variable, value = args[1:]
        result = tuple(value if i == variable else v for i, v in enumerate(stack))
    elif tag == "load":
        variable, address = args[1:]
        value = read(whole, actor, address)
        if value is None:
            return True, ()
        result = tuple(value if i == variable else v for i, v in enumerate(stack))
    elif tag == "store":
        address, value = args[1:]
        if read(whole, actor, address) is None:
            return True, ()
        after = enqueue(whole, actor, address, value)
    elif tag == "fence":
        if whole.buffers[actor]:
            return False, ()
    else:
        raise ValueError(command)
    return False, ((tag, actor, HALT, result, after),)


# Complete buffer-free models of the tested invariants, not a sampled pool set.
EMP_POOL = replace(EMPTY, marks=3)
INVARIANTS = ((EMP_POOL,), (cell(1, 0),), (cell(1, 0), cell(1, 1)))
FRAMES = tuple([EMPTY, replace(EMPTY, marks=3), cell(1, 0), cell(1, 1)]
               + [pending(i, 1, v) for i, v in product(range(2), (0, 1))])
INPUTS = tuple([replace(EMPTY, marks=m) for m in range(4)]
               + [cell(1, v, m) for v, m in product((0, 1), (1, 2, 3))]
               + [pending(i, 1, v, m) for i, v, m in product(range(2), (0, 1), range(4))])
STACKS = tuple(product((-1, 0, 1), repeat=2))


@lru_cache(None)
def safe(pools, n, command, stack, local, post):
    if n == 0:
        return True
    for later in futures(local):
        if command == HALT and not holds(post, stack, later):
            return False
        for pool, frame in product(pools, FRAMES):
            for whole in worlds(pool, frame, later):
                aborts, transitions = events(command, stack, whole)
                if aborts:
                    return False
                for kind, actor, nxt, st, after in transitions:
                    if not any(safe(pools, n-1, nxt, st, local2, post)
                               for local2, pool2 in successors(pools, frame, later, pool, after, kind, actor)):
                        return False
                for actor in range(2):
                    if whole.buffers[actor] and not any(safe(pools, n-1, command, stack, local2, post)
                            for _, local2, frame2, pool2 in flush_successors(pools, frame, later, pool, whole, actor)):
                        return False
    return True


@lru_cache(None)
def valid(pools, n, pre, command, post):
    return all(safe(pools, n, command, stack, local, post)
               for stack, local in product(STACKS, INPUTS) if holds(pre, stack, local))


def inhabited(pre):
    return any(holds(pre, stack, local) for stack, local in product(STACKS, INPUTS))


def access_and_store():
    counts = Counter()
    findings = []
    # Real enabled load sees an earlier same-processor frame write.
    pool, frame, local = cell(1, 0), pending(0, 1, 1), EMPTY
    whole, = worlds(pool, frame, local)
    assert read(whole, 0, 1) == 1
    counts["load_wrong_value_witnesses"] += 1
    findings.append(dict(rule="ACCESS-load", reason="same-processor frame forwarding",
                         pool=asdict(pool), frame=asdict(frame), local=asdict(local), actual=1, promised=0))
    # Copying a cell into Q is an honest temporal private post: cell ; cell
    # equals the same cell on these models. Foreign pending writes prevent
    # ANY corresponding local-cell successor, even with a full mark budget.
    for kind in ("load", "assign", "assume", "assert", "fence"):
        primitive = {"load": ("load", 0, 0, 1), "assign": ("assign", 0, 0, 0),
                     "assume": ("assume", 0, True), "assert": ("assert", 0, True), "fence": ("fence", 0)}[kind]
        for marks in (1, 2, 3):
            c = cell(1, 0, marks)
            assert c in compose("tm", c, c)
            ab, ts = events(primitive, (0, 0), c)
            assert not ab and ts
            assert all(physical(after) == physical(c) for *_, after in ts)
            assert c in compose("tm", c, c)
            counts["private_cell_copy_model_checks"] += 1
        frame, local = pending(1, 1, 0), replace(EMPTY, marks=3)
        whole, = worlds(pool, frame, local)
        ab, ts = events(primitive, (0, 0), whole)
        assert not ab and len(ts) == 1
        tag, actor, _, st, after = ts[0]
        options = tuple(successors((pool,), frame, local, pool, after, tag, actor))
        assert not any(holds(("cell", 1, 0), st, successor) for successor, _ in options)
        counts["cell_copy_no_successor_checks"] += 1
        findings.append(dict(rule="ACCESS-"+kind, reason="frame pending write forbids copying pool cell into local",
                             frame_write_value=0, residuals_checked=len(options)))
    assert not holds(("cell", 1, 0), (0, 0), EMPTY)
    counts["skip_terminal_transfer_failures"] += 1
    findings.append(dict(rule="ACCESS-skip", reason="skip is terminal; emp does not satisfy cell"))
    # The invariant permits both values, hence is stable under this store.
    # A distinct processor already has a pending write to its shared address.
    pools = (cell(1, 0), cell(1, 1))
    pool, frame, local = pools[0], pending(1, 1, 1), EMPTY
    whole, = worlds(pool, frame, local)
    after = enqueue(whole, 0, 1, 1)
    options = tuple(successors(pools, frame, local, pool, after, "store", 0))
    assert not options
    counts["stable_store_no_successor_checks"] += 1
    findings.append(dict(rule="STORE", reason="two pending writers violate stable compatibility",
                         pool=asdict(pool), frame=asdict(frame), after=asdict(after)))
    # Same raw flush attribution works, but constant J is not preserved.
    pool, frame = cell(1, 0), pending(0, 1, 1)
    whole, = worlds(pool, frame, EMPTY)
    assert pool_flush(pool, 0, whole) == cell(1, 1)
    assert not tuple(flush_successors((pool,), frame, EMPTY, pool, whole, 0))
    assert not safe((pool,), 1, HALT, (0, 0), EMPTY, ("emp",))
    counts["skip_external_flush_failures"] += 1
    findings.append(dict(rule="SKIP", reason="an unconstrained frame flush need not preserve J"))
    return dict(counts=counts, findings=findings)


def algebra_search():
    counts = Counter()
    failure = None
    # Exhaustive 2 processors, 2 addresses, 2 values, buffer lengths 0..2.
    words = ((),) + tuple((w,) for w in product((1, 2), (0, 1)))
    words += tuple(product(tuple(product((1, 2), (0, 1))), repeat=2))
    for actor, fb, lb in product(range(2), words, words):
        fbuf, lbuf = [(), ()], [(), ()]
        fbuf[actor], lbuf[actor] = fb, lb
        frame, local = replace(EMPTY, buffers=tuple(fbuf)), replace(EMPTY, buffers=tuple(lbuf))
        for pool in (EMP_POOL, cell(1, 0), cell(1, 1), cell(2, 0), cell(2, 1)):
            for whole in worlds(pool, frame, local):
                counts["pool_first_worlds"] += 1
                restored = tuple(residual_buffer(f, w) for f, w in zip(frame.buffers, whole.buffers))
                assert restored == local.buffers
                counts["residual_cancellations"] += 1
                if whole.buffers[actor]:
                    returned = pool_flush(pool, actor, whole)
                    options = tuple(flush_successors((returned,), frame, local, pool, whole, actor))
                    counts["physical_flushes"] += 1
                    if not options and failure is None:
                        failure = dict(pool=asdict(pool), frame=asdict(frame), local=asdict(local), whole=asdict(whole))
                    if fb and lb and fb[0] == lb[0]:
                        counts["duplicate_heads"] += 1
                        assert options and all(side == "frame" for side, *_ in options)
    # Different processors and heap-containing components: focused exhaustive atoms.
    pieces = (EMPTY, cell(1, 0), cell(1, 1), cell(2, 0)) + tuple(
        pending(i, a, v) for i, a, v in product(range(2), (1, 2), (0, 1)))
    for pool, frame, local in product((EMP_POOL, cell(1, 0), cell(1, 1)), pieces, pieces):
        for whole in worlds(pool, frame, local):
            counts["heap_and_foreign_worlds"] += 1
            for actor in range(2):
                if whole.buffers[actor]:
                    counts["heap_and_foreign_flushes"] += 1
                    returned = pool_flush(pool, actor, whole)
                    if not tuple(flush_successors((returned,), frame, local, pool, whole, actor)) and failure is None:
                        failure = dict(pool=asdict(pool), frame=asdict(frame), local=asdict(local), whole=asdict(whole))
    return dict(counts=counts, counterexample=failure)


def reconstruction_search():
    counts = Counter()
    failures = {}
    pieces = (EMPTY, replace(EMPTY, marks=1), cell(1, 0, 1), cell(2, 0, 1)) + tuple(
        pending(i, a, v, marks=1) for i, a, v in product(range(2), (1, 2), (0, 1)))
    pools = (EMP_POOL, cell(1, 0), cell(1, 1))
    for pool, frame, retained, local in product(pools, pieces, pieces, pieces):
        for combined_local in compose("sp", retained, local):
            for whole in worlds(pool, frame, combined_local):
                counts["input_environments"] += 1
                groups = tuple(g for g in compose("ov", frame, retained) if matches(pool, g, local, whole))
                assert groups
                for grouped in groups:
                    for kind, actor, after in (("assume", 0, whole), ("store", 0, enqueue(whole, 0, 1, 1))):
                        if kind == "store" and read(whole, 0, 1) is None:
                            continue
                        for successor, returned in successors(pools, grouped, local, pool, after, kind, actor):
                            counts["successors_"+kind] += 1
                            sp = [big for big in compose("sp", retained, successor)
                                  if matches(returned, frame, big, after)
                                  and update_ok(combined_local, pool, big, returned, kind, actor)]
                            if not sp and "FRAME-SP" not in failures:
                                failures["FRAME-SP"] = dict(action=kind, pool=asdict(pool), frame=asdict(frame),
                                    retained=asdict(retained), local=asdict(local), successor=asdict(successor), returned=asdict(returned))
                            # Parallel also needs the other thread's view after this step.
                            parallel = [big for big in sp if any(matches(returned, g, retained, after)
                                        for g in compose("ov", frame, successor))]
                            if not parallel and "CONC" not in failures:
                                failures["CONC"] = dict(action=kind, pool=asdict(pool), frame=asdict(frame),
                                    retained=asdict(retained), local=asdict(local), successor=asdict(successor), returned=asdict(returned))
                            if any(frame.buffers) and frame.domain() & pool.domain():
                                counts["successors_with_pending_frame_on_pool"] += 1
    return dict(counts=counts, failures=failures,
                interpretation="Failures of sufficient reconstruction obligations, not by themselves rule counterexamples")


def structural_search():
    counts, failures = Counter(), []
    emp, true, zero, c0 = ("emp",), ("true",), ("eq", 0, 0), ("cell", 1, 0)
    base = [(emp, HALT, emp), (emp, ("assume", 0, True), emp),
            (emp, ("assign", 0, 0, 0), ("and", emp, zero)),
            (emp, ("fence", 0), emp), (c0, ("assume", 0, True), c0),
            (zero, ("assume", 0, True), zero), (true, HALT, true)]
    # Equal indices test same-index obligations; n=4 reaches the end of
    # two primitive steps plus their administrative sequence/parallel step.
    for pools, n in product((INVARIANTS[0], INVARIANTS[2]), (2, 4)):
        good = [(p, c, q) for p, c, q in base
                if inhabited(p) and valid(pools, n, p, c, q)]
        counts["inhabited_valid_base_triples"] += len(good)
        def check(rule, pre, command, post):
            if not inhabited(pre):
                counts[rule+"_uninhabited_skipped"] += 1
                return
            counts[rule] += 1
            if not valid(pools, n, pre, command, post):
                failures.append(dict(rule=rule, index=n, pool_values=[p.heap for p in pools],
                                     pre=pre, command=command, post=post))
        for p, c, q in good:
            # CONS: weakening to true; also identity entailments.
            check("CONS", p, c, ("true",))
            check("CONS", p, c, q)
            # A real finite existential: reg 1 is absent from J,c,q.
            if q not in (("eq", 1, 0),):
                check("EX", ("exists", 1, ("and", p, ("eq", 1, 0))), c, q)
            for r in (("emp",), ("cell", 1, 0)):
                check("FRAME-SP", ("sp", r, p), c, ("sp", r, q))
            if p == q:
                check("LOOP", p, ("loop", c), p)
            for p2, d, q2 in good:
                if c == d and q == q2:
                    check("DISJ", ("or", p, p2), c, q)
                if p == p2 and q == q2:
                    check("CHOICE", p, ("choice", c, d), q)
                if q == p2:
                    check("SEQ", p, ("seq", c, d), q2)
                # c and d here either preserve registers or assign only r0;
                # only use pure-free assertions and at most one assignment.
                if all(f[0] in ("emp", "true", "cell") for f in (p, q, p2, q2)) and not (c[0] == d[0] == "assign"):
                    check("CONC", ("sp", p, p2), ("par", c, d), ("sp", q, q2))
        safe.cache_clear()
        valid.cache_clear()
    return dict(counts=counts, failures=failures[:12], total_failures=len(failures),
                bounds=dict(processors=2, heap_addresses=1, values=[0, 1], stack_values=[-1, 0, 1],
                            input_resources=len(INPUTS), frames=len(FRAMES), indices=[2, 4]))


def ghost_search():
    # 1=f0,2=f1,3=w,4=t0,5=q0,6=p0,7=t1,8=q1,9=p1.
    size = 9
    def heap(entries, marks=3):
        return Resource(tuple(entries.get(a) for a in range(1, size+1)), ((), ()), marks=marks)
    g0 = ({5: 0, 1: 0}, {5: 0, 1: 1}, {4: 0, 1: 1})
    g1 = ({8: 0, 2: 0}, {8: 0, 2: 1}, {7: 0, 2: 1})
    model_entries = [{3: 0} | a | b for a, b in product(g0, g1)]
    model_entries += [{6: 0, 4: 0, 1: 1} | b for b in g1]
    model_entries += [{9: 0, 7: 0, 2: 1} | a for a in g0]
    pools = tuple(heap(e) for e in model_entries)
    assert len(set(pools)) == 15
    counts = Counter(invariant_heap_models=len(pools))
    for pool, address in product(pools, (1, 2)):
        changed = list(pool.heap)
        assert changed[address-1] is not None
        changed[address-1] = 1
        assert replace(pool, heap=tuple(changed)) in pools
        counts["store_stability_checks"] += 1
    private = heap({4: 0, 6: 0}, marks=1)
    pending_private, = compose("tm", private, pending(0, 1, 1, size=size))
    drained = flushed(pending_private, 0)
    bad = []
    for pool in pools:
        # All branches compose, including supposedly excluded ones.
        assert worlds(pool, replace(EMPTY, heap=(None,)*size), pending_private)
        counts["allowed_pre_fence_models"] += 1
        if 5 not in pool.domain() | drained.domain():
            counts["missing_q0_after_fence"] += 1
            bad.append(dict(pool=asdict(pool), local_after_flush=asdict(drained), required_new_address=5))
    return dict(counts=counts, counterexample=bad[0],
                interpretation="The proposed fence entailment cannot manufacture q0; temporal composition does not exclude duplicate ghost cells")


def dekker(fenced):
    # Direct physical reachability. PC 0 store, optional PC 1 fence, then load.
    program = ("store", "fence", "load") if fenced else ("store", "load")
    start = ((0, 0), (0, 0), ((), ()), (-1, -1))
    seen, todo, parent = {start}, deque([start]), {}
    terminal, bad = set(), None
    while todo:
        state = todo.popleft()
        pcs, heap, buffers, regs = state
        if all(pc == len(program) for pc in pcs):
            terminal.add(regs)
            if regs == (0, 0) and bad is None:
                bad = state
        successors_ = []
        for actor in range(2):
            if buffers[actor]:
                addr, val = buffers[actor][0]
                h, b = list(heap), list(buffers)
                h[addr], b[actor] = val, b[actor][1:]
                successors_.append((f"flush {actor}", (pcs, tuple(h), tuple(b), regs)))
            if pcs[actor] == len(program):
                continue
            op = program[pcs[actor]]
            p, b, r = list(pcs), list(buffers), list(regs)
            if op == "fence" and b[actor]:
                continue
            p[actor] += 1
            if op == "store":
                b[actor] += ((actor, 1),)
            elif op == "load":
                address = 1-actor
                r[actor] = next((v for a, v in reversed(b[actor]) if a == address), heap[address])
            successors_.append((f"{op} {actor}", (tuple(p), heap, tuple(b), tuple(r))))
        for label, target in successors_:
            if target not in seen:
                seen.add(target)
                parent[target] = state, label
                todo.append(target)
    trace = []
    if bad:
        while bad != start:
            bad, label = parent[bad]
            trace.append(label)
        trace.reverse()
    assert ((0, 0) not in terminal) == fenced
    return dict(fenced=fenced, reachable_states=len(seen), terminal_registers=sorted(terminal),
                zero_zero_trace=trace, aborts=0, scope="exhaustive for this finite constant-address machine program")


if __name__ == "__main__":
    for name, run in (("access_and_store", access_and_store), ("algebra", algebra_search),
                      ("reconstruction", reconstruction_search), ("structural", structural_search),
                      ("ghost_invariant", ghost_search), ("fenced_machine", lambda: dekker(True)),
                      ("unfenced_machine", lambda: dekker(False))):
        result = run()
        print(json.dumps(dict(search=name, **result), sort_keys=True), flush=True)
