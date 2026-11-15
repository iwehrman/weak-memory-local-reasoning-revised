#!/usr/bin/env python3
"""Second daring candidate: finite searches, not general soundness proofs.

Statement: review/buffered-pool-candidate-statement.md / BufferedPoolCandidate.v.
Only memory composition/futures and the physical primitive interpreter are
reused. No environment or safety definition from the withdrawn candidate
is used here. Script processors 0/1 mean Rocq processors 1/2.
"""
from collections import Counter
from dataclasses import asdict, replace
from functools import lru_cache
from itertools import product
import json

from search_frame_shape import Resource, compose, flushed, futures
from search_owned_frames import physical, residual_buffer
from search_daring_rules import cell, pending, read, enqueue, events, HALT


def empty(size=3, marks=0):
    return Resource((None,) * size, ((), ()), marks=marks)


def heap_resource(entries, marks=3, size=3):
    return Resource(tuple(entries.get(a) for a in range(1, size + 1)), ((), ()), marks=marks)


def history_models(address, old, actor, value, marks, size=3):
    if not marks:
        return ()
    buffered = enqueue(cell(address, old, marks, size), actor, address, value)
    return (buffered,) + ((cell(address, value, marks, size),) if marks & (1 << actor) else ())


@lru_cache(None)
def worlds(mode, pool, frame, local):
    if pool.blocked or frame.blocked or local.blocked or pool.marks != 3:
        return ()
    if mode == "dj" and frame.domain() & local.domain():
        return ()
    return tuple(w for combined in compose("ov", frame, local)
                 for w in compose("sp", pool, combined))


@lru_cache(None)
def matches(mode, pool, frame, local, whole):
    return any(physical(w) == physical(whole) for w in worlds(mode, pool, frame, local))


def update_ok(local, pool, successor, returned, kind, actor):
    earned = (1 << actor) if kind == "fence" else 0
    return ((successor.domain() | returned.domain()) <= (local.domain() | pool.domain())
            and not successor.marks & ~(local.marks | earned))


@lru_cache(None)
def splits(joint, local_budget):
    """Every spatial address split, canonical full pool and all legal private marks.

    All copies of an address, in the heap and on any buffer, go together.
    Private/pool buffer order is inherited from the joint buffer.
    """
    out = []
    addresses = sorted(joint.domain())
    for owners in product(("pool", "local"), repeat=len(addresses)):
        own = dict(zip(addresses, owners))
        heaps = [tuple(v if own.get(a + 1) == side else None for a, v in enumerate(joint.heap))
                 for side in ("pool", "local")]
        buffers = [tuple(tuple(w for w in b if own[w[0]] == side) for b in joint.buffers)
                   for side in ("pool", "local")]
        pool = Resource(heaps[0], buffers[0], marks=3)
        for marks in range(4):
            if marks & ~local_budget:
                continue
            local = Resource(heaps[1], buffers[1], marks=marks)
            if local.well_formed():
                assert any(physical(w) == physical(joint) for w in compose("sp", pool, local))
                out.append((local, pool))
    return tuple(out)


@lru_cache(None)
def successors(mode, frame, local, pool, after, kind, actor):
    """Enumerate all permitted residuals, without imposing a particular J/Q.

    With a fixed frame, buffers of the JOINT pool/local residual cancel.
    With overlap, a frame heap may supply a cell absent from that residual;
    enumerate both possibilities. In DJ that optional case is excluded by
    the input footprint bound. Never infer local-buffer uniqueness while
    the pool itself is being repartitioned.
    """
    buffers = tuple(residual_buffer(f, w) for f, w in zip(frame.buffers, after.buffers))
    if None in buffers:
        return ()
    allowed = local.domain() | pool.domain()
    if any(a not in allowed for b in buffers for a, _ in b):
        return ()
    options = []
    for a, v in enumerate(after.heap, 1):
        if a not in allowed:
            options.append((None,))
        elif v is not None and frame.heap[a-1] is not None:
            options.append((None, v))
        else:
            options.append((v,))
    budget = local.marks | ((1 << actor) if kind == "fence" else 0)
    out = []
    for heap in product(*options):
        joint = Resource(heap, buffers, marks=3)
        for successor, returned in splits(joint, budget):
            if update_ok(local, pool, successor, returned, kind, actor) and matches(mode, returned, frame, successor, after):
                out.append((successor, returned))
    return tuple(out)


@lru_cache(None)
def flush_choices(mode, pool, frame, local, whole, actor):
    after = flushed(whole, actor)
    if after is None:
        return ()
    out = []
    for side, component in (("pool", pool), ("frame", frame), ("local", local)):
        changed = flushed(component, actor)
        if changed is None:
            continue
        pp, ff, ll = (changed, frame, local) if side == "pool" else (
            (pool, changed, local) if side == "frame" else (pool, frame, changed))
        if matches(mode, pp, ff, ll, after):
            out.append((side, pp, ff, ll))
    return tuple(out)


def marks_search():
    counts, remarks = Counter(), []
    for actor, old, value, marks in product(range(2), (0, 1), (0, 1), (1, 2, 3)):
        for resource in history_models(1, old, actor, value, marks):
            counts["history_models"] += 1
            for later in futures(resource):
                counts["history_future_checks"] += 1
                assert later in history_models(1, old, actor, value, later.marks)
            for new_marks in (1, 2, 3):
                remarked = replace(resource, marks=new_marks)
                counts["remark_checks"] += 1
                if remarked not in history_models(1, old, actor, value, new_marks):
                    counts["remark_failures"] += 1
                    if not remarks and old != value and marks == 3:
                        remarks.append(dict(actor=actor, old=old, value=value, before=asdict(resource), after=asdict(remarked)))
    # Empty private input is allowed to have no marks. Full pool marks must
    # NOT be counted in the budget for a private barrier postcondition.
    for actor, kind, before, after in product(range(2), ("ordinary", "fence"), range(4), range(4)):
        pool = cell(1, 0)
        original, successor = empty(marks=before), empty(marks=after)
        earned = 1 << actor if kind == "fence" else 0
        allowed = update_ok(original, pool, successor, pool, kind, actor)
        counts["mark_budget_checks"] += 1
        assert allowed == (after & ~(before | earned) == 0)
        if not before and after & (1 << (1-actor)):
            assert not allowed
            counts["unearned_foreign_barriers_rejected"] += 1
        if not before and after == (1 << actor) and kind == "fence":
            assert allowed
            counts["earned_own_barriers_allowed"] += 1
    for actor, old, value in product(range(2), (0, 1), (0, 1)):
        for pool in history_models(1, old, actor, value, 3):
            for later in futures(pool):
                counts["full_pool_future_checks"] += 1
                assert later.marks == 3 and later in history_models(1, old, actor, value, 3)
    return dict(counts=counts, remark_counterexample=remarks[0],
                interpretation="Arbitrary re-marking fails; the candidate uses full pool marks throughout")


def fence_and_load_search():
    counts = Counter()
    for writer, old, value in product(range(2), (0, 1), (0, 1)):
        pool = history_models(1, old, writer, value, 3)[0]
        after = flushed(pool, writer)
        for marks, stack in product(range(4), product((-1, 0, 1), repeat=2)):
            local = empty(marks=marks)
            whole, = worlds("dj", pool, empty(), local)
            aborts, steps = events(("fence", writer), stack, whole)
            counts["own_pending_fences"] += 1
            assert not aborts and not steps
            drained, = worlds("dj", after, empty(), local)
            aborts, steps = events(("fence", writer), stack, drained)
            counts["own_drained_fences"] += 1
            assert not aborts and len(steps) == 1
            other = 1-writer
            ab, foreign_fence = events(("fence", other), stack, whole)
            assert not ab and len(foreign_fence) == 1
            counts["foreign_pending_fences_enabled"] += 1
            for memory, expected in ((whole, old), (drained, value)):
                ab, loads = events(("load", other, other, 1), stack, memory)
                counts["foreign_loads"] += 1
                assert not ab and len(loads) == 1
                assert loads[0][3][other] == expected
                assert loads[0][3][other] in (old, value)
            counts["own_forwarding_reads"] += 1
            assert read(whole, writer, 1) == value
    return dict(counts=counts, counterexample=None)


def overlap_diagnostic():
    # Honest one-step ownership swap, using the N3-style two-cell invariant.
    pools = (cell(1, 0), cell(2, 0))
    counts = Counter()
    for marks in (1, 2, 3):
        local = cell(2, 0, marks)
        for pool in pools:
            for joint in compose("sp", pool, local):
                counts["honest_frameless_inputs"] += 1
                ab, steps = events(("assume", 0, True), (0, 0), joint)
                assert not ab and len(steps) == 1
                good = [(ll, pp) for ll, pp in successors("dj", empty(), local, pool, joint, "ordinary", 0)
                        if pp in pools and ll == cell(1, 0, ll.marks) and ll.marks]
                assert good
                counts["honest_frameless_successors"] += len(good)
    pool, frame, local = pools[0], cell(2, 0, 1), cell(2, 0, 1)
    whole, = worlds("ov", pool, frame, local)
    good = [(ll, pp) for ll, pp in successors("ov", frame, local, pool, whole, "ordinary", 0)
            if pp in pools and ll == cell(1, 0, ll.marks) and ll.marks]
    assert not good and not worlds("dj", pool, frame, local)
    return dict(counts=counts, overlap_counterexample=dict(pool=asdict(pool), frame=asdict(frame), local=asdict(local)),
                conclusion="Unframed ownership-transfer premise fails for OV; DJ excludes this environment")


# Dekker addresses: f0,f1,w,a0,b0,q0,t0,p0,a1,b1,q1,t1,p1.
N = 13
FLAGS = (1, 2)
PRIZE = 3
TOKENS = ({"a": 4, "b": 5, "q": 6, "t": 7, "p": 8},
          {"a": 9, "b": 10, "q": 11, "t": 12, "p": 13})


def ghost_cells(addresses, marks):
    return heap_resource({a: 0 for a in addresses}, marks, N)


def g_model(actor, stage):
    tok, address = TOKENS[actor], FLAGS[actor]
    if stage == "unstored":
        return heap_resource({tok["b"]: 0, tok["q"]: 0, address: 0}, size=N)
    if stage in ("pending", "drained"):
        h = heap_resource({tok["a"]: 0, tok["q"]: 0, address: 0 if stage == "pending" else 1}, size=N)
        return enqueue(h, actor, address, 1) if stage == "pending" else h
    assert stage == "fenced"
    return heap_resource({tok["a"]: 0, tok["t"]: 0, address: 1}, size=N)


def spatial_unique(*parts):
    out = empty(len(parts[0].heap), marks=3)
    for part in parts:
        choices = compose("sp", out, part)
        assert len(choices) == 1  # This family has at most one address on each processor's buffer.
        out, = choices
    return out


def dekker_models():
    states = ("unstored", "pending", "drained", "fenced")
    models = []
    for left, right in product(states, repeat=2):
        models.append(("none", left, right, spatial_unique(ghost_cells([PRIZE], 3), g_model(0, left), g_model(1, right))))
    for winner in range(2):
        for other in states:
            stages = ("fenced", other) if winner == 0 else (other, "fenced")
            models.append((str(winner), *stages, spatial_unique(ghost_cells([TOKENS[winner]["p"]], 3),
                          g_model(0, stages[0]), g_model(1, stages[1]))))
    assert len(models) == len({r for *_, r in models}) == 24
    return tuple(models)


def dekker_search():
    models = dekker_models()
    pools = tuple(r for *_, r in models)
    counts, rows = Counter(invariant_memory_models=len(models)), []
    for pool in pools:
        for later in futures(pool):
            counts["invariant_future_checks"] += 1
            assert later in pools and later.marks == 3
    for actor, operation in product(range(2), ("store", "fence", "load")):
        tok = TOKENS[actor]
        pre_names = {"store": ("a", "t", "p"), "fence": ("b", "t", "p"), "load": ("b", "q", "p")}[operation]
        primitive = {"store": ("store", actor, FLAGS[actor], 1), "fence": ("fence", actor),
                     "load": ("load", actor, actor, FLAGS[1-actor])}[operation]
        row = Counter()
        accepted_pools = set()
        for (winner, left, right, pool), marks, stack in product(models, (1, 2, 3), product((-1, 0, 1), repeat=2)):
            local = ghost_cells([tok[k] for k in pre_names], marks)
            for whole in compose("sp", pool, local):
                accepted_pools.add(pool)
                row["inputs"] += 1
                ab, steps = events(primitive, stack, whole)
                assert not ab
                if not steps:
                    assert operation == "fence" and pool.buffers[actor]
                    row["waiting_fences"] += 1
                    continue
                row["enabled_steps"] += len(steps)
                for kind, who, nxt, st, after in steps:
                    assert nxt == HALT and st[1-actor] == stack[1-actor]
                    if operation == "store":
                        addresses = [tok[k] for k in ("b", "t", "p")]
                    elif operation == "fence":
                        addresses = [tok[k] for k in ("b", "q", "p")]
                    elif st[actor] == 1:
                        addresses = [tok[k] for k in ("b", "q", "p")]
                        row["loads_one"] += 1
                    else:
                        assert st[actor] == 0
                        addresses = [tok["b"], tok["q"], PRIZE]
                        row["loads_zero"] += 1
                    answers = []
                    for returned, new_marks in product(pools, (1, 2, 3)):
                        successor = ghost_cells(addresses, new_marks)
                        if not update_ok(local, pool, successor, returned, kind, who):
                            continue
                        if any(physical(w) == physical(after) for w in compose("sp", returned, successor)):
                            answers.append((successor, returned))
                    assert answers, (actor, operation, winner, left, right, marks, stack)
                    row["post_splits"] += len(answers)
                    if operation == "fence" and pool.buffers[1-actor]:
                        row["fences_preserving_foreign_pending_write"] += 1
                    if operation == "load" and pool.buffers[1-actor]:
                        row["loads_with_foreign_pending_write"] += 1
        row["distinct_input_pool_models"] = len(accepted_pools)
        rows.append(dict(actor=actor, operation=operation, **row))
        counts.update(row)
    for m0, m1 in product((1, 2, 3), repeat=2):
        p0 = ghost_cells([TOKENS[0]["b"], TOKENS[0]["q"], PRIZE], m0)
        p1 = ghost_cells([TOKENS[1]["b"], TOKENS[1]["q"], PRIZE], m1)
        assert not compose("sp", p0, p1)
        counts["double_prize_splits_rejected"] += 1
    counts["input_pool_cases_over_six_steps"] = counts.pop("distinct_input_pool_models")
    return dict(counts=counts, six_steps=rows, counterexample=None,
                scope="All memory shapes and nonempty private mark sets of the fixed 13-address formulas; 9 incoming stacks")


def component_family(address, full=False, size=3):
    cases = []
    for value in (None, 0, 1):
        h = cell(address, value, 3 if full else (1 if value is not None else 0), size)
        # cell(...,None) is the empty heap, possibly fully marked for a pool.
        cases.append(h)
        for actor, length in product(range(2), (1, 2)):
            for values in product((0, 1), repeat=length):
                buffers = [(), ()]
                buffers[actor] = tuple((address, v) for v in values)
                cases.append(replace(h, buffers=tuple(buffers)))
    assert len(cases) == len(set(cases)) == 39
    return tuple(cases)


def foundation_search():
    counts = Counter()
    for pool, frame, local in product(component_family(1, True), component_family(2), component_family(3)):
        if sum(len(b) for part in (pool, frame, local) for b in part.buffers) > 3:
            continue
        counts["input_triples"] += 1
        for whole in worlds("dj", pool, frame, local):
            counts["worlds"] += 1
            combined = tuple(tuple(w for w in b if w[0] not in pool.domain()) for b in whole.buffers)
            recovered = tuple(residual_buffer(f, w) for f, w in zip(frame.buffers, combined))
            assert recovered == local.buffers
            counts["fixed_pool_frame_cancellations"] += 1
            joint = tuple(residual_buffer(f, w) for f, w in zip(frame.buffers, whole.buffers))
            assert any(r.buffers == joint for r in compose("sp", pool, local))
            counts["joint_pool_local_cancellations"] += 1
            for actor in range(2):
                if not whole.buffers[actor]:
                    continue
                choices = flush_choices("dj", pool, frame, local, whole, actor)
                assert len(choices) == 1
                side, pp, ff, ll = choices[0]
                counts[side+"_flushes"] += 1
                assert pp.marks == 3
                component = {"pool": pool, "frame": frame, "local": local}[side]
                if len(component.buffers[actor]) == 2 and component.buffers[actor][0] == component.buffers[actor][1]:
                    counts["duplicate_head_flushes"] += 1
                if side == "pool":
                    assert ff == frame and ll == local
                elif side == "frame":
                    assert pp == pool and ll == local
                else:
                    assert pp == pool and ff == frame
    # Changing the pool invalidates the stronger claim about LOCAL buffers.
    pool = history_models(1, 0, 0, 1, 3)[0]
    local = empty(marks=1)
    transferred = replace(pool, marks=1)
    whole, = worlds("dj", pool, empty(), local)
    assert matches("dj", empty(marks=3), empty(), transferred, whole)
    assert update_ok(local, pool, transferred, empty(marks=3), "ordinary", 0)
    assert local.buffers != transferred.buffers
    return dict(counts=counts, counterexample=None,
                stronger_claim_counterexample=dict(before_pool=asdict(pool), before_local=asdict(local),
                    after_pool=asdict(empty(marks=3)), after_local=asdict(transferred)),
                scope="3 separate component addresses; values 0/1; each buffer <=2, total writes <=3; two processors")


def multiaddress_foundation_search():
    """A pool can own writes to two addresses on the same buffer."""
    counts = Counter()
    writes = tuple(product((1, 2), (0, 1)))
    words = ((),) + tuple((w,) for w in writes) + tuple(product(writes, repeat=2))
    pool_cases = set()
    for entries, actor, word in product(({}, {1: 0}, {2: 0}, {1: 0, 2: 0}), range(2), words):
        b = [(), ()]
        b[actor] = word
        pool_cases.add(replace(heap_resource(entries, size=4), buffers=tuple(b)))
    def others(address):
        return (empty(4), cell(address, 0, 1, 4), pending(0, address, 0, size=4),
                pending(1, address, 1, size=4), enqueue(cell(address, 0, 1, 4), 0, address, 1))
    for pool, frame, local in product(sorted(pool_cases, key=repr), others(3), others(4)):
        if sum(len(b) for part in (pool, frame, local) for b in part.buffers) > 3:
            continue
        for whole in worlds("dj", pool, frame, local):
            counts["worlds"] += 1
            no_pool = tuple(tuple(w for w in b if w[0] not in pool.domain()) for b in whole.buffers)
            assert tuple(residual_buffer(f, w) for f, w in zip(frame.buffers, no_pool)) == local.buffers
            joint = tuple(residual_buffer(f, w) for f, w in zip(frame.buffers, whole.buffers))
            assert any(r.buffers == joint for r in compose("sp", pool, local))
            if any(len({a for a, _ in b}) == 2 for b in pool.buffers):
                counts["two_addresses_on_one_pool_buffer"] += 1
            for actor in range(2):
                if whole.buffers[actor]:
                    options = flush_choices("dj", pool, frame, local, whole, actor)
                    assert len(options) == 1
                    counts[options[0][0]+"_flushes"] += 1
    return dict(counts=counts, counterexample=None,
                scope="4 addresses; pool owns addresses 1/2; buffer length <=2, total writes <=3; four pool heap layouts")


def small_component(address, full=False, size=4):
    m = 3 if full else 1
    return tuple(dict.fromkeys((empty(size, 3 if full else 0), empty(size, m), cell(address, 0, m, size),
            cell(address, 1, m, size), pending(0, address, 0, 3 if full else 0, size),
            pending(1, address, 1, 3 if full else 0, size),
            history_models(address, 0, 0, 1, m, size)[0],
            history_models(address, 0, 1, 1, m, size)[0],
            pending(0, address, 1, 3 if full else 0, size, copies=2))))


def actual_actions(whole, allowed):
    yield "ordinary", 0, whole
    for actor in range(2):
        if not whole.buffers[actor]:
            yield "fence", actor, whole
        for address in sorted(allowed):
            if read(whole, actor, address) is not None:
                yield "store", actor, enqueue(whole, actor, address, 1)


def reconstruction_search():
    counts = Counter()
    for pool, frame, retained, local in product(*(small_component(a, a == 1) for a in (1, 2, 3, 4))):
        if sum(len(b) for part in (pool, frame, retained, local) for b in part.buffers) > 2:
            continue
        for big in compose("sp", retained, local):
            for whole in worlds("dj", pool, frame, big):
                counts["input_environments"] += 1
                groups = [g for g in compose("ov", frame, retained) if matches("dj", pool, g, local, whole)]
                assert groups
                for grouped in groups:
                    for kind, actor, after in actual_actions(whole, pool.domain() | local.domain()):
                        for successor, returned in successors("dj", grouped, local, pool, after, kind, actor):
                            counts["successors_"+kind] += 1
                            if physical(returned) != physical(pool):
                                counts["pool_changing_successors"] += 1
                                if any(pool.buffers) or any(returned.buffers):
                                    counts["pool_changing_with_buffers"] += 1
                            pairings = [r for r in compose("sp", retained, successor)
                                        if matches("dj", returned, frame, r, after)
                                        and update_ok(big, pool, r, returned, kind, actor)]
                            assert pairings
                            counts["spatial_reconstructions"] += 1
                            assert any(matches("dj", returned, f, retained, after)
                                       for f in compose("ov", frame, successor))
                            counts["sibling_views"] += 1
    return dict(counts=counts, counterexample=None,
                scope="4 component addresses; 8 pool and 9 profiles per other role, <=2 initial writes; store adds at most one")


def primitive_lifting_search():
    counts = Counter()
    for pool, frame, local in product(small_component(1, True, 3), small_component(2, False, 3), small_component(3, False, 3)):
        if sum(len(b) for r in (pool, frame, local) for b in r.buffers) > 2:
            continue
        for whole in worlds("dj", pool, frame, local):
            allowed = pool.domain() | local.domain()
            joint_buffers = tuple(residual_buffer(f, w) for f, w in zip(frame.buffers, whole.buffers))
            joint = Resource(tuple(v if a+1 in allowed else None for a, v in enumerate(whole.heap)), joint_buffers, marks=3)
            assert any(physical(j) == physical(joint) for j in compose("sp", pool, local))
            counts["environments"] += 1
            for actor in range(2):
                if not joint.buffers[actor] and whole.buffers[actor]:
                    ab, own_steps = events(("fence", actor), (0, 0), joint)
                    ab2, whole_steps = events(("fence", actor), (0, 0), whole)
                    assert not ab and not ab2 and len(own_steps) == 1 and not whole_steps
                    counts["frame_only_fences_wait"] += 1
                for address in sorted(allowed):
                    counts["read_projection_checks"] += 1
                    assert read(whole, actor, address) == read(joint, actor, address)
            for kind, actor, after in actual_actions(whole, allowed):
                if kind == "store":
                    added = after.buffers[actor][-1]
                    own_after = enqueue(joint, actor, *added)
                else:
                    own_after = joint
                if kind == "fence":
                    assert not joint.buffers[actor]
                # Every post-split of a frameless premise must extend with
                # the exact frame, not merely one convenient post-split.
                for successor, returned in successors("dj", empty(), local, pool, own_after, kind, actor):
                    counts["all_post_splits_"+kind] += 1
                    assert matches("dj", returned, frame, successor, after)
    return dict(counts=counts, counterexample=None,
                scope="3 addresses, 8 pool and 9 profiles per other role, <=2 initial writes; every frameless post-split")


if __name__ == "__main__":
    for name, run in (("marks", marks_search), ("fence_and_foreign_load", fence_and_load_search),
                      ("overlap_diagnostic", overlap_diagnostic), ("buffer_foundations", foundation_search),
                      ("multiaddress_pool_buffers", multiaddress_foundation_search), ("primitive_lifting", primitive_lifting_search), ("spatial_and_parallel", reconstruction_search),
                      ("dekker_six_steps", dekker_search)):
        print(json.dumps(dict(search=name, **run()), sort_keys=True), flush=True)
