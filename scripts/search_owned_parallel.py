#!/usr/bin/env python3
"""Checkpoint-8 search of parallel reconstruction and stack transport.

Finite/sampled evidence only; the statements and limits are recorded in
review/checkpoint-8-statement.md. The unbounded Rocq proofs are authoritative.
"""
from collections import Counter
from dataclasses import asdict, replace
from itertools import product
import json

from search_frame_shape import Resource, EMPTY, compose
from search_owned_frames import (POOLS, physical, phase, matches, actions,
                                 residuals, update_ok, overlapping_family, sampled_family)


def reconstruct(mode, frame, acting, sibling, pool, whole, grouped, after, action, actor, successor, returned):
    answers = []
    for pair in compose("sp", successor, sibling):
        if not matches(returned, frame, pair, after, mode):
            continue
        sibling_frames = tuple(g for g in compose("ov", frame, successor)
                               if matches(returned, g, sibling, after, mode))
        if sibling_frames:
            answers.append((pair, sibling_frames))
    return answers


def parallel_search(mode):
    counts = Counter()
    for family, inputs in (("overlap", overlapping_family()), ("sample", sampled_family())):
        for frame, left, right, pool in inputs:
            counts[family + "_inputs"] += 1
            compose.cache_clear()
            for pair in compose("sp", left, right):
                for combined in compose("ov", frame, pair):
                    for whole in compose("sp", pool, combined):
                        if not matches(pool, frame, pair, whole, mode):
                            continue
                        counts["input_environments"] += 1
                        for side, acting, sibling in (("left", left, right), ("right", right, left)):
                            groups = tuple(g for g in compose("ov", frame, sibling)
                                           if matches(pool, g, acting, whole, mode))
                            if not groups:
                                return dict(counts=counts, counterexample=dict(reason="unframe", side=side))
                            for grouped in groups:
                                for action, actor, after in actions(whole):
                                    counts[side + "_steps_" + action] += 1
                                    for successor, returned in residuals(grouped, acting, pool, whole, after, action, actor):
                                        if not matches(returned, grouped, successor, after, mode):
                                            continue
                                        counts[side + "_successors_" + action] += 1
                                        candidates = reconstruct(mode, frame, acting, sibling, pool, whole, grouped,
                                                                 after, action, actor, successor, returned)
                                        if not any(update_ok(pair, new_pair, pool, returned, phase(whole), phase(after),
                                                             action, actor) for new_pair, _ in candidates):
                                            return dict(counts=counts, counterexample=dict(reason="reconstruct or switch view",
                                                side=side, action=action, actor=actor, frame=asdict(frame),
                                                acting=asdict(acting), sibling=asdict(sibling), pool=asdict(pool),
                                                whole=asdict(whole), successor=asdict(successor),
                                                returned=asdict(returned), after=asdict(after)))
                                        counts["fresh_sibling_views"] += 1
    return dict(counts=counts, counterexample=None)


def acquire_then_blocked_store(mode):
    counts = Counter()
    for owner, pool_value, private_value, stored_value, marks in product(range(2), (0, 1), (0, 1), (0, 1), (1, 2, 3)):
        other = 1 - owner
        pool = Resource((pool_value, None, None), ((), ()), marks=3)
        left = EMPTY
        right = Resource((None, private_value, None), ((), ()), marks=marks)
        whole = compose("sp", pool, right)[0]
        acquired = replace(whole, blocked=3 ^ (1 << owner))
        left_after = Resource(pool.heap, ((), ()), acquired.blocked, 1 << owner)
        assert matches(pool, right, left, whole, mode)
        assert update_ok(left, left_after, pool, POOLS[0], "free", owner, "acquire", owner)
        assert matches(POOLS[0], right, left_after, acquired, mode)
        assert matches(POOLS[0], left_after, right, acquired, mode)
        counts["acquisitions"] += 1
        for action, actor, after in actions(acquired):
            if action != "store" or actor != other or after.buffers[other] != ((2, stored_value),):
                continue
            assert acquired.blocked & (1 << other)
            buffers = [(), ()]
            buffers[other] = ((2, stored_value),)
            right_after = replace(right, buffers=tuple(buffers))
            assert update_ok(right, right_after, POOLS[0], POOLS[0], owner, owner, "store", other)
            assert matches(POOLS[0], left_after, right_after, after, mode)
            assert matches(POOLS[0], right_after, left_after, after, mode)
            counts["stores_while_blocked"] += 1
    assert counts["acquisitions"] == counts["stores_while_blocked"] == 48
    return dict(counts=counts, counterexample=None)


# Primitive tuples: kind, processor expression, operand expressions.
# Expressions are ("var", index) or ("const", integer).
def evaluate(e, stack):
    return stack[e[1]] if e[0] == "var" else e[1]


def variables(e):
    return {e[1]} if e[0] == "var" else set()


def read(world, actor, address):
    if address not in (1, 2, 3):
        return None
    for loc, value in reversed(world.buffers[actor]):
        if loc == address:
            return value
    return world.heap[address - 1]


def primitive(command, stack, world):
    kind, annotation, operands = command
    processor = evaluate(annotation, stack)
    if processor not in (1, 2):
        return ("stuck",)
    actor = processor - 1
    values = tuple(evaluate(e, stack) for e in operands)
    if kind in ("assume", "assert"):
        if values[0] != values[1]:
            return ("abort",) if kind == "assert" else ("stuck",)
    elif kind == "assign":
        result = list(stack)
        result[0] = values[0]
        return ("step", "ordinary", tuple(result), physical(world))
    elif kind == "load":
        if world.blocked & (1 << actor):
            return ("stuck",)
        value = read(world, actor, values[0])
        if value is None:
            return ("abort",)
        result = list(stack)
        result[0] = value
        return ("step", "ordinary", tuple(result), physical(world))
    elif kind == "store":
        if read(world, actor, values[0]) is None:
            return ("abort",)
        buffers = list(world.buffers)
        buffers[actor] += ((values[0], values[1]),)
        return ("step", "ordinary", stack, physical(replace(world, buffers=tuple(buffers))))
    elif kind in ("fence", "acquire", "release"):
        if world.buffers[actor]:
            return ("stuck",)
        if kind == "acquire":
            if phase(world) != "free":
                return ("stuck",)
            world = replace(world, blocked=3 ^ (1 << actor))
        if kind == "release":
            if phase(world) != actor:
                return ("stuck",)
            world = replace(world, blocked=0)
        return ("step", (kind, actor), stack, physical(world))
    return ("step", "ordinary", stack, physical(world))


def stack_search():
    counts = Counter()
    stacks = tuple(product((0, 1, 2), repeat=3))
    expressions = (("var", 1), ("var", 2), ("const", 1), ("const", 2))
    memories = (Resource((0, 1, None), ((), ()), marks=3),
                Resource((0, 1, None), ((), ((2, 0),)), blocked=2, marks=3),
                Resource((0, 1, None), (((1, 1),), ()), blocked=1, marks=3))
    commands = []
    for annotation in (("const", 1), ("const", 2), ("var", 2)):
        for kind in ("assume", "assert", "store"):
            commands += [(kind, annotation, operands) for operands in product(expressions, repeat=2)]
        for kind in ("assign", "load"):
            commands += [(kind, annotation, (e,)) for e in expressions]
        commands += [(kind, annotation, ()) for kind in ("fence", "acquire", "release")]
    for command in commands:
        fv = variables(command[1]).union(*(variables(e) for e in command[2]))
        if command[0] in ("assign", "load"):
            fv.add(0)
        for mask in range(8):
            support = {i for i in range(3) if mask & (1 << i)}
            if not fv <= support:
                continue
            for before, other in product(stacks, repeat=2):
                if any(before[i] != other[i] for i in support):
                    continue
                for world in memories:
                    result, counterpart = primitive(command, before, world), primitive(command, other, world)
                    counts["checks_" + command[0]] += 1
                    okay = result[0] == counterpart[0]
                    if result[0] == counterpart[0] == "step":
                        okay = (result[1] == counterpart[1] and result[3] == counterpart[3]
                                and all(result[2][i] == counterpart[2][i] for i in support))
                    if not okay:
                        return dict(counts=counts, counterexample=dict(command=command, support=sorted(support),
                            before=before, other=other, world=asdict(world), result=result, counterpart=counterpart))
    return dict(counts=counts, counterexample=None)


if __name__ == "__main__":
    for mode in ("ov", "dj"):
        print(json.dumps(dict(search="parallel_reconstruction", mode=mode, seed=7, draws=4000,
                              **parallel_search(mode)), sort_keys=True), flush=True)
        print(json.dumps(dict(search="acquire_then_blocked_store", mode=mode,
                              **acquire_then_blocked_store(mode)), sort_keys=True), flush=True)
    print(json.dumps(dict(search="primitive_stack_agreement", **stack_search()), sort_keys=True), flush=True)
