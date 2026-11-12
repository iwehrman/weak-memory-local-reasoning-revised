#!/usr/bin/env python3
"""Restricted SHARE: bounded DJ resource simulation, not a validity proof.

Two processors, three addresses, values 0/1, buffers of length <=1 per
component initially, all mark choices; all enabled one-step actions and
all bounded source residuals. The source invariant is emp or one cell.
Token placement is local, external, or free. No stack/pure assertions are
modelled. OV is intentionally not inferred from this DJ simulation.
"""
from collections import Counter
from dataclasses import replace, asdict
from itertools import product
import json
from search_frame_shape import Resource, EMPTY, compose, futures
from search_owned_frames import POOLS, physical, phase, matches, actions, residuals, update_ok


def family():
    # Invariant address 1; retained local and external cells/writes range
    # over addresses 2/3. Includes identical writes before disjoint filtering.
    components = [EMPTY]
    for a, v, m in product((2, 3), (0, 1), range(4)):
        if m:
            components.append(Resource(tuple(v if a == k else None for k in (1, 2, 3)), ((), ()), marks=m))
        for i in range(2):
            bs = [(), ()]; bs[i] = ((a, v),)
            components.append(replace(EMPTY, buffers=tuple(bs), marks=m))
    invariants = [replace(EMPTY, marks=m) for m in range(4)] + [
        Resource((v, None, None), ((), ()), marks=m) for v in (0, 1) for m in (1, 2, 3)]
    for j, p, f, token in product(invariants, components, components, (0, 1, 2)):
        yield j, p, replace(f, blocked=token)


def search():
    counts = Counter()
    for j, p, f in family():
        compose.cache_clear(); futures.cache_clear()
        for big in compose('sp', j, p):
            for world in compose('sp', f, big):
                counts['closed_environments'] += 1
                source_pool = replace(j, marks=3) if phase(world) == 'free' else POOLS[0]
                grouped = f if phase(world) == 'free' else compose('sp', f, j)[0]
                assert matches(source_pool, grouped, p, world, 'dj')
                for action, actor, after in actions(world):
                    for pp, returned in residuals(grouped, p, source_pool, world, after, action, actor):
                        if not matches(returned, grouped, pp, after, 'dj'):
                            continue
                        counts['closed_successors_' + action] += 1
                        candidates = (pp,) if action == 'acquire' else compose('sp', j, pp)
                        assert any(matches(POOLS[0], f, out, after, 'dj') and
                                   update_ok(big, out, POOLS[0], POOLS[0], phase(world), phase(after), action, actor)
                                   for out in candidates), (action, j, p, f, pp, returned)
        # Held locally: there is no separately retained J component.
        for owner in range(2):
            local = replace(p, blocked=3 ^ (1 << owner))
            for world in compose('sp', replace(f, blocked=0), local):
                frame = replace(f, blocked=0)
                counts['held_environments'] += 1
                for action, actor, after in actions(world):
                    for pp, returned in residuals(frame, local, POOLS[0], world, after, action, actor):
                        if not matches(returned, frame, pp, after, 'dj'):
                            continue
                        counts['held_successors_' + action] += 1
                        # A release may choose any one-cell pool in POOLS;
                        # re-mark it only for the actor, never for everyone.
                        candidates = compose('sp', replace(returned, marks=1 << actor), pp) if action == 'release' else (pp,)
                        assert any(matches(POOLS[0], frame, out, after, 'dj') and
                                   update_ok(local, out, POOLS[0], POOLS[0], phase(world), phase(after), action, actor)
                                   for out in candidates), (action, local, frame, pp, returned)
    return {'scope': __doc__, 'counts': dict(counts), 'counterexample': None}


if __name__ == '__main__':
    print(json.dumps(search(), sort_keys=True))


def overlap_search(draws=12000):
    """Seeded OV simulation using an invariant-dependent frame projection.
    Not a finite-state semantic validity test. Frames may overlap the retained
    invariant heap and may share same-processor pending writes with the local.
    """
    import random
    rng = random.Random(31)
    counts = Counter()
    def component():
        bs = [[], []]
        for _ in range(rng.randrange(3)):
            bs[rng.randrange(2)].append((rng.randrange(1, 4), rng.randrange(2)))
        return Resource(tuple(rng.choice((None, None, 0, 1)) for _ in range(3)),
                        tuple(tuple(b) for b in bs), marks=rng.randrange(4))
    for _ in range(draws):
        f, p = component(), component()
        j = replace(rng.choice(POOLS), marks=rng.randrange(1, 4))
        f = replace(f, blocked=rng.choice((0, 1, 2)))
        if not (f.well_formed() and p.well_formed()):
            continue
        compose.cache_clear()
        for big in compose('sp', j, p):
            for world in compose('ov', f, big):
                counts['closed_environments'] += 1
                pool = replace(j, marks=3) if phase(world) == 'free' else POOLS[0]
                cut = replace(f, heap=tuple(None if a is not None else b for a, b in zip(j.heap, f.heap)))
                groups = (cut,) if phase(world) == 'free' else compose('ov', f, j)
                assert groups
                for grouped in groups:
                    assert matches(pool, grouped, p, world, 'ov')
                    for action, actor, after in actions(world):
                        for pp, returned in residuals(grouped, p, pool, world, after, action, actor):
                            if not matches(returned, grouped, pp, after, 'ov'):
                                continue
                            counts['closed_successors_' + action] += 1
                            candidates = (pp,) if action == 'acquire' else compose('sp', j, pp)
                            assert any(matches(POOLS[0], f, out, after, 'ov') and
                                update_ok(big, out, POOLS[0], POOLS[0], phase(world), phase(after), action, actor)
                                for out in candidates), (action, j, p, f, pp, returned)
        for owner in range(2):
            local, frame = replace(p, blocked=3 ^ (1 << owner)), replace(f, blocked=0)
            for world in compose('ov', frame, local):
                counts['held_environments'] += 1
                for action, actor, after in actions(world):
                    for pp, returned in residuals(frame, local, POOLS[0], world, after, action, actor):
                        if not matches(returned, frame, pp, after, 'ov'):
                            continue
                        counts['held_successors_' + action] += 1
                        candidates = compose('sp', replace(returned, marks=1 << actor), pp) if action == 'release' else (pp,)
                        assert any(matches(POOLS[0], frame, out, after, 'ov') and
                            update_ok(local, out, POOLS[0], POOLS[0], phase(world), phase(after), action, actor)
                            for out in candidates), (action, local, frame, pp, returned)
    return {'scope': overlap_search.__doc__, 'seed': 31, 'draws': draws,
            'counts': dict(counts), 'counterexample': None}


if __name__ == '__main__':
    print(json.dumps(overlap_search(), sort_keys=True))
