"""Exact physical-fibre screen for entry from root outdegree k+1 to k.

All generated artifacts stay next to this file. No source project is imported.
The exhaustive part is over every internal physical orientation of a sampled
boundary signature. Every complete directed cut is computed exactly.
"""
from collections import Counter, deque
from itertools import combinations
from pathlib import Path
import hashlib
import json
import random
import time

ROOT = Path(__file__).resolve().parent


def induced_counts(n, edges):
    adj = [[0] * n for _ in range(n)]
    for u, v in edges:
        adj[u][v] += 1
        adj[v][u] += 1
    rows = [0] * (1 << n)
    for s in range(1, 1 << n):
        bit = s & -s
        v = bit.bit_length() - 1
        rest = s ^ bit
        rows[s] = rows[rest] + sum(adj[v][u] for u in range(n)
                                 if rest >> u & 1)
    return rows


def outvector(n, edges, mask):
    out = [0] * n
    for i, (u, v) in enumerate(edges):
        out[v if mask >> i & 1 else u] += 1
    return tuple(out)


def legal_vector(out, induced, k):
    subtotal = [0] * len(induced)
    for s in range(1, len(induced) - 1):
        bit = s & -s
        subtotal[s] = subtotal[s ^ bit] + out[bit.bit_length() - 1]
        if subtotal[s] - induced[s] < k:
            return False
    return True


def mincut(n, edges, induced):
    deg = [sum(v in e for e in edges) for v in range(n)]
    sub = [0] * len(induced)
    for s in range(1, len(induced) - 1):
        bit = s & -s
        sub[s] = sub[s ^ bit] + deg[bit.bit_length() - 1]
    return min(sub[s] - 2 * induced[s]
               for s in range(1, len(induced) - 1))


def sd(c, h, k):
    if len(h) <= k * (c - 1):
        return False
    rows = induced_counts(c, h)
    return all(rows[s] <= k * (s.bit_count() - 1)
               for s in range(1, (1 << c) - 1))


def components(legal, m):
    unseen = set(legal)
    answer = []
    while unseen:
        start = min(unseen)
        unseen.remove(start)
        comp, queue = [start], deque([start])
        while queue:
            state = queue.popleft()
            for eid in range(m):
                nxt = state ^ (1 << eid)
                if nxt in unseen:
                    unseen.remove(nxt)
                    comp.append(nxt)
                    queue.append(nxt)
        answer.append(comp)
    return answer


def run(seed=20261011, seconds=90):
    rng = random.Random(seed)
    stats = Counter()
    cores = [
        (2, 3, [(0, 1)] * 2 + [(1, 2)] * 2 + [(0, 2)] * 1),
        (2, 4, list(combinations(range(4), 2)) + [(0, 1)]),
        (2, 4, [(i, (i + 1) % 4) for i in range(4) for _ in range(2)]),
        (3, 4, [(u, v) for u, v in combinations(range(4), 2)
                for _ in range(2 if (u, v) != (2, 3) else 1)]),
        (2, 7, [(u, v) for u in range(3) for v in range(3, 7)] + [(3, 4)]),
        (2, 8, [(u, v) for u in range(4) for v in range(4, 8)
                if (u, v) != (0, 4)]),
    ]
    cores = [(k, c, h) for k, c, h in cores if sd(c, h, k)]
    stats['sd_cores'] = len(cores)
    core_profiles = {}
    for k, c, h in cores:
        vectors = {}
        for mask in range(1 << len(h)):
            vectors.setdefault(outvector(c, h, mask), []).append(mask)
        core_profiles[tuple(h)] = vectors
    started = time.monotonic()
    examples = []
    failure = None
    tried = set()
    while time.monotonic() - started < seconds and failure is None:
        k, c, h = rng.choice(cores)
        b = rng.choice([2, 3])
        n = c + b
        # At least one exterior port per vertex; high boundary is intentional.
        ports = [(v, c + rng.randrange(b)) for v in range(c)
                 for _ in range(rng.randint(1, 4))]
        exterior = [(c + u, c + v) for u, v in combinations(range(b), 2)
                    for _ in range(rng.randint(k, 2 * k + 1))]
        outer = ports + exterior
        edges = h + outer
        induced = induced_counts(n, edges)
        if mincut(n, edges, induced) < 2 * k + 1:
            continue
        qedges = [(0 if u < c else u - c + 1,
                   0 if v < c else v - c + 1) for u, v in outer]
        qi = induced_counts(b + 1, qedges)
        # Select exactly k+1 outgoing physical root ports.
        if len(ports) < k + 1:
            continue
        outgoing = set(rng.sample(range(len(ports)), k + 1))
        sigma = sum(1 << eid for eid in range(len(ports)) if eid not in outgoing)
        sigma |= rng.getrandbits(len(exterior)) << len(ports)
        qo = outvector(b + 1, qedges, sigma)
        if not legal_vector(qo, qi, k):
            continue
        legal_decreases = [eid for eid in outgoing
                           if legal_vector(outvector(b + 1, qedges,
                                                     sigma ^ (1 << eid)), qi, k)]
        if not legal_decreases:
            continue
        key = (k, tuple(h), tuple(outer), sigma)
        if key in tried:
            continue
        tried.add(key)
        base = outvector(n, outer, sigma)
        deg = [sum(v in e for e in edges) for v in range(n)]
        fullvectors = core_profiles[tuple(h)]
        legal = set()
        vertex_legal = 0
        rejected = []
        for internal, masks in fullvectors.items():
            out = tuple(base[v] + (internal[v] if v < c else 0)
                        for v in range(n))
            if any(out[v] < k or out[v] > deg[v] - k for v in range(n)):
                continue
            vertex_legal += len(masks)
            stats['full_degree_vectors_tested'] += 1
            if legal_vector(out, induced, k):
                legal.update(masks)
            else:
                rejected.append(out)
        comps = components(legal, len(h))
        stats['boundary_signatures'] += 1
        stats['physical_legal_states'] += len(legal)
        stats['physical_vertex_legal_states'] += vertex_legal
        stats['rejected_profiles'] += len(rejected)
        stats['fibre_components'] += len(comps)
        if len(comps) > 1:
            stats['disconnected_fibres'] += 1
        for eid in legal_decreases:
            x, _ = ports[eid]
            for comp in comps:
                ready = [state for state in comp
                         if base[x] + outvector(c, h, state)[x] > k]
                if not ready:
                    failure = dict(k=k, c=c, n=n, h=h, outer=outer, sigma=sigma,
                                   decrease_outer_eid=eid, component=sorted(comp),
                                   component_sizes=list(map(len, comps)),
                                   rejected_profiles=rejected, edges=edges)
                    break
                stats['component_decrease_pairs_checked'] += 1
            if failure:
                break
        if len(examples) < 6 and rejected:
            examples.append(dict(k=k, c=c, h=h, outer=outer, sigma=sigma,
                                 legal_decreases=legal_decreases,
                                 component_sizes=list(map(len, comps)),
                                 legal_state_count=len(legal),
                                 rejected_profile_count=len(rejected)))
        if stats['boundary_signatures'] % 100 == 0:
            print(json.dumps(dict(stats), sort_keys=True), flush=True)
    result = dict(seed=seed, elapsed_seconds=time.monotonic() - started,
                  status='COUNTEREXAMPLE' if failure else 'FINITE_SCREEN_ONLY',
                  stats=dict(stats), examples=examples, failure=failure,
                  program_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest())
    (ROOT / 'root_entry_screen.json').write_text(
        json.dumps(result, ensure_ascii=False, indent=2), encoding='utf-8')
    print(json.dumps({k: v for k, v in result.items()
                      if k not in {'examples', 'failure'}}, ensure_ascii=False), flush=True)
    if failure:
        print(json.dumps(failure, ensure_ascii=False), flush=True)


if __name__ == '__main__':
    run()
