"""Finite exploration of a single-packet entry without a legal root decrease.

This does not claim a theorem or prove fibre connectivity. Each sampled boundary
has its entire physical core fibre enumerated. No archived file is modified.
"""
from collections import Counter, deque
from itertools import combinations
from pathlib import Path
import hashlib
import json
import random
import time

ROOT = Path(__file__).resolve().parent


def induced(n, edges):
    adj = [[0]*n for _ in range(n)]
    for u, v in edges:
        adj[u][v] += 1
        adj[v][u] += 1
    ans = [0]*(1 << n)
    for s in range(1, 1 << n):
        v = (s & -s).bit_length()-1
        rest = s ^ (1 << v)
        ans[s] = ans[rest]+sum(adj[v][u] for u in range(n) if rest >> u & 1)
    return ans


def vector(n, edges, mask):
    out = [0]*n
    for eid, (u, v) in enumerate(edges):
        out[v if mask >> eid & 1 else u] += 1
    return tuple(out)


def rows(out, inside):
    subtotal = [0]*len(inside)
    ans = []
    for s in range(1, len(inside)-1):
        v = (s & -s).bit_length()-1
        subtotal[s] = subtotal[s ^ (1 << v)]+out[v]
        ans.append(subtotal[s]-inside[s])
    return ans


def mincut(n, edges, inside):
    deg = [sum(v in e for e in edges) for v in range(n)]
    return min(rows(deg, [2*t for t in inside]))


def shortest(c, arcs, start, target, allowed):
    queue, parent = deque([start]), {start: None}
    while queue:
        u = queue.popleft()
        if u == target:
            word, vertices = [], [u]
            while parent[u] is not None:
                p, eid = parent[u]
                word.append(eid)
                vertices.append(p)
                u = p
            return list(reversed(word)), list(reversed(vertices))
        for eid, (tail, head) in enumerate(arcs):
            if tail == u and allowed >> head & 1 and head not in parent:
                parent[head] = (u, eid)
                queue.append(head)
    return None


def component_entry(legal, start, m, target, base, h, c, k):
    todo, parent = deque([start]), {start: None}
    while todo:
        hm = todo.popleft()
        if base[target]+vector(c, h, hm)[target] > k:
            word = []
            end = hm
            while parent[hm] is not None:
                hm, eid = parent[hm]
                word.append(eid)
            return list(reversed(word)), end, len(parent)
        for eid in range(m):
            nxt = hm ^ (1 << eid)
            if nxt in legal and nxt not in parent:
                parent[nxt] = (hm, eid)
                todo.append(nxt)
    return None, None, len(parent)


def run(seconds=100, seed=2026101103):
    rng, stats = random.Random(seed), Counter()
    cores = [
        (2, 3, [(0, 1)]*2+[(1, 2)]*2+[(0, 2)]),
        (2, 4, list(combinations(range(4), 2))+[(0, 1)]),
        (2, 4, [(i, (i+1) % 4) for i in range(4) for _ in range(2)]),
        (2, 5, [(0, 1)]*2+[(2, 3)]*2+[(0, 2), (1, 3), (1, 4), (2, 4), (0, 4)]),
        (3, 4, [(u, v) for u, v in combinations(range(4), 2)
                for _ in range(2 if (u, v) != (2, 3) else 1)]),
    ]
    profiles = {}
    for k, c, h in cores:
        hi = induced(c, h)
        assert len(h) > k*(c-1)
        assert all(hi[s] <= k*(s.bit_count()-1) for s in range(1, (1 << c)-1))
        byvector = {}
        for hm in range(1 << len(h)):
            byvector.setdefault(vector(c, h, hm), []).append(hm)
        profiles[tuple(h)] = byvector
    failure, examples, seen = None, [], set()
    started = time.monotonic()
    while time.monotonic()-started < seconds and failure is None:
        k, c, h = rng.choice(cores)
        b = rng.choice([2, 3, 4])
        n, m = c+b, len(h)
        ports = [(v, c+rng.randrange(b)) for v in range(c) for _ in range(rng.randint(1, 3))]
        exterior = [(c+u, c+v) for u, v in combinations(range(b), 2)
                    for _ in range(rng.randint(0, 2*k+1))]
        outer, edges = ports+exterior, h+ports+exterior
        full_i = induced(n, edges)
        stats['raw_environments'] += 1
        if mincut(n, edges, full_i) < 2*k+1:
            continue
        outgoing = set(rng.sample(range(len(ports)), k+1))
        sigma = sum(1 << eid for eid in range(len(ports)) if eid not in outgoing)
        sigma |= rng.getrandbits(len(exterior)) << len(ports)
        qe = [(0 if u < c else u-c+1, 0 if v < c else v-c+1) for u, v in outer]
        qi = induced(b+1, qe)
        if min(rows(vector(b+1, qe, sigma), qi)) < k:
            continue
        signature = (k, tuple(h), tuple(outer), sigma)
        if signature in seen:
            continue
        seen.add(signature)
        legal_decreases = [eid for eid in outgoing
                           if min(rows(vector(b+1, qe, sigma ^ (1 << eid)), qi)) >= k]
        base, deg = vector(n, outer, sigma), [sum(v in e for e in edges) for v in range(n)]
        fullvectors, legal = {}, set()
        for hv, masks in profiles[tuple(h)].items():
            out = tuple(base[v]+(hv[v] if v < c else 0) for v in range(n))
            if any(out[v] < k or out[v] > deg[v]-k for v in range(n)):
                continue
            rr = rows(out, full_i)
            if min(rr) >= k:
                legal.update(masks)
                fullvectors[hv] = (out, rr, masks)
        assert legal, ('legal quotient without expansion', signature)
        stats['valid_boundary_signatures'] += 1
        stats['no_legal_decrease_signatures'] += not legal_decreases
        stats['legal_physical_states'] += len(legal)
        whole, core = (1 << n)-1, (1 << c)-1
        outside = whole ^ core
        for hv, (out, rr, masks) in fullvectors.items():
            a = [out[v]-k for v in range(c)]
            guard = {u: [] for u in range(c) if a[u] > 0}
            tight = [s for s, value in enumerate(rr, 1) if value == k]
            for s in tight:
                xtrace, ztrace = s & core, s & outside
                if xtrace not in (0, core) and ztrace not in (0, outside):
                    for u in guard:
                        if xtrace >> u & 1:
                            guard[u].append(s)
            intersection = {u: (core if not ss else core & ss[0]) for u, ss in guard.items()}
            for u, ss in guard.items():
                for s in ss:
                    intersection[u] &= s
            for target in sorted({ports[eid][0] for eid in outgoing}):
                if a[target] > 0:
                    stats['already_positive_profile_target_pairs'] += 1
                    continue
                excluded = [u for u in guard if guard[u] and not (intersection[u] >> target & 1)]
                assert len(excluded) <= 1, ('guard multiplicity lemma failed', signature, a, target, guard)
                stats['low_profile_target_pairs'] += 1
                stats['excluded_guard_cases'] += bool(excluded)
                for hm in masks:
                    arcs = [(v, u) if hm >> eid & 1 else (u, v) for eid, (u, v) in enumerate(h)]
                    success = None
                    for donor in guard:
                        allowed = intersection[donor]
                        allowed &= ~sum(1 << v for v in range(c)
                                       if a[v] == deg[v]-2*k and v != donor)
                        if not (allowed >> target & 1):
                            continue
                        answer = shortest(c, arcs, donor, target, allowed)
                        if answer is not None:
                            word, vertices = answer
                            if all(all(not (s >> donor & 1) or (s >> v & 1) for s in tight)
                                   for v in vertices[1:]):
                                success = (word, vertices, donor)
                                break
                    stats['low_physical_state_target_pairs'] += 1
                    if success is None:
                        bfs_word, end, visited = component_entry(legal, hm, m, target, base, h, c, k)
                        failure = dict(k=k, c=c, n=n, h=h, outer=outer, sigma=sigma,
                                       source_internal_mask=hm, target_endpoint=target, core_a=a,
                                       core_mu=[deg[v]-2*k for v in range(c)],
                                       legal_decreases=legal_decreases, guards=guard,
                                       guard_intersections=intersection,
                                       legal_internal_masks=sorted(legal),
                                       actual_entry_word=bfs_word, actual_entry_target=end,
                                       visited_internal_states=visited,
                                       failure_kind='NO_SINGLE_PACKET_PATH' if bfs_word is not None
                                       else 'NO_INTERNAL_ENTRY_IN_SOURCE_COMPONENT')
                        break
                    stats['single_packet_entries'] += 1
                if failure:
                    break
            if failure:
                break
        if len(examples) < 12 and not legal_decreases:
            examples.append(dict(k=k, c=c, n=n, h=h, outer=outer, sigma=sigma,
                                 legal_physical_states=len(legal)))
        if stats['valid_boundary_signatures'] % 100 == 0:
            print(json.dumps(dict(stats), sort_keys=True), flush=True)
    result = dict(status='FINITE_COUNTERWITNESS' if failure else 'FINITE_SCREEN_ONLY',
                  allowed_frontiers='originally_unsaturated_core_vertices',
                  seed=seed, elapsed_seconds=time.monotonic()-started, stats=dict(stats),
                  examples=examples, failure=failure,
                  program_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest())
    (ROOT / 'unshadowed_entry_H3_screen.json').write_text(json.dumps(result, indent=2), encoding='utf-8')
    print(json.dumps({key: value for key, value in result.items() if key not in ('examples', 'failure')}), flush=True)
    if failure:
        print(json.dumps(failure), flush=True)


if __name__ == '__main__':
    run()
