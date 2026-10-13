"""Exact check of a two-guard, low-port candidate; exploratory only."""
from collections import Counter, deque
from pathlib import Path
import json

ROOT = Path(__file__).resolve().parent


def run():
    k, c, n = 2, 5, 9
    # Core pairs 01 and 23, target low endpoint 4.
    h = [(0, 1), (0, 1), (2, 3), (2, 3), (0, 2), (1, 3), (1, 4), (2, 4), (0, 4)]
    # Exterior a=5, b=6, z=7, t=8.
    ports = [(0, 5), (2, 6), (4, 7), (0, 5), (1, 5), (2, 6),
             (3, 6), (4, 7), (1, 8), (3, 8)]
    exterior = [(7, 5)] * 2 + [(7, 6)] * 2 + [(7, 8)] * 2 + [(8, 7)]
    outer, edges = ports + exterior, h + ports + exterior
    m = len(h)
    sigma = sum(1 << i for i in range(3, len(ports)))
    degrees = [sum(v in edge for edge in edges) for v in range(n)]
    induced = [sum(bool(s >> u & 1) and bool(s >> v & 1) for u, v in edges)
               for s in range(1, (1 << n) - 1)]
    minimum = min(sum(degrees[v] for v in range(n) if s >> v & 1) - 2 * inside
                  for s, inside in enumerate(induced, 1))
    sd = all(sum(bool(s >> u & 1) and bool(s >> v & 1) for u, v in h)
             <= k * (s.bit_count() - 1) for s in range(1, (1 << c) - 1))
    legal, vectors, tight = set(), {}, {}
    for hm in range(1 << m):
        bits = hm | sigma << m
        arcs = [(v, u) if bits >> i & 1 else (u, v) for i, (u, v) in enumerate(edges)]
        out = tuple(sum(u == v for u, w in arcs) for v in range(n))
        if any(out[v] < k or out[v] > degrees[v] - k for v in range(n)):
            continue
        values = [sum(out[v] for v in range(n) if s >> v & 1) - inside
                  for s, inside in enumerate(induced, 1)]
        if min(values) >= k:
            legal.add(hm)
            vectors[hm] = out
            tight[hm] = [s for s, value in enumerate(values, 1) if value == k]
    remaining, components = set(legal), []
    while remaining:
        first = min(remaining)
        remaining.remove(first)
        comp, todo = [first], deque([first])
        while todo:
            hm = todo.popleft()
            for eid in range(m):
                nxt = hm ^ (1 << eid)
                if nxt in remaining:
                    remaining.remove(nxt)
                    comp.append(nxt)
                    todo.append(nxt)
        components.append(sorted(comp))
    incident = [i for i, edge in enumerate(h) if 4 in edge]
    expected_hm = (1 << 1) | (1 << 3) | (1 << 5) | (1 << 8)
    qedges = [(0 if u < c else u-c+1, 0 if v < c else v-c+1) for u, v in outer]
    qarcs = [(v, u) if sigma >> i & 1 else (u, v) for i, (u, v) in enumerate(qedges)]
    quotient_rows = [(s, sum(bool(s >> u & 1) and not bool(s >> v & 1) for u, v in qarcs))
                     for s in range(1, (1 << (n-c+1))-1)]
    quotient_bad = [(s, amount) for s, amount in quotient_rows if amount < k]
    source_mask = expected_hm | sigma << m
    source_arcs = [(v, u) if source_mask >> i & 1 else (u, v) for i, (u, v) in enumerate(edges)]
    source_bad = [(s, sum(bool(s >> u & 1) and not bool(s >> v & 1) for u, v in source_arcs))
                  for s in range(1, (1 << n)-1)]
    source_bad = [(s, amount) for s, amount in source_bad if amount < k]
    summary = dict(status='REJECTED_QUOTIENT_NOT_K_ARC_STRONG', k=k, c=c, n=n, m=m, q=m-k*(c-1),
                   sd=sd, minimum_cut=minimum, h=h, outer=outer, edges=edges, sigma=sigma,
                   quotient_is_legal=not quotient_bad, quotient_bad_outcuts=quotient_bad,
                   source_bad_outcuts=source_bad,
                   source_internal_mask=expected_hm, source_is_legal=expected_hm in legal,
                   legal_internal_masks=sorted(legal), component_sizes=list(map(len, components)),
                   components=components, target_endpoint_outdegrees=sorted({vectors[hm][4] for hm in legal}),
                   target_incident_signatures=sorted({tuple((hm >> eid) & 1 for eid in incident) for hm in legal}),
                   core_outprofiles=sorted({vectors[hm][:c] for hm in legal}),
                   expected_guards=[(1 << 0) | (1 << 1) | (1 << 5),
                                    (1 << 2) | (1 << 3) | (1 << 6)])
    (ROOT / 'trapped_ports_H3_probe.json').write_text(json.dumps(summary, indent=2), encoding='utf-8')
    print(json.dumps({key: value for key, value in summary.items()
                      if key not in ('h', 'outer', 'edges', 'legal_internal_masks', 'components')}), flush=True)


if __name__ == '__main__':
    run()
