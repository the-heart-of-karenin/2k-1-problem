"""Target the sole possible saturated gate, rather than random boundaries."""
from collections import Counter, deque
from itertools import combinations
from pathlib import Path
import json
import time

ROOT = Path(__file__).resolve().parent


def reachable(c, arcs, start, forbidden):
    seen, todo = {start}, deque([start])
    while todo:
        u = todo.popleft()
        for tail, head in arcs:
            if tail == u and head != forbidden and head not in seen:
                seen.add(head)
                todo.append(head)
    return seen


def run():
    cores = [
        (2, 3, [(0, 1)]*2+[(1, 2)]*2+[(0, 2)]),
        (2, 4, list(combinations(range(4), 2))+[(0, 1)]),
        (2, 5, [(0, 1)]*2+[(2, 3)]*2+[(0, 2), (1, 3), (1, 4), (2, 4), (0, 4)]),
        (2, 5, [(0, 1)]*2+[(0, 2), (0, 3), (0, 4), (1, 2)]+[(2, 3)]*2+[(3, 4)]),
        (2, 7, [(u, v) for u in range(3) for v in range(3, 7)]+[(3, 4)]),
        (2, 8, [(u, v) for u in range(4) for v in range(4, 8) if (u, v) != (0, 4)]),
    ]
    stats, failure = Counter(), None
    started = time.monotonic()
    for k, c, h in cores:
        inside = [sum(bool(s >> u & 1) and bool(s >> v & 1) for u, v in h)
                  for s in range(1 << c)]
        if not all(inside[s] <= k*(s.bit_count()-1) for s in range(1, (1 << c)-1)):
            continue
        assert len(h) == k*(c-1)+1
        weak = [s for s in range(1, (1 << c)-1) if inside[s] == k*(s.bit_count()-1)]
        deg = [sum(v in edge for edge in h) for v in range(c)]
        stats['sd_cores'] += 1
        for hm in range(1 << len(h)):
            arcs = [(v, u) if hm >> eid & 1 else (u, v) for eid, (u, v) in enumerate(h)]
            hv = [sum(tail == v for tail, head in arcs) for v in range(c)]
            stats['core_orientations'] += 1
            for u in range(c):
                for donor in range(c):
                    if donor == u:
                        continue
                    a = [int(v in (u, donor)) for v in range(c)]
                    r = [k+a[v]-hv[v] for v in range(c)]
                    if any(t < 0 for t in r) or deg[u]+r[u] > 2*k+1:
                        continue
                    iu = 2*k+1-deg[u]-r[u]
                    guards = [s for s in weak if s >> u & 1 and not (s >> donor & 1)
                              and sum(r[v] for v in range(c) if s >> v & 1) >= 1
                              and (s.bit_count() >= 2 or r[u]+iu >= k+1)]
                    if not guards:
                        continue
                    stats['saturated_guard_architectures'] += 1
                    targets = [x for x in range(c) if a[x] == 0 and r[x] > 0
                               and any(not (s >> x & 1) for s in guards)]
                    if not targets:
                        continue
                    seen = reachable(c, arcs, donor, u)
                    stats['target_pairs'] += len(targets)
                    bad = [x for x in targets if x not in seen]
                    if bad:
                        failure = dict(k=k, c=c, h=h, source_internal_mask=hm,
                                       core_a=a, core_outports=r, core_internal_degrees=deg,
                                       saturated_guard_point=u, incoming_ports_at_guard=iu,
                                       unguarded_donor=donor, unreachable_targets=bad,
                                       weak_guard_candidates=guards, reachable_avoiding_guard=sorted(seen))
                        break
                if failure:
                    break
            if failure:
                break
        print(json.dumps(dict(stats)), flush=True)
        if failure:
            break
    result = dict(status='FINITE_ARCHITECTURE_WITNESS' if failure else 'FINITE_SCREEN_ONLY',
                  q=1, stats=dict(stats), failure=failure,
                  elapsed_seconds=time.monotonic()-started)
    (ROOT / 'saturated_guard_H3_architecture_screen.json').write_text(json.dumps(result, indent=2), encoding='utf-8')
    print(json.dumps(result), flush=True)


if __name__ == '__main__':
    run()
