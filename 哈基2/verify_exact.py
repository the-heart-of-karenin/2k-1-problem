"""Independent audit using every cut, rather than the C++ sparsity shortcut."""
from collections import deque
from hashlib import sha256
from pathlib import Path
import json

BASE = Path(__file__).resolve().parent
data = json.loads((BASE / "exact_results.json").read_text(encoding="utf-8"))

def masks(graph):
    n, edges = graph["n"], graph["edges"]
    pos, neg = [0] * n, [0] * n
    for i, (u, v) in enumerate(edges):
        pos[u] |= 1 << i
        neg[v] |= 1 << i
    cuts = []
    for x in range(1, (1 << n) - 1):
        p = q = 0
        for i, (u, v) in enumerate(edges):
            if x >> u & 1 and not (x >> v & 1):
                p |= 1 << i
            if x >> v & 1 and not (x >> u & 1):
                q |= 1 << i
        cuts.append((x, p, q))
    return pos, neg, cuts

def degree(state, vertex, pos, neg):
    return (state & pos[vertex]).bit_count() + ((~state) & neg[vertex]).bit_count()

def mincut(state, cuts):
    return min((state & p).bit_count() + ((~state) & q).bit_count() for _, p, q in cuts)

def components(states, m):
    unseen = set(states)
    sizes = []
    while unseen:
        start = unseen.pop()
        queue = [start]
        for u in queue:
            for i in range(m):
                v = u ^ (1 << i)
                if v in unseen:
                    unseen.remove(v)
                    queue.append(v)
        sizes.append(len(queue))
    return sorted(sizes)

audits = []
for g in data["graphs"]:
    if g["m"] > 18:
        continue
    n, m, k = g["n"], g["m"], g["k"]
    pos, neg, cuts = masks(g)
    degs = [(p | q).bit_count() for p, q in zip(pos, neg)]
    lam = min((p | q).bit_count() for _, p, q in cuts)
    host, good = [], []
    for s in range(1 << m):
        out = [degree(s, v, pos, neg) for v in range(n)]
        if all(k <= out[v] <= degs[v] - k for v in range(n)):
            host.append(s)
            if mincut(s, cuts) >= k:
                good.append(s)
    assert lam == g["lambda"]
    assert len(host) == g["vertex_legal"]
    assert len(good) == g["fully_legal"]
    assert components(host, m) == [len(host)]
    assert components(good, m) == sorted(g["good_component_sizes"])
    bad = set(host) - set(good)
    bs = components(bad, m)
    assert len(bs) == g["bad_components"]
    assert max(bs, default=0) == g["largest_bad_component"]
    cap_queries = cap_failures = nontrivial_queries = 0
    goodset = set(good)
    for root in range(n):
        if degs[root] <= 2 * k + 1:
            continue
        out = {s: degree(s, root, pos, neg) for s in good}
        eta = min(out.values())
        assert eta == g["eta_by_root"][root]
        for r in range(eta + 1, degs[root] - k + 1):
            allowed = {s for s in good if out[s] <= r}
            # Multi-source flood from ALL minimum-layer states, checking the cap.
            reached = {s for s in good if out[s] == eta}
            queue = list(reached)
            for u in queue:
                for i in range(m):
                    v = u ^ (1 << i)
                    if v in allowed and v not in reached:
                        reached.add(v)
                        queue.append(v)
            queries = {s for s in good if out[s] == r}
            cap_queries += len(queries)
            if r < max(out.values()):
                nontrivial_queries += len(queries)
            cap_failures += len(queries - reached)
    assert cap_queries == g["root_cap_queries"]
    assert cap_failures == g["root_cap_failures"]
    assert nontrivial_queries == g["root_cap_nontrivial_queries"]
    audits.append({"name": g["name"], "all_orientations": 1 << m,
                   "all_cuts_per_legal_check": len(cuts), "host": len(host),
                   "good": len(good), "root_cap_queries": cap_queries,
                   "root_cap_nontrivial_queries": nontrivial_queries,
                   "status": "PASS"})
    print(g["name"], "PASS", flush=True)

# All-cut verification of stored counterexamples and physical paths, including
# large census inputs. A bad vertex with no legal neighbor disproves only a
# one-step repair assertion, not the original connectivity conjecture.
witnesses = []
for g in data["graphs"]:
    pos, neg, cuts = masks(g)
    k, m = g["k"], g["m"]
    if g["bad_vertices_without_legal_neighbor"]:
        s = g["bad_no_neighbor_witness"]
        assert mincut(s, cuts) < k
        neighbors = [mincut(s ^ (1 << i), cuts) for i in range(m)]
        assert max(neighbors) < k
        witnesses.append({"name": g["name"], "state": s,
                          "minimum_outcut": mincut(s, cuts),
                          "neighbor_minimum_outcuts": neighbors})
    if "hamming_trap" in g:
        h = g["hamming_trap"]
        s, target = h["start"], h["target"]
        assert mincut(s, cuts) >= k and mincut(target, cuts) >= k
        diff = s ^ target
        for i in range(m):
            if diff >> i & 1:
                assert mincut(s ^ (1 << i), cuts) < k
        visited = {s: 0}
        queue = deque([s])
        while target not in visited:
            u = queue.popleft()
            for i in range(m):
                v = u ^ (1 << i)
                if v not in visited and mincut(v, cuts) >= k:
                    visited[v] = visited[u] + 1
                    queue.append(v)
        assert visited[target] == len(h["shortest_word"])
        cut_checks = 0
        for i in h["shortest_word"]:
            s ^= 1 << i
            assert mincut(s, cuts) >= k
            cut_checks += len(cuts)
        assert s == target
        witnesses.append({"name": g["name"], "type": "nonmonotone_shortest_word",
                          "distance": visited[target], "hamming": diff.bit_count(),
                          "prefix_cut_rows": cut_checks, "status": "PASS"})

# Result148's root-shadow control, rechecked as a physical example.
g = next(g for g in data["graphs"] if g["name"] == "root_shadow_control_k2")
pos, neg, cuts = masks(g)
s = 3867
assert degree(s, 0, pos, neg) == 4 and mincut(s, cuts) >= 2
for i, (u, v) in enumerate(g["edges"]):
    tail = u if s >> i & 1 else v
    if tail == 0:
        assert mincut(s ^ (1 << i), cuts) < 2
word = [8, 0, 9, 1]
states = [s]
for i in word:
    s ^= 1 << i
    assert mincut(s, cuts) >= 2
    states.append(s)
assert degree(s, 0, pos, neg) == 2
witnesses.append({"name": g["name"], "start": states[0], "word": word,
                  "states": states, "root_heights": [degree(t, 0, pos, neg) for t in states],
                  "status": "PASS"})

result = {"status": "PASS", "method": "independent Python, full cut enumeration",
          "exact_censuses_independently_repeated": len(audits),
          "audits": audits, "witnesses": witnesses,
          "limits": "m>18 census counts are C++ only; stored witnesses are independently checked",
          "sha256": {p.name: sha256(p.read_bytes()).hexdigest() for p in
                     [BASE / "exact_routes.cpp", BASE / "exact_results.json", Path(__file__)]}}
(BASE / "independent_audit.json").write_text(json.dumps(result, ensure_ascii=False, indent=2), encoding="utf-8")
print("independent_audit.json PASS", flush=True)
