"""Full-cut checks of B1/B2 and paid-port B3/B4 on an eta>k example."""
from itertools import combinations, product
from hashlib import sha256
from pathlib import Path
import json

BASE = Path(__file__).resolve().parent
k, core, outside = 2, (0, 1, 2), (3, 4, 5)
internal = [(0, 1), (0, 1), (0, 2), (0, 2), (1, 2)]
ports = [(v, w) for w in outside for v in (0, 0, 1, 1, 2)]
edges = internal + ports
n, m, q, eta, j = 6, 20, 1, 6, 4
degs = [sum(v in e for e in edges) for v in range(n)]
mu = [degs[v] - 2 * k for v in core]

def directed(state):
    return [(u, v) if state >> i & 1 else (v, u) for i, (u, v) in enumerate(edges)]

def outcut(arcs, mask):
    return sum((mask >> u & 1) and not (mask >> v & 1) for u, v in arcs)

def all_legal(state):
    arcs = directed(state)
    return all(outcut(arcs, x) >= k for x in range(1, (1 << n) - 1))

def baseline_rows(port_state, activity=()):
    A = set(activity)
    rows = {}
    for x in range(1, 7):
        y = 7 ^ x
        alpha = k * (x.bit_count() - 1) - sum((x >> u & 1) and (x >> v & 1) for u, v in internal)
        vals = []
        for z in range(1, 7):
            # Quotient filled cut c U Z: only outgoing c-to-outside ports count.
            oq = sum((port_state >> i & 1) and not (z >> (w - 3) & 1) for i, (v, w) in enumerate(ports))
            p = sum((y >> v & 1) and (z >> (w - 3) & 1) for v, w in ports)
            t = sum((y >> ports[i][0] & 1) and (z >> (ports[i][1] - 3) & 1) for i in A)
            vals.append((z, oq - k + p - t))
        rows[x] = (alpha, min(value for _, value in vals), vals)
    return rows

signatures = []
for choices in product(list(combinations(range(5), 2)), repeat=3):
    s = sum(1 << (5 * group + offset) for group, pair in enumerate(choices) for offset in pair)
    signatures.append(s)
assert len(signatures) == 1000
baseline_profiles = baseline_legal = identity_rows = 0
cube_count = cube_states = actual_cut_rows = 0
words = []
profile_records = []
selected = {signatures[index] for index in range(0, len(signatures), 37)}
for sigma in signatures:
    rows = baseline_rows(sigma)
    r = [sum((sigma >> i & 1) and v == u for i, (u, w) in enumerate(ports)) for v in core]
    for h in range(1 << len(internal)):
        full = h | sigma << len(internal)
        arcs = directed(full)
        b = [sum(u == v for u, w in arcs) for v in core]
        a = [value - k for value in b]
        if not all(0 <= a[v] <= mu[v] for v in core):
            continue
        baseline_profiles += 1
        assert sum(a) == q + j
        predicted = all(sum(a[v] for v in core if x >> v & 1) + alpha + beta >= j
                        for x, (alpha, beta, vals) in rows.items())
        actual = all_legal(full)
        assert predicted == actual
        actual_cut_rows += (1 << n) - 2
        for x, (alpha, beta, vals) in rows.items():
            for z, value in vals:
                actual_out = outcut(arcs, x | (z << 3))
                expected = k + sum(a[v] for v in core if x >> v & 1) + alpha - j + value
                assert actual_out == expected
                identity_rows += 1
        baseline_legal += actual
        if sigma not in selected or not actual:
            continue
        incoming = [[None] + [5 * group + t for t in range(5) if not (sigma >> (5 * group + t) & 1)]
                    for group in range(3)]
        for picks in product(*incoming):
            A = tuple(i for i in picks if i is not None)
            if not A:
                continue
            obligations = [sum(ports[i][0] == v for i in A) for v in core]
            if any(a[v] + obligations[v] > mu[v] for v in core):
                continue
            paid = baseline_rows(sigma, A)
            condition = all(sum(a[v] for v in core if x >> v & 1) + alpha + beta >= j
                            for x, (alpha, beta, vals) in paid.items())
            if not condition:
                continue
            cube_count += 1
            for subset in range(1 << len(A)):
                state = full ^ sum(1 << (len(internal) + A[t]) for t in range(len(A)) if subset >> t & 1)
                assert all_legal(state)
                cube_states += 1
                actual_cut_rows += (1 << n) - 2
            if len(words) < 12 and len(A) == 3:
                word = [len(internal) + i for i in A]
                states = [full]
                state = full
                for physical_id in word + list(reversed(word)):
                    state ^= 1 << physical_id
                    assert all_legal(state)
                    states.append(state)
                assert state == full
                words.append({"start": full, "word": word + list(reversed(word)),
                              "states": states, "core_extra_outdegrees": a,
                              "activity_core_counts": obligations})
            if len(profile_records) < 8:
                profile_records.append({"sigma": sigma, "internal": h, "a": a,
                                        "activity_port_ids": list(A),
                                        "beta_paid": {str(x): val[1] for x, val in paid.items()}})

lam = min(sum(bool(x >> u & 1) != bool(x >> v & 1) for u, v in edges) for x in range(1, (1 << n) - 1))
assert lam >= 2 * k + 1
# Outside is three isolated vertices: summing their in>=k constraints forces
# quotient root-out>=3k=6. Every saved sigma attains 6; no root-out=k layer exists.
result = {"status": "PASS", "n": n, "m": m, "k": k, "lambda": lam,
          "core": list(core), "edges": edges, "q": q, "eta": eta, "j": j,
          "mu_core": mu, "minimum_layer_signatures": len(signatures),
          "vertex_legal_internal_assignments": baseline_profiles,
          "fully_legal_baseline_assignments": baseline_legal,
          "identity_rows": identity_rows, "paid_signature_sample": len(selected),
          "paid_port_cubes": cube_count, "paid_cube_states": cube_states,
          "full_outcut_rows": actual_cut_rows, "words": words,
          "profile_records": profile_records,
          "limits": "Baseline all 1000 minimum signatures and all 32 internal directions; paid-port enumeration uses 28 specified signatures only.",
          "source_sha256": sha256(Path(__file__).read_bytes()).hexdigest()}
(BASE / "external_budget_results.json").write_text(json.dumps(result, ensure_ascii=False, indent=2), encoding="utf-8")
print(json.dumps({key: value for key, value in result.items() if key not in {"edges", "words", "profile_records"}}, ensure_ascii=False), flush=True)
