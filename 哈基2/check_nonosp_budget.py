"""Check the new budget on Result146's non-OSP eta=3 anchor, read-only source."""
from array import array
from hashlib import sha256
from pathlib import Path
import json

BASE = Path(__file__).resolve().parent
fixture = BASE / "nonosp_source_input.json"
if not fixture.exists():
    source = BASE.parent / "2k+1" / "sd_global_anchor_independent_audit_2026-10-10.json"
    anchor = json.loads(source.read_text(encoding="utf-8-sig"))["actual_anchor"]
    fixture.write_text(json.dumps({"k": 2, "core": anchor["core"],
                                  "arcs": anchor["full_physical_orientation"],
                                  "eta": anchor["outside_eta"],
                                  "source": str(source), "source_sha256": sha256(source.read_bytes()).hexdigest()},
                                 ensure_ascii=False, indent=2), encoding="utf-8")
g = json.loads(fixture.read_text(encoding="utf-8"))
arcs, C, k = [tuple(e) for e in g["arcs"]], g["core"], g["k"]
n = 1 + max(max(e) for e in arcs)
B = sorted(set(range(n)) - set(C))
cset, bset = set(C), set(B)
ci, bi = {v: i for i, v in enumerate(C)}, {v: i for i, v in enumerate(B)}
cfull, bfull, full = (1 << len(C)) - 1, (1 << len(B)) - 1, (1 << n) - 1
cmask = sum(1 << v for v in C)
adj, deg, out = [0] * n, [0] * n, [0] * n
for u, v in arcs:
    assert u != v and not (adj[u] >> v & 1), "This fixture is simple"
    adj[u] |= 1 << v
    adj[v] |= 1 << u
    deg[u] += 1
    deg[v] += 1
    out[u] += 1
R = sum(u in cset and v in bset for u, v in arcs)
j = R - k
a = [out[v] - k for v in C]
mu = [deg[v] - 2 * k for v in C]
internal = [(u, v) for u, v in arcs if u in cset and v in cset]
q = len(internal) - k * (len(C) - 1)
assert R == g["eta"] == 3 and j == 1 and q == 1
assert sum(a) == q + j

# Full cut counts by the independent identity out(S)=sum out(v)-e(S).
inside, sumout, sumdeg, baseline = (array("H", [0]) * (1 << n) for _ in range(4))
lam = len(arcs)
osp = True
for s in range(1, 1 << n):
    bit = s & -s
    v = bit.bit_length() - 1
    t = s ^ bit
    inside[s] = inside[t] + (adj[v] & t).bit_count()
    sumout[s] = sumout[t] + out[v]
    sumdeg[s] = sumdeg[t] + deg[v]
    baseline[s] = sumout[s] - inside[s]
    if s != full:
        lam = min(lam, sumdeg[s] - 2 * inside[s])
for s in range(1, full):
    if inside[s] > k * (s.bit_count() - 1) and inside[full ^ s] > k * ((full ^ s).bit_count() - 1):
        osp = False
        break
assert lam == 5 and not osp and min(baseline[1:full]) == k
print("20-point source: every full cut verified; non-OSP; eta=3", flush=True)

global_x = [sum(1 << v for i, v in enumerate(C) if x >> i & 1) for x in range(cfull + 1)]
global_z = [sum(1 << v for i, v in enumerate(B) if z >> i & 1) for z in range(bfull + 1)]
filled = [baseline[cmask | z] for z in global_z]
ports = [(i, u, v) if u in cset else (i, v, u)
         for i, (u, v) in enumerate(arcs) if (u in cset) != (v in cset)]
incoming = [i for i, (u, v) in enumerate(arcs) if u in bset and v in cset]
rows, dangerous = {}, []
identity_count = 0
for x in range(1, cfull):
    gx, y = global_x[x], cfull ^ x
    alpha = k * (x.bit_count() - 1) - sum((gx >> u & 1) and (gx >> v & 1) for u, v in internal)
    ax = sum(a[i] for i in range(len(C)) if x >> i & 1)
    counts = [sum((y >> ci[u] & 1) and v == w for _, u, v in ports) for w in B]
    p = array("H", [0]) * (bfull + 1)
    for z in range(1, bfull + 1):
        bit = z & -z
        p[z] = p[z ^ bit] + counts[bit.bit_length() - 1]
    for z in range(1, bfull):
        expected = filled[z] + ax + alpha - j + p[z]
        assert expected == baseline[gx | global_z[z]]
        identity_count += 1
    beta = min(filled[z] - k + p[z] for z in range(1, bfull))
    assert ax + alpha + beta >= j
    if ax + alpha < j:
        dangerous.append(x)
        rows[x] = (ax, alpha, p)
print("B1/B2: all four-corner rows verified", identity_count, flush=True)

def quotient_legal(A):
    # Both root-containing and root-avoiding quotient cuts; global_z is exact.
    for z in range(bfull + 1):
        for s in (global_z[z], cmask | global_z[z]):
            if not s or s == full:
                continue
            delta = sum(int(s >> arcs[i][1] & 1) - int(s >> arcs[i][0] & 1) for i in A)
            if baseline[s] + delta < k:
                return False
    return True

accepted, selected = [], []
for mask in range(1, 1 << len(incoming)):
    A = tuple(incoming[t] for t in range(len(incoming)) if mask >> t & 1)
    obligations = [sum(arcs[i][1] == v for i in A) for v in C]
    if any(a[t] + obligations[t] > mu[t] for t in range(len(C))) or not quotient_legal(A):
        continue
    ok = True
    paid_betas = {}
    for x in dangerous:
        ax, alpha, p = rows[x]
        y = cfull ^ x
        counts = [sum((y >> ci[arcs[i][1]] & 1) and arcs[i][0] == w for i in A) for w in B]
        tvalues = array("H", [0]) * (bfull + 1)
        for z in range(1, bfull + 1):
            bit = z & -z
            tvalues[z] = tvalues[z ^ bit] + counts[bit.bit_length() - 1]
        beta = min(filled[z] - k + p[z] - tvalues[z] for z in range(1, bfull))
        paid_betas[str(x)] = beta
        if ax + alpha + beta < j:
            ok = False
            break
    if ok:
        accepted.append((A, paid_betas))
assert accepted
# Select maximal activity and several different physical identities, rather than
# calling this a census of every physical prefix in the 20-point graph.
accepted.sort(key=lambda item: (-len(item[0]), item[0]))
for item in accepted:
    if len(selected) < 4:
        selected.append(item)

checked_states = {}
words = []
for A, betas in selected:
    for mask in range(1 << len(A)):
        active = tuple(A[t] for t in range(len(A)) if mask >> t & 1)
        if active in checked_states:
            continue
        d = [0] * n
        for i in active:
            u, v = arcs[i]
            d[u] -= 1
            d[v] += 1
        sums = array("h", [0]) * (1 << n)
        best = len(arcs)
        for s in range(1, full):
            bit = s & -s
            sums[s] = sums[s ^ bit] + d[bit.bit_length() - 1]
            best = min(best, baseline[s] + sums[s])
        assert best >= k
        checked_states[active] = best
    word = list(A) + list(reversed(A))
    bits = 0
    states = [bits]
    for physical_id in word:
        bits ^= 1 << physical_id
        assert tuple(i for i in A if bits >> i & 1) in checked_states
        states.append(bits)
    assert bits == 0
    words.append({"activity_ids": list(A), "paid_betas": betas,
                  "word": word, "states": states})
print("paid words: full-cut prefix verification complete", len(checked_states), flush=True)
result = {"status": "PASS", "encoding": "bit1 reverses the stored source arc; start=0",
          "n": n, "m": len(arcs), "k": k, "lambda": lam, "osp": osp,
          "core": C, "eta": R, "j": j, "q": q, "a": a,
          "identity_rows": identity_count, "dangerous_trace_masks": dangerous,
          "activity_sets_satisfying_B3": len(accepted), "selected_words": words,
          "distinct_physical_prefix_states_full_cut_checked": len(checked_states),
          "full_cut_rows": (1 + len(checked_states)) * (full - 1),
          "limits": "One specified eta=3 source from Result146; all mixed identities; all incoming subsets checked for B3; four selected cubes receive full-cut checks. No universal source-entry claim.",
          "sha256": {p.name: sha256(p.read_bytes()).hexdigest() for p in [fixture, Path(__file__)]}}
(BASE / "nonosp_budget_results.json").write_text(json.dumps(result, ensure_ascii=False, indent=2), encoding="utf-8")
print("nonosp_budget_results.json PASS", flush=True)
