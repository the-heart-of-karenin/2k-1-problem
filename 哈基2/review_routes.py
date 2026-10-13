"""Targeted route review; original experiments and source files stay read-only.

20-point orientations use bit1 = reverse the stored source arc. The new root
census instead uses bit1 = stored u -> v, as stated in its JSON.
"""
from array import array
from collections import deque
from hashlib import sha256
from itertools import combinations
from pathlib import Path
import json

BASE = Path(__file__).resolve().parent


def write_json(name, value):
    (BASE / name).write_text(json.dumps(value, ensure_ascii=False, indent=2), encoding="utf-8")


def cutout(arcs, shore):
    return sum((shore >> u & 1) and not (shore >> v & 1) for u, v in arcs)


def orientation(arcs, active):
    return [(v, u) if i in active else (u, v) for i, (u, v) in enumerate(arcs)]


def limited_flow(n, arcs, source, sink, threshold):
    """Edmonds-Karp to threshold; unsuccessful flows return a real outcut."""
    residual = [[0] * n for _ in range(n)]
    for u, v in arcs:
        residual[u][v] += 1
    value = 0
    while value < threshold:
        parent = [-1] * n
        parent[source] = source
        queue = deque([source])
        while queue and parent[sink] < 0:
            u = queue.popleft()
            for v, cap in enumerate(residual[u]):
                if cap and parent[v] < 0:
                    parent[v] = u
                    queue.append(v)
        if parent[sink] < 0:
            shore = sum(1 << v for v, p in enumerate(parent) if p >= 0)
            assert cutout(arcs, shore) == value
            return value, shore
        aug = threshold - value
        v = sink
        while v != source:
            aug = min(aug, residual[parent[v]][v])
            v = parent[v]
        v = sink
        while v != source:
            u = parent[v]
            residual[u][v] -= aug
            residual[v][u] += aug
            v = u
        value += aug
    return value, None


def strong(n, arcs, k, root=0):
    for v in range(n):
        if v == root:
            continue
        for s, t in ((root, v), (v, root)):
            value, shore = limited_flow(n, arcs, s, t, k)
            if value < k:
                return False, {"shore_mask": shore, "outcut": value}
    return True, None


def partition_eta(n, edges, k, root):
    vertices = [v for v in range(n) if v != root]
    blocks = []
    best, best_partition, count = -1, None, 0

    def visit(t):
        nonlocal best, best_partition, count
        if t == len(vertices):
            label = {v: j for j, block in enumerate(blocks) for v in block}
            crossing = sum(u != root and v != root and label[u] != label[v] for u, v in edges)
            value = k * len(blocks) - crossing
            count += 1
            if value > best:
                best, best_partition = value, [list(b) for b in blocks]
            return
        v = vertices[t]
        for block in blocks:
            block.append(v)
            visit(t + 1)
            block.pop()
        blocks.append([v])
        visit(t + 1)
        blocks.pop()

    visit(0)
    return {"eta": best, "maximizing_partition": best_partition, "partitions_examined": count}


def review_roots():
    old = json.loads((BASE / "exact_results.json").read_text(encoding="utf-8"))
    assert all(all(x == g["k"] for x in g["eta_by_root"]) for g in old["graphs"])
    data = json.loads((BASE / "review_root_caps.json").read_text(encoding="utf-8"))
    audits = []
    for g in data["graphs"]:
        edges, n, k = g["edges"], g["n"], g["k"]
        p = partition_eta(n, edges, k, 0)
        assert p["eta"] == g["eta"] > k
        full = (1 << n) - 1
        lam = min(sum(bool(s >> u & 1) != bool(s >> v & 1) for u, v in edges) for s in range(1, full))
        assert lam == g["lambda"] >= 2 * k + 1
        audit = {"name": g["name"], "partition": p, "lambda": lam}
        witness = g["preparation_witness"]
        if witness:
            state = witness["start"]
            heights = []
            minima = []
            for edge_id in [None] + witness["word"]:
                if edge_id is not None:
                    state ^= 1 << edge_id
                arcs = [(u, v) if state >> i & 1 else (v, u) for i, (u, v) in enumerate(edges)]
                heights.append(sum(u == 0 for u, _ in arcs))
                minima.append(min(cutout(arcs, s) for s in range(1, full)))
            assert min(minima) >= k and max(heights) <= witness["cap"] and heights[-1] == g["eta"]
            source = witness["start"]
            blocked = []
            for i, (u, v) in enumerate(edges):
                a, b = (u, v) if source >> i & 1 else (v, u)
                if a == 0:
                    flipped = source ^ (1 << i)
                    arcs = [(x, y) if flipped >> j & 1 else (y, x) for j, (x, y) in enumerate(edges)]
                    shore = next(s for s in range(1, full) if cutout(arcs, s) < k)
                    blocked.append({"edge_id": i, "shore_mask": shore, "outcut_after": cutout(arcs, shore)})
            assert len(blocked) == heights[0]
            audit["preparation_witness"] = {**witness, "heights": heights, "minimum_full_outcuts": minima, "blocked_root_outgoing": blocked}

        # A different algorithm, with every full outcut, for the two m=15 inputs.
        if g["m"] == 15:
            pos, neg = [0] * n, [0] * n
            for i, (u, v) in enumerate(edges):
                pos[u] |= 1 << i
                neg[v] |= 1 << i
            cut_masks = []
            for s in range(1, full):
                cp = cn = 0
                for i, (u, v) in enumerate(edges):
                    if (s >> u & 1) and not (s >> v & 1):
                        cp |= 1 << i
                    elif (s >> v & 1) and not (s >> u & 1):
                        cn |= 1 << i
                cut_masks.append((cp, cn))
            good = {}
            for state in range(1 << len(edges)):
                if all((state & cp).bit_count() + ((~state) & cn).bit_count() >= k for cp, cn in cut_masks):
                    good[state] = (state & pos[0]).bit_count() + ((~state) & neg[0]).bit_count()
            assert len(good) == g["fully_legal"]
            eta = min(good.values())
            queries = nontrivial = 0
            for cap in range(eta + 1, max(good.values()) + 1):
                reached = {s for s, h in good.items() if h == eta}
                queue = deque(reached)
                while queue:
                    s = queue.popleft()
                    for i in range(len(edges)):
                        t = s ^ (1 << i)
                        if t in good and good[t] <= cap and t not in reached:
                            reached.add(t)
                            queue.append(t)
                queried = {s for s, h in good.items() if h == cap}
                assert queried <= reached
                queries += len(queried)
                if cap < g["root_max"]:
                    nontrivial += len(queried)
            assert queries == g["queries"] and nontrivial == g["nontrivial_queries"]
            audit["independent_census"] = {"fully_legal": len(good), "queries": queries, "nontrivial_queries": nontrivial, "method": "all full cuts, capped multi-source BFS"}
        audits.append(audit)
    return {"old_scope": "Every old tested root has eta=k; none tested eta>k.", "new_census_audits": audits,
            "new_queries": sum(g["queries"] for g in data["graphs"]),
            "new_nontrivial_queries": sum(g["nontrivial_queries"] for g in data["graphs"]),
            "limits": "Only four specified graphs; connected outside examples are chains of dense pairs joined by single bridges. Full independent state census only for the two m=15 inputs; other inputs get independent static and witness audits."}


def review_port_cube(g=None):
    if g is None:
        g = json.loads((BASE / "nonosp_source_input.json").read_text(encoding="utf-8"))
    arcs, C, k = [tuple(e) for e in g["arcs"]], g["core"], g["k"]
    n, cset = 1 + max(max(e) for e in arcs), set(C)
    B = sorted(set(range(n)) - cset)
    ci, bi = {v: i for i, v in enumerate(C)}, {v: i for i, v in enumerate(B)}
    cfull, bfull, full = (1 << len(C)) - 1, (1 << len(B)) - 1, (1 << n) - 1
    cmask = sum(1 << v for v in C)
    incoming = [i for i, (u, v) in enumerate(arcs) if u not in cset and v in cset]
    limit = 1 << len(incoming)
    out, deg = [0] * n, [0] * n
    for u, v in arcs:
        out[u] += 1
        deg[u] += 1
        deg[v] += 1
    a = [out[v] - k for v in C]
    mu = [deg[v] - 2 * k for v in C]
    j = sum(u in cset and v not in cset for u, v in arcs) - k
    gx = [sum(1 << v for i, v in enumerate(C) if x >> i & 1) for x in range(cfull + 1)]
    gz = [sum(1 << v for i, v in enumerate(B) if z >> i & 1) for z in range(bfull + 1)]
    filled = [cutout(arcs, cmask | s) for s in gz]
    empty = [cutout(arcs, s) for s in gz]
    z_ports = [sum(1 << t for t, i in enumerate(incoming) if s >> arcs[i][0] & 1) for s in gz]
    internal = [(u, v) for u, v in arcs if u in cset and v in cset]
    ports = [(u, v) if u in cset else (v, u) for u, v in arcs if (u in cset) != (v in cset)]
    danger = []
    for x in range(1, cfull):
        ax = sum(a[t] for t in range(len(C)) if x >> t & 1)
        alpha = k * (x.bit_count() - 1) - sum((gx[x] >> u & 1) and (gx[x] >> v & 1) for u, v in internal)
        if ax + alpha >= j:
            continue
        y = cfull ^ x
        y_ports = sum(1 << t for t, i in enumerate(incoming) if y >> ci[arcs[i][1]] & 1)
        p = [sum((y >> ci[u] & 1) and (s >> v & 1) for u, v in ports) for s in gz]
        danger.append((x, ax, alpha, y_ports, p))
    legal, deleted, failure = [], [], []
    for mask in range(limit):
        active = {incoming[t] for t in range(len(incoming)) if mask >> t & 1}
        ok, witness = strong(n, orientation(arcs, active), k)
        free, _ = strong(n, [e for i, e in enumerate(arcs) if i not in active], k)
        legal.append(ok)
        deleted.append(free)
        failure.append(witness)
    assert legal[0] and deleted[0]
    cubes = []
    predicted = []
    budget_witnesses = []
    endpoint_conditions = []
    for mask in range(limit):
        sub = mask
        all_legal = True
        while True:
            all_legal &= legal[sub]
            if not sub:
                break
            sub = (sub - 1) & mask
        assert all_legal == deleted[mask]
        cubes.append(all_legal)
        active = [incoming[t] for t in range(len(incoming)) if mask >> t & 1]
        capacity = all(a[t] + sum(arcs[i][1] == v for i in active) <= mu[t] for t, v in enumerate(C))
        quotient = all(empty[z] - (mask & z_ports[z]).bit_count() >= k for z in range(1, bfull + 1))
        budget_ok, bad_row = True, None
        for x, ax, alpha, yp, p in danger:
            beta, z = min((filled[z] - k + p[z] - (mask & yp & z_ports[z]).bit_count(), z) for z in range(1, bfull))
            if ax + alpha + beta < j:
                budget_ok = False
                bad_row = {"core_trace_mask": x, "external_trace_mask": z, "shore_mask": gx[x] | gz[z], "paid_beta": beta,
                           "aX": ax, "alpha": alpha, "j": j,
                           "negative_activity_mask": mask & yp & z_ports[z]}
                break
        prediction = capacity and quotient and budget_ok
        assert prediction == all_legal
        predicted.append(prediction)
        budget_witnesses.append(bad_row)
        endpoint_conditions.append(capacity and quotient)
    # Monotone port scheduling can be possible even when not every permutation is.
    parent = [None] * limit
    parent[0] = (-1, -1)
    for mask in range(1, limit):
        if legal[mask]:
            for t in range(len(incoming)):
                old = mask ^ (1 << t)
                if (mask >> t & 1) and parent[old] is not None:
                    parent[mask] = (old, t)
                    break
    choices = [mask for mask in range(1, limit) if parent[mask] is not None and not cubes[mask] and budget_witnesses[mask]]
    if choices:
        mask = min(choices, key=lambda s: (s.bit_count(), s))
    else:
        mask = min((s for s in range(limit) if cubes[s]), key=lambda s: (-s.bit_count(), s))
    word = []
    v = mask
    while v:
        v, t = parent[v]
        word.append(incoming[t])
    word.reverse()
    row = budget_witnesses[mask]
    negative = row["negative_activity_mask"] if row else None
    if negative is not None:
        assert not legal[negative]
        bad_first = [incoming[t] for t in range(len(incoming)) if negative >> t & 1]
        bad_first += [incoming[t] for t in range(len(incoming)) if (mask & ~negative) >> t & 1]
    # Full-cut checking is a separate algorithm from the max-flow classifications.
    adjacency = [0] * n
    multiplicity = [[0] * n for _ in range(n)]
    for u, v in arcs:
        multiplicity[u][v] += 1
        multiplicity[v][u] += 1
        adjacency[u] |= 1 << v
        adjacency[v] |= 1 << u
    simple = all(multiplicity[u][v] <= 1 for u in range(n) for v in range(n))
    inside, initial_out = (array("H", [0]) * (1 << n) for _ in range(2))
    for s in range(1, 1 << n):
        bit = s & -s
        v = bit.bit_length() - 1
        rest = s ^ bit
        added = (adjacency[v] & rest).bit_count() if simple else sum(multiplicity[v][u] for u in range(n) if rest >> u & 1)
        inside[s] = inside[rest] + added
        initial_out[s] = initial_out[rest] + out[v]
    states = [0]
    state = 0
    for edge_id in word:
        state |= 1 << incoming.index(edge_id)
        states.append(state)
    assert states[-1] == mask
    to_check = sorted(set(states + ([] if negative is None else [negative])))
    cut_audits = {}
    for mask_s in to_check:
        delta = [0] * n
        for t, i in enumerate(incoming):
            if mask_s >> t & 1:
                u, v = arcs[i]
                delta[u] -= 1
                delta[v] += 1
        sums = array("h", [0]) * (1 << n)
        best, shore = len(arcs), None
        for s in range(1, full):
            bit = s & -s
            sums[s] = sums[s ^ bit] + delta[bit.bit_length() - 1]
            value = initial_out[s] - inside[s] + sums[s]
            if value < best:
                best, shore = value, s
        assert (best >= k) == legal[mask_s]
        cut_audits[str(mask_s)] = {"minimum_outcut": best, "minimizing_shore": shore}
    ordered_witness = None
    if negative is not None:
        current_bad = orientation(arcs, {incoming[t] for t in range(len(incoming)) if negative >> t & 1})
        assert cutout(current_bad, row["shore_mask"]) < k
        assert all(k <= sum(u == v for u, _ in current_bad) <= deg[v] - k for v in range(n))
        ordered_witness = {"activity_mask": mask, "activity_ids": sorted(word),
                "legal_order": word, "legal_prefix_activity_masks": states, "bad_order": bad_first,
                "bad_prefix_activity_mask": negative, "bad_prefix_is_vertex_legal": True,
                "violated_B3_row": row, "bad_shore_outcut": cutout(current_bad, row["shore_mask"]),
                "full_cut_audits": cut_audits}
    return {"encoding": "activity masks index incoming_ids; physical state bit1 reverses source arc", "incoming_ids": incoming,
            "n": n, "m": len(arcs), "k": k, "core": C, "source_arcs": arcs,
            "all_activity_sets": limit, "nonempty_free_cubes": sum(cubes) - 1,
            "B3_vs_full_cube_mismatches": 0, "deletion_vs_full_cube_mismatches": 0,
            "source_states_classified_by_root_pair_flows": len(legal),
            "ordered_nonfree_endpoint_count": len(choices),
            "B3_extra_rejections_after_vertex_capacity_and_terminal_quotient": sum(ok and not cubes[s] for s, ok in enumerate(endpoint_conditions)),
            "ordered_but_not_universal_witness": ordered_witness,
            "selected_legal_word_full_cut_audits": {"word": word, "prefix_masks": states, "cuts": cut_audits},
            "full_cut_rows_independently_checked": len(to_check) * (full - 1),
            "limits": "All incoming-port subsets at one specified source; no internal preparation or arbitrary-source claim. Full-cut enumeration cross-checks saved words/witnesses, not every classified state."}


def review_structural_examples():
    k = 2
    arcs = []
    for base in (0, 7):
        for i in range(7):
            for step in (1, 2):
                arcs.append((base + i, base + (i + step) % 7))
    for i in range(7):
        arcs.append((i, i + 7) if i < 3 else (i + 7, i))
    n = 14
    full = (1 << n) - 1
    cuts = [(sum(bool(s >> u & 1) != bool(s >> v & 1) for u, v in arcs), s) for s in range(1, full)]
    lam = min(value for value, _ in cuts)
    minshores = [s for value, s in cuts if value == lam]
    nontrivial = [s for s in minshores if min(s.bit_count(), n - s.bit_count()) > 1]
    assert lam == 5 and len(minshores) == 28 and not nontrivial
    shore = (1 << 7) - 1
    dense_each = [sum((s >> u & 1) and (s >> v & 1) for u, v in arcs) for s in (shore, full ^ shore)]
    assert dense_each == [14, 14] and all(x > k * 6 for x in dense_each)
    minimum_out = min(cutout(arcs, s) for s in range(1, full))
    assert minimum_out >= k

    # A legal 4-edge macro on a triangle-free, 5-edge-connected input.
    bip_arcs = []
    for i in range(5):
        for j in range(5):
            if i == j:
                bip_arcs.append((i, 5 + j) if i < 3 else (5 + j, i))
            elif (j - i) % 5 in (1, 2):
                bip_arcs.append((i, 5 + j))
            else:
                bip_arcs.append((5 + j, i))
    path = [0, 6, 2, 8, 3]
    path_ids = [bip_arcs.index(e) for e in zip(path, path[1:])]
    target = orientation(bip_arcs, set(path_ids))
    bip_full = (1 << 10) - 1
    lam_bip = min(sum(bool(s >> u & 1) != bool(s >> v & 1) for u, v in bip_arcs) for s in range(1, bip_full))
    endpoint_minima = [min(cutout(d, s) for s in range(1, bip_full)) for d in (bip_arcs, target)]
    assert lam_bip == 5 and min(endpoint_minima) >= k
    # r=4: the inequalities permit only s=2,t=1, hence a triangle.
    candidates = []
    for i in range(len(path)):
        for j in range(i + 1, len(path)):
            span = j - i
            for t in range(1, span):
                if span + t < len(path) - 1:
                    assert span == 2 and t == 1
                    if (path[i], path[j]) in bip_arcs or (path[j], path[i]) in bip_arcs:
                        candidates.append([i, j, t])
    assert not candidates
    return {"mincut_tree_obstruction": {"n": n, "m": len(arcs), "k": k, "arcs": arcs,
                "lambda": lam, "minimum_cut_oriented_shore_count": len(minshores),
                "nontrivial_minimum_cuts": nontrivial, "nonOSP_shore": shore,
                "internal_edges_on_both_sides": dense_each, "full_legal_source_minimum_outcut": minimum_out,
                "full_cut_count": full - 1,
                "scope": "A mincut-tree reduction alone leaves a nonOSP input with no nontrivial minimum split; not a MAIN counterexample."},
            "balanced_ear_obstruction": {"graph": "K5,5", "k": k, "lambda": lam_bip,
                "arcs": bip_arcs, "path": path, "path_ids": path_ids, "length": 4,
                "source_target_minimum_outcuts": endpoint_minima, "balanced_ears": candidates,
                "full_cut_rows": 2 * (bip_full - 1),
                "scope": "Refutes universal supply of a strictly shortening balanced ear, not the conditional ear decomposition or the possibility of a separate short-macro base case."}}


def review_geometry():
    # Integral full-dimensional parity tetrahedron: all rows have integer data.
    rows = [([1, 1, 1], 2), ([1, -1, -1], 0), ([-1, 1, -1], 0), ([-1, -1, 1], 0)]
    feasible = []
    for mask in range(8):
        x = [mask >> i & 1 for i in range(3)]
        if all(sum(c[i] * x[i] for i in range(3)) <= b for c, b in rows):
            feasible.append(mask)
    assert feasible == [0, 3, 5, 6]
    neighbors = {str(s): [t for t in feasible if (s ^ t).bit_count() == 1] for s in feasible}
    assert all(not x for x in neighbors.values())
    center_slacks = [b - sum(c) / 2 for c, b in rows]
    assert center_slacks == [0.5] * 4
    # Nonnegative barycentric coefficients follow exactly from the four rows:
    # w0=1-(x1+x2+x3)/2; w3=(x1+x2-x3)/2;
    # w5=(x1-x2+x3)/2; w6=(-x1+x2+x3)/2.
    return {"variables": 3, "rows": [{"coefficients": c, "upper_bound": b} for c, b in rows],
            "box": [0, 1], "center": [0.5] * 3, "center_row_slacks": center_slacks,
            "integer_feasible_masks": feasible, "single_coordinate_neighbors": neighbors,
            "integral_polytope_vertices": [[s >> i & 1 for i in range(3)] for s in feasible],
            "full_dimensional": True,
            "scope": "Generic integral polytope counterexample to convexity + integrality + half-unit strict slack implying integer flip connectivity. These are not asserted to be graph outcut rows; not a MAIN counterexample."}


def review_boundaries():
    data = json.loads((BASE / "review_bad_boundary.json").read_text(encoding="utf-8"))
    old = json.loads((BASE / "exact_results.json").read_text(encoding="utf-8"))
    original = next(g for g in old["graphs"] if g["name"] == data["graph"])
    assert data["edges"] == original["edges"]
    edges, n, k = data["edges"], data["n"], data["k"]
    full = (1 << n) - 1
    dense = []
    for s in range(1, full):
        t = full ^ s
        es = sum((s >> u & 1) and (s >> v & 1) for u, v in edges)
        et = sum((t >> u & 1) and (t >> v & 1) for u, v in edges)
        if (s & 1) and es > k * (s.bit_count() - 1) and et > k * (t.bit_count() - 1):
            dense.append(s)
    assert dense == [15, 51]
    C, T = dense
    # These two pairs of opposite corners are sparse. Their diagonal arcs are
    # absent, so directed cut submodularity gives o(C)+o(T)>=4 and
    # o(C)+o(V-T)>=4 throughout the vertex-legal host.
    corner_counts = []
    for s in (C & T, full ^ (C | T), C & (full ^ T), T & (full ^ C)):
        e = sum((s >> u & 1) and (s >> v & 1) for u, v in edges)
        assert e == k * (s.bit_count() - 1) == 2
        corner_counts.append({"mask": s, "internal_edges": e})
    w = data["witness"]
    word, states = w["word"], w["states"]
    assert word == [18, 17] and edges[17] == edges[18] == [1, 5]
    shared = w["start"] ^ (1 << 17)
    assert shared == w["target"] ^ (1 << 18) == 70916
    audits = []
    for state in states + [shared]:
        arcs = [(u, v) if state >> i & 1 else (v, u) for i, (u, v) in enumerate(edges)]
        degree = [sum(u == v or z == v for u, z in edges) for v in range(n)]
        out = [sum(u == v for u, _ in arcs) for v in range(n)]
        assert all(k <= out[v] <= degree[v] - k for v in range(n))
        minimum = min(cutout(arcs, s) for s in range(1, full))
        audits.append({"state": state, "vertex_legal": True, "minimum_full_outcut": minimum,
                       "oC": cutout(arcs, C), "oT": cutout(arcs, T)})
    assert [r["oC"] for r in audits] == [2, 3, 2, 1]
    assert all(r["minimum_full_outcut"] >= k for r in audits[:3]) and audits[3]["minimum_full_outcut"] < k
    assert data["bad_components_with_disconnected_immediate_legal_boundary"] == data["bad_components"] == 122
    return {"census": {key: data[key] for key in ("graph", "n", "m", "k", "lambda", "host", "fully_legal", "bad_components", "bad_components_with_disconnected_immediate_legal_boundary")},
            "independent_witness": {"dense_cut_shores_up_to_complement": dense, "sparse_corners": corner_counts,
                "shared_bad_neighbor": shared, "start": w["start"], "target": w["target"], "word": word,
                "prefix_and_bad_state_full_cut_audits": audits,
                "argument": "If o(C)<=1, both o(T),o(V-T)>=3; one host flip cannot make T illegal. Thus its bad component stays at o(C)<=1, and its legal boundary has o(C)=2. No edge of that boundary can change the C port identities. The two saved boundary points exchange distinct parallel C ports, so they need the saved legal excursion to height3.",
                "full_cut_rows": len(audits) * (full - 1)},
            "limits": "Full 122-component boundary census uses one C++ implementation. Python independently verifies the selected witness and its analytic boundary separation, without repeating that entire state census. This is not a closed legal component or a MAIN counterexample."}


def main():
    roots = review_roots()
    print("root cap scope + new partition/BFS audits PASS", flush=True)
    anchor = review_port_cube()
    assert anchor["all_activity_sets"] == 128 and anchor["nonempty_free_cubes"] == 20
    counter = {"k": 2, "core": [1, 2], "eta": 3,
               "arcs": [(0, 1), (0, 1), (1, 0), (1, 2), (2, 1), (2, 1),
                        (3, 2), (2, 3), (2, 3), (3, 0), (0, 2), (3, 1)]}
    ordered = review_port_cube(counter)
    assert ordered["ordered_but_not_universal_witness"] is not None
    lam = min(sum(bool(s >> u & 1) != bool(s >> v & 1) for u, v in counter["arcs"]) for s in range(1, 15))
    assert lam == 5
    ordered["lambda"] = lam
    ordered["quotient_root_eta"] = partition_eta(3, [(0 if u in (1, 2) else (1 if u == 0 else 2),
                                                     0 if v in (1, 2) else (1 if v == 0 else 2))
                                                    for u, v in counter["arcs"] if not (u in (1, 2) and v in (1, 2))], 2, 0)
    assert ordered["quotient_root_eta"]["eta"] == 3
    ports = {"twenty_point_anchor": anchor, "four_point_ordered_counterexample": ordered}
    print("B3 = deletion = universal cube at both sources; four-point ordered/nonfree witness PASS", flush=True)
    structures = review_structural_examples()
    geometry = review_geometry()
    boundaries = review_boundaries()
    print("bad boundary, mincut tree, balanced ear and integral half-margin obstructions PASS", flush=True)
    result = {"status": "PASS", "root_cap_review": roots, "port_cube_review": ports,
              "bad_boundary_review": boundaries, "structural_examples": structures, "fractional_geometry": geometry,
              "sha256": {p.name: sha256(p.read_bytes()).hexdigest() for p in [Path(__file__), BASE / "review_root_caps.cpp", BASE / "review_root_caps.json", BASE / "review_bad_boundary.cpp", BASE / "review_bad_boundary.json", BASE / "nonosp_source_input.json", BASE / "exact_results.json"]}}
    write_json("review_results.json", result)
    print("review_results.json PASS", flush=True)


if __name__ == "__main__":
    main()
