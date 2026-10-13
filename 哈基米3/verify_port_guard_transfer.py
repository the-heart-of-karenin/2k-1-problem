"""Execute a safe one-unit transport across current g-guard extrema."""
from collections import deque
from pathlib import Path
import hashlib
import json
from verify_deficit_budget_entry import (
    flow_cut, orientation, internal_degrees, full_arc_minimum,
    cone_obstruction, budget_networks, root_pairs,
)

HERE = Path(__file__).resolve().parent


def quotient_arcs(case, mask, omit=None):
    n = case["core_n"]
    out = []
    for e, u, v in orientation(case, mask):
        if e == omit:
            continue
        a = 0 if u < n else u - n + 1
        b = 0 if v < n else v - n + 1
        if a != b:
            out.append((a, b, 1))
    return out


def prepare(case):
    k, n, total, g = case["k"], case["core_n"], case["vertex_n"], case["g"]
    source = case["source_mask"]
    assert full_arc_minimum(case, source) >= k
    qn = total - n + 1
    for mask in (source, source ^ (1 << g)):
        qa = quotient_arcs(case, mask)
        assert min(flow_cut(qn, qa, s, t)[0] for s, t in root_pairs(qn)) >= k
    arcs = [(u, v, 1) for _, u, v in orientation(case, source)]
    g_arc = next((u, v) for e, u, v in orientation(case, source) if e == g)
    x, y = g_arc
    assert x < n <= y
    minimum, small = flow_cut(total, arcs, x, y)
    assert minimum == k  # The controls deliberately exercise blocked g.
    reverse_minimum, reverse_small = flow_cut(total, [(v, u, cap) for u, v, cap in arcs], y, x)
    assert reverse_minimum == k
    large = set(range(total)) - reverse_small
    assert small <= large
    before = internal_degrees(case, source)
    assert sum(before[v] - k for v in small if v < n) < 0
    assert sum(before[v] - k for v in large if v < n) < 0
    trials = []
    selected = None
    for s in range(n):
        if s in large or before[s] <= k:
            continue
        safe = {s}
        local_values = {}
        for v in range(n):
            if v != s:
                value, _ = flow_cut(total, arcs, s, v)
                local_values[str(v)] = value
                if value >= k + 1:
                    safe.add(v)
        outgoing = [[] for _ in range(n)]
        for e, u, v in orientation(case, source, range(case["core_m"])):
            if u in safe and v in safe:
                outgoing[u].append((v, e))
        parent, queue, end = {s: None}, deque([s]), None
        while queue and end is None:
            u = queue.popleft()
            for v, e in outgoing[u]:
                if v not in parent:
                    parent[v] = (u, e)
                    if v in small and before[v] < k:
                        end = v
                        break
                    queue.append(v)
        trials.append({"s": s, "safe_vertices": sorted(safe),
                       "local_flow_values": local_values, "succeeds": end is not None})
        if end is not None:
            vertices, word = [end], []
            while parent[vertices[-1]] is not None:
                u, e = parent[vertices[-1]]
                vertices.append(u)
                word.append(e)
            selected = {"s": s, "t": end, "vertices": list(reversed(vertices)),
                        "word": list(reversed(word))}
            break
    assert selected is not None
    current = source
    for e in selected["word"]:
        current ^= 1 << e
        assert full_arc_minimum(case, current) >= k
    after_arcs = [(u, v, 1) for _, u, v in orientation(case, current)]
    release_value, _ = flow_cut(total, after_arcs, x, y)
    assert release_value >= k + 1
    assert full_arc_minimum(case, current ^ (1 << g)) >= k
    case.update(guard_min_mask=sum(1 << v for v in small),
                guard_max_mask=sum(1 << v for v in large),
                source_g_local_connectivity=minimum, ready_g_local_connectivity=release_value,
                trials=trials, selected_transport=selected, ready_mask=current,
                after_g_mask=current ^ (1 << g),
                source_budget=budget_networks(case),
                source_phi=sum(max(0, k - d) for d in before),
                ready_phi=sum(max(0, k - d) for d in internal_degrees(case, current)))
    return case


def wide_guard(k=2):
    side, n = 2 * k, 4 * k
    z, w = n, n + 1
    edges, mask = [], 0
    for i in range(side):
        for j in range(side):
            e = len(edges)
            edges.append((i, side + j))
            if i == 0 and j >= k:
                mask |= 1 << e
    core_m = len(edges)
    special = {0, side}
    for v in range(n):
        outer = z if v in special else w
        edges.extend([(v, outer)] * k)
        edges.extend([(outer, v)] * k)
    g = len(edges)
    edges.append((0, w))
    return {"name": "positive_width_guard", "family": "read_only_ledger_wide_guard",
            "k": k, "core_n": n, "core_m": core_m, "vertex_n": n + 2,
            "edges": edges, "source_mask": mask, "g": g}


def nested_guards(k=3):
    edges, mask = [], 0
    for u, v, count, reverse in [(0, 1, k, True), (0, 2, 1, True),
                                  (0, 3, k - 1, False), (3, 1, 1, False),
                                  (3, 2, k, False), (1, 2, k - 1, False)]:
        for _ in range(count):
            if reverse:
                mask |= 1 << len(edges)
            edges.append((u, v))
    core_m = len(edges)
    for vertices, z in [([0], 4), ([1, 2], 5), ([3], 6)]:
        for v in vertices:
            edges.extend([(v, z)] * (k + 1))
            edges.extend([(z, v)] * (k + 1))
    g = len(edges)
    edges.append((0, 6))
    return {"name": "two_nested_guards_single_transport", "family": "read_only_ledger_chain",
            "k": k, "core_n": 4, "core_m": core_m, "vertex_n": 7,
            "edges": edges, "source_mask": mask, "g": g}


def critical_after_helper():
    case = cone_obstruction(2)
    case["name"] = "one_port_critical_after_new_unit"
    case["family"] = "known_cone_with_explicit_nonuniversal_preconditioning"
    case["base_source_mask"] = case["source_mask"]
    case["preconditioning_word"] = [5]  # Original R_1 -> L_1.
    case["source_mask"] ^= 1 << 5
    case["g"] = case["core_m"] + 4  # Original R_0 -> r.
    case["preconditioning_is_general_theorem"] = False
    return case


def main():
    cases = [prepare(wide_guard()), prepare(nested_guards()), prepare(critical_after_helper())]
    output = {"status": "PASS", "unconditional_transport_existence": False,
              "source": "candidate172_section11",
              "constructor_sha256": hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
              "cases": cases}
    path = HERE / "port_guard_transfer_certificate.json"
    path.write_text(json.dumps(output, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")
    print(json.dumps({"status": "PASS", "controls": [
        {"name": c["name"], "source_phi": c["source_phi"], "ready_phi": c["ready_phi"],
         "db": c["source_budget"]["passes"], "transport": c["selected_transport"],
         "M": c["guard_min_mask"], "U": c["guard_max_mask"]} for c in cases]}, ensure_ascii=False))


if __name__ == "__main__":
    main()
