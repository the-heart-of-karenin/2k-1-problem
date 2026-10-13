"""Construct the proposed general entry mechanism; no reconfiguration search."""
from collections import deque
from pathlib import Path
import hashlib
import json

HERE = Path(__file__).resolve().parent
ROOT = HERE.parent


def flow_cut(n, arcs, source, sink):
    adj = [[] for _ in range(n)]
    for u, v, cap in arcs:
        if cap:
            adj[u].append([v, cap, len(adj[v])])
            adj[v].append([u, 0, len(adj[u]) - 1])
    value = 0
    while True:
        level = [-1] * n
        level[source] = 0
        queue = deque([source])
        while queue:
            u = queue.popleft()
            for v, cap, _ in adj[u]:
                if cap and level[v] < 0:
                    level[v] = level[u] + 1
                    queue.append(v)
        if level[sink] < 0:
            break
        at = [0] * n

        def push(u, amount):
            if u == sink:
                return amount
            while at[u] < len(adj[u]):
                edge = adj[u][at[u]]
                v, cap, reverse = edge
                if cap and level[v] == level[u] + 1:
                    sent = push(v, min(amount, cap))
                    if sent:
                        edge[1] -= sent
                        adj[v][reverse][1] += sent
                        return sent
                at[u] += 1
            return 0

        while True:
            sent = push(source, sum(c for _, _, c in arcs) + 1)
            if not sent:
                break
            value += sent
    seen = {source}
    queue = deque([source])
    while queue:
        for v, cap, _ in adj[queue.popleft()]:
            if cap and v not in seen:
                seen.add(v)
                queue.append(v)
    return value, seen


def orientation(case, mask, ids=None):
    for e in range(len(case["edges"])) if ids is None else ids:
        u, v = case["edges"][e]
        if mask >> e & 1:
            u, v = v, u
        yield e, u, v


def internal_degrees(case, mask):
    degrees = [0] * case["core_n"]
    for _, u, _ in orientation(case, mask, range(case["core_m"])):
        degrees[u] += 1
    return degrees


def full_arc_minimum(case, mask):
    arcs = [(u, v, 1) for _, u, v in orientation(case, mask)]
    return min(flow_cut(case["vertex_n"], arcs, u, v)[0]
               for u, v in root_pairs(case["vertex_n"]))


def root_pairs(n):
    return [(0, v) for v in range(1, n)] + [(v, 0) for v in range(1, n)]


def budget_networks(case):
    n, total, k = case["core_n"], case["vertex_n"], case["k"]
    source_mask = case["source_mask"]
    deficits = [max(0, k - x) for x in internal_degrees(case, source_mask)]
    phi = sum(deficits)
    mutable = []
    for u, v in case["edges"][:case["core_m"]]:
        mutable.extend([(u, v, 1), (v, u, 1)])
    frozen = [(u, v, 2) for _, u, v in orientation(
        case, source_mask, range(case["core_m"], len(case["edges"])))]
    weighted = mutable + frozen + [(total, v, 2 * amount)
                                  for v, amount in enumerate(deficits) if amount]
    big = sum(c for _, _, c in weighted) + 1
    queries = []
    for u, v in root_pairs(n):
        value, side = flow_cut(total + 2, weighted + [(total, u, big),
                                                    (v, total + 1, big)],
                               total, total + 1)
        queries.append({"u": u, "v": v, "value": value,
                        "shore_mask": sum(1 << x for x in side if x < total)})
    terminal_queries = []
    for u, v in root_pairs(n):
        value, side = flow_cut(total, [(a, b, cap // 2) for a, b, cap in frozen], u, v)
        terminal_queries.append({"u": u, "v": v, "value": value,
                                 "shore_mask": sum(1 << x for x in side)})
    minimum = min(q["value"] for q in queries)
    return {"source_deficits": deficits, "source_phi": phi,
            "threshold": 2 * (k + phi), "minimum": minimum,
            "passes": minimum >= 2 * (k + phi), "queries": queries,
            "terminal_rho": min(q["value"] for q in terminal_queries),
            "terminal_queries": terminal_queries}


def difference_path(case, current, target):
    n, k = case["core_n"], case["k"]
    degrees = internal_degrees(case, current)
    adj = [[] for _ in range(n)]
    for e, u, v in orientation(case, current, range(case["core_m"])):
        if (current ^ target) >> e & 1:
            adj[u].append((v, e))
    parent = {v: None for v in range(n) if degrees[v] > k}
    queue = deque(parent)
    end = None
    while queue and end is None:
        u = queue.popleft()
        for v, e in adj[u]:
            if v not in parent:
                parent[v] = (u, e)
                if degrees[v] < k:
                    end = v
                    break
                queue.append(v)
    assert end is not None
    path, vertices = [], [end]
    while parent[vertices[-1]] is not None:
        u, e = parent[vertices[-1]]
        path.append(e)
        vertices.append(u)
    return list(reversed(path)), list(reversed(vertices))


def difference_cycle(case, current, target):
    adj = [[] for _ in range(case["core_n"])]
    for e, u, v in orientation(case, current, range(case["core_m"])):
        if (current ^ target) >> e & 1:
            adj[u].append((v, e))
    start = next(v for v, outgoing in enumerate(adj) if outgoing)
    positions, vertices, edges = {}, [], []
    u = start
    while u not in positions:
        positions[u] = len(vertices)
        vertices.append(u)
        v, e = adj[u][0]
        edges.append(e)
        u = v
    first = positions[u]
    return edges[first:], vertices[first:] + [u]


def construct(case):
    network = budget_networks(case)
    case["budget_certificate"] = network
    assert full_arc_minimum(case, case["source_mask"]) >= case["k"]
    if case["mode"] == "reject":
        assert not network["passes"]
        case.update(word=[], macros=[], entrance_steps=None,
                    final_mask=case["source_mask"])
        return case
    assert network["passes"]
    if case["mode"] == "exact":
        assert network["terminal_rho"] >= 1
    current, target = case["source_mask"], case["target_mask"]
    word, macros = [], []

    def append_macro(ids, vertices, kind):
        nonlocal current
        begin = len(word)
        for e in ids:
            assert (current ^ target) >> e & 1
            current ^= 1 << e
            word.append(e)
            assert full_arc_minimum(case, current) >= case["k"]
        macros.append({"kind": kind, "begin": begin, "end": len(word),
                       "ids": ids, "vertices": vertices})

    while any(x != case["k"] for x in internal_degrees(case, current)):
        ids, vertices = difference_path(case, current, target)
        append_macro(ids, vertices, "path")
    entrance_steps = len(word)
    if case["mode"] == "exact":
        while (current ^ target) & ((1 << case["core_m"]) - 1):
            ids, vertices = difference_cycle(case, current, target)
            append_macro(ids, vertices, "cycle")
        assert current == target
    case.update(word=word, macros=macros, entrance_steps=entrance_steps,
                final_mask=current)
    return case


def ring_case(name, k, n, amounts, paths, cycles, mode="exact"):
    assert n >= 2 * k + 1
    edges = [(i, (i + j) % n) for i in range(n) for j in range(1, k + 1)]
    core_m = len(edges)
    by_arc = {arc: e for e, arc in enumerate(edges)}
    source = 0
    selected = []
    for vertices in paths + cycles:
        for u, v in zip(vertices, vertices[1:]):
            selected.append(by_arc[u, v])
    assert len(set(selected)) == len(selected)
    for e in selected:
        source |= 1 << e
    for i, amount in enumerate(amounts):
        j, z = (i + 1) % n, n + i
        edges.extend([(i, z)] * (k - amount))
        edges.extend([(z, i)] * amount)
        edges.extend([(j, z)] * (amount + 1))
        edges.extend([(z, j)] * (k - amount))
    return {"name": name, "family": "critical_exterior_ring", "k": k,
            "core_n": n, "core_m": core_m, "vertex_n": 2 * n,
            "edges": edges, "source_mask": source, "target_mask": 0,
            "mode": mode, "amounts": amounts,
            "definition_paths": paths, "definition_cycles": cycles}


def cone_obstruction(k=2):
    n, r, side = 4 * k, 4 * k, 2 * k
    edges, source, target = [], 0, 0
    for i in range(side):
        for j in range(side):
            if i == 0:
                lr = 1 <= j <= k + 1
            elif j == 0:
                lr = i <= k + 1
            else:
                lr = (j - i) % (side - 1) in range(1, k) or (i == j and i >= k + 2)
            e = len(edges)
            edges.append((i, side + j))
            if not lr:
                source |= 1 << e
            if (j - i) % side not in range(k):
                target |= 1 << e
    core_m = len(edges)
    edges.extend([(r, i) for i in range(side)])
    edges.extend([(side + j, r) for j in range(side)])
    return {"name": "one_port_cone_known_negative_control", "family": "known_cone",
            "k": k, "core_n": n, "core_m": core_m, "vertex_n": n + 1,
            "edges": edges, "source_mask": source, "target_mask": target,
            "mode": "reject", "analytic_failure_trace": ((1 << n) - 1) ^ (1 << (side + 1)),
            "analytic_failure_shore": ((1 << (n + 1)) - 1) ^ (1 << (side + 1))}


def main():
    references = [
        "2k+1/研究启动必读_方法与停止规则_2026-10-12.md",
        "2k+1/研究续接_2026-10-13_结果172进行中.json",
        "2k+1/研究结果170_双单位入守卫与任意端口尾准备_2026-10-12.md",
        "2k+1/研究结果171_最大余量核的最小割递归与通用商代表_2026-10-13.md",
        "2k+1/研究探索172_最小割窄面与回路构造保持_2026-10-13.md",
    ]
    baseline = {p: hashlib.sha256((ROOT / p).read_bytes()).hexdigest() for p in references}
    cases = [
        ring_case("one_unit_path_and_cycle", 2, 8, [1] + [0] * 7,
                  [[0, 2, 4]], [[0, 1, 3, 5, 7, 0]]),
        ring_case("two_unit_paths_and_cycle", 3, 7, [1] + [0] * 6,
                  [[0, 2, 4], [1, 3, 5]], [[0, 1, 4, 0]]),
        ring_case("zero_terminal_rho_valid_entry", 2, 8, [2] + [0] * 7,
                  [[1, 3, 5]], [], mode="entry"),
        cone_obstruction(),
    ]
    output = {"status": "PASS", "scope": "general_mechanism_controls_not_classification",
              "source_baseline_sha256": baseline,
              "constructor_sha256": hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
              "cases": [construct(case) for case in cases],
              "does_not_claim": ["arbitrary_far_entry", "MAIN", "all_zero_rho_phases"]}
    destination = HERE / "deficit_budget_entry_certificate.json"
    destination.write_text(json.dumps(output, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")
    print(json.dumps({"status": "PASS", "file": str(destination),
                      "controls": [{"name": case["name"], "rho": case["budget_certificate"]["terminal_rho"],
                                    "phi": case["budget_certificate"]["source_phi"],
                                    "budget": case["budget_certificate"]["passes"],
                                    "entrance_steps": case["entrance_steps"],
                                    "word_length": len(case["word"])} for case in output["cases"]]},
                     ensure_ascii=False))


if __name__ == "__main__":
    main()
