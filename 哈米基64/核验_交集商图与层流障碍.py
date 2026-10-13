"""Selected literal controls for the general derivations, not orientation enumeration."""
from collections import deque
from pathlib import Path
import json


class UnionFind:
    def __init__(self, n):
        self.p = list(range(n))

    def find(self, x):
        while self.p[x] != x:
            self.p[x] = self.p[self.p[x]]
            x = self.p[x]
        return x

    def union(self, x, y):
        x, y = self.find(x), self.find(y)
        if x != y:
            self.p[x] = y


def components(n, edges, ids):
    uf = UnionFind(n)
    for e in ids:
        uf.union(*edges[e])
    roots = sorted({uf.find(v) for v in range(n)})
    index = {v: i for i, v in enumerate(roots)}
    return [index[uf.find(v)] for v in range(n)], len(roots)


def bfs_path(adj, start, goal):
    if start == goal:
        return []
    parent = {start: None}
    q = deque([start])
    while q and goal not in parent:
        u = q.popleft()
        for v, e, sign in adj[u]:
            if v not in parent:
                parent[v] = (u, e, sign)
                q.append(v)
    assert goal in parent
    path = []
    u = goal
    while u != start:
        v, e, sign = parent[u]
        path.append((e, sign))
        u = v
    return path[::-1]


def divergence(n, edges, f):
    b = [0] * n
    for (u, v), value in zip(edges, f):
        b[u] += value
        b[v] -= value
    return b


def classify_intersection(n, edges, requirements):
    free = [e for e, req in enumerate(requirements) if not req]
    zero = [e for e, req in enumerate(requirements) if len(req) == 2]
    hard = [e for e, req in enumerate(requirements) if len(req) == 1]
    comp, count = components(n, edges, free)
    qadj = [[] for _ in range(count)]
    qrev = [[] for _ in range(count)]
    arcs = []
    for e in hard:
        sign = next(iter(requirements[e]))
        tail, head = edges[e] if sign == 1 else edges[e][::-1]
        u, v = comp[tail], comp[head]
        arcs.append((u, v, e, sign, tail, head))
        qadj[u].append((v, e, sign))
        qrev[v].append((u, e, sign))
    visited, order = set(), []

    def visit(u):
        visited.add(u)
        for v, _, _ in qadj[u]:
            if v not in visited:
                visit(v)
        order.append(u)

    for u in range(count):
        if u not in visited:
            visit(u)
    scc = [-1] * count

    def assign(u, label):
        scc[u] = label
        for v, _, _ in qrev[u]:
            if scc[v] == -1:
                assign(v, label)

    label = 0
    for u in reversed(order):
        if scc[u] == -1:
            assign(u, label)
            label += 1
    cyclic = [arc for arc in arcs if scc[arc[0]] == scc[arc[1]]]
    surviving = free + [arc[2] for arc in cyclic]
    _, surviving_count = components(n, edges, surviving)
    dim = len(surviving) - n + surviving_count
    lineality_dim = len(free) - n + count
    witness = None
    if cyclic:
        u, v, e, sign, _, _ = cyclic[0]
        cycle = [(e, sign)] + bfs_path(qadj, v, u)
        f = [0] * len(edges)
        free_adj = [[] for _ in range(n)]
        for eid in free:
            a, b = edges[eid]
            free_adj[a].append((b, eid, 1))
            free_adj[b].append((a, eid, -1))
        for i, (eid, direction) in enumerate(cycle):
            tail, head = edges[eid] if direction == 1 else edges[eid][::-1]
            next_e, next_sign = cycle[(i + 1) % len(cycle)]
            next_tail = edges[next_e][0 if next_sign == 1 else 1]
            f[eid] += direction
            for path_e, path_sign in bfs_path(free_adj, head, next_tail):
                f[path_e] += path_sign
        assert divergence(n, edges, f) == [0] * n
        assert all(f[eid] == 0 for eid in zero)
        assert all(f[eid] * next(iter(requirements[eid])) >= 0 for eid in hard)
        assert any(f[eid] * next(iter(requirements[eid])) > 0 for eid in hard)
        witness = {"nonzero_identities": sum(x != 0 for x in f), "exact_conservation": True}
    return {
        "nonlinear": bool(cyclic), "dimension": dim,
        "lineality_dimension": lineality_dim,
        "quotient_vertices": count, "forced_zero_conflicts": len(zero),
        "cycle_witness": witness,
    }


def maxflow(n, arcs, source, target):
    g = [[] for _ in range(n)]
    for u, v in arcs:
        g[u].append([v, 1, len(g[v])])
        g[v].append([u, 0, len(g[u]) - 1])
    total = 0
    while True:
        level = [-1] * n
        level[source] = 0
        q = deque([source])
        while q:
            u = q.popleft()
            for v, cap, _ in g[u]:
                if cap and level[v] == -1:
                    level[v] = level[u] + 1
                    q.append(v)
        if level[target] == -1:
            return total
        it = [0] * n

        def send(u, amount):
            if u == target:
                return amount
            while it[u] < len(g[u]):
                edge = g[u][it[u]]
                v, cap, rev = edge
                if cap and level[v] == level[u] + 1:
                    value = send(v, min(amount, cap))
                    if value:
                        edge[1] -= value
                        g[v][rev][1] += value
                        return value
                it[u] += 1
            return 0

        while True:
            value = send(source, len(arcs) + 1)
            if not value:
                break
            total += value


def rooted_global_mincut(n, arcs):
    return min(maxflow(n, arcs, u, v)
               for target in range(1, n) for u, v in [(0, target), (target, 0)])


def cut_requirements(edges, shore, allowed, polarity):
    result = [set() for _ in edges]
    for e, (u, v) in enumerate(edges):
        epsilon = int(u in shore) - int(v in shore)
        if epsilon and e not in allowed:
            result[e].add(-epsilon if polarity == "+" else epsilon)
    return result


def merge_requirements(*families):
    return [set().union(*(family[e] for family in families))
            for e in range(len(families[0]))]


def positive_circulation(n, edges, directions):
    adj = [[] for _ in range(n)]
    for e, sign in directions.items():
        u, v = edges[e] if sign == 1 else edges[e][::-1]
        adj[u].append((v, e, sign))
    f = [0] * len(edges)
    for e, sign in directions.items():
        u, v = edges[e] if sign == 1 else edges[e][::-1]
        f[e] += sign
        for path_e, path_sign in bfs_path(adj, v, u):
            f[path_e] += path_sign
    assert divergence(n, edges, f) == [0] * n
    assert all(f[e] * sign > 0 for e, sign in directions.items())
    assert all(f[e] == 0 for e in range(len(edges)) if e not in directions)
    return f


def laminar_obstruction_control():
    r, s = 2, 7
    n = 3 * s
    blocks = [list(range(i * s, (i + 1) * s)) for i in range(3)]
    R, T, outside = blocks
    A = set(R + T)
    edges, lookup = [], {}

    def add(u, v):
        pair = tuple(sorted((u, v)))
        assert pair not in lookup
        lookup[pair] = len(edges)
        edges.append(pair)
        return lookup[pair]

    for block in blocks:
        for i in range(s):
            for j in range(i + 1, s):
                add(block[i], block[j])
    for u in R + T:
        for v in outside:
            add(u, v)
    cross = [add(R[j], T[j]) for j in range(r)]
    cross += [add(R[j], T[j + r]) for j in range(r)]
    F = {lookup[tuple(sorted((T[j], outside[j])))] for j in range(r)}
    J = {lookup[tuple(sorted((T[j], outside[j + r])))] for j in range(r)}
    req = merge_requirements(cut_requirements(edges, A, F, "+"),
                             cut_requirements(edges, A, J, "-"))
    data = classify_intersection(n, edges, req)
    assert data["nonlinear"]
    original_arcs = [arc for u, v in edges for arc in [(u, v), (v, u)]]
    original_lambda = rooted_global_mincut(n, original_arcs)
    assert original_lambda >= 2 * r + 3
    states = []
    for outgoing in [set(cross[:r]), set(cross[r:])]:
        directions = {}
        for block in blocks:
            for i in range(s):
                for j in range(i + 1, s):
                    e = lookup[(block[i], block[j])]
                    directions[e] = 1 if j - i <= (s - 1) // 2 else -1
        for e in cross:
            directions[e] = 1 if e in outgoing else -1
        for e in F:
            directions[e] = 1
        for e in J:
            directions[e] = -1
        active_arcs = [edges[e] if sign == 1 else edges[e][::-1]
                       for e, sign in directions.items()]
        value = rooted_global_mincut(n, active_arcs)
        assert value == r
        f = positive_circulation(n, edges, directions)
        assert all(not sign_set or
                   (f[e] == 0 if len(sign_set) == 2
                    else f[e] * next(iter(sign_set)) >= 0)
                   for e, sign_set in enumerate(req))
        assert sum(f[e] > 0 for e in cross) == r
        assert sum(f[e] < 0 for e in cross) == r
        states.append({"active_mincut": value, "positive_flow_exact": True})
    opposite_same = merge_requirements(cut_requirements(edges, A, F, "+"),
                                      cut_requirements(edges, A, F, "-"))
    linear_data = classify_intersection(n, edges, opposite_same)
    assert not linear_data["nonlinear"]
    assert linear_data["dimension"] == linear_data["lineality_dimension"]
    return {"r": r, "s": s, "vertices": n, "identities": len(edges),
            "original_undirected_mincut": original_lambda,
            "nonlinear_intersection": data, "linear_intersection": linear_data,
            "two_distinct_cut_assignments": states}


def directed_cycle_controls():
    n = 37
    edges = [(u, (u + 1) % n) for u in range(n)]
    positive = [{1} for _ in edges]
    a = classify_intersection(n, edges, positive)
    assert a["nonlinear"] and a["dimension"] == 1
    negative_one = [set(req) for req in positive]
    negative_one[0] = {-1}
    b = classify_intersection(n, edges, negative_one)
    assert not b["nonlinear"] and b["dimension"] == 0
    return {"vertices": n, "cyclic": a, "acyclic": b}


def uncrossing_controls():
    r, n = 2, 12
    edges = [(u, v) for u in range(n) for v in range(u + 1, n)]
    I, A, D, W = [set(range(3 * i, 3 * i + 3)) for i in range(4)]
    S, T = I | A, I | D

    def between(X, Y):
        return {e for e, (u, v) in enumerate(edges)
                if (u in X and v in Y) or (u in Y and v in X)}

    def selected(X, Y):
        return set(sorted(between(X, Y))[:r])

    checks = []
    for mixed, strict in [(False, False), (False, True), (True, False), (True, True)]:
        if not mixed:
            F = selected(A, D) if strict else selected(A, W)
            J = selected(A, D) if strict else selected(I, A)
            M1 = (J & between(I, A)) | (F & between(I, D)) | (F & J & between(I, W))
            M2 = (F & between(A, W)) | (J & between(D, W)) | (F & J & between(I, W))
            new = [(I, M1, "+"), (S | T, M2, "+")]
            lost = len(F & between(A, D)) + len(J & between(A, D))
            lost += len((F ^ J) & between(I, W))
        else:
            F = selected(I, W) if strict else selected(A, W)
            J = selected(I, W) if strict else selected(D, W)
            M1 = (J & between(I, A)) | (F & between(A, W)) | (F & J & between(A, D))
            M2 = (F & between(I, D)) | (J & between(D, W)) | (F & J & between(A, D))
            new = [(A, M1, "+"), (D, M2, "-")]
            lost = len(F & between(I, W)) + len(J & between(I, W))
            lost += len((F ^ J) & between(A, D))
        old_req = merge_requirements(cut_requirements(edges, S, F, "+"),
                                     cut_requirements(edges, T, J, "-" if mixed else "+"))
        for shore, allowed, polarity in new:
            new_req = cut_requirements(edges, shore, allowed, polarity)
            for old, current in zip(old_req, new_req):
                assert not current or len(old) == 2 or old == current
        assert len(M1) + len(M2) == 2 * r - lost
        assert (len(M1), len(M2)) == ((0, 0) if strict else (r, r))
        checks.append({"mixed_polarity": mixed, "strict_budget_loss": strict,
                       "coordinatewise_cone_inclusion": True, "exact_budget_identity": True})
    return checks


def main():
    result = {
        "status": "PASS",
        "scope": "Selected exact controls of the general mechanism; no orientation-state enumeration.",
        "universal_quantifiers_from_analytic_proof": True,
        "MAIN_claimed": False,
        "laminar_obstruction": laminar_obstruction_control(),
        "mixed_quotient": directed_cycle_controls(),
        "uncrossing_inclusions": uncrossing_controls(),
    }
    destination = Path(__file__).resolve().parent / "核验_交集商图与层流障碍.json"
    destination.write_text(json.dumps(result, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")
    print(json.dumps({"status": result["status"], "controls_only": True}, ensure_ascii=False))


if __name__ == "__main__":
    main()
