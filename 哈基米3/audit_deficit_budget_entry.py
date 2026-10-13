"""Independent complete physical-cut audit. Does not import the constructor."""
from pathlib import Path
from collections import Counter
import hashlib
import json

HERE = Path(__file__).resolve().parent


def physical_tables(n, indexed_edges):
    adjacency = [Counter() for _ in range(n)]
    for _, u, v in indexed_edges:
        assert u != v
        adjacency[u][v] += 1
        adjacency[v][u] += 1
    induced = [0] * (1 << n)
    for shore in range(1, 1 << n):
        bit = shore & -shore
        u, rest = bit.bit_length() - 1, shore ^ bit
        induced[shore] = induced[rest] + sum(count for v, count in adjacency[u].items()
                                            if rest >> v & 1)
    return adjacency, induced


def subset_sums(weights):
    answer = [0] * (1 << len(weights))
    for shore in range(1, len(answer)):
        bit = shore & -shore
        answer[shore] = answer[shore ^ bit] + weights[bit.bit_length() - 1]
    return answer


def directed_ids(case, mask):
    answer = []
    for e, (u, v) in enumerate(case["edges"]):
        answer.append((e, v, u) if mask >> e & 1 else (e, u, v))
    return answer


def outgoing_table(n, directed_edges, induced):
    degrees = [0] * n
    for _, u, _ in directed_edges:
        degrees[u] += 1
    total = subset_sums(degrees)
    return degrees, [total[shore] - induced[shore] for shore in range(1 << n)]


def audit_case(case):
    n, total, k, m = case["core_n"], case["vertex_n"], case["k"], case["core_m"]
    indexed = [(e, *pair) for e, pair in enumerate(case["edges"])]
    all_adjacency, all_induced = physical_tables(total, indexed)
    _, core_induced = physical_tables(n, indexed[:m])
    _, frozen_induced = physical_tables(total, indexed[m:])
    degrees = [sum(row.values()) for row in all_adjacency]
    degree_sums = subset_sums(degrees)
    undirected = [degree_sums[x] - 2 * all_induced[x] for x in range(1 << total)]
    lambda_g = min(undirected[1:-1])
    assert lambda_g >= 2 * k + 1
    core_degrees = [0] * n
    for _, u, v in indexed[:m]:
        core_degrees[u] += 1
        core_degrees[v] += 1
    assert core_degrees == [2 * k] * n
    for trace in range(1, (1 << n) - 1):
        assert core_induced[trace] <= k * (trace.bit_count() - 1)
    target_arcs = directed_ids(case, case["target_mask"])
    target_degrees = [0] * n
    for _, u, _ in target_arcs[:m]:
        target_degrees[u] += 1
    assert target_degrees == [k] * n
    source_arcs = directed_ids(case, case["source_mask"])
    frozen_degrees, frozen_cuts = outgoing_table(total, source_arcs[m:], frozen_induced)
    f = [0] * (1 << n)
    minimizers = [0] * (1 << n)
    for trace in range(1, (1 << n) - 1):
        candidates = [(frozen_cuts[trace | (z << n)], z)
                      for z in range(1 << (total - n))]
        f[trace], minimizers[trace] = min(candidates)
    delta_h = [2 * k * x.bit_count() - 2 * core_induced[x] for x in range(1 << n)]
    capacity = [delta_h[x] // 2 - k + f[x] for x in range(1 << n)]
    source_internal = [0] * n
    for _, u, _ in source_arcs[:m]:
        source_internal[u] += 1
    deficits = [max(0, k - degree) for degree in source_internal]
    deficit_sums = subset_sums(deficits)
    phi = sum(deficits)
    db = all(deficit_sums[x] <= capacity[x] for x in range(1, (1 << n) - 1))
    rho = min(f[1:-1])
    cert = case["budget_certificate"]
    assert cert["source_deficits"] == deficits and cert["source_phi"] == phi
    assert cert["passes"] == db and cert["terminal_rho"] == rho
    for query in cert["queries"]:
        u, v, shore = query["u"], query["v"], query["shore_mask"]
        trace = shore & ((1 << n) - 1)
        assert trace >> u & 1 and not trace >> v & 1
        value = delta_h[trace] + 2 * frozen_cuts[shore] + 2 * (phi - deficit_sums[trace])
        expected = min(delta_h[x] + 2 * f[x] + 2 * (phi - deficit_sums[x])
                       for x in range(1, (1 << n) - 1) if x >> u & 1 and not x >> v & 1)
        assert value == query["value"] == expected
    for query in cert["terminal_queries"]:
        u, v, shore = query["u"], query["v"], query["shore_mask"]
        assert shore >> u & 1 and not shore >> v & 1
        expected = min(f[x] for x in range(1, (1 << n) - 1)
                       if x >> u & 1 and not x >> v & 1)
        assert frozen_cuts[shore] == query["value"] == expected

    physical_rows, full_rows, visited = 0, 0, set()
    cache = {}

    def inspect(mask):
        nonlocal physical_rows, full_rows
        if mask not in cache:
            arcs = directed_ids(case, mask)
            vertex_out, cuts = outgoing_table(total, arcs, all_induced)
            minimum = min(cuts[1:-1])
            assert minimum >= k, (case["name"], mask, minimum)
            internal = [0] * n
            for _, u, _ in arcs[:m]:
                internal[u] += 1
            now_deficits = [max(0, k - degree) for degree in internal]
            full_rows += (1 << total) - 2
            # Literal edge counting cross-checks the complete-cut degree identity.
            sample = range(1, (1 << total) - 1) if total <= 9 else {
                1, (1 << n) - 1, (1 << total) - 2,
                *(1 << v for v in range(total)),
                *(((v * 811 + 37) % ((1 << total) - 2)) + 1 for v in range(128)),
            }
            for shore in sample:
                literal = sum(bool(shore >> u & 1) and not (shore >> v & 1)
                              for _, u, v in arcs)
                assert literal == cuts[shore]
                physical_rows += 1
            cache[mask] = (internal, now_deficits, minimum)
        visited.add(mask)
        return cache[mask]

    inspect(case["source_mask"])
    if case["mode"] == "reject":
        assert not db
        x, s = case["analytic_failure_trace"], case["analytic_failure_shore"]
        assert deficit_sums[x] == 1 and capacity[x] == 0
        assert frozen_cuts[s] == 0 and delta_h[x] == 2 * k
        external_counts = [degrees[v] - 2 * k for v in range(n)]
        assert external_counts == [1] * n
        return {"name": case["name"], "status": "PASS_EXPECTED_REJECTION",
                "lambda_g": lambda_g, "rho": rho, "phi": phi,
                "full_cut_rows": full_rows, "literal_cut_crosschecks": physical_rows,
                "failure_trace": x, "failure_shore": s}

    assert db
    current = case["source_mask"]
    word = case["word"]
    assert len(set(word)) == len(word)
    differing = case["source_mask"] ^ case["target_mask"]
    assert all(0 <= e < m and differing >> e & 1 for e in word)
    phi_history, entrance_deficits = [phi], [deficits]
    mask_history = [current]
    for step, e in enumerate(word, 1):
        current ^= 1 << e
        internal, now_deficits, _ = inspect(current)
        assert (current ^ case["source_mask"]) >> m == 0
        phi_history.append(sum(now_deficits))
        mask_history.append(current)
        if step <= case["entrance_steps"]:
            assert all(a <= b for a, b in zip(now_deficits, entrance_deficits[-1]))
            assert phi_history[-1] <= phi_history[-2]
            now_n = subset_sums(now_deficits)
            assert all(now_n[x] <= capacity[x] for x in range(1, (1 << n) - 1))
            entrance_deficits.append(now_deficits)
    assert current == case["final_mask"]
    assert inspect(mask_history[case["entrance_steps"]])[0] == [k] * n
    assert inspect(current)[0] == [k] * n
    if case["mode"] == "exact":
        assert current == case["target_mask"]
        assert len(word) == differing.bit_count()
        assert rho >= 1
        assert max(phi_history) <= max(phi, 1)
    for macro in case["macros"]:
        begin, end = macro["begin"], macro["end"]
        assert word[begin:end] == macro["ids"]
        assert end - begin == len(macro["vertices"]) - 1
        source = mask_history[begin]
        vertices = macro["vertices"]
        arc_dict = {e: (u, v) for e, u, v in directed_ids(case, source)}
        assert all(arc_dict[e] == (u, v) for e, u, v in
                   zip(macro["ids"], vertices, vertices[1:]))
        before = inspect(source)[0]
        after = inspect(mask_history[end])[0]
        if macro["kind"] == "path":
            assert len(set(vertices)) == len(vertices)
            assert before[vertices[0]] > k and before[vertices[-1]] < k
            assert all(before[v] == k for v in vertices[1:-1])
            expected = before[:]
            expected[vertices[0]] -= 1
            expected[vertices[-1]] += 1
            assert after == expected
            assert phi_history[end] == phi_history[begin] - 1
        else:
            assert vertices[0] == vertices[-1]
            assert len(set(vertices[:-1])) == len(vertices) - 1
            assert before == after == [k] * n
    # Accurate reverse replay uses each identical physical ID.
    for e in reversed(word):
        current ^= 1 << e
        inspect(current)
    assert current == case["source_mask"]

    r_out = sum(frozen_degrees[:n])
    s_in = sum(1 for _, u, v in source_arcs[m:] if u >= n and v < n)
    if case["family"] == "critical_exterior_ring":
        assert not any(u >= n and v >= n for _, u, v in indexed)
        assert all(sum(1 for _, u, _ in source_arcs if u == z) == k for z in range(n, total))
        assert r_out == n * (k + 1) and s_in == n * k
        assert n * k > k + 1
        assert rho == (k - case["amounts"][0])
    return {"name": case["name"], "status": "PASS", "lambda_g": lambda_g,
            "rho": rho, "phi": phi, "budget_passes": db,
            "quotient_root_out_in": [r_out, s_in],
            "exterior_independent": not any(u >= n and v >= n for _, u, v in indexed),
            "entrance_steps": case["entrance_steps"], "word_length": len(word),
            "paths": sum(m["kind"] == "path" for m in case["macros"]),
            "cycles": sum(m["kind"] == "cycle" for m in case["macros"]),
            "phi_history": phi_history, "physical_states": len(visited),
            "full_cut_rows": full_rows, "literal_cut_crosschecks": physical_rows,
            "literal_trace_rows": (1 << n) - 2,
            "external_trace_minimizations": ((1 << n) - 2) * (1 << (total - n))}


def main():
    certificate_path = HERE / "deficit_budget_entry_certificate.json"
    payload = json.loads(certificate_path.read_text(encoding="utf-8"))
    source_integrity = {}
    for relative, expected in payload["source_baseline_sha256"].items():
        actual = hashlib.sha256((HERE.parent / relative).read_bytes()).hexdigest()
        assert actual == expected, relative
        source_integrity[relative] = "UNCHANGED"
    results = [audit_case(case) for case in payload["cases"]]
    output = {"status": "PASS", "constructor_imported": False,
              "source_integrity": source_integrity,
              "certificate_sha256": hashlib.sha256(certificate_path.read_bytes()).hexdigest(),
              "auditor_sha256": hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
              "cases": results,
              "total_complete_directed_cut_rows": sum(x["full_cut_rows"] for x in results),
              "total_literal_identity_crosschecks": sum(x["literal_cut_crosschecks"] for x in results),
              "universal_quantifiers_supplied_by": "analytic_proof_not_controls"}
    destination = HERE / "deficit_budget_entry_independent_audit.json"
    destination.write_text(json.dumps(output, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")
    print(json.dumps(output, ensure_ascii=False))


if __name__ == "__main__":
    main()
