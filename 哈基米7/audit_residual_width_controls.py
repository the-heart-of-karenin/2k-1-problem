"""Independent literal-cut audit. Does not import the constructor or old engines."""
from __future__ import annotations

import hashlib
import json
from pathlib import Path

ROOT = Path(__file__).resolve().parent


def undirected_cut(edges, shore):
    return sum(((shore >> u) & 1) != ((shore >> v) & 1) for u, v in edges)


def outgoing_cut(edges, tails, shore):
    total = 0
    for (u, v), tail in zip(edges, tails):
        assert tail in (u, v)
        head = v if tail == u else u
        total += bool((shore >> tail) & 1) and not bool((shore >> head) & 1)
    return total


def audit_case(case):
    k, n, nc = case["k"], case["vertices"], case["core_size"]
    mh, edges = case["core_edge_count"], case["edges"]
    core, exterior = edges[:mh], edges[mh:]
    full_core = (1 << nc) - 1
    full = (1 << n) - 1
    q = mh - k * (nc - 1)
    assert q >= 1 and all(u != v for u, v in edges)
    assert all(u < nc and v < nc for u, v in core)
    assert all(u >= nc or v >= nc for u, v in exterior), "H must be induced"

    delta_h = {}
    for trace in range(1, full_core):
        e = sum(bool((trace >> u) & 1) and bool((trace >> v) & 1) for u, v in core)
        assert e <= k * (trace.bit_count() - 1)
        delta_h[trace] = undirected_cut(core, trace)
        assert delta_h[trace] >= k + q

    physical_lambda = min(undirected_cut(edges, s) for s in range(1, full))
    assert physical_lambda >= 2 * k + 1
    actual_states = []
    for state in case["states"]:
        assert len(state["tails"]) == len(edges)
        cut_values = [outgoing_cut(edges, state["tails"], s) for s in range(1, full)]
        actual_min = min(cut_values)
        assert (actual_min >= k) == state["k_strong"], state["name"]
        actual_states.append({"name": state["name"], "minimum_out": actual_min,
                              "k_strong": actual_min >= k,
                              "literal_directed_rows": full - 1})

    exterior_subsets = [z << nc for z in range(1 << (n - nc))]
    physical_minima = {}
    for trace in range(1, full_core):
        values = [(undirected_cut(exterior, trace | z), trace | z)
                  for z in exterior_subsets]
        minimum = min(v for v, _ in values)
        minimizers = [s for v, s in values if v == minimum]
        physical_minima[trace] = (minimum, minimizers)
        if minimum <= k:
            assert len(minimizers) == 1, "Small exterior undirected completion must be unique"

    sigma_results, all_widths = [], []
    for sigma in case["sigmas"]:
        tails = sigma["tails"]
        external_tails = tails[mh:]
        # Every quotient cut respects C. Inspect all such original physical cuts.
        quotient_rows = []
        for trace in (0, full_core):
            for z in exterior_subsets:
                s = trace | z
                if 0 < s < full:
                    quotient_rows.append(outgoing_cut(exterior, external_tails, s))
        assert min(quotient_rows) >= k
        root_out = outgoing_cut(exterior, external_tails, full_core)
        root_in = undirected_cut(exterior, full_core) - root_out
        assert root_out >= k + 2 and root_in >= k + 2, "These specified sigmas should be far"

        directed_minima = {}
        for trace in range(1, full_core):
            values = [(outgoing_cut(exterior, external_tails, trace | z), trace | z)
                      for z in exterior_subsets]
            minimum = min(v for v, _ in values)
            directed_minima[trace] = (minimum, [s for v, s in values if v == minimum])

        widths = {}
        narrow_oriented = []
        narrow_witnesses = []
        low_width_count = 0
        for trace in range(1, full_core):
            other = full_core ^ trace
            fx, sx = directed_minima[trace]
            fy, sy = directed_minima[other]
            c, undirected_minimizers = physical_minima[trace]
            total_f = fx + fy
            mu = delta_h[trace] - 2 * k + total_f
            trace_lambda = delta_h[trace] + c
            widths[trace] = mu
            assert min(total_f, k) == min(c, k)
            threshold = delta_h[trace] - k
            assert min(mu, threshold) == min(trace_lambda - 2 * k, threshold)
            assert min(mu, q) == min(trace_lambda - 2 * k, q)
            assert mu >= 1
            if total_f < k:
                # Independent full-shore test of every pair of directed minimizers.
                assert len(sx) == len(sy) == len(undirected_minimizers) == 1
                assert sx[0] ^ sy[0] == full and sx[0] & sy[0] == 0
                assert sx == undirected_minimizers
                assert c == total_f
            if mu < q:
                low_width_count += 1
                assert trace_lambda == 2 * k + mu
                assert len(sx) == len(sy) == 1 and c <= k - 1
                assert undirected_cut(edges, sx[0]) == 2 * k + mu
            if q >= 2:
                assert (mu == 1) == (trace_lambda == 2 * k + 1)
                if mu == 1 and not trace & 1:
                    shore = undirected_minimizers[0]
                    narrow_oriented.append(trace)
                    assert outgoing_cut(exterior, external_tails, shore) == fx
                    assert outgoing_cut(exterior, external_tails, full ^ shore) == fy
                    assert c <= k - 1
                    assert delta_h[trace] - k + fy == k + 1 - fx
                    narrow_witnesses.append({"trace": trace, "shore": shore,
                                             "exterior_physical_cut": c,
                                             "external_out": fx,
                                             "internal_out_interval": [k - fx, k + 1 - fx]})
        if q >= 2:
            for i, x in enumerate(narrow_oriented):
                for y in narrow_oriented[i + 1:]:
                    assert not x & y or x & y == x or x & y == y, "Narrow traces must be laminar"
            assert len(narrow_oriented) <= 2 * nc - 3
            for i, x in enumerate(narrow_witnesses):
                for y in narrow_witnesses[i + 1:]:
                    a, b = x["shore"], y["shore"]
                    assert not a & b or a & b == a or a & b == b

        all_widths.append(widths)
        sigma_results.append({
            "name": sigma["name"], "quotient_minimum_out": min(quotient_rows),
            "root_out_in": [root_out, root_in], "proper_core_traces": full_core - 1,
            "low_width_traces_below_q": low_width_count,
            "narrow_unoriented_splits": len(narrow_oriented) if q >= 2 else None,
            "narrow_witnesses": narrow_witnesses,
            "width_at_trace_1": widths[1],
        })

    for trace in range(1, full_core):
        assert len({min(widths[trace], q) for widths in all_widths}) == 1
    checks = case["checks"]
    if case["kind"] == "physical_narrow_lift":
        s = checks["module_shore"]
        trace = s & full_core
        assert undirected_cut(edges, s) == 2 * k + 1
        assert physical_minima[trace] == (1, [s])
        assert outgoing_cut(exterior, case["sigmas"][0]["tails"][mh:], s) == 1
        assert outgoing_cut(exterior, case["sigmas"][1]["tails"][mh:], s) == 0
        if "blocked_shore_out" in checks:
            invalid = case["states"][-1]
            assert outgoing_cut(edges, invalid["tails"], s) == checks["blocked_shore_out"]
            # A physically legal predecessor differs by exactly the bridge identity.
            good = case["states"][-2]["tails"]
            bad = invalid["tails"]
            assert [i for i, (u, v) in enumerate(zip(good, bad)) if u != v] == [checks["bridge_identity"]]
    elif case["kind"] == "q1_exception":
        assert q == 1 and physical_lambda == checks["expected_lambda"] > 2 * k + 1
        assert [w[1] for w in all_widths] == checks["expected_widths_at_trace_1"]
        assert all(delta_h[x] + physical_minima[x][0] > 2 * k + 1 for x in range(1, full_core))
    elif case["kind"] == "wide_crossing":
        x, y = checks["crossing_traces"]
        assert x & y and x & ~y and y & ~x and full_core & ~(x | y)
        for widths in all_widths:
            assert widths[x] == widths[y] == checks["expected_crossing_width"] < q
        assert physical_minima[x][1][0] & physical_minima[y][1][0]
    elif case["kind"] == "port_deletion_q1":
        assert q == 1
        word = checks["two_step_word"]
        initial = case["states"][0]["tails"]
        prepared = case["states"][2]["tails"]
        finished = case["states"][3]["tails"]
        assert [i for i, (x, y) in enumerate(zip(initial, prepared)) if x != y] == word[:1]
        assert [i for i, (x, y) in enumerate(zip(prepared, finished)) if x != y] == word[1:]
    elif case["kind"] == "wide_budget_obstruction":
        assert physical_lambda == checks["expected_lambda"]
        assert all(min(w.values()) >= checks["minimum_residual_width"] for w in all_widths)
        original = case["states"][0]["tails"]
        root_ports_out = outgoing_cut(exterior, original[mh:], full_core)
        invariant_core_out_total = mh + root_ports_out
        assert (k + 1) * nc - invariant_core_out_total == checks["baseline_core_out_total_deficit"]
        assert all(sum(v in edge for edge in edges) == 2 * k + 2 for v in range(nc))
        word = checks["borrow_return_word"]
        replay = original[:]
        for step, identity in enumerate(word, 1):
            u, v = edges[identity]
            replay[identity] = v if replay[identity] == u else u
            assert replay == case["states"][step]["tails"]
        assert replay[mh:] == original[mh:], "Exterior helper must return by physical identity"
        strict_index = checks["strict_state_prefix"]
        assert actual_states[strict_index]["minimum_out"] >= k + 1

    deletion_results = []
    for task in case.get("deletion_tasks", []):
        g = task["identity"]
        assert g >= mh
        source_tails = case["sigmas"][0]["tails"]
        gu, gv = edges[g]
        gt = source_tails[g]
        gh = gv if gt == gu else gu
        eg = [e for i, e in enumerate(edges) if i >= mh and i != g]
        tg = [t for i, t in enumerate(source_tails) if i >= mh and i != g]
        quotient_rows = [outgoing_cut(eg, tg, trace | z)
                         for trace in (0, full_core) for z in exterior_subsets
                         if 0 < trace | z < full]
        assert min(quotient_rows) >= k, "Deleted g must be quotient-legal"
        fg = {}
        cg = {}
        for trace in range(1, full_core):
            ds = [(outgoing_cut(eg, tg, trace | z), trace | z) for z in exterior_subsets]
            us = [(undirected_cut(eg, trace | z), trace | z) for z in exterior_subsets]
            fd, cu = min(v for v, _ in ds), min(v for v, _ in us)
            fg[trace] = (fd, [s for v, s in ds if v == fd])
            cg[trace] = (cu, [s for v, s in us if v == cu])
        zero_shores = {}
        for trace in range(1, full_core):
            fy = fg[full_core ^ trace][0]
            fx, dx = fg[trace]
            c, ux = cg[trace]
            mu_g = delta_h[trace] - 2 * k + fx + fy
            lambda_deleted_trace = delta_h[trace] + c
            assert mu_g >= 0
            assert min(mu_g, q) == min(lambda_deleted_trace - 2 * k, q)
            assert (mu_g == 0) == (lambda_deleted_trace == 2 * k)
            if mu_g == 0:
                assert len(dx) == len(ux) == len(fg[full_core ^ trace][1]) == 1
                assert dx == ux
                s = ux[0]
                assert ((s >> gu) & 1) != ((s >> gv) & 1)
                assert undirected_cut(edges, s) == 2 * k + 1
                assert c <= k - q
                if not (s >> gt) & 1:
                    s = full ^ s
                assert (s >> gt) & 1 and not (s >> gh) & 1
                x = s & full_core
                need = k - outgoing_cut(eg, tg, s)
                current = outgoing_cut(core, source_tails[:mh], x)
                assert current in (need - 1, need)
                zero_shores[s] = {"shore": s, "trace": x,
                                  "remaining_external_cut": c,
                                  "current_internal_out": current,
                                  "required_internal_out_after_deletion": need}
        chain = sorted(zero_shores, key=int.bit_count)
        assert all(a & b == a and a != b for a, b in zip(chain, chain[1:]))
        assert len(chain) <= nc - 1
        if task["positive_remaining_exterior_cut_expected"]:
            assert any(v["remaining_external_cut"] > 0 for v in zero_shores.values())
        deletion_results.append({"deleted_identity": g, "quotient_minimum_out_after_deletion": min(quotient_rows),
                                 "rigid_chain": [zero_shores[s] for s in chain]})

    return {
        "case": case["name"], "k": k, "q": q, "vertices": n,
        "core_size": nc, "physical_edges": len(edges), "physical_lambda": physical_lambda,
        "status": "PASS", "sigmas": sigma_results, "states": actual_states,
        "deletion_tasks": deletion_results,
        "literal_undirected_full_cut_rows": full - 1,
        "literal_directed_full_cut_rows": (full - 1) * len(actual_states),
    }


def main():
    controls = ROOT / "residual_width_controls.json"
    raw = controls.read_bytes()
    payload = json.loads(raw)
    rows = [audit_case(case) for case in payload["cases"]]
    result = {
        "candidate_result": 172, "status": "PASS",
        "controls_sha256": hashlib.sha256(raw).hexdigest(),
        "independent_of_constructor": True,
        "orientation_state_search_used": False,
        "universal_quantifiers_from_analytic_proof": True,
        "main_status": "OPEN",
        "literal_undirected_full_cut_rows": sum(r["literal_undirected_full_cut_rows"] for r in rows),
        "literal_directed_full_cut_rows": sum(r["literal_directed_full_cut_rows"] for r in rows),
        "cases": rows,
    }
    output = ROOT / "residual_width_audit.json"
    output.write_text(json.dumps(result, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")
    print(json.dumps({"status": result["status"], "controls": len(rows),
                      "literal_directed_full_cut_rows": result["literal_directed_full_cut_rows"],
                      "literal_undirected_full_cut_rows": result["literal_undirected_full_cut_rows"]}))


if __name__ == "__main__":
    main()
