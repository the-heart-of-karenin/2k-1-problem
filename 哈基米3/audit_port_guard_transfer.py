"""Enumerate original full cuts to audit guard extrema and physical transports."""
from pathlib import Path
import hashlib
import json
from audit_deficit_budget_entry import physical_tables, subset_sums, directed_ids, outgoing_table

HERE = Path(__file__).resolve().parent


def audit(case):
    n, total, k, m, g = (case[x] for x in ["core_n", "vertex_n", "k", "core_m", "g"])
    indexed = [(e, *uv) for e, uv in enumerate(case["edges"])]
    adjacency, induced = physical_tables(total, indexed)
    degree_sums = subset_sums([sum(row.values()) for row in adjacency])
    lambda_g = min(degree_sums[x] - 2 * induced[x] for x in range(1, (1 << total) - 1))
    assert lambda_g >= 2 * k + 1
    _, core_induced = physical_tables(n, indexed[:m])
    core_degrees = [0] * n
    for _, u, v in indexed[:m]:
        core_degrees[u] += 1
        core_degrees[v] += 1
    assert core_degrees == [2 * k] * n
    assert all(core_induced[x] <= k * (x.bit_count() - 1) for x in range(1, (1 << n) - 1))
    x, y = next((u, v) for e, u, v in directed_ids(case, case["source_mask"]) if e == g)
    assert x < n <= y
    cache = {}
    full_rows = 0

    def state(mask):
        nonlocal full_rows
        if mask not in cache:
            arcs = directed_ids(case, mask)
            _, cuts = outgoing_table(total, arcs, induced)
            assert min(cuts[1:-1]) >= k
            internal = [0] * n
            for _, u, _ in arcs[:m]:
                internal[u] += 1
            # All complete cut rows are also cross-checked by physical edge IDs here.
            for shore in range(1, (1 << total) - 1):
                assert cuts[shore] == sum(bool(shore >> u & 1) and not (shore >> v & 1)
                                          for _, u, v in arcs)
            full_rows += (1 << total) - 2
            cache[mask] = (arcs, cuts, internal)
        return cache[mask]

    source = case["source_mask"]
    arcs, cuts, before = state(source)
    guards = [s for s in range(1, (1 << total) - 1)
              if s >> x & 1 and not s >> y & 1 and cuts[s] == k]
    assert guards
    small, large = (1 << total) - 1, 0
    for s in guards:
        small &= s
        large |= s
    assert small == case["guard_min_mask"] and large == case["guard_max_mask"]
    assert cuts[small] == cuts[large] == k
    assert sum(before[v] - k for v in range(n) if small >> v & 1) <= -1
    assert sum(before[v] - k for v in range(n) if large >> v & 1) <= -1
    tight = [s for s in range(1, (1 << total) - 1) if cuts[s] == k]
    for trial in case["trials"]:
        s = trial["s"]
        expected = [v for v in range(n)
                    if all(not (shore >> s & 1) or (shore >> v & 1) for shore in tight)]
        assert trial["safe_vertices"] == expected
        for v, value in trial["local_flow_values"].items():
            v = int(v)
            literal_min = min(cuts[shore] for shore in range(1, (1 << total) - 1)
                              if shore >> s & 1 and not shore >> v & 1)
            assert value == literal_min
    selected = case["selected_transport"]
    donor, receiver = selected["s"], selected["t"]
    assert not large >> donor & 1 and small >> receiver & 1
    assert before[donor] > k and before[receiver] < k
    vertices, word = selected["vertices"], selected["word"]
    assert len(set(vertices)) == len(vertices) and len(vertices) - 1 == len(word)
    assert vertices[0] == donor and vertices[-1] == receiver
    selected_trial = next(t for t in case["trials"] if t["s"] == donor)
    assert all(v in selected_trial["safe_vertices"] for v in vertices)
    by_id = {e: (u, v) for e, u, v in arcs}
    assert all(e < m and by_id[e] == (u, v) for e, u, v in zip(word, vertices, vertices[1:]))
    current, history = source, [source]
    phi = sum(max(0, k - d) for d in before)
    for e in word:
        current ^= 1 << e
        _, _, internal = state(current)
        assert (current ^ source) >> m == 0
        assert sum(max(0, k - d) for d in internal) <= phi
        history.append(current)
    assert current == case["ready_mask"]
    _, after_cuts, after = state(current)
    expected = before[:]
    expected[donor] -= 1
    expected[receiver] += 1
    assert after == expected
    assert sum(max(0, k - d) for d in after) == phi - 1 == case["ready_phi"]
    assert min(after_cuts[s] for s in range(1, (1 << total) - 1)
               if s >> x & 1 and not s >> y & 1) >= k + 1
    assert all(after_cuts[s] >= k + 1 for s in guards)
    assert not any(after_cuts[s] == k for s in range(1, (1 << total) - 1)
                   if s >> x & 1 and not s >> y & 1)
    current ^= 1 << g
    assert current == case["after_g_mask"]
    state(current)
    # Replay g and the same transport identities back, without substitution.
    current ^= 1 << g
    for e in reversed(word):
        current ^= 1 << e
        state(current)
    assert current == source
    # Recheck all quotient cuts as exactly the original cuts respecting C.
    for qmask in (source, case["after_g_mask"]):
        _, original_cuts, _ = state(qmask)
        for outside in range(1 << (total - n)):
            for whole in (0, (1 << n) - 1):
                shore = whole | (outside << n)
                if shore not in (0, (1 << total) - 1):
                    assert original_cuts[shore] >= k

    preconditioning_phi = None
    base_safe_transport_exists = None
    alternative_new_donor_length = None
    if "base_source_mask" in case:
        base = case["base_source_mask"]
        _, base_cuts, base_internal = state(base)
        preconditioning_phi = [sum(max(0, k - d) for d in base_internal)]
        for e in case["preconditioning_word"]:
            base ^= 1 << e
            _, _, base_internal = state(base)
            preconditioning_phi.append(sum(max(0, k - d) for d in base_internal))
        assert base == source
        assert preconditioning_phi == [1, 2]
        assert any(base_cuts[s] == k for s in range(1, (1 << total) - 1)
                   if s >> x & 1 and not s >> y & 1)
        assert case["preconditioning_is_general_theorem"] is False
        base_mask = case["base_source_mask"]
        base_arcs, base_cuts, base_internal = state(base_mask)
        base_guards = [s for s in range(1, (1 << total) - 1)
                       if s >> x & 1 and not s >> y & 1 and base_cuts[s] == k]
        base_m, base_u = (1 << total) - 1, 0
        for shore in base_guards:
            base_m &= shore
            base_u |= shore
        base_tight = [s for s in range(1, (1 << total) - 1) if base_cuts[s] == k]
        base_safe_transport_exists = False
        for donor in range(n):
            if base_internal[donor] <= k or base_u >> donor & 1:
                continue
            safe = {v for v in range(n) if all(not (shore >> donor & 1) or (shore >> v & 1)
                                              for shore in base_tight)}
            reachable = {donor}
            changed = True
            while changed:
                changed = False
                for _, u, v in base_arcs[:m]:
                    if u in reachable and v in safe and v not in reachable:
                        reachable.add(v)
                        changed = True
            if any(base_m >> v & 1 and base_internal[v] < k for v in reachable):
                base_safe_transport_exists = True
        assert base_safe_transport_exists is False
        # Also check the one-letter L_1 -> R_0 transfer named in the proof.
        one_letter = 4
        assert dict((e, (u, v)) for e, u, v in arcs)[one_letter] == (1, 4)
        _, alternative_cuts, _ = state(source ^ (1 << one_letter))
        assert min(alternative_cuts[s] for s in range(1, (1 << total) - 1)
                   if s >> x & 1 and not s >> y & 1) >= k + 1
        state(source ^ (1 << one_letter) ^ (1 << g))
        alternative_new_donor_length = 1

    # Independently verify that the global deficit budget really fails.
    frozen = arcs[m:]
    _, frozen_induced = physical_tables(total, indexed[m:])
    _, frozen_cuts = outgoing_table(total, frozen, frozen_induced)
    nsum = subset_sums([max(0, k - degree) for degree in before])
    budget_failures = []
    for trace in range(1, (1 << n) - 1):
        f = min(frozen_cuts[trace | (z << n)] for z in range(1 << (total - n)))
        margin = k * trace.bit_count() - core_induced[trace] - k + f
        if nsum[trace] > margin:
            budget_failures.append(trace)
    assert budget_failures and case["source_budget"]["passes"] is False
    return {"name": case["name"], "status": "PASS", "lambda_g": lambda_g,
            "source_phi": phi, "ready_phi": phi - 1,
            "guard_count": len(guards), "guard_min_mask": small, "guard_max_mask": large,
            "transport": vertices, "transport_length": len(word),
            "ready_is_eulerian": after == [k] * n,
            "global_budget_fails": True, "preconditioning_phi": preconditioning_phi,
            "base_safe_transport_exists": base_safe_transport_exists,
            "alternative_new_donor_length": alternative_new_donor_length,
            "complete_physical_cut_rows": full_rows, "physical_states": len(cache),
            "preparation_freezes_external": True, "g_original_identity": g,
            "reverse_replay_exact": True}


def main():
    path = HERE / "port_guard_transfer_certificate.json"
    data = json.loads(path.read_text(encoding="utf-8"))
    cases = [audit(c) for c in data["cases"]]
    output = {"status": "PASS", "constructor_imported": False,
              "independent_helper_module": "audit_deficit_budget_entry",
              "certificate_sha256": hashlib.sha256(path.read_bytes()).hexdigest(),
              "auditor_sha256": hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
              "cases": cases,
              "total_complete_physical_cut_rows": sum(c["complete_physical_cut_rows"] for c in cases),
              "does_not_prove": "unconditional safe transport or a universal preparation prefix"}
    destination = HERE / "port_guard_transfer_independent_audit.json"
    destination.write_text(json.dumps(output, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")
    print(json.dumps(output, ensure_ascii=False))


if __name__ == "__main__":
    main()
