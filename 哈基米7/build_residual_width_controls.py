"""Prescribed controls for candidate 172. No orientation-state enumeration."""
from __future__ import annotations

import hashlib
import json
from pathlib import Path

ROOT = Path(__file__).resolve().parent


def euler_tails(edges, n):
    adjacency = [[] for _ in range(n)]
    for identity, (u, v) in enumerate(edges):
        adjacency[u].append((identity, v))
        adjacency[v].append((identity, u))
    used = set()
    stack = [(0, None)]
    reverse_steps = []
    while stack:
        u = stack[-1][0]
        while adjacency[u] and adjacency[u][-1][0] in used:
            adjacency[u].pop()
        if adjacency[u]:
            identity, v = adjacency[u].pop()
            used.add(identity)
            stack.append((v, identity))
        else:
            reverse_steps.append(stack.pop())
    steps = list(reversed(reverse_steps))
    assert len(used) == len(edges) and len(steps) == len(edges) + 1
    tails = [None] * len(edges)
    for (u, _), (_, identity) in zip(steps, steps[1:]):
        tails[identity] = u
    assert all(t is not None for t in tails)
    return tails


def two_modules(k, removed_edges=0):
    size = 2 * k + 1
    core_size = 2 * size
    a, b = core_size, core_size + 1
    edges = []
    for offset in (0, size):
        for u in range(size):
            for v in range(u + 1, size):
                if u < 2 * k and u % 2 == 0 and v == u + 1:
                    continue
                edges.append([offset + u, offset + v])
    for u in range(2 * k):
        edges.append([u, size + u])
    core_tails = euler_tails(edges, core_size)
    crossing = edges.index([0, size])
    if core_tails[crossing] != 0:
        core_tails = [v if t == u else u for (u, v), t in zip(edges, core_tails)]

    removed = []
    if removed_edges:
        candidates = [i for i, (u, v) in enumerate(edges) if v < size]
        for identity in candidates[:removed_edges]:
            u, v = edges[identity]
            t = core_tails[identity]
            removed.append((t, v if t == u else u))
        chosen = set(candidates[:removed_edges])
        core_tails = [t for i, t in enumerate(core_tails) if i not in chosen]
        edges = [edge for i, edge in enumerate(edges) if i not in chosen]
    core_edge_count = len(edges)
    tails = core_tails[:]
    for u in range(size):
        edges.append([u, a])
        tails.append(u if u <= k else a)
    for u in range(size):
        edges.append([size + u, b])
        tails.append(b if u <= k else size + u)
    for u, v in removed:
        # Replacing the deleted directed arc by a physical directed two-edge path.
        edges.extend([[u, a], [a, v]])
        tails.extend([u, a])
    bridge = len(edges)
    edges.append([a, b])
    tails.append(a)
    sigmas = [
        {"name": "far_baseline", "tails": tails},
        {"name": "far_bridge_reversed", "tails": tails[:bridge] + [b]},
    ]
    states = [{"name": "physical_source", "tails": tails, "k_strong": True}]
    checks = {"module_shore": (1 << size) - 1 | (1 << a), "bridge_identity": bridge}
    if not removed_edges:
        crossing = edges.index([0, size])
        changed = tails[:]
        changed[crossing] = size
        invalid = changed[:]
        invalid[bridge] = b
        states.extend([
            {"name": "one_core_flip_far_source", "tails": changed, "k_strong": True},
            {"name": "quotient_legal_bridge_flip_is_physically_illegal", "tails": invalid,
             "k_strong": False},
        ])
        checks.update({"core_flip_identity": crossing, "blocked_shore_out": k - 1})
    deletion_tasks = []
    if removed_edges:
        deletion_tasks.append({"identity": core_edge_count + core_size,
                               "positive_remaining_exterior_cut_expected": True})
    return {
        "name": f"two_modules_k{k}_q{k - removed_edges}",
        "kind": "physical_narrow_lift", "k": k, "core_size": core_size,
        "vertices": core_size + 2, "core_edge_count": core_edge_count,
        "edges": edges, "sigmas": sigmas, "states": states, "checks": checks,
        "deletion_tasks": deletion_tasks,
    }


def virtual_q1(k=3, a=1):
    # A (k+1)-fold triangle, with a private exterior vertex attached to core vertex 0.
    # Its frozen quotient is far in both directions, while the entire graph has lambda=2k+2.
    edges = [[0, 1] for _ in range(k + 1)]
    tails = [0] * a + [1] * (k + 1 - a)
    first_outgoing_port = len(edges)
    for vertex, outgoing in ((0, k + 1 - a), (1, a + 1)):
        for j in range(k + 1):
            edges.append([vertex, 2])
            tails.append(vertex if j < outgoing else 2)
    for j in range(2 * (k + 2)):
        edges.append([0, 3])
        tails.append(0 if j < k + 2 else 3)
    alternate = tails[:]
    alternate[first_outgoing_port] = 2
    return {
        "name": f"virtual_q1_far_k{k}", "kind": "q1_exception", "k": k,
        "core_size": 2, "vertices": 4, "core_edge_count": k + 1,
        "edges": edges,
        "sigmas": [{"name": "far_width_one", "tails": tails},
                   {"name": "far_width_two", "tails": alternate}],
        "states": [{"name": "source_width_one", "tails": tails, "k_strong": True},
                   {"name": "source_width_two", "tails": alternate, "k_strong": True}],
        "checks": {"expected_lambda": 2 * k + 2, "expected_widths_at_trace_1": [1, 2]},
    }


def crossing_wide(k=3):
    length = 2 * k + 5
    root = length
    edges, tails = [], []
    for u in range(length):
        v = (u + 1) % length
        for _ in range(k):
            edges.append([u, v])
            tails.append(u)
    core_edge_count = len(edges)
    for u in range(length):
        edges.append([u, root])
        tails.append(u if u < k + 2 else root)
    reversed_exterior = tails[:core_edge_count] + [
        v if t == u else u
        for (u, v), t in zip(edges[core_edge_count:], tails[core_edge_count:])
    ]
    return {
        "name": f"crossing_width_two_k{k}", "kind": "wide_crossing", "k": k,
        "core_size": length, "vertices": length + 1, "core_edge_count": core_edge_count,
        "edges": edges,
        "sigmas": [{"name": "far_clockwise_ports", "tails": tails},
                   {"name": "far_reversed_ports", "tails": reversed_exterior}],
        "states": [{"name": "canonical_source", "tails": tails, "k_strong": True}],
        "checks": {"crossing_traces": [3, 6], "expected_crossing_width": 2},
    }


def q1_port_deletion(k=3, a=1):
    # Core 0 has physical degree 2k+1. Private exterior vertex 3 is attached to core 1.
    # This makes the quotient far without removing the actual critical singleton at 0.
    edges = [[0, 1] for _ in range(k + 1)]
    tails = [0] * a + [1] * (k + 1 - a)
    g = len(edges)
    for vertex, number, outgoing in ((0, k, k - a), (1, k + 1, a + 1)):
        for j in range(number):
            edges.append([vertex, 2])
            tails.append(vertex if j < outgoing else 2)
    for j in range(2 * (k + 2)):
        edges.append([1, 3])
        tails.append(1 if j < k + 2 else 3)
    direct_invalid = tails[:]
    direct_invalid[g] = 2
    prepared = tails[:]
    prepared[a] = 0
    finished = prepared[:]
    finished[g] = 2
    return {
        "name": f"q1_far_port_deletion_k{k}", "kind": "port_deletion_q1", "k": k,
        "core_size": 2, "vertices": 4, "core_edge_count": k + 1,
        "edges": edges, "sigmas": [{"name": "far_source", "tails": tails}],
        "states": [{"name": "unpaid_source", "tails": tails, "k_strong": True},
                   {"name": "direct_g_illegal", "tails": direct_invalid, "k_strong": False},
                   {"name": "one_core_edge_prepared", "tails": prepared, "k_strong": True},
                   {"name": "g_flipped_after_preparation", "tails": finished, "k_strong": True}],
        "checks": {"two_step_word": [a, g]},
        "deletion_tasks": [{"identity": g, "positive_remaining_exterior_cut_expected": True}],
    }


def wide_budget_obstruction():
    # One finite control of the analytic family k>=2, t>=k, length=2t+1.
    # This k=t=2 control additionally gives a literal exterior borrow/return word.
    k, t = 2, 2
    length = 2 * t + 1
    root = length
    edges, tails = [], []
    for u in range(length):
        for _ in range(k):
            edges.append([u, (u + 1) % length])
            tails.append(u)
    mh = len(edges)
    for u in range(length):
        for _ in range(2):
            edges.append([u, root])
            tails.append(u if u < t else root)
    helper = mh + 2 * t
    word = [helper, 2, 4, 0, 3, 5, 6, helper]
    current = tails[:]
    states = [{"name": "far_wide_source", "tails": current[:], "k_strong": True}]
    alternate = None
    for step, identity in enumerate(word, 1):
        u, v = edges[identity]
        current[identity] = v if current[identity] == u else u
        states.append({"name": f"borrow_word_prefix_{step}", "tails": current[:], "k_strong": True})
        if step == 1:
            alternate = current[:]
    return {
        "name": "all_widths_two_far_no_frozen_strict_state",
        "kind": "wide_budget_obstruction", "k": k, "core_size": length,
        "vertices": length + 1, "core_edge_count": mh, "edges": edges,
        "sigmas": [{"name": "far_point_budget_short_by_one", "tails": tails},
                   {"name": "far_one_exterior_letter_changed", "tails": alternate}],
        "states": states,
        "checks": {"expected_lambda": 2 * k + 2, "minimum_residual_width": 2,
                   "baseline_core_out_total_deficit": 1, "borrow_return_word": word,
                   "strict_state_prefix": 7},
    }


def main():
    cases = [two_modules(2), two_modules(3, 1), virtual_q1(), crossing_wide(),
             q1_port_deletion(), wide_budget_obstruction()]
    payload = {
        "candidate_result": 172,
        "scope": "Prescribed structural and physical controls; no orientation-state search; "
                 "universal quantifiers belong to the analytic proof.",
        "cases": cases,
    }
    path = ROOT / "residual_width_controls.json"
    path.write_text(json.dumps(payload, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")
    print(json.dumps({"controls": len(cases), "path": str(path),
                      "sha256": hashlib.sha256(path.read_bytes()).hexdigest()}, ensure_ascii=False))


if __name__ == "__main__":
    main()
