"""Independent all-cut audit of supplied physical frames and words.

No import of the constructor or an earlier orientation/interval engine.
Only identical physical masks on an identical physical frame are cached.
"""
from pathlib import Path
from array import array
import hashlib
import json

OUT = Path(__file__).resolve().parent
ROOT = OUT.parent
COUNTS = {"directed_cut_rows": 0, "undirected_cut_rows": 0,
          "physical_state_visits": 0, "distinct_frame_masks": 0}


class CutAudit:
    def __init__(self, vertex_count, edges, original_ids=None):
        self.n = vertex_count
        self.edges = edges
        self.original_ids = list(range(len(edges))) if original_ids is None else original_ids
        self.size = 1 << vertex_count
        adjacency = [0] * vertex_count
        deg = [0] * vertex_count
        # Controls are simple; each physical edge is checked, never collapsed.
        assert len({tuple(sorted(e)) for e in edges}) == len(edges)
        for u, v in edges:
            assert u != v
            adjacency[u] |= 1 << v
            adjacency[v] |= 1 << u
            deg[u] += 1
            deg[v] += 1
        self.internal = array("i", [0]) * self.size
        sums = array("i", [0]) * self.size
        min_cut = 10**9
        for s in range(1, self.size):
            low = s & -s
            v = low.bit_length()-1
            r = s ^ low
            self.internal[s] = self.internal[r] + (adjacency[v] & r).bit_count()
            sums[s] = sums[r] + deg[v]
            if s != self.size-1:
                min_cut = min(min_cut, sums[s] - 2*self.internal[s])
        self.undirected_min = min_cut
        COUNTS["undirected_cut_rows"] += self.size-2
        self.cache = {}

    def outdegrees(self, physical_mask):
        out = [0] * self.n
        for (u, v), original_id in zip(self.edges, self.original_ids):
            out[v if physical_mask >> original_id & 1 else u] += 1
        return out

    def state(self, physical_mask):
        COUNTS["physical_state_visits"] += 1
        if physical_mask in self.cache:
            return self.cache[physical_mask]
        out = self.outdegrees(physical_mask)
        sums = array("i", [0]) * self.size
        min_cut = 10**9
        witness = None
        for s in range(1, self.size-1):
            low = s & -s
            r = s ^ low
            sums[s] = sums[r] + out[low.bit_length()-1]
            cut = sums[s] - self.internal[s]
            if cut < min_cut:
                min_cut, witness = cut, s
        COUNTS["directed_cut_rows"] += self.size-2
        COUNTS["distinct_frame_masks"] += 1
        value = {"min_out_cut": min_cut, "outdegrees": out,
                 "minimum_witness_mask": witness}
        self.cache[physical_mask] = value
        return value


def subframe(frame, selected_vertices, selected_ids):
    ix = {v: i for i, v in enumerate(selected_vertices)}
    return CutAudit(len(selected_vertices),
                    [[ix[frame["edges"][e][0]], ix[frame["edges"][e][1]]]
                     for e in selected_ids], selected_ids)


def root_out_in(frame, mask, block=None):
    C = set(frame["core"])
    B = set(frame["blocks"][block]) if block is not None else None
    out = incoming = 0
    for e, (u, v) in enumerate(frame["edges"]):
        if (u in C) == (v in C):
            continue
        outside = v if u in C else u
        if B is not None and outside not in B:
            continue
        tail = v if mask >> e & 1 else u
        out += tail in C
        incoming += tail not in C
    return [out, incoming]


def quotient(frame):
    C = set(frame["core"])
    B = [v for v in range(frame["vertex_count"]) if v not in C]
    ix = {v: i+1 for i, v in enumerate(B)}
    edges, ids = [], []
    for e, (u, v) in enumerate(frame["edges"]):
        if u in C and v in C:
            continue
        edges.append([0 if u in C else ix[u], 0 if v in C else ix[v]])
        ids.append(e)
    return CutAudit(len(B)+1, edges, ids)


def core_degrees(frame, mask):
    out = [0] * len(frame["core"])
    C = set(frame["core"])
    for e, (u, v) in enumerate(frame["edges"]):
        if u in C and v in C:
            out[v if mask >> e & 1 else u] += 1
    return out


def main():
    data = json.loads((OUT / "protective_environment_certificate.json").read_text(encoding="utf-8"))
    results = []
    for index, frame in enumerate(data["frames"]):
        k = frame["k"]
        whole = CutAudit(frame["vertex_count"], frame["edges"])
        assert whole.undirected_min == 2*k+1
        q = quotient(frame)
        assert q.undirected_min == 2*k+1
        assert q.state(frame["source_mask"])["min_out_cut"] >= k
        assert root_out_in(frame, frame["source_mask"]) == [4, 6]
        # Cut on each entire B_i forces k incoming and k outgoing ports.
        assert k*frame["t"] > k+1
        protectors = [subframe(frame, p["vertices"], p["edge_ids"])
                      for p in frame["protective_subgraphs"]]
        for p in protectors:
            assert p.undirected_min == 2*k+1

        source_check = whole.state(frame["source_mask"])
        assert source_check["min_out_cut"] >= k
        if "tasks" in frame:
            # B has two disconnected components. B_0 is additionally not k-strong.
            B0 = frame["blocks"][0]
            ids = [e for e, (u, v) in enumerate(frame["edges"])
                   if u in B0 and v in B0]
            B0_audit = subframe(frame, B0, ids)
            assert B0_audit.state(frame["source_mask"])["min_out_cut"] == k-1
            task_results = []
            H_mask = sum(1 << e for e, label in enumerate(frame["edge_labels"]) if label == "H")
            for task in frame["tasks"]:
                mask = task["source_mask"]
                original = mask
                pa = protectors[task["protective_block"]]
                history = []
                for step, e in enumerate([None] + task["word"]):
                    if e is not None:
                        assert frame["edge_labels"][e] == "H"
                        mask ^= 1 << e
                    assert (mask ^ original) & ~H_mask == 0
                    a = whole.state(mask)
                    b = pa.state(mask)
                    assert a["min_out_cut"] >= k
                    assert b["min_out_cut"] >= k
                    assert root_out_in(frame, mask) == [4, 6]
                    assert root_out_in(frame, mask, 0) == [2, 3]
                    hc = core_degrees(frame, mask)
                    history.append({"step": step, "physical_mask": mask,
                                    "full_min_cut": a["min_out_cut"],
                                    "protective_min_cut": b["min_out_cut"],
                                    "H_outdegrees": hc,
                                    "Phi_H": sum(abs(z-k) for z in hc)//2})
                assert mask == task["target_mask"]
                assert core_degrees(frame, mask) == [k]*len(frame["core"])
                if "net_core_edges" in task:
                    expected = sum(1 << e for e in task["net_core_edges"])
                    assert mask ^ original == expected
                    assert not ((mask ^ original) >> task["returned_helper"] & 1)
                    assert core_degrees(frame, original) == [k]*len(frame["core"])
                else:
                    assert core_degrees(frame, original) != [k]*len(frame["core"])
                for e in reversed(task["word"]):
                    mask ^= 1 << e
                    assert whole.state(mask)["min_out_cut"] >= k
                    assert pa.state(mask)["min_out_cut"] >= k
                assert mask == original
                task_results.append({"name": task["name"], "status": "PASS",
                                     "length": len(task["word"]), "history": history})
            results.append({"frame": index, "status": "PASS", "tasks": task_results,
                            "B0_internal_min_cut": k-1})
        else:
            v = frame["failed_core_vertex"]
            assert source_check["outdegrees"][v] == k
            failures = []
            for p in protectors:
                check = p.state(frame["source_mask"])
                assert check["outdegrees"][v] == k-1
                assert check["min_out_cut"] < k
                failures.append(check["min_out_cut"])
            results.append({"frame": index, "status": "PASS",
                            "full_min_cut": source_check["min_out_cut"],
                            "restricted_min_cuts": failures,
                            "meaning": "projection legality is an additional obligation"})

    references = json.loads((OUT / "参考入口源_SHA256.json").read_text(encoding="utf-8"))
    mutable_entries = {
        "2k+1/研究启动必读_方法与停止规则_2026-10-12.md",
        "2k+1/研究续接_2026-10-13_结果172进行中.json",
    }
    entry_updates = []
    unchanged = 0
    for name, expected in references.items():
        current = hashlib.sha256((ROOT / name).read_bytes()).hexdigest()
        if current == expected:
            unchanged += 1
        else:
            assert name in mutable_entries, f"A proof/reference source changed: {name}"
            entry_updates.append({"path": name, "initial_sha256": expected,
                                  "current_sha256": current})
    report = {"status": "PASS", "counts": COUNTS,
              "controls": results, "reference_sources_unchanged": unchanged,
              "mutable_entry_updates": entry_updates,
              "full_old_hash_chain_audit_claimed": False,
              "main_status": "OPEN", "orientation_components_enumerated": False,
              "universal_statements_proved_by": "analytic note, not sample counts"}
    (OUT / "protective_environment_independent_audit.json").write_text(
        json.dumps(report, ensure_ascii=False, indent=2), encoding="utf-8")
    print(json.dumps({"status": report["status"], "counts": COUNTS,
                      "reference_sources_unchanged": unchanged,
                      "mutable_entry_updates": len(entry_updates)}, ensure_ascii=False))


if __name__ == "__main__":
    main()
