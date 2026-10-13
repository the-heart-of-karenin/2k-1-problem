"""Independent physical all-cut audit, including weighted parallel identities.

Does not import the constructor, its box connector, or a previous audit.
Static multiplicities are used only to count induced physical edges; physical
directions and cache keys are never merged by degree profile.
"""
from array import array
from pathlib import Path
import hashlib
import json

OUT = Path(__file__).resolve().parent
COUNTS = {"original_directed_cut_rows": 0, "original_undirected_cut_rows": 0,
          "auxiliary_directed_cut_rows": 0, "auxiliary_undirected_cut_rows": 0,
          "external_trace_cut_rows": 0, "physical_state_visits": 0,
          "distinct_frame_masks": 0}


class Cuts:
    def __init__(self, n, edges, ids=None, kind="auxiliary"):
        self.n, self.edges, self.kind = n, edges, kind
        self.ids = list(range(len(edges))) if ids is None else ids
        self.size = 1 << n
        neighbors = [dict() for _ in range(n)]
        self.deg = [0]*n
        for u, v in edges:
            assert u != v
            neighbors[u][v] = neighbors[u].get(v, 0)+1
            neighbors[v][u] = neighbors[v].get(u, 0)+1
            self.deg[u] += 1
            self.deg[v] += 1
        self.internal = array("i", [0])*self.size
        degree_sum = array("i", [0])*self.size
        least = None
        for s in range(1, self.size):
            bit = s & -s
            v, rest = bit.bit_length()-1, s ^ bit
            self.internal[s] = self.internal[rest] + sum(
                count for w, count in neighbors[v].items() if rest >> w & 1)
            degree_sum[s] = degree_sum[rest] + self.deg[v]
            if s != self.size-1:
                val = degree_sum[s] - 2*self.internal[s]
                least = val if least is None else min(least, val)
        self.lambda_undirected = least
        if kind != "external":
            COUNTS[kind+"_undirected_cut_rows"] += self.size-2
        self.cache = {}

    def state(self, mask):
        COUNTS["physical_state_visits"] += 1
        if mask in self.cache:
            return self.cache[mask]
        b = [0]*self.n
        for (u, v), identity in zip(self.edges, self.ids):
            b[v if mask >> identity & 1 else u] += 1
        sums, values = array("i", [0])*self.size, array("i", [0])*self.size
        least, witness = None, None
        for s in range(1, self.size-1):
            bit, rest = s & -s, s ^ (s & -s)
            sums[s] = sums[rest] + b[bit.bit_length()-1]
            values[s] = sums[s] - self.internal[s]
            if least is None or values[s] < least:
                least, witness = values[s], s
        if self.kind == "external":
            COUNTS["external_trace_cut_rows"] += self.size-2
        else:
            COUNTS[self.kind+"_directed_cut_rows"] += self.size-2
        COUNTS["distinct_frame_masks"] += 1
        result = {"outdegree": b, "minimum": least, "witness": witness,
                  "values": values}
        self.cache[mask] = result
        return result


def restricted(frame, vertices, identities, kind="auxiliary"):
    ix = {v: j for j, v in enumerate(vertices)}
    return Cuts(len(vertices), [[ix[frame["edges"][e][0]], ix[frame["edges"][e][1]]]
                               for e in identities], identities, kind)


def main():
    certificate_bytes = (OUT / "synchronized_lobes_certificate.json").read_bytes()
    data = json.loads(certificate_bytes.decode("utf-8"))
    results = []
    branch_counts = {}
    for fi, f in enumerate(data["frames"]):
        k, n, mask = f["k"], len(f["core"]), f["source_mask"]
        assert f["core"] == list(range(n))
        assert set(v for B in f["blocks"] for v in B) == set(range(n, f["vertex_count"]))
        membership = {v: i for i, B in enumerate(f["blocks"]) for v in B}
        Hids, Eids = [], []
        Ri, Si, counts = [[0]*n for _ in f["blocks"]], [[0]*n for _ in f["blocks"]], [[0]*n for _ in f["blocks"]]
        for e, (u, v) in enumerate(f["edges"]):
            if u < n and v < n:
                Hids.append(e)
                assert f["edge_labels"][e] == "H"
                continue
            Eids.append(e)
            if u >= n and v >= n:
                assert membership[u] == membership[v]
            else:
                cv, bv = (u, v) if u < n else (v, u)
                i = membership[bv]
                counts[i][cv] += 1
                tail = v if mask >> e & 1 else u
                (Ri if tail == cv else Si)[i][cv] += 1
        weights = []
        for row in counts:
            assert min(row) == max(row) and row[0] >= 1
            weights.append(row[0])
        hcuts = restricted(f, list(range(n)), Hids)
        m = len(Hids)
        q = m-k*(n-1)
        assert q >= 1
        for x in range(1, (1 << n)-1):
            assert hcuts.internal[x] <= k*(x.bit_count()-1)
        whole = Cuts(f["vertex_count"], f["edges"], kind="original")
        assert whole.lambda_undirected >= 2*k+1
        for B in f["blocks"]:
            ids = [e for e in Eids if f["edges"][e][0] in B and f["edges"][e][1] in B]
            body = restricted(f, B, ids)
            if len(B) > 1:
                assert body.state(mask)["minimum"] >= k
        B = list(range(n, f["vertex_count"]))
        ix = {v: j+1 for j, v in enumerate(B)}
        qed = [[0 if u < n else ix[u], 0 if v < n else ix[v]] for e in Eids for u, v in [f["edges"][e]]]
        Q = Cuts(len(B)+1, qed, Eids)
        assert Q.state(mask)["minimum"] >= k

        R = [sum(row[v] for row in Ri) for v in range(n)]
        S = [sum(row[v] for row in Si) for v in range(n)]
        L = [max(0, k-R[v]) for v in range(n)]
        U = [min(hcuts.deg[v], hcuts.deg[v]-k+S[v]) for v in range(n)]
        ext = Cuts(f["vertex_count"], [f["edges"][e] for e in Eids], Eids, "external")
        ext_values = ext.state(mask)["values"]
        residual = [10**9]*(1 << n)
        for shore in range(1, ext.size-1):
            x = shore & ((1 << n)-1)
            if 0 < x < (1 << n)-1:
                residual[x] = min(residual[x], ext_values[shore])
        trace_rows = []
        for x in range(1, (1 << n)-1):
            minimum_whole_lobes = sum(min(
                sum(Ri[i][v] for v in range(n) if x >> v & 1),
                sum(Si[i][v] for v in range(n) if not (x >> v & 1)))
                for i in range(len(weights)))
            pure_minimum = min(sum(R[v] for v in range(n) if x >> v & 1),
                               sum(S[v] for v in range(n) if not (x >> v & 1)))
            assert min(k, residual[x]) == min(k, minimum_whole_lobes)
            if "task" in f:
                assert minimum_whole_lobes == pure_minimum
            trace_rows.append((x, minimum_whole_lobes, pure_minimum))

        if "task" in f:
            a = f["synchronizing_integer"]
            for i, d in enumerate(weights):
                assert a*d <= sum(Si[i]) <= (a+1)*d
            t = f["task"]
            assert t["source_mask"] == mask
            assert t["L"] == L and t["U"] == U
            Hmask = sum(1 << e for e in Hids)
            history = []
            for step, identity in enumerate([None]+t["word"]):
                if identity is not None:
                    assert identity in Hids
                    mask ^= 1 << identity
                assert (mask ^ t["source_mask"]) & ~Hmask == 0
                full = whole.state(mask)
                assert full["minimum"] >= k
                hb = hcuts.state(mask)["outdegree"]
                assert all(L[v] <= hb[v] <= U[v] for v in range(n))
                history.append({"step": step, "physical_mask": mask,
                                "full_minimum_cut": full["minimum"], "H_outdegree": hb})
            assert mask == t["target_mask"]
            for identity in t["word"][::-1]:
                mask ^= 1 << identity
                assert whole.state(mask)["minimum"] >= k
            assert mask == t["source_mask"]
            assert len(t["word"]) <= (n+1)*m
            block_mask = mask
            flat = []
            for block in t["blocks"]:
                assert block_mask == block["start_mask"]
                initial = block_mask
                for identity in block["word"]:
                    block_mask ^= 1 << identity
                    flat.append(identity)
                assert block_mask == block["end_mask"]
                for helper in block["returned_helper_ids"]:
                    assert not ((block_mask ^ initial) >> helper & 1)
                if "cycle_exact" in block["kind"]:
                    net = [e for e in Hids if (block_mask ^ initial) >> e & 1]
                    nodes = {v for e in net for v in f["edges"][e]}
                    hb = hcuts.state(initial)["outdegree"]
                    bounds = L if block["kind"].startswith("lower") else U
                    assert all(hb[v] == bounds[v] for v in nodes)
                branch_counts[block["kind"]] = branch_counts.get(block["kind"], 0)+1
            assert flat == t["word"] and block_mask == t["target_mask"]
            results.append({"frame": fi, "role": f["role"], "status": "PASS",
                            "q": q, "port_weights": weights,
                            "word_length": len(t["word"]), "history": history})
        else:
            full = whole.state(mask)
            assert all(k <= full["outdegree"][v] <= whole.deg[v]-k for v in range(whole.n))
            hb = hcuts.state(mask)["outdegree"]
            assert all(L[v] <= hb[v] <= U[v] for v in range(n))
            bad = sum(1 << v for v in f["bad_full_shore"])
            assert full["values"][bad] == k-1
            assert full["minimum"] == k-1
            x = sum(1 << v for v in f["bad_core_trace"])
            row = next(row for row in trace_rows if row[0] == x)
            assert row[1:] == (0, 1)
            assert sum(Si[0]) == k and sum(Si[1]) == k+2
            results.append({"frame": fi, "role": f["role"], "status": "PASS",
                            "point_box_assignment_is_not_legal": True,
                            "bad_shore_out_cut": k-1, "root_star_is_legal": True,
                            "not_a_MAIN_counterexample": True})
    report = {"status": "PASS", "counts": COUNTS, "controls": results,
              "certificate_sha256": hashlib.sha256(certificate_bytes).hexdigest(),
              "constructed_branch_counts": branch_counts,
              "orientation_component_enumeration": False,
              "main_status": "OPEN",
              "universal_quantifiers_from": "analytic proof, not the controls"}
    (OUT / "synchronized_lobes_independent_audit.json").write_text(
        json.dumps(report, ensure_ascii=False, indent=2), encoding="utf-8")
    print(json.dumps({"status": "PASS", "counts": COUNTS,
                      "constructed_branch_counts": branch_counts}, ensure_ascii=False))


if __name__ == "__main__":
    main()
