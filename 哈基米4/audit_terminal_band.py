"""Independent literal-cut replay. Does not import the constructor."""
from pathlib import Path
from collections import Counter
import hashlib
import json

ROOT = Path(__file__).resolve().parent
STATS = Counter()


def orientation(edges, mask):
    return [(v, u) if mask & (1 << i) else (u, v)
            for i, (u, v) in enumerate(edges)]


def outdegrees(edges, mask, n):
    b = [0]*n
    for tail, _ in orientation(edges, mask):
        b[tail] += 1
    return b


def imbalance(b, k):
    assert sum(b) == len(b)*k
    return sum(abs(t-k) for t in b)//2


class LiteralCuts:
    def __init__(self, edges, n, k):
        self.edges, self.n, self.k = edges, n, k
        self.full = (1 << len(edges))-1
        self.rows = []
        self.cache = {}
        for shore in range(1, (1 << n)-1):
            forward = backward = 0
            for e, (u, v) in enumerate(edges):
                su, sv = shore >> u & 1, shore >> v & 1
                if su and not sv: forward |= 1 << e
                if sv and not su: backward |= 1 << e
            self.rows.append((shore, forward, backward))
        self.undirected_min = min((a | b).bit_count() for _, a, b in self.rows)
        STATS['undirected_cut_rows'] += len(self.rows)

    def min_out(self, mask):
        assert 0 <= mask <= self.full
        STATS['state_visits'] += 1
        if mask not in self.cache:
            opposite = self.full ^ mask
            minimum = len(self.edges)+1
            witness = None
            for shore, forward, backward in self.rows:
                out = (opposite & forward).bit_count() + (mask & backward).bit_count()
                if out < minimum:
                    minimum, witness = out, shore
            self.cache[mask] = (minimum, witness)
            STATS['distinct_physical_states'] += 1
            STATS['directed_complete_cut_rows'] += len(self.rows)
        return self.cache[mask]

    def out(self, mask, shore):
        forward, backward = next((a, b) for s, a, b in self.rows if s == shore)
        return ((self.full ^ mask) & forward).bit_count() + (mask & backward).bit_count()

    def legal(self, mask):
        return self.min_out(mask)[0] >= self.k


def terminal_parameters(inst):
    k, n = inst['k'], inst['core_n']
    mh, edges = inst['internal_count'], inst['edges']
    frozen = int(inst['frozen_mask'], 16)
    assert not frozen & ((1 << mh)-1)
    internal_degrees = [0]*n
    for u, v in edges[:mh]:
        assert u < n and v < n and u != v
        internal_degrees[u] += 1
        internal_degrees[v] += 1
    assert internal_degrees == [2*k]*n and mh == n*k
    for u, v in edges[mh:]:
        assert not (u < n and v < n)
    # Contract C to one vertex, preserving each non-H physical identity.
    qedges, qmask = [], 0
    for i, (u, v) in enumerate(edges[mh:], start=mh):
        u, v = (0 if u < n else u-n+1), (0 if v < n else v-n+1)
        assert u != v
        qedges.append((u, v))
        if frozen >> i & 1: qmask |= 1 << (i-mh)
    quotient = LiteralCuts(qedges, inst['vertex_n']-n+1, k)
    assert quotient.undirected_min >= 2*k+1 and quotient.legal(qmask)
    # These controls have TWO isolated outside vertices. Thus every quotient
    # orientation has root out/in at least 2k, and no k/k+1 layer exists.
    assert inst['vertex_n']-n == 2
    assert all(u == 0 or v == 0 for u, v in qedges)
    STATS['controls_without_any_quotient_near_layer'] += 1
    directed_external = orientation(edges, frozen)[mh:]
    f = []
    for x in range(1 << n):
        values = []
        for z in range(1 << (inst['vertex_n']-n)):
            shore = x | (z << n)
            values.append(sum(1 for u, v in directed_external
                              if shore >> u & 1 and not (shore >> v & 1)))
        f.append(min(values))
        STATS['terminal_min_cut_rows'] += len(values)
    assert f == inst['f'] and f[0] == f[-1] == 0
    # Elementary submodular inequalities imply all submodular inequalities.
    for x in range(1 << n):
        missing = [v for v in range(n) if not (x >> v & 1)]
        for i, u in enumerate(missing):
            for v in missing[i+1:]:
                assert f[x | (1 << u)]+f[x | (1 << v)] >= f[x]+f[x | (1 << u) | (1 << v)]
                STATS['terminal_submodular_rows'] += 1
    allc = (1 << n)-1
    lo = [max(0, k-f[1 << v]) for v in range(n)]
    hi = [min(2*k, k+f[allc ^ (1 << v)]) for v in range(n)]
    assert lo == inst['lower'] and hi == inst['upper']
    assert all(l < u and l <= k <= u for l, u in zip(lo, hi))
    assert min(lo) < k < max(hi)
    budget, rows = None, []
    for x in range(1, allc):
        cut = sum(1 for u, v in edges[:mh] if (x >> u & 1) != (x >> v & 1))
        assert cut >= 2*k
        alpha = cut//2-k
        assert cut % 2 == 0
        assert cut-2*k+f[x]+f[allc ^ x] >= 1
        s = x.bit_count()
        if s in (1, n-1): continue
        a = sum(k-lo[v] for v in range(n) if x >> v & 1)
        b = sum(hi[v]-k for v in range(n) if not (x >> v & 1))
        h = alpha+f[x]
        rows.append([x, alpha, f[x], a, b])
        if h < min(a, b): budget = h if budget is None else min(budget, h)
    assert rows == inst['margin_rows'] and budget == inst['safe_band']
    return lo, hi, budget


def audit_tasks(inst):
    k, n, mh = inst['k'], inst['core_n'], inst['internal_count']
    edges, frozen = inst['edges'], int(inst['frozen_mask'], 16)
    lo, hi, budget = terminal_parameters(inst)
    literal = LiteralCuts(edges, inst['vertex_n'], k)
    assert literal.undirected_min >= 2*k+1
    internal = edges[:mh]
    if 'source_coverage' in inst:
        eligible = {mask for mask in range(1 << mh)
                    if imbalance(outdegrees(internal, mask, n), k) <= 2}
        assert eligible == {int(t['source'], 16) for t in inst['tasks']}
        assert len(eligible) == inst['source_coverage']['eligible_masks']
        STATS['selected_frozen_fibre_internal_masks_checked'] += 1 << mh
    for task in inst['tasks']:
        source, target = int(task['source'], 16), int(task['target'], 16)
        cap = max(2, imbalance(outdegrees(internal, source, n), k)+1)
        assert cap == task['phi_cap'] and (budget is None or cap <= budget)
        assert outdegrees(internal, target, n) == [k]*n
        masks, phis, degree_history = [source], [], []
        state = source
        for step in [None]+task['word']:
            if step is not None:
                assert 0 <= step < mh
                state ^= 1 << step
            assert literal.legal(state | frozen)
            b = outdegrees(internal, state, n)
            assert all(l <= t <= u for l, t, u in zip(lo, b, hi))
            p = imbalance(b, k)
            assert p <= cap
            phis.append(p)
            degree_history.append(b)
            if step is not None: masks.append(state)
        assert state == target
        assert phis[0] == task['phi_source'] and max(phis) == task['phi_peak']
        for macro in task['macros']:
            a, b = macro['begin'], macro['end']
            ids, word = macro['edges'], task['word'][a:b]
            initial_arcs = orientation(internal, masks[a])
            chosen = [initial_arcs[e] for e in ids]
            for (_, v), (u, _) in zip(chosen, chosen[1:]): assert v == u
            if macro['kind'] == 'normalization_path':
                assert chosen[-1][1] != chosen[0][0]
                nodes = [chosen[0][0]]+[v for _, v in chosen]
                assert len(nodes) == len(set(nodes))
                assert Counter(word) == Counter(ids)
                assert all(degree_history[a][v] == k for v in nodes[1:-1])
                assert degree_history[a][nodes[0]] > k > degree_history[a][nodes[-1]]
                assert phis[a] == macro['phi_before']
                assert phis[b] == macro['phi_after'] == phis[a]-1
                assert max(phis[a:b+1]) <= phis[a]+1
            else:
                assert chosen[-1][1] == chosen[0][0]
                assert len(set(u for u, _ in chosen)) == len(chosen)
                assert degree_history[a] == degree_history[b] == [k]*n
                assert max(phis[a:b+1]) <= 2
                helpers = macro['helpers']
                assert not set(helpers) & set(ids)
                assert Counter(word) == Counter(ids+helpers+helpers)
                net = masks[a] ^ masks[b]
                assert net == sum(1 << e for e in ids)
                assert (masks[a] ^ target).bit_count() - (masks[b] ^ target).bit_count() == len(ids)
            STATS[macro.get('branch', macro['kind'])] += 1
            STATS['macro_count'] += 1
        for step in reversed(task['word']):
            state ^= 1 << step
            assert literal.legal(state | frozen)
        assert state == source
        STATS['tasks'] += 1
        STATS['physical_flips'] += len(task['word'])
        STATS['reverse_replay_flips'] += len(task['word'])
    return literal


def main():
    cert_path = ROOT/'terminal_band_certificate.json'
    cert = json.loads(cert_path.read_text(encoding='utf-8'))
    assert cert['constructor_state_graph_search'] is False
    assert cert['regularization_used'] is False and cert['main_status'] == 'OPEN'
    assert cert['constructor_sha256'] == hashlib.sha256((ROOT/'construct_terminal_band.py').read_bytes()).hexdigest()
    for inst in cert['instances']:
        audit_tasks(inst)
    for inst in cert['unsafe_band_controls']:
        lo, hi, budget = terminal_parameters(inst)
        literal = LiteralCuts(inst['edges'], inst['vertex_n'], inst['k'])
        assert literal.undirected_min >= 2*inst['k']+1
        witness = inst['witness']
        mask = int(witness['internal_mask'], 16)
        b = outdegrees(inst['edges'][:inst['internal_count']], mask, inst['core_n'])
        assert all(l <= t <= u for l, t, u in zip(lo, b, hi))
        assert imbalance(b, inst['k']) == witness['phi'] == inst['k']
        assert budget == inst['k']-1
        state = mask | int(inst['frozen_mask'], 16)
        assert literal.out(state, witness['violating_shore']) == witness['expected_out'] == inst['k']-1
        assert not literal.legal(state)
        STATS['point_valid_mixed_invalid_controls'] += 1
    for inst in cert['one_unit_controls']:
        k, n, mh = inst['k'], inst['core_n'], inst['internal_count']
        edges, outside = inst['edges'], int(inst['frozen_mask'], 16)
        literal = LiteralCuts(edges, inst['vertex_n'], k)
        assert literal.undirected_min >= 2*k+1
        source, target = int(inst['source'], 16), int(inst['target'], 16)
        assert outdegrees(edges[:mh], source, n) == outdegrees(edges[:mh], target, n) == [k]*n
        assert literal.legal(source | outside) and literal.legal(target | outside)
        for e in range(mh):
            nxt = source ^ 1 << e
            if not literal.legal(nxt | outside): continue
            assert imbalance(outdegrees(edges[:mh], nxt, n), k) == 1
            feasible_next = []
            for g in range(mh):
                nn = nxt ^ 1 << g
                if imbalance(outdegrees(edges[:mh], nn, n), k) <= 1 and literal.legal(nn | outside):
                    feasible_next.append(g)
            assert feasible_next == [e]
            STATS['one_unit_neighbour_dead_end_checks'] += 1
        state, trace = source, [0]
        for e in inst['word']:
            state ^= 1 << e
            assert literal.legal(state | outside)
            trace.append(imbalance(outdegrees(edges[:mh], state, n), k))
        assert state == target and trace == [0, 1, 2, 1, 0]
        STATS['one_unit_lower_bound_controls'] += 1
    result = dict(status='PASS', date='2026-10-13', main_status='OPEN',
                  mathematical_proof='result172_candidate_terminal_band.md',
                  controls_are_not_universal_proof=True, statistics=dict(STATS),
                  certificate_sha256=hashlib.sha256(cert_path.read_bytes()).hexdigest(),
                  constructor_sha256=cert['constructor_sha256'],
                  audit_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest())
    (ROOT/'independent_audit.json').write_text(json.dumps(result, ensure_ascii=False, indent=2), encoding='utf-8')
    print(json.dumps(result, ensure_ascii=False))


if __name__ == '__main__':
    main()
