"""Construct words for the terminal-cut band theorem. No state-graph search."""
from collections import deque
from pathlib import Path
import hashlib
import json
import random

ROOT = Path(__file__).resolve().parent


def tails(edges, mask):
    return [(v, u) if mask >> i & 1 else (u, v)
            for i, (u, v) in enumerate(edges)]


def degrees(edges, mask, n):
    b = [0] * n
    for u, _ in tails(edges, mask):
        b[u] += 1
    return b


def phi(b, k):
    return sum(max(0, x-k) for x in b)


def clique(k):
    n = 2*k+1
    edges = [(u, v) for u in range(n) for v in range(u+1, n)]
    mask = sum(1 << i for i, (u, v) in enumerate(edges) if v-u > k)
    assert degrees(edges, mask, n) == [k] * n
    return n, edges, mask


def make_instance(name, k, supports=None, copies=1, port_high=None):
    n, edges, base = clique(k)
    mh = len(edges)
    outside_mask = 0
    if port_high is not None:
        for r in (n, n+1):
            for v in range(n):
                i = len(edges)
                edges.append((v, r))
                if v not in port_high:
                    outside_mask |= 1 << i
    else:
        for r, support in enumerate(supports, start=n):
            for v in support:
                for _ in range(copies):
                    edges.append((v, r))
                    i = len(edges)
                    edges.append((v, r))
                    outside_mask |= 1 << i
    nv = max(max(e) for e in edges)+1
    f = []
    oriented = tails(edges, outside_mask)
    for x in range(1 << n):
        best = len(edges)+1
        for z in range(1 << (nv-n)):
            shore = x | z << n
            cost = sum(bool(shore >> u & 1) and not (shore >> v & 1)
                       for u, v in oriented[mh:])
            best = min(best, cost)
        f.append(best)
    allc = (1 << n)-1
    lo = [max(0, k-f[1 << v]) for v in range(n)]
    hi = [min(2*k, k+f[allc ^ (1 << v)]) for v in range(n)]
    assert all(l < u and l <= k <= u for l, u in zip(lo, hi))
    assert min(lo) < k < max(hi)
    budget = None
    rows = []
    for x in range(1, allc):
        count = x.bit_count()
        eh = sum((x >> u & 1) and (x >> v & 1) for u, v in edges[:mh])
        alpha = k*(count-1)-eh
        assert alpha >= 0
        if count in (1, n-1):
            continue
        a = sum(k-lo[v] for v in range(n) if x >> v & 1)
        b = sum(hi[v]-k for v in range(n) if not (x >> v & 1))
        h = alpha+f[x]
        rows.append([x, alpha, f[x], a, b])
        if h < min(a, b):
            budget = h if budget is None else min(budget, h)
    return dict(name=name, k=k, core_n=n, vertex_n=nv, edges=edges,
                internal_count=mh, frozen_mask=hex(outside_mask),
                eulerian_mask=hex(base), f=f, lower=lo, upper=hi,
                safe_band=budget, margin_rows=rows, tasks=[])


class Router:
    def __init__(self, instance, source):
        self.inst = instance
        self.k = instance['k']
        self.n = instance['core_n']
        self.edges = instance['edges'][:instance['internal_count']]
        self.mask = source
        self.b = degrees(self.edges, source, self.n)
        self.lo, self.hi = instance['lower'], instance['upper']
        self.word = []
        self.macros = []
        self.initial_phi = phi(self.b, self.k)
        self.peak = self.initial_phi
        self.cap = max(2, self.initial_phi+1)
        assert instance['safe_band'] is None or self.cap <= instance['safe_band']
        assert all(l <= b <= u for l, b, u in zip(self.lo, self.b, self.hi))

    def flip(self, e):
        u, v = self.edges[e]
        if self.mask >> e & 1:
            u, v = v, u
        self.b[u] -= 1
        self.b[v] += 1
        self.mask ^= 1 << e
        self.word.append(e)
        assert all(l <= b <= u for l, b, u in zip(self.lo, self.b, self.hi))
        p = phi(self.b, self.k)
        self.peak = max(self.peak, p)
        assert p <= self.cap

    def adjacency(self, allowed=None):
        adj = [[] for _ in range(self.n)]
        for e, (u, v) in enumerate(tails(self.edges, self.mask)):
            if allowed is None or e in allowed:
                adj[u].append((v, e))
        return adj

    def path(self, starts, goals, allowed=None):
        adj = self.adjacency(allowed)
        pred = {s: None for s in starts}
        queue = deque(starts)
        while queue:
            u = queue.popleft()
            if u in goals:
                nodes, ids = [u], []
                while pred[u] is not None:
                    p, e = pred[u]
                    ids.append(e)
                    nodes.append(p)
                    u = p
                return nodes[::-1], ids[::-1]
            for v, e in adj[u]:
                if v not in pred:
                    pred[v] = (u, e)
                    queue.append(v)
        raise AssertionError('No actual directed path')

    def serialize_path(self, nodes, ids):
        assert len(nodes) == len(ids)+1
        assert self.b[nodes[0]] > self.lo[nodes[0]]
        assert self.b[nodes[-1]] < self.hi[nodes[-1]]
        assert all(self.b[v] == self.k for v in nodes[1:-1])
        initial = len(self.word)
        i = 0
        while i < len(ids):
            j = i+1
            while self.b[nodes[j]] == self.hi[nodes[j]]:
                assert j < len(ids)
                assert self.b[nodes[j]] == self.k
                assert self.lo[nodes[j]] < self.k
                j += 1
            # Open the end of the saturated upper run, then fill backwards.
            for t in range(j-1, i-1, -1):
                e = ids[t]
                actual = tails([self.edges[e]], (self.mask >> e) & 1)[0]
                assert actual == (nodes[t], nodes[t+1])
                self.flip(e)
            i = j
        assert sorted(self.word[initial:]) == sorted(ids)

    def normalize(self):
        while phi(self.b, self.k):
            p = phi(self.b, self.k)
            begin = len(self.word)
            nodes, ids = self.path([v for v in range(self.n) if self.b[v] > self.k],
                                   {v for v in range(self.n) if self.b[v] < self.k})
            self.serialize_path(nodes, ids)
            assert phi(self.b, self.k) == p-1
            self.macros.append(dict(kind='normalization_path', begin=begin,
                                    end=len(self.word), edges=ids,
                                    phi_before=p, phi_after=p-1))

    def difference_cycle(self, target):
        diff = {e for e in range(len(self.edges)) if (self.mask ^ target) >> e & 1}
        adj = self.adjacency(diff)
        start = next(v for v in range(self.n) if adj[v])
        nodes, ids, positions = [], [], {}
        u = start
        while u not in positions:
            positions[u] = len(nodes)
            nodes.append(u)
            assert adj[u]
            v, e = adj[u][0]
            ids.append(e)
            u = v
        p = positions[u]
        return nodes[p:], ids[p:]

    def reverse_cycle(self, nodes, ids):
        assert all(b == self.k for b in self.b)
        begin = len(self.word)
        before = self.mask
        launch = next((i for i, u in enumerate(nodes)
                       if self.lo[u] < self.k
                       and self.hi[nodes[(i+1) % len(nodes)]] > self.k), None)
        helpers = []
        if launch is not None:
            self.flip(ids[launch])
            remaining = [ids[(launch+1+t) % len(ids)] for t in range(len(ids)-1)]
            pn = [nodes[(launch+1+t) % len(nodes)] for t in range(len(nodes))]
            self.serialize_path(pn, remaining)
            branch = 'mixed_or_free'
        elif all(self.lo[v] == self.k for v in nodes):
            pn, pe = self.path([v for v in range(self.n) if self.lo[v] < self.k], set(nodes))
            prep = len(self.word)
            self.serialize_path(pn, pe)
            helper_word = self.word[prep:]
            helpers = pe
            i = nodes.index(pn[-1])
            for t in range(len(ids)):
                self.flip(ids[(i+t) % len(ids)])
            for e in helper_word[::-1]:
                self.flip(e)
            branch = 'all_lower_stem'
        else:
            assert all(self.hi[v] == self.k for v in nodes)
            pn, pe = self.path(nodes, {v for v in range(self.n) if self.hi[v] > self.k})
            prep = len(self.word)
            self.serialize_path(pn, pe)
            helper_word = self.word[prep:]
            helpers = pe
            i = nodes.index(pn[0])
            for t in range(len(ids)):
                self.flip(ids[(i-1-t) % len(ids)])
            for e in helper_word[::-1]:
                self.flip(e)
            branch = 'all_upper_stem'
        expected = before
        for e in ids:
            expected ^= 1 << e
        assert self.mask == expected and self.b == [self.k] * self.n
        assert not set(helpers) & set(ids)
        self.macros.append(dict(kind='cycle', branch=branch, begin=begin,
                                end=len(self.word), edges=ids, helpers=helpers))

    def connect(self, target):
        assert degrees(self.edges, target, self.n) == [self.k] * self.n
        self.normalize()
        while self.mask != target:
            nodes, ids = self.difference_cycle(target)
            hamming = (self.mask ^ target).bit_count()
            self.reverse_cycle(nodes, ids)
            assert (self.mask ^ target).bit_count() == hamming-len(ids)
        return dict(source=hex(self.source), target=hex(target), word=self.word,
                    macros=self.macros, phi_source=self.initial_phi,
                    phi_peak=self.peak, phi_cap=self.cap)

    @property
    def source(self):
        mask = self.mask
        for e in self.word:
            mask ^= 1 << e
        return mask


def add_task(inst, source, target):
    task = Router(inst, source).connect(target)
    inst['tasks'].append(task)


def random_sources(inst, p, number):
    rng = random.Random(173000+inst['k']*100+p)
    edges = inst['edges'][:inst['internal_count']]
    seen = set()
    state = int(inst['eulerian_mask'], 16)
    steps = 0
    while len(seen) < number:
        steps += 1
        assert steps < 200000
        e = rng.randrange(len(edges))
        nxt = state ^ 1 << e
        b = degrees(edges, nxt, inst['core_n'])
        if phi(b, inst['k']) <= p and all(l <= t <= u for l, t, u in
                                        zip(inst['lower'], b, inst['upper'])):
            state = nxt
            if phi(b, inst['k']) == p:
                seen.add(state)
    return sorted(seen)


def tail_assignment(edges, desired):
    # Only creates an ILLEGAL-band control witness; never a reachability oracle.
    m, n = len(edges), len(desired)
    src, sink = m+n, m+n+1
    adj = [[] for _ in range(sink+1)]
    def add(u, v, c):
        adj[u].append([v, c, len(adj[v])])
        adj[v].append([u, 0, len(adj[u])-1])
    for i, (u, v) in enumerate(edges):
        add(src, i, 1)
        add(i, m+u, 1)
        add(i, m+v, 1)
    for v, b in enumerate(desired):
        add(m+v, sink, b)
    flow = 0
    while True:
        pred = {src: None}
        q = deque([src])
        while q and sink not in pred:
            u = q.popleft()
            for j, (v, c, _) in enumerate(adj[u]):
                if c and v not in pred:
                    pred[v] = (u, j)
                    q.append(v)
        if sink not in pred:
            break
        u = sink
        while pred[u] is not None:
            v, j = pred[u]
            rev = adj[v][j][2]
            adj[v][j][1] -= 1
            adj[u][rev][1] += 1
            u = v
        flow += 1
    assert flow == m
    mask = 0
    for i, (u, v) in enumerate(edges):
        used = next(t for t, cap, _ in adj[i] if m <= t < m+n and cap == 0)-m
        if used == v:
            mask |= 1 << i
        else:
            assert used == u
    assert degrees(edges, mask, n) == desired
    return mask


def main():
    instances = []
    k = 2
    overlap = make_instance('k2_far_overlapping_terminal_supports', k,
                            supports=[[0, 1, 2], [2, 3, 4]], copies=k)
    assert overlap['safe_band'] == 3
    base = int(overlap['eulerian_mask'], 16)
    checked = eligible = 0
    for mask in range(1 << overlap['internal_count']):
        checked += 1
        b = degrees(overlap['edges'][:overlap['internal_count']], mask, 5)
        if phi(b, k) <= 2:
            eligible += 1
            add_task(overlap, mask, base)
    overlap['source_coverage'] = dict(all_internal_masks_checked=checked,
                                       eligible_masks=eligible,
                                       criterion='Phi <= 2; fixed selected sigma only')
    instances.append(overlap)
    for k in (3, 4, 5):
        n = 2*k+1
        inst = make_instance(f'k{k}_far_disjoint_terminal_supports', k,
                             supports=[[0, 1], list(range(2, n))], copies=k)
        assert inst['safe_band'] == k-1
        base = int(inst['eulerian_mask'], 16)
        for p in range(1, k-1):
            for j, source in enumerate(random_sources(inst, p, 3)):
                target = base if j % 2 else base ^ ((1 << inst['internal_count'])-1)
                add_task(inst, source, target)
        add_task(inst, base, base ^ ((1 << inst['internal_count'])-1))
        instances.append(inst)
    polarized = make_instance('k3_far_all_lower_and_all_upper_cycles', 3,
                              port_high={0, 2, 4, 6})
    assert polarized['safe_band'] is None
    base = int(polarized['eulerian_mask'], 16)
    for cycle in ([0, 2, 4], [1, 3, 5]):
        target = base
        for u, v in zip(cycle, cycle[1:]+cycle[:1]):
            e = polarized['edges'].index(tuple(sorted((u, v))))
            target ^= 1 << e
        add_task(polarized, base, target)
    for source in random_sources(polarized, 2, 3):
        add_task(polarized, source, base ^ ((1 << polarized['internal_count'])-1))
    instances.append(polarized)

    unsafe = []
    for k in (2, 3):
        n = 2*k+1
        inst = make_instance(f'k{k}_point_valid_but_mixed_cut_invalid', k,
                             supports=[[0, 1], list(range(2, n))], copies=k)
        b = [k-1, 1, 2*k]+[k]*(n-3)
        bad = tail_assignment(inst['edges'][:inst['internal_count']], b)
        inst['witness'] = dict(internal_mask=hex(bad), phi=phi(b, k),
                               violating_shore=(1 << 0) | (1 << 1) | (1 << n),
                               expected_out=k-1)
        unsafe.append(inst)

    one_unit = []
    for k in (2, 3):
        n = 4*k
        edges = [(u, 2*k+v) for u in range(2*k) for v in range(2*k)]
        mh = len(edges)
        # A union of k cyclic perfect matchings is L -> R; complement is R -> L.
        base = sum(1 << e for e, (u, v) in enumerate(edges)
                   if (v-2*k-u) % (2*k) >= k)
        outside = 0
        for u in range(n):
            e = len(edges)
            edges.append((u, n))
            if u < 2*k:
                outside |= 1 << e
        # Extract a directed rectangle. Every matching index has a transition.
        rect = None
        oriented = tails(edges[:mh], base)
        for a in range(2*k):
            for b in range(a+1, 2*k):
                for c in range(2*k, 4*k):
                    for d in range(c+1, 4*k):
                        cyc = [a, c, b, d]
                        ids = [edges.index(tuple(sorted((u, v)))) for u, v in
                               zip(cyc, cyc[1:]+cyc[:1])]
                        if all(oriented[e] == (u, v) for e, u, v in
                               zip(ids, cyc, cyc[1:]+cyc[:1])):
                            rect = (cyc, ids)
                            break
                    if rect: break
                if rect: break
            if rect: break
        assert rect
        cyc, ids = rect
        # Cycle is L -> R -> L -> R; first perform its two R -> L edges.
        word = [ids[1], ids[3], ids[0], ids[2]]
        target = base
        for e in ids: target ^= 1 << e
        one_unit.append(dict(name=f'k{k}_one_unit_isolation_control', k=k,
                             core_n=n, vertex_n=n+1, edges=edges,
                             internal_count=mh, frozen_mask=hex(outside),
                             source=hex(base), target=hex(target), word=word))

    cert = dict(date='2026-10-13', main_status='OPEN', regularization_used=False,
                theorem_scope='conditional terminal-cut safe band, arbitrary core and outside size',
                constructor_state_graph_search=False, instances=instances,
                unsafe_band_controls=unsafe, one_unit_controls=one_unit,
                constructor_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest())
    (ROOT/'terminal_band_certificate.json').write_text(json.dumps(cert, ensure_ascii=False, indent=2), encoding='utf-8')
    stats = dict(status='CONSTRUCTION_PASS_PENDING_INDEPENDENT_AUDIT',
                 instances=len(instances), tasks=sum(len(x['tasks']) for x in instances),
                 flips=sum(len(t['word']) for x in instances for t in x['tasks']),
                 source_phi_max=max(t['phi_source'] for x in instances for t in x['tasks']),
                 peak_phi_max=max(t['phi_peak'] for x in instances for t in x['tasks']),
                 branches={})
    for x in instances:
        for t in x['tasks']:
            for macro in t['macros']:
                kind = macro.get('branch', macro['kind'])
                stats['branches'][kind] = stats['branches'].get(kind, 0)+1
    (ROOT/'construction_summary.json').write_text(json.dumps(stats, ensure_ascii=False, indent=2), encoding='utf-8')
    print(json.dumps(stats, ensure_ascii=False))


if __name__ == '__main__':
    main()
