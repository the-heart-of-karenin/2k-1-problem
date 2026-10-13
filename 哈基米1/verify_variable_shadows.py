"""Construct and verify variable-shadow words on explicit physical controls.

Internal preparation uses the proved vertex-interval search at root degree k.
Every saved word is checked by literal complete-cut counting, not only profiles.
No source project is imported and no writes occur outside this directory.
"""
from collections import Counter, deque
from itertools import combinations
from pathlib import Path
import hashlib
import json

ROOT = Path(__file__).resolve().parent


def arcs(edges, mask):
    return [(v, u) if mask >> i & 1 else (u, v)
            for i, (u, v) in enumerate(edges)]


def outs(n, edges, mask):
    row = [0] * n
    for u, _ in arcs(edges, mask):
        row[u] += 1
    return tuple(row)


def cuts(n, edges, mask):
    oriented = arcs(edges, mask)
    return [sum((s >> u & 1) and not (s >> v & 1) for u, v in oriented)
            for s in range(1, (1 << n) - 1)]


class Control:
    def __init__(self, name, k, c, h, ports, exterior):
        self.name, self.k, self.c = name, k, c
        self.h, self.ports, self.exterior = h, ports, exterior
        self.outer, self.edges = ports + exterior, h + ports + exterior
        self.m, self.d = len(h), len(ports)
        self.n = 1 + max(max(e) for e in self.edges)
        self.q = self.m - k * (c - 1)
        self.deg = tuple(sum(v in e for e in self.edges) for v in range(self.n))
        self.mu = tuple(self.deg[v] - 2 * k for v in range(c))
        self.qedges = [(0 if u < c else u - c + 1,
                        0 if v < c else v - c + 1) for u, v in self.outer]
        self.qn = self.n - c + 1
        self.hvec = [outs(c, h, mask) for mask in range(1 << self.m)]
        self.stats = Counter()
        self.signatures, self.words = {}, []
        assert self.q >= 1 and min(self.mu) >= 1
        for s in range(1, (1 << c) - 1):
            assert sum((s >> u & 1) and (s >> v & 1) for u, v in h) <= k * (s.bit_count() - 1)
        minimum = min(sum(bool(s >> u & 1) != bool(s >> v & 1)
                          for u, v in self.edges)
                      for s in range(1, (1 << self.n) - 1))
        assert minimum >= 2 * k + 1, (name, minimum)
        self.minimum_cut = minimum

    def qlegal(self, sigma):
        return min(cuts(self.qn, self.qedges, sigma)) >= self.k

    def outgoing(self, sigma):
        return frozenset(i for i in range(self.d) if not (sigma >> i & 1))

    def shadow(self, sigma, base):
        return (sigma | ((1 << self.d) - 1)) ^ sum(1 << i for i in base)

    def counts(self, collection):
        row = [0] * self.c
        for i in collection:
            row[self.ports[i][0]] += 1
        return tuple(row)

    def vertex_out(self, sigma, hm):
        fixed = outs(self.n, self.outer, sigma)
        return tuple(fixed[v] + self.hvec[hm][v] for v in range(self.c))

    def vertex_ok(self, sigma, hm):
        out = self.vertex_out(sigma, hm)
        return all(self.k <= out[v] <= self.deg[v] - self.k
                   for v in range(self.c))

    def paid(self, sigma, hm, base):
        if not self.vertex_ok(sigma, hm):
            return False
        need = self.counts(self.outgoing(sigma) - base)
        out = self.vertex_out(sigma, hm)
        return all(out[v] - self.k >= need[v] for v in range(self.c))

    def choose_paid(self, sigma, base, last=False):
        possibilities = [hm for hm in range(1 << self.m) if self.paid(sigma, hm, base)]
        assert possibilities, (self.name, sigma, sorted(base))
        return possibilities[-1 if last else 0]

    def enumerate_shadows(self):
        for sigma in range(1 << len(self.outer)):
            if not self.qlegal(sigma):
                continue
            outgoing = self.outgoing(sigma)
            bases, funded = [], []
            for choice in combinations(sorted(outgoing), self.k):
                base = frozenset(choice)
                if not self.qlegal(self.shadow(sigma, base)):
                    continue
                bases.append(base)
                need = self.counts(outgoing - base)
                if all(need[v] <= self.mu[v] for v in range(self.c)):
                    funded.append(base)
            self.signatures[sigma] = (bases, funded)
            self.stats['legal_quotient_signatures'] += 1
            self.stats['shadow_bases'] += len(bases)
            self.stats['capacity_shadow_bases'] += len(funded)
            if not bases:
                self.stats['no_root_k_shadow_signatures'] += 1
            elif not funded:
                self.stats['no_capacity_shadow_signatures'] += 1
            family = set(bases)
            for first in bases:
                for target in bases:
                    for g in first - target:
                        exchanges = [(f, (first - {g}) | {f}) for f in target - first
                                     if (first - {g}) | {f} in family]
                        assert exchanges, (self.name, sigma, first, target, g)
                        self.stats['all_element_basis_exchange_checks'] += 1
                        for f, nxt in exchanges:
                            upper = self.shadow(sigma, first) ^ (1 << f)
                            assert self.qlegal(upper)
                            assert self.qlegal(self.shadow(sigma, nxt))

    def descriptor(self):
        negatives = []
        for sigma, (bases, funded) in self.signatures.items():
            if bases and not funded and len(negatives) < 3:
                hm = next((hm for hm in range(1 << self.m)
                           if min(cuts(self.n, self.edges, hm | sigma << self.m)) >= self.k), None)
                assert hm is not None
                negatives.append(dict(sigma=sigma, actual_internal_mask=hm,
                                      shadow_bases=[sorted(e) for e in bases],
                                      capacity_shortfalls=[list(self.counts(self.outgoing(sigma) - e))
                                                           for e in bases]))
        return dict(name=self.name, k=self.k, c=self.c, n=self.n,
                    h=self.h, ports=self.ports, exterior=self.exterior,
                    edges=self.edges, minimum_cut=self.minimum_cut,
                    q=self.q, mu=self.mu, stats=dict(self.stats), words=self.words,
                    no_capacity_shadow_examples=negatives)


class Word:
    def __init__(self, control, label, sigma, hm, base):
        self.c = control
        self.label, self.sigma, self.hm = label, sigma, hm
        self.initial = hm | sigma << control.m
        self.base = base
        self.word = []
        self.check()
        assert control.paid(sigma, hm, base)

    def check(self):
        mask = self.hm | self.sigma << self.c.m
        amounts = cuts(self.c.n, self.c.edges, mask)
        self.c.stats['literal_complete_cut_checks'] += len(amounts)
        self.c.stats['actual_prefixes_checked'] += 1
        assert min(amounts) >= self.c.k, (self.label, len(self.word), mask, min(amounts))

    def flip(self, eid):
        if eid < self.c.m:
            self.hm ^= 1 << eid
        else:
            self.sigma ^= 1 << (eid - self.c.m)
        self.word.append(eid)
        self.check()

    def prepare(self, target):
        assert len(self.c.outgoing(self.sigma)) == self.c.k
        assert self.c.vertex_ok(self.sigma, self.hm)
        assert self.c.vertex_ok(self.sigma, target)
        if target == self.hm:
            return
        queue, pred = deque([self.hm]), {self.hm: None}
        while queue and target not in pred:
            old = queue.popleft()
            for eid in range(self.c.m):
                new = old ^ (1 << eid)
                if new not in pred and self.c.vertex_ok(self.sigma, new):
                    pred[new] = (old, eid)
                    queue.append(new)
        assert target in pred, (self.label, 'anchor preparation disconnected')
        sequence = []
        at = target
        while pred[at] is not None:
            before, eid = pred[at]
            sequence.append(eid)
            at = before
        self.c.stats['preparation_search_states'] += len(pred)
        for eid in reversed(sequence):
            self.flip(eid)
        assert self.hm == target

    def pair(self, f, g):
        xf, xg = self.c.ports[f][0], self.c.ports[g][0]
        chosen = None
        for hm in range(1 << self.c.m):
            if not self.c.vertex_ok(self.sigma, hm):
                continue
            out = self.c.vertex_out(self.sigma, hm)
            a = [v - self.c.k for v in out]
            if a[xf] <= self.c.mu[xf] - 1 and (xf == xg or a[xg] >= 1):
                chosen = hm
                break
        assert chosen is not None
        self.prepare(chosen)
        self.flip(self.c.m + f)
        self.flip(self.c.m + g)
        self.c.stats['actual_shadow_basis_exchanges'] += 1

    def root_transition(self, target_sigma, target_base, target_hm=None):
        old_sigma, old_base = self.sigma, self.base
        assert (old_sigma >> self.c.d) == (target_sigma >> self.c.d)
        assert self.c.paid(old_sigma, self.hm, old_base)
        old_out, new_out = self.c.outgoing(old_sigma), self.c.outgoing(target_sigma)
        assert len(old_out ^ new_out) <= 1
        for eid in sorted(old_out - old_base):
            self.flip(self.c.m + eid)
        current = old_base
        while current != target_base:
            pair = None
            for g in sorted(current - target_base):
                for f in sorted(target_base - current):
                    candidate = (current - {g}) | {f}
                    future = self.c.shadow(target_sigma, candidate)
                    if self.c.qlegal(future) and self.c.qlegal(self.sigma ^ (1 << f)):
                        pair = (f, g, candidate)
                        break
                if pair:
                    break
            assert pair is not None, (self.label, old_sigma, target_sigma, current, target_base)
            f, g, candidate = pair
            self.pair(f, g)
            current = candidate
        assert self.sigma == self.c.shadow(target_sigma, target_base)
        if target_hm is None:
            target_hm = self.c.choose_paid(target_sigma, target_base)
        assert self.c.paid(target_sigma, target_hm, target_base)
        self.prepare(target_hm)
        for eid in sorted(new_out - target_base):
            self.flip(self.c.m + eid)
        assert self.sigma == target_sigma and self.hm == target_hm
        self.base = target_base
        assert self.c.paid(self.sigma, self.hm, self.base)

    def exterior_transition(self, eid, target_base, target_hm=None):
        assert eid >= self.c.d
        old_sigma, target_sigma = self.sigma, self.sigma ^ (1 << eid)
        old_options = self.c.signatures[old_sigma][1]
        new_options = self.c.signatures[target_sigma][1]
        outgoing = self.c.outgoing(old_sigma)
        def joint_ok(e, f):
            ea = self.c.counts(outgoing - e)
            fa = self.c.counts(outgoing - f)
            return sum(max(a, b) for a, b in zip(ea, fa)) <= self.c.q + len(outgoing) - self.c.k
        chosen = next(((e, f) for e in old_options for f in new_options if joint_ok(e, f)), None)
        assert chosen is not None
        first, second = chosen
        ba, bb = self.c.counts(outgoing - first), self.c.counts(outgoing - second)
        minimum = tuple(max(x, y) for x, y in zip(ba, bb))
        joint_hm = next((hm for hm in range(1 << self.c.m)
                         if self.c.vertex_ok(old_sigma, hm)
                         and all(self.c.vertex_out(old_sigma, hm)[v] - self.c.k >= minimum[v]
                                 for v in range(self.c.c))), None)
        assert joint_hm is not None
        assert self.c.paid(old_sigma, joint_hm, first)
        assert self.c.paid(target_sigma, joint_hm, second)
        self.root_transition(old_sigma, first, joint_hm)
        self.flip(self.c.m + eid)
        self.base = second
        self.root_transition(target_sigma, target_base, target_hm)
        self.c.stats['actual_exterior_one_step_bridges'] += 1

    def save(self, intended):
        final = self.hm | self.sigma << self.c.m
        outer_actual = [eid - self.c.m for eid in self.word if eid >= self.c.m]
        exterior_actual = [eid for eid in outer_actual if eid >= self.c.d]
        exterior_intended = [eid for eid in intended if eid >= self.c.d]
        assert exterior_actual == exterior_intended
        projected = self.initial >> self.c.m
        for eid in intended:
            projected ^= 1 << eid
        assert projected == self.sigma
        assert self.c.paid(self.sigma, self.hm, self.base)
        record = dict(label=self.label, initial_mask=self.initial, word=self.word,
                      final_mask=final, intended_outer_word=intended,
                      final_shadow=sorted(self.base))
        self.c.words.append(record)
        self.c.stats['saved_actual_words'] += 1
        self.c.stats['saved_actual_single_flips'] += len(self.word)


def controls():
    yield Control('triangle_q1_capacity_more_than_one', 2, 3,
                  [(0, 1)] * 2 + [(1, 2)] * 2 + [(0, 2)],
                  [(0, 3)] * 2 + [(1, 3)] * 2 + [(1, 4)] * 2 + [(2, 4)] * 2,
                  [(3, 4)] * 2)
    yield Control('four_vertex_q1_multiple_ports', 2, 4,
                  list(combinations(range(4), 2)) + [(0, 1)],
                  [(v, 4 if v in (0, 2) else 5) for v in range(4) for _ in range(2)],
                  [(4, 5)] * 3)
    yield Control('k3_q2_parallel_physical_copies', 3, 4,
                  [(u, v) for u, v in combinations(range(4), 2)
                   for _ in range(1 if (u, v) == (2, 3) else 2)],
                  [(0, 4)] * 2 + [(1, 5)] + [(2, 4)] * 2 + [(3, 5)] * 2,
                  [(4, 5)] * 4)
    yield Control('doubled_cycle_q2', 2, 4,
                  [(i, (i + 1) % 4) for i in range(4) for _ in range(2)],
                  [(0, 4), (1, 5)] + [(2, 4)] * 2 + [(3, 5)] * 2,
                  [(4, 5)] * 3)


def unpaid_entry_family(k):
    h = [(0, 1)] * k + [(1, 2)] * k + [(0, 2)]
    ports = [(0, 3)] * k + [(1, 3)] * k + [(1, 4)] * k + [(2, 4)] * k
    exterior = [(3, 4)] * k
    edges = h + ports + exterior
    m = len(h)
    initial = ((1 << k) - 1) | (((1 << k) - 1) << (m + 2 * k))
    word = [m]
    for j in range(1, k - 1):
        word.extend([j - 1, m + j])
    word.extend(m + 4 * k + j for j in range(k - 1))
    word.append(k)
    state = initial
    prefix_minima = [min(cuts(5, edges, state))]
    for eid in word:
        state ^= 1 << eid
        prefix_minima.append(min(cuts(5, edges, state)))
    assert min(prefix_minima) >= k
    assert len(word) == 3 * k - 3
    assert outs(5, edges, initial) == (k + 1, 3 * k, k, k, k)
    assert outs(5, edges, state) == (k, 2 * k + 1, k + 1, k, 2 * k - 1)
    final_base = [k - 1] + [3 * k + j for j in range(k - 1)]
    sigma = state >> m
    shadow = (sigma | ((1 << (4 * k)) - 1)) ^ sum(1 << eid for eid in final_base)
    qedges = [(0 if u < 3 else u - 2, 0 if v < 3 else v - 2) for u, v in ports + exterior]
    assert min(cuts(3, qedges, shadow)) >= k
    return dict(k=k, c=3, n=5, h=h, ports=ports, exterior=exterior, edges=edges,
                q=1, mu=[1, 2 * k, 1], initial_mask=initial, word=word,
                final_mask=state, final_shadow=final_base,
                prefix_minima=prefix_minima,
                no_capacity_shadow_reason='Every initial root-k shadow sends all k base ports to a; w has k outgoing ports but mu_w=1.',
                exact_cut_checks=30 * (len(word) + 1))


def flow_threshold(n, edges, mask, source, target, threshold, undirected=False):
    residual = [[0] * n for _ in range(n)]
    for eid, (u, v) in enumerate(edges):
        if undirected:
            residual[u][v] += 1
            residual[v][u] += 1
        else:
            if mask >> eid & 1:
                u, v = v, u
            residual[u][v] += 1
    amount = 0
    while amount < threshold:
        queue = deque([source])
        before = [-1] * n
        before[source] = source
        while queue and before[target] < 0:
            u = queue.popleft()
            for v in range(n):
                if residual[u][v] and before[v] < 0:
                    before[v] = u
                    queue.append(v)
        if before[target] < 0:
            break
        unit, v = threshold - amount, target
        while v != source:
            u = before[v]
            unit = min(unit, residual[u][v])
            v = u
        v = target
        while v != source:
            u = before[v]
            residual[u][v] -= unit
            residual[v][u] += unit
            v = u
        amount += unit
    assert amount >= threshold, (n, source, target, amount, threshold)


def large_identity_change_family(k):
    assert k % 2 == 0 and k >= 4
    nc, z = k + 1, k
    h, ports, exterior, bits = [], [], [], []
    def add(bucket, u, v, tail):
        bucket.append((u, v))
        bits.append(int(tail == v))
    for i, j in combinations(range(k), 2):
        if (i, j) != (0, 1):
            add(h, i, j, i)
        add(h, i, j, j)
    for i in range(k):
        add(h, z, i, z)
    add(h, z, 0, 0)
    add(h, z, 1, z)
    for i in range(k):
        add(ports, i, nc + i, i)
        add(ports, i, nc + (i + 1) % k, i)
    for i in range(k):
        add(ports, z, nc + i, nc + i)
    add(ports, z, nc, nc)
    changed = None
    r = k // 2
    for i, j in combinations(range(k), 2):
        if (i, j) == (0, r):
            changed = len(h) + len(ports) + len(exterior)
        add(exterior, nc + i, nc + j, nc + i)
        add(exterior, nc + i, nc + j, nc + j)
    edges = h + ports + exterior
    n, m, d = 2 * k + 1, len(h), len(ports)
    initial = sum(bit << eid for eid, bit in enumerate(bits))
    final = initial ^ (1 << changed)
    sigma, target_sigma = initial >> m, final >> m
    diag = [2 * i for i in range(k)]
    shift = [2 * i + 1 for i in range(k)]
    mixed = [2 * i + int(i < r) for i in range(k)]
    assert min(len(set(mixed) - set(e)) for e in (diag, shift)) == r
    assert m == k * k + 1
    qedges = [(0 if u < nc else u - nc + 1, 0 if v < nc else v - nc + 1)
              for u, v in ports + exterior]
    flow_checks = 0
    for v in range(1, n):
        flow_threshold(n, edges, initial, 0, v, 2 * k + 1, True)
        flow_checks += 1
    for state in (initial, final):
        for v in range(1, n):
            flow_threshold(n, edges, state, 0, v, k)
            flow_threshold(n, edges, state, v, 0, k)
            flow_checks += 2
    for sig, base in ((sigma, diag), (sigma, shift), (target_sigma, mixed)):
        shadow = (sig | ((1 << d) - 1)) ^ sum(1 << eid for eid in base)
        for v in range(1, k + 1):
            flow_threshold(k + 1, qedges, shadow, 0, v, k)
            flow_threshold(k + 1, qedges, shadow, v, 0, k)
            flow_checks += 2
    expected = [k + 1] * nc + [k + 1] + [k] * (k - 1)
    assert list(outs(n, edges, initial)) == expected
    expected[nc] -= 1
    expected[nc + r] += 1
    assert list(outs(n, edges, final)) == expected
    return dict(k=k, c=nc, n=n, h=h, ports=ports, exterior=exterior, edges=edges,
                q=1, initial_mask=initial, word=[changed], final_mask=final,
                old_capacity_shadow_bases=[diag, shift], new_capacity_shadow_base=mixed,
                minimum_physical_shadow_distance=r, common_extra_payment_units=0,
                root_flow_threshold_checks=flow_checks,
                verification='Undirected root flows; two directed root flows per other vertex per prefix; shadow root flows.')


def main():
    output = []
    for index, c in enumerate(controls()):
        c.enumerate_shadows()
        root_samples, exterior_samples, forced_sample = [], [], None
        bridge_negative = []
        for sigma, (bases, funded) in c.signatures.items():
            if not funded:
                continue
            for eid in range(len(c.outer)):
                nxt = sigma ^ (1 << eid)
                if nxt not in c.signatures or not c.signatures[nxt][1]:
                    continue
                target_options = c.signatures[nxt][1]
                if eid < c.d:
                    c.stats['eligible_root_neighbours'] += 1
                    if len(root_samples) < 8 and len(c.outgoing(sigma)) > c.k:
                        root_samples.append((sigma, eid, funded[0], target_options[-1]))
                else:
                    outgoing = c.outgoing(sigma)
                    eligible = any(sum(max(a, b) for a, b in zip(c.counts(outgoing - e), c.counts(outgoing - f)))
                                   <= c.q + len(outgoing) - c.k
                                   for e in funded for f in target_options)
                    if eligible:
                        c.stats['eligible_exterior_neighbours'] += 1
                        if len(exterior_samples) < 8:
                            exterior_samples.append((sigma, eid, funded[0], target_options[-1]))
                        if not (set(funded) & set(target_options)):
                            c.stats['exterior_neighbours_without_common_shadow'] += 1
                            if forced_sample is None:
                                forced_sample = (sigma, eid, funded[0], target_options[-1])
                    else:
                        c.stats['exterior_neighbours_without_common_payment_budget'] += 1
                        if len(bridge_negative) < 3:
                            bridge_negative.append(dict(sigma=sigma, eid=eid, target=nxt))
        for i, (sigma, eid, base, target) in enumerate(root_samples):
            initial = c.choose_paid(sigma, base, last=bool(i % 2))
            w = Word(c, f'root_neighbour_{i}', sigma, initial, base)
            final_h = c.choose_paid(sigma ^ (1 << eid), target, last=True)
            w.root_transition(sigma ^ (1 << eid), target, final_h)
            w.save([eid])
        selected = exterior_samples + ([forced_sample] if forced_sample else [])
        for i, (sigma, eid, base, target) in enumerate(selected):
            w = Word(c, f'exterior_bridge_{i}', sigma,
                     c.choose_paid(sigma, base, last=True), base)
            final_h = c.choose_paid(sigma ^ (1 << eid), target, last=True)
            w.exterior_transition(eid, target, final_h)
            w.save([eid])
        if index == 0:
            base = frozenset([0, 2])
            sigma = c.shadow(0, base)
            intended = [6, 8, 2, 2, 8, 6]
            w = Word(c, 'forced_shadow_change_return', sigma,
                     c.choose_paid(sigma, base), base)
            common = set(c.outgoing(sigma))
            for pos, eid in enumerate(intended):
                nxt = w.sigma ^ (1 << eid)
                target = (frozenset([0, 6]) if pos in (1, 2, 3)
                          else frozenset([0, 2]))
                assert target in c.signatures[nxt][1]
                final_h = c.choose_paid(nxt, target, last=True) if pos == len(intended) - 1 else None
                if eid < c.d:
                    w.root_transition(nxt, target, final_h)
                else:
                    w.exterior_transition(eid, target, final_h)
                common &= set(c.outgoing(nxt))
            assert len(common) < c.k
            assert w.sigma == sigma
            w.save(intended)
            c.stats['no_fixed_k_baseline_return_histories'] += 1
            base = frozenset([0, 6])
            sigma = c.shadow(1 << 8, base)
            intended = [2, 0, 4, 6, 1, 2, 7, 4, 0, 1, 6, 7]
            w = Word(c, 'root_star_rotation_without_fixed_baseline', sigma,
                     c.choose_paid(sigma, base), base)
            common = set(base)
            for pos, eid in enumerate(intended):
                nxt = w.sigma ^ (1 << eid)
                target = c.signatures[nxt][1][0]
                final_h = c.choose_paid(nxt, target, last=True) if pos == len(intended) - 1 else None
                w.root_transition(nxt, target, final_h)
                common &= set(c.outgoing(nxt))
            assert len(common) < c.k and w.sigma == sigma
            w.save(intended)
            c.stats['no_fixed_k_baseline_return_histories'] += 1
        descriptor = c.descriptor()
        descriptor['bridge_criterion_negative_examples'] = bridge_negative
        output.append(descriptor)
        print(json.dumps(dict(name=c.name, stats=dict(c.stats)), ensure_ascii=False), flush=True)
    source = ROOT.parent / '2k+1'
    dependency_names = [
        '研究结果94_严格稠密核小边界实际收缩_2026-10-08.md',
        '研究结果148_极小坏岸祖先与逐端口共同保护_2026-10-10.md',
        '研究结果146_共同根紧层的树缺额与非OSP核供给反例_2026-10-10.md',
    ]
    dependencies = {name: hashlib.sha256((source / name).read_bytes()).hexdigest()
                    for name in dependency_names}
    result = dict(status='PASS', theorem='H1', controls=output,
                  unpaid_entry_family=[unpaid_entry_family(k) for k in (2, 3, 4, 7, 12, 30, 100)],
                  large_identity_change_family=[large_identity_change_family(k) for k in (4, 6, 10, 20)],
                  scope='Exact finite controls; universal assertions use the analytic proof.',
                  edge_identity_convention='Zero based index into each saved edges array.',
                  dependency_sha256=dependencies,
                  program_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest())
    (ROOT / 'variable_shadows_certificate.json').write_text(
        json.dumps(result, ensure_ascii=False, indent=2), encoding='utf-8')
    print('PASS: variable_shadows_certificate.json', flush=True)


if __name__ == '__main__':
    main()
