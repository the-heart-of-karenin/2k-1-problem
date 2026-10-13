"""Construct physical H2 entry words; exact finite enumeration and flow controls.

The source archive is never imported or written. Bit i reverses physical edge i.
Finite controls enumerate every internal mask and every legal root decrease.
All unpaid pairs have saved actual words, including their last specified port.
"""
from collections import Counter, deque
from itertools import combinations
from pathlib import Path
import hashlib
import json

ROOT = Path(__file__).resolve().parent


def orient(edges, mask):
    return [(v, u) if mask >> i & 1 else (u, v)
            for i, (u, v) in enumerate(edges)]


def out_vector(n, arcs):
    out = [0] * n
    for u, v in arcs:
        out[u] += 1
    return tuple(out)


class CutTable:
    def __init__(self, n, edges, k):
        self.n, self.edges, self.k = n, edges, k
        self.adj = [[0] * n for _ in range(n)]
        self.deg = [0] * n
        for u, v in edges:
            self.adj[u][v] += 1
            self.adj[v][u] += 1
            self.deg[u] += 1
            self.deg[v] += 1
        self.inside = [0] * (1 << n)
        for s in range(1, 1 << n):
            b = s & -s
            u = b.bit_length() - 1
            rem = s ^ b
            self.inside[s] = self.inside[rem] + sum(
                self.adj[u][v] for v in range(n) if rem >> v & 1)
        self.rows_cache = {}
        self.checks = 0

    def rows(self, out):
        if out not in self.rows_cache:
            subtotal = [0] * (1 << self.n)
            rows = []
            for s in range(1, (1 << self.n) - 1):
                b = s & -s
                subtotal[s] = subtotal[s ^ b] + out[b.bit_length() - 1]
                rows.append(subtotal[s] - self.inside[s])
            self.rows_cache[out] = rows
            self.checks += len(rows)
        return self.rows_cache[out]

    def legal(self, mask):
        return min(self.rows(out_vector(self.n, orient(self.edges, mask)))) >= self.k

    def undirected_minimum(self):
        sums = [0] * (1 << self.n)
        result = len(self.edges)
        for s in range(1, (1 << self.n) - 1):
            b = s & -s
            sums[s] = sums[s ^ b] + self.deg[b.bit_length() - 1]
            result = min(result, sums[s] - 2 * self.inside[s])
        return result


def path_in_core(c, h_arcs, sources, target, allowed):
    todo = deque(sorted(sources))
    parent = {v: None for v in sources}
    adj = [[] for _ in range(c)]
    for eid, (u, v) in enumerate(h_arcs):
        if allowed >> u & 1 and allowed >> v & 1:
            adj[u].append((v, eid))
    while todo:
        u = todo.popleft()
        if u == target:
            vertices, word = [u], []
            while parent[u] is not None:
                v, eid = parent[u]
                word.append(eid)
                vertices.append(v)
                u = v
            return list(reversed(vertices)), list(reversed(word))
        for v, eid in adj[u]:
            if v not in parent:
                parent[v] = (u, eid)
                todo.append(v)
    raise AssertionError(('path does not exist', sources, target, allowed))


def prepare(control, hm, g, full_table):
    k, c, h, outer, sigma = (control[key] for key in ('k', 'c', 'h', 'outer', 'sigma'))
    edges, m, n = h + outer, len(h), full_table.n
    mask = hm | sigma << m
    arcs = orient(edges, mask)
    out = out_vector(n, arcs)
    a = tuple(out[v] - k for v in range(c))
    x, y = outer[g]
    assert x < c <= y and not (sigma >> g & 1)
    assert a[x] == 0
    core = (1 << c) - 1
    whole = (1 << n) - 1
    outside = whole ^ core
    mixed_guards = {u: [] for u in range(c) if a[u] > 0}
    for s, amount in enumerate(full_table.rows(out), 1):
        trace, z = s & core, s & outside
        if amount == k and trace not in (0, core) and z not in (0, outside):
            for u in mixed_guards:
                if trace >> u & 1:
                    assert a[u] == 1 and trace >> x & 1
                    assert sum(a[v] for v in range(c) if trace >> v & 1) == 1
                    assert full_table.inside[trace] == k * (trace.bit_count() - 1)
                    mixed_guards[u].append((s, trace))
    guarded = [u for u in mixed_guards if mixed_guards[u]]
    if guarded:
        u = min(guarded)
        allowed = core
        for s, trace in mixed_guards[u]:
            allowed &= trace
        assert allowed >> x & 1
        assert full_table.inside[allowed] == k * (allowed.bit_count() - 1)
        vertices, word = path_in_core(c, arcs[:m], {u}, x, allowed)
        branch = 'intersection_of_all_mixed_guards'
    else:
        allowed = core
        vertices, word = path_in_core(c, arcs[:m], set(mixed_guards), x, allowed)
        u = vertices[0]
        branch = 'no_mixed_guard_for_donor'
    assert a[u] > 0 and all(a[v] == 0 for v in vertices[1:])
    assert len(word) <= c - 1
    tight = [s for s, value in enumerate(full_table.rows(out), 1) if value == k]
    for frontier in vertices[1:]:
        assert all(not (s >> u & 1) or (s >> frontier & 1) for s in tight)
    current = mask
    for eid in word:
        current ^= 1 << eid
        assert full_table.legal(current)
    assert out_vector(n, orient(edges, current))[x] == k + 1
    current ^= 1 << (m + g)
    assert full_table.legal(current)
    return dict(initial_internal_mask=hm, decrease_outer_eid=g, donor=u,
                branch=branch, guard_count=len(mixed_guards[u]),
                distinct_guard_traces=len({t for s, t in mixed_guards[u]}),
                guard_trace_intersection=allowed, path_vertices=vertices,
                physical_word=word + [m + g], final_full_mask=current)


def finite_controls():
    screen = json.loads((ROOT / 'root_entry_screen.json').read_text(encoding='utf-8'))
    answer = [dict(name=f'archived_mixed_{i + 1}', k=e['k'], c=e['c'],
                   h=e['h'], outer=e['outer'], sigma=e['sigma'])
              for i, e in enumerate(screen['examples'])]
    kernels = [
        (2, 3, [(0, 1)] * 2 + [(1, 2)] * 2 + [(0, 2)]),
        (2, 4, list(combinations(range(4), 2)) + [(0, 1)]),
        (2, 4, [(i, (i + 1) % 4) for i in range(4) for _ in range(2)]),
        (3, 4, [(u, v) for u, v in combinations(range(4), 2)
                for _ in range(2 if (u, v) != (2, 3) else 1)]),
        (2, 7, [(u, v) for u in range(3) for v in range(3, 7)] + [(3, 4)]),
        (2, 8, [(u, v) for u in range(4) for v in range(4, 8)
                if (u, v) != (0, 4)]),
    ]
    for i, (k, c, h) in enumerate(kernels):
        ports = [(v, c) for v in range(c)
                 for _ in range(max(1, 2 * k + 1 - sum(v in e for e in h)))]
        while len(ports) < 2 * k + 1:
            ports.append((0, c))
        outgoing = set(range(k + 1))
        sigma = sum(1 << eid for eid in range(len(ports)) if eid not in outgoing)
        answer.append(dict(name=f'single_outside_{i + 1}', k=k, c=c,
                           h=h, outer=ports, sigma=sigma))
    answer.append(dict(name='nested_distinct_mixed_guards', k=2, c=4,
                       h=[(0, 1)] * 2 + [(0, 2)] * 2 + [(0, 3), (1, 3), (2, 3)],
                       outer=[(1, 4)] * 3 + [(2, 5)] * 2 + [(3, 6)] * 2
                       + [(0, 4)] + [(5, 4)] * 2 + [(5, 6)] * 3,
                       sigma=6358, expected_internal_mask=50,
                       expected_decrease_outer_eid=0))
    answer.extend(no_shadow_control(k) for k in (2, 3, 4))
    return answer


def no_shadow_control(k):
    c, count = 3, k + 1
    z = c + count
    h = [(0, 1)] * k + [(1, 2)] * k + [(2, 0)] * k
    ports = [(i % c, c + i) for i in range(count)]
    ports += [(j % c, z) for j in range(k + 2)]
    inside = [(c + i, c + j) for i in range(count) for j in range(count)
              if i != j and j != (i + 1) % count]
    toward_z = [(c + i, z) for i in range(count) for _ in range(2)]
    outer = ports + inside + toward_z
    original = sum(1 << i for i in range(count, len(ports)))
    unlock = len(ports) + len(inside)
    return dict(name=f'no_shadow_unlock_k{k}', k=k, c=c, h=h, outer=outer,
                sigma=original ^ (1 << unlock), original_no_shadow_sigma=original,
                exterior_unlock_outer_eid=unlock, specified_root_decrease_outer_eid=0)


def anchor_bridge(c, h, outer, sigma, start, target, degrees, k):
    fixed = out_vector(len(degrees), orient(outer, sigma))
    parent, todo = {start: None}, deque([start])
    while todo:
        hm = todo.popleft()
        if hm == target:
            word = []
            while parent[hm] is not None:
                prev, eid = parent[hm]
                word.append(eid)
                hm = prev
            return list(reversed(word))
        for eid in range(len(h)):
            nxt = hm ^ (1 << eid)
            if nxt in parent:
                continue
            internal = out_vector(c, orient(h, nxt))
            if all(k <= fixed[v] + internal[v] <= degrees[v] - k for v in range(c)):
                parent[nxt] = (hm, eid)
                todo.append(nxt)
    raise AssertionError('root-k physical preparation failed')


def exact_service_words(control, entries, ft):
    k, c, h, outer, sigma = (control[key] for key in ('k', 'c', 'h', 'outer', 'sigma'))
    m = len(h)
    g = entries[0]['decrease_outer_eid']
    same = [w for w in entries if w['decrease_outer_eid'] == g]
    source, target = same[0], same[-1]
    lower_sigma = sigma ^ (1 << g)
    first_hm = source['final_full_mask'] & ((1 << m) - 1)
    last_hm = target['final_full_mask'] & ((1 << m) - 1)
    bridge = anchor_bridge(c, h, outer, lower_sigma, first_hm, last_hm, ft.deg, k)
    p = (c + 1) * m
    assert len(bridge) <= p
    down = source['physical_word'] + bridge
    closed = down + [m + g] + list(reversed(target['physical_word'][:-1]))
    high_source = source['initial_internal_mask'] | sigma << m
    low_target = last_hm | lower_sigma << m
    high_target = target['initial_internal_mask'] | sigma << m
    specifications = [
        ('exact_down_to_specified_anchor_phase', high_source, low_target, down, [m + g], p + c),
        ('exact_up_to_unpaid_specified_phase', low_target, high_source, list(reversed(down)), [m + g], p + c),
        ('two_port_flips_exact_unpaid_phase_return', high_source, high_target, closed, [m + g] * 2, p + 2 * c),
    ]
    result = []
    for label, initial, final, word, outside_word, bound in specifications:
        assert len(word) <= bound
        assert [eid for eid in word if eid >= m] == outside_word
        state = initial
        assert ft.legal(state)
        for eid in word:
            state ^= 1 << eid
            assert ft.legal(state)
        assert state == final
        result.append(dict(label=label, initial_full_mask=initial, final_full_mask=final,
                           physical_word=word, expected_nonH_word=outside_word,
                           length_bound=bound))
    return result


def no_shadow_exits(control, entries, ft, qt):
    k, c, h, outer, sigma = (control[key] for key in ('k', 'c', 'h', 'outer', 'sigma'))
    original, unlock, g = (control[key] for key in (
        'original_no_shadow_sigma', 'exterior_unlock_outer_eid', 'specified_root_decrease_outer_eid'))
    m = len(h)
    assert original ^ (1 << unlock) == sigma
    assert qt.legal(original) and qt.legal(sigma ^ (1 << g))
    assert all(not qt.legal(original ^ (1 << i)) for i, (u, v) in enumerate(qt.edges)
               if u == 0 and not (original >> i & 1))
    lookup = {(w['initial_internal_mask'], w['decrease_outer_eid']): w for w in entries}
    result = []
    for hm in range(1 << m):
        initial = hm | original << m
        out = out_vector(ft.n, orient(ft.edges, initial))
        if not all(k <= out[v] <= ft.deg[v] - k for v in range(ft.n)) or not ft.legal(initial):
            continue
        after_unlock = initial ^ (1 << (m + unlock))
        assert ft.legal(after_unlock)
        entry = lookup.get((hm, g))
        if entry:
            assert out[outer[g][0]] == k
            service = entry['physical_word']
        else:
            assert out[outer[g][0]] >= k + 1
            service = [m + g]
        word = [m + unlock] + service
        assert len(word) <= c + 1
        current = initial
        for eid in word:
            current ^= 1 << eid
            assert ft.legal(current)
        result.append(dict(initial_internal_mask=hm, initial_full_mask=initial,
                           physical_word=word, final_full_mask=current,
                           internal_preparation_required=entry is not None))
    assert result and any(w['internal_preparation_required'] for w in result)
    return result


def enumerate_control(control):
    k, c, h, outer, sigma = (control[key] for key in ('k', 'c', 'h', 'outer', 'sigma'))
    edges, m = h + outer, len(h)
    n = 1 + max(max(e) for e in edges)
    q = m - k * (c - 1)
    ht, ft = CutTable(c, h, k), CutTable(n, edges, k)
    assert q >= 1
    assert all(ht.inside[s] <= k * (s.bit_count() - 1)
               for s in range(1, (1 << c) - 1))
    minimum = ft.undirected_minimum()
    assert minimum >= 2 * k + 1
    qedges = [(0 if u < c else u - c + 1, 0 if v < c else v - c + 1)
              for u, v in outer]
    qt = CutTable(n - c + 1, qedges, k)
    assert qt.legal(sigma)
    assert out_vector(qt.n, orient(qedges, sigma))[0] == k + 1
    decreases = [eid for eid, (u, v) in enumerate(qedges)
                 if u == 0 and not (sigma >> eid & 1) and qt.legal(sigma ^ (1 << eid))]
    assert decreases
    stats, words, legal_masks = Counter(), [], []
    for hm in range(1 << m):
        mask = hm | sigma << m
        out = out_vector(n, orient(edges, mask))
        if not all(k <= out[v] <= ft.deg[v] - k for v in range(n)):
            continue
        stats['vertex_legal_internal_masks'] += 1
        if not ft.legal(mask):
            stats['rejected_internal_masks'] += 1
            continue
        legal_masks.append(hm)
        stats['legal_internal_masks'] += 1
        for g in decreases:
            stats['state_decrease_pairs'] += 1
            if out[outer[g][0]] >= k + 1:
                assert ft.legal(mask ^ (1 << (m + g)))
                stats['already_ready_pairs'] += 1
                continue
            word = prepare(control, hm, g, ft)
            words.append(word)
            stats['unpaid_entry_words'] += 1
            stats['physical_flips_in_saved_words'] += len(word['physical_word'])
            stats[word['branch']] += 1
            if word['guard_count'] >= 2:
                stats['multiple_guard_words'] += 1
            if word['distinct_guard_traces'] >= 2:
                stats['distinct_multiple_guard_trace_words'] += 1
            stats['maximum_internal_path_length'] = max(
                stats['maximum_internal_path_length'], len(word['physical_word']) - 1)
    assert legal_masks
    if 'expected_internal_mask' in control:
        expected = next(w for w in words
                        if w['initial_internal_mask'] == control['expected_internal_mask']
                        and w['decrease_outer_eid'] == control['expected_decrease_outer_eid'])
        assert expected['distinct_guard_traces'] >= 2
    services = exact_service_words(control, words, ft)
    stats['exact_service_words'] = len(services)
    stats['exact_service_physical_flips'] = sum(len(w['physical_word']) for w in services)
    exits = []
    if 'original_no_shadow_sigma' in control:
        exits = no_shadow_exits(control, words, ft, qt)
        stats['no_shadow_source_legal_masks'] = len(exits)
        stats['no_shadow_unpaid_after_unlock'] = sum(w['internal_preparation_required'] for w in exits)
        stats['no_shadow_exit_flips'] = sum(len(w['physical_word']) for w in exits)
    stats['distinct_full_degree_vectors_checked'] = len(ft.rows_cache)
    stats['full_cut_rows_via_degree_vectors'] = ft.checks
    result = dict(control, n=n, m=m, q=q, edges=edges, minimum_cut=minimum,
                  legal_decreases=decreases, stats=dict(stats), words=words,
                  exact_service_words=services,
                  no_shadow_exit_words=exits,
                  legal_internal_masks_sha256=hashlib.sha256(
                      json.dumps(legal_masks, separators=(',', ':')).encode()).hexdigest())
    print(json.dumps({'control': control['name'], 'stats': dict(stats)}), flush=True)
    return result


def flow_at_least(n, arcs, source, sink, required):
    cap = [[0] * n for _ in range(n)]
    for u, v in arcs:
        cap[u][v] += 1
    sent = 0
    while sent < required:
        prev = [-1] * n
        prev[source] = source
        todo = deque([source])
        while todo and prev[sink] < 0:
            u = todo.popleft()
            for v in range(n):
                if cap[u][v] and prev[v] < 0:
                    prev[v] = u
                    todo.append(v)
        if prev[sink] < 0:
            return False
        add, v = required - sent, sink
        while v != source:
            add = min(add, cap[prev[v]][v])
            v = prev[v]
        v = sink
        while v != source:
            u = prev[v]
            cap[u][v] -= add
            cap[v][u] += add
            v = u
        sent += add
    return True


def full_flow_legal(n, arcs, k, stats):
    for v in range(1, n):
        for s, t in ((0, v), (v, 0)):
            stats['directed_root_flow_checks'] += 1
            assert flow_at_least(n, arcs, s, t, k)


def long_control(k, c, shortcut):
    a, b = c, c + 1
    h = [(i, i + 1) for i in range(c - 1) for _ in range(k)] + [(0, c - 1)]
    ports = [(0, b)] * k + [(c - 1, a)] * k + [(1, b), (1, a)]
    ports += [(i, a) for i in range(2, c - 1)]
    exterior = [(a, b)] * (2 * k + 1)
    outer = ports + exterior
    m, n = len(h), c + 2
    hm = 1 if shortcut else 0
    outgoing = set(range(k, 2 * k)) | ({0} if shortcut else {2 * k})
    sigma = sum(1 << i for i in range(len(ports)) if i not in outgoing)
    sigma |= sum(1 << i for i in range(len(ports) + k - 1, len(outer)))
    mask = hm | sigma << m
    word = [i * k for i in range(1, c - 1)] + [m + k]
    edges, stats = h + outer, Counter()
    arcs = orient(edges, mask)
    deg = [sum(v in e for e in edges) for v in range(n)]
    assert all(out_vector(n, arcs)[v] == k + (v in (0, 1)) for v in range(c))
    for v in range(1, n):
        stats['undirected_root_flow_checks'] += 1
        assert flow_at_least(n, edges + [(v, u) for u, v in edges], 0, v, 2 * k + 1)
    states = [mask]
    for eid in word:
        mask ^= 1 << eid
        states.append(mask)
    for state in states:
        full_flow_legal(n, orient(edges, state), k, stats)
    guard = ((1 << c) - 1) ^ 1 | (1 << a)
    initial_arcs = orient(edges, states[0])
    assert sum(bool(guard >> u & 1) and not (guard >> v & 1)
               for u, v in initial_arcs) == k
    unsafe = None
    if shortcut:
        unsafe_mask = states[0] ^ 1
        assert orient(edges, states[0])[0] == (1, 0)
        assert sum(bool(guard >> u & 1) and not (guard >> v & 1)
                   for u, v in orient(edges, unsafe_mask)) == k - 1
        unsafe = dict(physical_eid=0, blocking_shore=guard, cut_before=k, cut_after=k - 1)
    return dict(name=f'long_guard_k{k}_n{c}_shortcut{int(shortcut)}',
                k=k, c=c, n=n, m=m, q=1, h=h, outer=outer, edges=edges,
                sigma=sigma, initial_internal_mask=hm, initial_full_mask=states[0],
                specified_decrease_outer_eid=k, path_vertices=list(range(1, c)),
                physical_word=word, final_full_mask=states[-1],
                blocking_shore=guard, unsafe_shortcut=unsafe,
                mu=[deg[v] - 2 * k for v in range(c)], stats=dict(stats))


def large_no_shadow_control(k):
    control = no_shadow_control(k)
    h, outer = control['h'], control['outer']
    edges, m, n = h + outer, len(h), k + 5
    initial = control['original_no_shadow_sigma'] << m
    unlock, g = control['exterior_unlock_outer_eid'], control['specified_root_decrease_outer_eid']
    word = [m + unlock, m + g]
    stats = Counter()
    for v in range(1, n):
        assert flow_at_least(n, edges + [(b, a) for a, b in edges], 0, v, 2 * k + 1)
        stats['undirected_root_flow_checks'] += 1
    current = initial
    full_flow_legal(n, orient(edges, current), k, stats)
    for eid in word:
        current ^= 1 << eid
        full_flow_legal(n, orient(edges, current), k, stats)
    initial_arcs = orient(edges, initial)
    for v in range(3, 3 + k + 1):
        assert sum(b == v for a, b in initial_arcs) == k
    return dict(control, n=n, m=m, edges=edges, initial_full_mask=initial,
                physical_word=word, final_full_mask=current, stats=dict(stats))


def run():
    finite = [enumerate_control(c) for c in finite_controls()]
    large = []
    for k, n in [(2, 5), (3, 8), (7, 12), (20, 20), (50, 32)]:
        for shortcut in (False, True):
            item = long_control(k, n, shortcut)
            large.append(item)
            print(json.dumps({'control': item['name'], 'stats': item['stats']}), flush=True)
    no_shadow_large = [large_no_shadow_control(k) for k in (7, 20, 50)]
    counts = Counter()
    maximum = 0
    for item in finite:
        for key, value in item['stats'].items():
            if key.startswith('maximum_'):
                maximum = max(maximum, value)
            else:
                counts[key] += value
    counts['finite_controls'] = len(finite)
    counts['long_guard_controls'] = len(large)
    counts['large_no_shadow_controls'] = len(no_shadow_large)
    counts['maximum_enumerated_internal_path_length'] = maximum
    counts['maximum_long_control_internal_path_length'] = max(len(e['physical_word']) - 1 for e in large)
    result = dict(status='PASS', theorem='H2 arbitrary-source prescribed root decrease entry',
                  finite_scope='All internal physical masks and all legal root decreases on each saved boundary signature',
                  program_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
                  source_screen_sha256=hashlib.sha256((ROOT / 'root_entry_screen.json').read_bytes()).hexdigest(),
                  stats=dict(counts), finite_controls=finite, long_guard_controls=large,
                  large_no_shadow_controls=no_shadow_large)
    output = ROOT / 'root_entry_H2_certificate.json'
    output.write_text(json.dumps(result, ensure_ascii=False, indent=2), encoding='utf-8')
    print(json.dumps({'status': 'PASS', 'stats': dict(counts), 'output': output.name}), flush=True)


if __name__ == '__main__':
    run()
