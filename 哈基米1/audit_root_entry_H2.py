"""Independent audit of saved H2 physical inputs and words.

No primary constructor or path algorithm is imported. Finite legality is
re-enumerated; saved prefixes are counted by literal directed-cut crossings.
Large controls use a separate Dinic implementation for all directed cuts.
"""
from collections import Counter, deque
from pathlib import Path
import hashlib
import json

ROOT = Path(__file__).resolve().parent
TOTAL = Counter()


def directed_edges(edges, bits):
    result = []
    for index, edge in enumerate(edges):
        result.append(tuple(reversed(edge)) if (bits & (1 << index)) else tuple(edge))
    return result


def degrees(n, edges):
    row = [0] * n
    for u, v in edges:
        row[u] += 1
        row[v] += 1
    return row


def outgoing(n, edges, bits):
    row = [0] * n
    for tail, head in directed_edges(edges, bits):
        row[tail] += 1
    return row


class LiteralAudit:
    def __init__(self, n, edges, k):
        self.n, self.edges, self.k = n, edges, k
        self.cache = {}

    def inspect(self, bits):
        TOTAL['actual_prefix_state_visits'] += 1
        if bits not in self.cache:
            arcs = directed_edges(self.edges, bits)
            least, tight = len(arcs), []
            for s in range(1, (1 << self.n) - 1):
                amount = 0
                for tail, head in arcs:
                    if (s & (1 << tail)) and not (s & (1 << head)):
                        amount += 1
                least = min(least, amount)
                if amount == self.k:
                    tight.append(s)
            TOTAL['unique_actual_masks_literal_checked'] += 1
            TOTAL['literal_complete_directed_cut_rows'] += (1 << self.n) - 2
            self.cache[bits] = least, tight
        least, tight = self.cache[bits]
        assert least >= self.k, ('bad saved actual state', bits, least)
        return tight


def literal_qlegal(n, qedges, mask, k):
    arcs = directed_edges(qedges, mask)
    return all(sum(bool(s & (1 << u)) and not (s & (1 << v)) for u, v in arcs) >= k
               for s in range(1, (1 << n) - 1))


def audit_finite(item):
    k, c, n, m = (item[x] for x in ('k', 'c', 'n', 'm'))
    h, outer, edges, sigma = (item[x] for x in ('h', 'outer', 'edges', 'sigma'))
    assert edges == h + outer and len(h) == m
    assert m - k * (c - 1) == item['q'] >= 1
    whole_core, whole = (1 << c) - 1, (1 << n) - 1
    outside = whole ^ whole_core
    deg = degrees(n, edges)
    mu = [deg[v] - 2 * k for v in range(c)]
    assert min(mu) >= 1
    for s in range(1, whole_core):
        induced = sum(bool(s & (1 << u)) and bool(s & (1 << v)) for u, v in h)
        assert induced <= k * (s.bit_count() - 1)
        TOTAL['SD_subset_checks'] += 1
    minimum = min(sum(bool(s & (1 << u)) != bool(s & (1 << v)) for u, v in edges)
                  for s in range(1, whole))
    assert minimum == item['minimum_cut'] >= 2 * k + 1
    TOTAL['literal_undirected_cut_rows'] += whole - 1
    qedges = [[0 if u < c else u - c + 1, 0 if v < c else v - c + 1]
              for u, v in outer]
    qn = n - c + 1
    assert literal_qlegal(qn, qedges, sigma, k)
    assert outgoing(qn, qedges, sigma)[0] == k + 1
    decreases = [i for i, (u, v) in enumerate(directed_edges(qedges, sigma))
                 if u == 0 and literal_qlegal(qn, qedges, sigma ^ (1 << i), k)]
    assert decreases == item['legal_decreases']
    # Independent complete-profile enumeration, with induced counts constructed
    # directly from raw physical edges rather than the primary recurrence.
    induced = [sum(bool(s & (1 << u)) and bool(s & (1 << v)) for u, v in edges)
               for s in range(1, whole)]
    vertex_profiles = {}
    legal_masks, unpaid, ready, rejected = [], set(), [], 0
    for hm in range(1 << m):
        full = hm | (sigma << m)
        out = tuple(outgoing(n, edges, full))
        if any(out[v] < k or out[v] > deg[v] - k for v in range(n)):
            continue
        if out not in vertex_profiles:
            legal = True
            for s, inside in enumerate(induced, 1):
                value = sum(out[v] for v in range(n) if s & (1 << v)) - inside
                if value < k:
                    legal = False
            vertex_profiles[out] = legal
            TOTAL['independent_degree_profile_cut_rows'] += len(induced)
        if not vertex_profiles[out]:
            rejected += 1
            continue
        legal_masks.append(hm)
        for g in decreases:
            if out[outer[g][0]] == k:
                unpaid.add((hm, g))
            else:
                ready.append((hm, g))
    assert len(legal_masks) == item['stats']['legal_internal_masks']
    assert rejected == item['stats'].get('rejected_internal_masks', 0)
    digest = hashlib.sha256(json.dumps(legal_masks, separators=(',', ':')).encode()).hexdigest()
    assert digest == item['legal_internal_masks_sha256']
    saved = {(w['initial_internal_mask'], w['decrease_outer_eid']): w for w in item['words']}
    assert len(saved) == len(item['words']) and set(saved) == unpaid
    literal = LiteralAudit(n, edges, k)
    # Covers even pairs needing no preparation, by actual port reversal.
    for hm, g in ready:
        initial = hm | sigma << m
        literal.inspect(initial)
        literal.inspect(initial ^ (1 << (m + g)))
    for key, word in saved.items():
        hm, g = key
        initial = hm | sigma << m
        out = outgoing(n, edges, initial)
        a = [out[v] - k for v in range(c)]
        x = outer[g][0]
        vertices, physical = word['path_vertices'], word['physical_word']
        u = vertices[0]
        assert word['donor'] == u and a[u] > 0 and a[x] == 0
        assert vertices[-1] == x and len(vertices) == len(set(vertices))
        assert all(a[v] == 0 for v in vertices[1:])
        assert len(physical) == len(vertices) and len(physical) <= c
        assert physical[-1] == m + g
        assert all(0 <= eid < m for eid in physical[:-1])
        arcs = directed_edges(edges, initial)
        for index, eid in enumerate(physical[:-1]):
            assert arcs[eid] == (vertices[index], vertices[index + 1])
        tight = literal.inspect(initial)
        guards = [s for s in tight if s & (1 << u)
                  and (s & whole_core) not in (0, whole_core)
                  and (s & outside) not in (0, outside)]
        traces = {s & whole_core for s in guards}
        assert len(guards) == word['guard_count']
        assert len(traces) == word['distinct_guard_traces']
        if guards:
            intersection = whole_core
            for trace in traces:
                assert trace & (1 << x) and trace & (1 << u)
                assert sum(a[v] for v in range(c) if trace & (1 << v)) == 1
                assert sum(bool(trace & (1 << p)) and bool(trace & (1 << q))
                           for p, q in h) == k * (trace.bit_count() - 1)
                intersection &= trace
            assert intersection == word['guard_trace_intersection']
            assert all(intersection & (1 << v) for v in vertices)
            TOTAL['guarded_entry_words'] += 1
            if len(traces) >= 2:
                TOTAL['distinct_multiple_guard_trace_words'] += 1
        else:
            assert word['guard_trace_intersection'] == whole_core
            TOTAL['unguarded_entry_words'] += 1
        bits = initial
        for index, eid in enumerate(physical):
            bits ^= 1 << eid
            literal.inspect(bits)
            if index < len(physical) - 1:
                front = vertices[index + 1]
                delta = [int(v == front) - int(v == u) for v in range(n)]
                assert outgoing(n, edges, bits) == [out[v] + delta[v] for v in range(n)]
        assert bits == word['final_full_mask']
        assert outgoing(qn, qedges, bits >> m)[0] == k
        TOTAL['unpaid_entry_words'] += 1
        TOTAL['entry_word_physical_flips'] += len(physical)
    for service in item['exact_service_words']:
        bits = service['initial_full_mask']
        physical = service['physical_word']
        assert len(physical) <= service['length_bound']
        assert [eid for eid in physical if eid >= m] == service['expected_nonH_word']
        literal.inspect(bits)
        for eid in physical:
            assert 0 <= eid < len(edges)
            bits ^= 1 << eid
            literal.inspect(bits)
        assert bits == service['final_full_mask']
        TOTAL['exact_service_words'] += 1
        TOTAL['exact_service_flips'] += len(physical)
    if 'original_no_shadow_sigma' in item:
        original = item['original_no_shadow_sigma']
        unlock, g = item['exterior_unlock_outer_eid'], item['specified_root_decrease_outer_eid']
        assert original ^ (1 << unlock) == sigma
        assert literal_qlegal(qn, qedges, original, k)
        assert literal_qlegal(qn, qedges, sigma ^ (1 << g), k)
        assert all(not literal_qlegal(qn, qedges, original ^ (1 << eid), k)
                   for eid, (tail, head) in enumerate(directed_edges(qedges, original)) if tail == 0)
        sources = []
        for hm in range(1 << m):
            bits = hm | original << m
            out = tuple(outgoing(n, edges, bits))
            if any(out[v] < k or out[v] > deg[v] - k for v in range(n)):
                continue
            if out not in vertex_profiles:
                vertex_profiles[out] = all(
                    sum(out[v] for v in range(n) if s & (1 << v)) - inside >= k
                    for s, inside in enumerate(induced, 1))
                TOTAL['independent_degree_profile_cut_rows'] += len(induced)
            if vertex_profiles[out]:
                sources.append(hm)
        exits = {w['initial_internal_mask']: w for w in item['no_shadow_exit_words']}
        assert len(exits) == len(item['no_shadow_exit_words']) and set(exits) == set(sources)
        for hm in sources:
            exit_word = exits[hm]
            bits = hm | original << m
            assert bits == exit_word['initial_full_mask']
            physical = exit_word['physical_word']
            assert [eid for eid in physical if eid >= m] == [m + unlock, m + g]
            assert len(physical) <= c + 1
            unpaid_x = outgoing(n, edges, bits)[outer[g][0]] == k
            assert unpaid_x == exit_word['internal_preparation_required']
            if unpaid_x:
                assert physical[1:] == saved[(hm, g)]['physical_word']
                TOTAL['no_shadow_unpaid_after_unlock'] += 1
            else:
                assert physical == [m + unlock, m + g]
            literal.inspect(bits)
            for eid in physical:
                bits ^= 1 << eid
                literal.inspect(bits)
            assert bits == exit_word['final_full_mask']
            assert outgoing(qn, qedges, bits >> m)[0] == k
            TOTAL['no_shadow_exit_flips'] += len(physical)
        TOTAL['no_shadow_source_legal_masks'] += len(sources)
    # One physical dual witness per control: reversing the entire orientation
    # swaps root out/in and gives the stated incoming-port counterpart.
    dual = item['words'][0]
    bits = ((1 << len(edges)) - 1) ^ (dual['initial_internal_mask'] | sigma << m)
    literal.inspect(bits)
    for eid in dual['physical_word']:
        bits ^= 1 << eid
        literal.inspect(bits)
    TOTAL['dual_actual_words'] += 1
    TOTAL['legal_internal_masks'] += len(legal_masks)
    TOTAL['state_decrease_pairs'] += len(legal_masks) * len(decreases)
    TOTAL['already_ready_pairs'] += len(ready)
    print(json.dumps({'control': item['name'], 'unpaid_words': len(unpaid),
                      'literal_unique_masks': len(literal.cache)}), flush=True)


def dinic_reaches(n, arcs, source, sink, threshold):
    adjacency = [[] for _ in range(n)]
    for u, v in arcs:
        adjacency[u].append([v, 1, len(adjacency[v])])
        adjacency[v].append([u, 0, len(adjacency[u]) - 1])
    result = 0
    while result < threshold:
        level = [-1] * n
        level[source] = 0
        todo = deque([source])
        while todo:
            u = todo.popleft()
            for v, cap, back in adjacency[u]:
                if cap and level[v] < 0:
                    level[v] = level[u] + 1
                    todo.append(v)
        if level[sink] < 0:
            return False
        index = [0] * n
        def push(u, budget):
            if u == sink:
                return budget
            while index[u] < len(adjacency[u]):
                edge = adjacency[u][index[u]]
                v, cap, back = edge
                if cap and level[v] == level[u] + 1:
                    sent = push(v, min(budget, cap))
                    if sent:
                        edge[1] -= sent
                        adjacency[v][back][1] += sent
                        return sent
                index[u] += 1
            return 0
        while result < threshold:
            sent = push(source, threshold - result)
            if not sent:
                break
            result += sent
    return True


def audit_long(item):
    k, c, n, m = (item[x] for x in ('k', 'c', 'n', 'm'))
    h, outer, edges = (item[x] for x in ('h', 'outer', 'edges'))
    assert edges == h + outer and n == c + 2 and len(h) == m == k * (c - 1) + 1
    assert h == [[i, i + 1] for i in range(c - 1) for _ in range(k)] + [[0, c - 1]]
    # This raw shape proves SD without exponential enumeration: a proper
    # subset containing both path ends has at least two path components.
    deg = degrees(n, edges)
    assert [deg[v] - 2 * k for v in range(c)] == item['mu']
    assert item['mu'] == [2 if v == 1 else 1 for v in range(c)]
    arcs = edges + [list(reversed(e)) for e in edges]
    for v in range(1, n):
        assert dinic_reaches(n, arcs, 0, v, 2 * k + 1)
        TOTAL['independent_undirected_root_flow_checks'] += 1
    bits = item['initial_full_mask']
    assert bits == item['initial_internal_mask'] | item['sigma'] << m
    guard = item['blocking_shore']
    assert sum(bool(guard & (1 << u)) and not (guard & (1 << v))
               for u, v in directed_edges(edges, bits)) == k
    word = item['physical_word']
    assert word == [i * k for i in range(1, c - 1)] + [m + k]
    assert item['path_vertices'] == list(range(1, c))
    assert len(word) == c - 1
    states = [bits]
    for eid in word:
        bits ^= 1 << eid
        states.append(bits)
    assert bits == item['final_full_mask']
    for state in states:
        oriented = directed_edges(edges, state)
        for v in range(1, n):
            assert dinic_reaches(n, oriented, 0, v, k)
            assert dinic_reaches(n, oriented, v, 0, k)
            TOTAL['independent_directed_root_flow_checks'] += 2
    if item['unsafe_shortcut']:
        rejected = item['initial_full_mask'] ^ (1 << item['unsafe_shortcut']['physical_eid'])
        amount = sum(bool(guard & (1 << u)) and not (guard & (1 << v))
                     for u, v in directed_edges(edges, rejected))
        assert amount == k - 1 == item['unsafe_shortcut']['cut_after']
        assert directed_edges(edges, item['initial_full_mask'])[0] == (1, 0)
        TOTAL['blocked_naive_shortcuts'] += 1
    TOTAL['long_guard_words'] += 1
    TOTAL['long_guard_physical_flips'] += len(word)
    print(json.dumps({'control': item['name'], 'full_prefixes_by_flow': len(states)}), flush=True)


def audit_large_no_shadow(item):
    k, c, n, m = (item[x] for x in ('k', 'c', 'n', 'm'))
    edges, h, outer = (item[x] for x in ('edges', 'h', 'outer'))
    assert c == 3 and n == k + 5 and m == 3 * k
    assert h == [[0, 1]] * k + [[1, 2]] * k + [[2, 0]] * k and edges == h + outer
    original = item['original_no_shadow_sigma']
    unlock, g = item['exterior_unlock_outer_eid'], item['specified_root_decrease_outer_eid']
    bits = item['initial_full_mask']
    assert bits == original << m
    assert item['physical_word'] == [m + unlock, m + g]
    out = outgoing(n, edges, bits)
    # Every receiving exterior vertex is actually in-k tight, independently
    # blocking every outgoing physical root port in the original commercial state.
    deg = degrees(n, edges)
    for v in range(c, c + k + 1):
        assert deg[v] - out[v] == k
    assert sum(1 for u, v in directed_edges(outer, original) if u < c) == k + 1
    for v in range(1, n):
        assert dinic_reaches(n, edges + [list(reversed(e)) for e in edges], 0, v, 2 * k + 1)
        TOTAL['independent_undirected_root_flow_checks'] += 1
    states = [bits]
    for eid in item['physical_word']:
        bits ^= 1 << eid
        states.append(bits)
    assert bits == item['final_full_mask']
    for state in states:
        arcs = directed_edges(edges, state)
        for v in range(1, n):
            assert dinic_reaches(n, arcs, 0, v, k)
            assert dinic_reaches(n, arcs, v, 0, k)
            TOTAL['independent_directed_root_flow_checks'] += 2
    TOTAL['large_no_shadow_controls'] += 1
    TOTAL['large_no_shadow_actual_flips'] += 2
    print(json.dumps({'control': item['name'], 'no_shadow_flow_prefixes': 3}), flush=True)


def run():
    certificate_path = ROOT / 'root_entry_H2_certificate.json'
    certificate = json.loads(certificate_path.read_text(encoding='utf-8'))
    assert certificate['status'] == 'PASS'
    primary = ROOT / 'verify_root_entry_H2.py'
    assert hashlib.sha256(primary.read_bytes()).hexdigest() == certificate['program_sha256']
    for item in certificate['finite_controls']:
        audit_finite(item)
    for item in certificate['long_guard_controls']:
        audit_long(item)
    for item in certificate['large_no_shadow_controls']:
        audit_large_no_shadow(item)
    for key in ('legal_internal_masks', 'state_decrease_pairs', 'unpaid_entry_words',
                'already_ready_pairs', 'exact_service_words', 'distinct_multiple_guard_trace_words',
                'no_shadow_source_legal_masks', 'no_shadow_unpaid_after_unlock',
                'no_shadow_exit_flips', 'large_no_shadow_controls'):
        assert TOTAL[key] == certificate['stats'][key]
    assert TOTAL['entry_word_physical_flips'] == certificate['stats']['physical_flips_in_saved_words']
    assert TOTAL['exact_service_flips'] == certificate['stats']['exact_service_physical_flips']
    result = dict(status='PASS', independence='Raw certificate only; no primary imports or constructors',
                  scope='Re-enumerate finite internal states, literal physical-prefix cuts with actual-mask cache; independent Dinic on large controls',
                  stats=dict(TOTAL), certificate_sha256=hashlib.sha256(certificate_path.read_bytes()).hexdigest(),
                  primary_program_sha256=hashlib.sha256(primary.read_bytes()).hexdigest(),
                  auditor_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest())
    (ROOT / 'root_entry_H2_independent_audit.json').write_text(
        json.dumps(result, ensure_ascii=False, indent=2), encoding='utf-8')
    print(json.dumps(result), flush=True)


if __name__ == '__main__':
    run()
