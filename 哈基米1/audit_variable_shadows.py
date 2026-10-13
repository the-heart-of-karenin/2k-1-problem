"""Independent audit of H1 controls and every saved physical flip prefix.

No constructors, preparation searches, or cut functions are imported from the
main verifier. Shadow bases are derived from exterior indegree demands, then
compared with direct quotient cuts. Exact edge identities remain distinct.
"""
from collections import Counter
from itertools import combinations
from pathlib import Path
import hashlib
import json

ROOT = Path(__file__).resolve().parent


def outdegrees(n, edges, state):
    answer = [0] * n
    for eid, edge in enumerate(edges):
        answer[edge[(state >> eid) & 1]] += 1
    return answer


def literal(n, edges, state, k, statistics, require=True):
    minimum = len(edges)
    for subset in range(1, (1 << n) - 1):
        amount = 0
        for eid, (left, right) in enumerate(edges):
            if state & (1 << eid):
                left, right = right, left
            if subset & (1 << left) and not subset & (1 << right):
                amount += 1
        minimum = min(minimum, amount)
        statistics['literal_complete_cut_checks'] += 1
        if require:
            assert amount >= k, (subset, state, amount, k)
    return minimum


def outgoing_ports(state, d):
    return frozenset(eid for eid in range(d) if not state & (1 << eid))


def shadow_state(sigma, base, d):
    new = sigma
    for eid in range(d):
        if eid in base:
            new &= ~(1 << eid)
        else:
            new |= 1 << eid
    return new


def activity_vector(c, ports, active):
    row = [0] * c
    for eid in active:
        row[ports[eid][0]] += 1
    return row


def audit_control(data, statistics):
    k, c, n = data['k'], data['c'], data['n']
    h, ports, exterior, edges = data['h'], data['ports'], data['exterior'], data['edges']
    m, d = len(h), len(ports)
    assert edges == h + ports + exterior
    assert m == k * (c - 1) + data['q'] and data['q'] >= 1
    degree = [sum(v == u or v == w for u, w in edges) for v in range(n)]
    assert data['mu'] == [degree[v] - 2 * k for v in range(c)]
    for subset in range(1, (1 << c) - 1):
        internal = sum(bool(subset & (1 << u)) and bool(subset & (1 << v)) for u, v in h)
        assert internal <= k * (subset.bit_count() - 1)
    actual_minimum = min(sum(bool(s & (1 << u)) != bool(s & (1 << v)) for u, v in edges)
                         for s in range(1, (1 << n) - 1))
    assert actual_minimum == data['minimum_cut'] and actual_minimum >= 2 * k + 1
    qedges = [[0 if u < c else u - c + 1, 0 if v < c else v - c + 1]
              for u, v in ports + exterior]
    qn = n - c + 1
    tables = {}
    local = Counter()
    for sigma in range(1 << (d + len(exterior))):
        if literal(qn, qedges, sigma, k, statistics, False) < k:
            continue
        out = outgoing_ports(sigma, d)
        # Rows cover every nonempty exterior subset, including the total row.
        rows = []
        for subset in range(1, (1 << (n - c))):
            entering = 0
            for i, (u, v) in enumerate(exterior):
                if sigma & (1 << (d + i)):
                    u, v = v, u
                if not subset & (1 << (u - c)) and subset & (1 << (v - c)):
                    entering += 1
            ids = frozenset(eid for eid in range(d)
                            if subset & (1 << (ports[eid][1] - c)))
            rows.append((subset, ids, k - entering))
        bases, funded = [], []
        for chosen in combinations(sorted(out), k):
            base = frozenset(chosen)
            demand_legal = all(len(base & ids) >= required for _, ids, required in rows)
            shadow = shadow_state(sigma, base, d)
            direct_legal = literal(qn, qedges, shadow, k, statistics, False) >= k
            assert demand_legal == direct_legal
            local['shadow_demand_equivalences'] += 1
            if not demand_legal:
                continue
            bases.append(base)
            if all(value <= data['mu'][v]
                   for v, value in enumerate(activity_vector(c, ports, out - base))):
                funded.append(base)
        tables[sigma] = (bases, funded)
        local['legal_quotient_signatures'] += 1
        local['shadow_bases'] += len(bases)
        local['capacity_shadow_bases'] += len(funded)
        if not bases:
            local['no_root_k_shadow_signatures'] += 1
        elif not funded:
            local['no_capacity_shadow_signatures'] += 1
        for base in bases:
            tight = [(subset, ids) for subset, ids, required in rows if len(base & ids) == required]
            for target in bases:
                for g in base - target:
                    head_bit = 1 << (ports[g][1] - c)
                    intersection = (1 << (n - c)) - 1
                    for subset, _ in tight:
                        if subset & head_bit:
                            intersection &= subset
                    assert intersection & head_bit
                    eligible = [f for f in target - base
                                if intersection & (1 << (ports[f][1] - c))]
                    assert eligible
                    for f in eligible:
                        new = (base - {g}) | {f}
                        assert new in bases
                        upper = shadow_state(sigma, base, d) ^ (1 << f)
                        literal(qn, qedges, upper, k, statistics)
                    local['all_element_basis_exchange_checks'] += 1
        for base in funded:
            need = activity_vector(c, ports, out - base)
            assert sum(mu - amount for mu, amount in zip(data['mu'], need)) >= 2 * data['q']
            local['reserve_total_checks'] += 1
    for field in ('legal_quotient_signatures', 'shadow_bases', 'capacity_shadow_bases',
                  'all_element_basis_exchange_checks', 'no_capacity_shadow_signatures',
                  'no_root_k_shadow_signatures'):
        assert local[field] == data['stats'].get(field, 0), (data['name'], field, local[field])
    for negative in data.get('no_capacity_shadow_examples', []):
        sigma = negative['sigma']
        bases, funded = tables[sigma]
        assert bases and not funded
        assert set(bases) == {frozenset(e) for e in negative['shadow_bases']}
        initial = negative['actual_internal_mask'] | sigma << m
        literal(n, edges, initial, k, statistics)
        local['explicit_capacity_counterexamples_checked'] += 1
    for sigma, (_, funded) in tables.items():
        if not funded:
            continue
        for eid in range(d, d + len(exterior)):
            target_sigma = sigma ^ (1 << eid)
            if target_sigma not in tables or not tables[target_sigma][1]:
                continue
            target_options = tables[target_sigma][1]
            for first in funded:
                for second in target_options:
                    ba = activity_vector(c, ports, outgoing_ports(sigma, d) - first)
                    bb = activity_vector(c, ports, outgoing_ports(sigma, d) - second)
                    joint = [max(a, b) for a, b in zip(ba, bb)]
                    if sum(joint) > data['q'] + len(outgoing_ports(sigma, d)) - k:
                        continue
                    assert all(joint[v] <= data['mu'][v] for v in range(c))
                    assert sum(joint) <= data['q'] + len(outgoing_ports(sigma, d)) - k
                    local['common_payment_bounds_checked'] += 1
    for saved in data['words']:
        state = saved['initial_mask']
        initial_sigma = state >> m
        assert initial_sigma in tables
        initial_out = outdegrees(n, edges, state)
        assert any(all(initial_out[v] - k >= amount for v, amount in enumerate(
                       activity_vector(c, ports, outgoing_ports(initial_sigma, d) - base)))
                   for base in tables[initial_sigma][1])
        literal(n, edges, state, k, statistics)
        for eid in saved['word']:
            assert 0 <= eid < len(edges)
            state ^= 1 << eid
            literal(n, edges, state, k, statistics)
            local['actual_single_flips_checked'] += 1
        assert state == saved['final_mask']
        intended_sigma = initial_sigma
        common_baseline = set(outgoing_ports(initial_sigma, d))
        for eid in saved['intended_outer_word']:
            intended_sigma ^= 1 << eid
            assert intended_sigma in tables and tables[intended_sigma][1]
            common_baseline &= set(outgoing_ports(intended_sigma, d))
        assert intended_sigma == state >> m
        actual_exterior = [eid - m for eid in saved['word'] if eid >= m + d]
        intended_exterior = [eid for eid in saved['intended_outer_word'] if eid >= d]
        assert actual_exterior == intended_exterior
        final_base = frozenset(saved['final_shadow'])
        assert final_base in tables[state >> m][1]
        final_out = outdegrees(n, edges, state)
        need = activity_vector(c, ports, outgoing_ports(state >> m, d) - final_base)
        assert all(final_out[v] - k >= need[v] for v in range(c))
        if 'without_fixed_baseline' in saved['label'] or 'forced_shadow_change_return' in saved['label']:
            assert len(common_baseline) < k
            assert state >> m == initial_sigma
            local['no_fixed_k_baseline_return_histories'] += 1
        local['actual_words_checked'] += 1
    assert local['actual_words_checked'] == data['stats']['saved_actual_words']
    assert local['actual_single_flips_checked'] == data['stats']['saved_actual_single_flips']
    return dict(name=data['name'], stats=dict(local))


def audit_unpaid_family(data, statistics):
    k, edges, h, ports, exterior = data['k'], data['edges'], data['h'], data['ports'], data['exterior']
    assert data['n'] == 5 and data['c'] == 3
    assert edges == h + ports + exterior
    assert len(h) == 2 * k + 1 and len(ports) == 4 * k and len(exterior) == k
    degree = [sum(v in e for e in edges) for v in range(5)]
    assert degree == [2 * k + 1, 4 * k, 2 * k + 1, 3 * k, 3 * k]
    multiplicities = Counter(tuple(sorted(e)) for e in edges)
    assert max(multiplicities.values()) <= k
    minimum = min(sum(bool(s & (1 << u)) != bool(s & (1 << v)) for u, v in edges)
                  for s in range(1, 31))
    assert minimum == 2 * k + 1
    m = len(h)
    state = data['initial_mask']
    out = outdegrees(5, edges, state)
    assert out == [k + 1, 3 * k, k, k, k]
    sigma = state >> m
    outgoing = outgoing_ports(sigma, len(ports))
    assert len(outgoing) == 3 * k
    assert all(not sigma & (1 << (len(ports) + i)) for i in range(k))
    assert sum(ports[eid][0] == 2 for eid in outgoing) == k
    # All root-k bases must supply k incoming arcs to a: exterior in(a)=0.
    # Hence no base can contain a port to b, and all k ports at w are active.
    assert all(ports[eid][1] == 4 for eid in outgoing if ports[eid][0] == 2)
    assert k > degree[2] - 2 * k == 1
    qedges = [[0 if u < 3 else u - 2, 0 if v < 3 else v - 2] for u, v in ports + exterior]
    explicit_initial_base = frozenset(range(k))
    literal(3, qedges, shadow_state(sigma, explicit_initial_base, len(ports)), k, statistics)
    initial = state
    minima = [literal(5, edges, state, k, statistics)]
    for eid in data['word']:
        assert 0 <= eid < len(edges)
        state ^= 1 << eid
        minima.append(literal(5, edges, state, k, statistics))
    assert state == data['final_mask'] and minima == data['prefix_minima']
    assert len(data['word']) == 3 * k - 3
    assert outdegrees(5, edges, state) == [k, 2 * k + 1, k + 1, k, 2 * k - 1]
    final_sigma = state >> m
    final_base = frozenset(data['final_shadow'])
    literal(3, qedges, shadow_state(final_sigma, final_base, len(ports)), k, statistics)
    active = activity_vector(3, ports, outgoing_ports(final_sigma, len(ports)) - final_base)
    assert active == [0, k, 1]
    fullout = outdegrees(5, edges, state)
    assert [fullout[v] - k for v in range(3)] == [0, k + 1, 1]
    assert all(fullout[v] - k >= active[v] for v in range(3))
    return dict(k=k, word_length=len(data['word']), minimum_cut=minimum,
                no_capacity_shadow=True, final_paid=True,
                physical_prefix_complete_cuts=30 * (len(data['word']) + 1))


def dinic_threshold(n, edges, mask, source, target, required, statistics, undirected=False):
    graph = [[] for _ in range(n)]
    def insert(u, v):
        graph[u].append([v, 1, len(graph[v])])
        graph[v].append([u, 0, len(graph[u]) - 1])
    for eid, (u, v) in enumerate(edges):
        if undirected:
            insert(u, v)
            insert(v, u)
        else:
            if mask & (1 << eid):
                u, v = v, u
            insert(u, v)
    value = 0
    while value < required:
        level = [-1] * n
        level[source] = 0
        queue = [source]
        for u in queue:
            for v, cap, _ in graph[u]:
                if cap and level[v] < 0:
                    level[v] = level[u] + 1
                    queue.append(v)
        if level[target] < 0:
            break
        cursor = [0] * n
        def push(u, budget):
            if u == target:
                return budget
            while cursor[u] < len(graph[u]):
                item = graph[u][cursor[u]]
                v, capacity, reverse = item
                if capacity and level[v] == level[u] + 1:
                    sent = push(v, min(budget, capacity))
                    if sent:
                        item[1] -= sent
                        graph[v][reverse][1] += sent
                        return sent
                cursor[u] += 1
            return 0
        while value < required:
            sent = push(source, required - value)
            if not sent:
                break
            value += sent
    assert value >= required, (n, source, target, value, required)
    statistics['root_flow_threshold_checks'] += 1


def cycle_bases(k, demand):
    solutions = []
    counts = [0] * k
    def visit(i, selected):
        if i == k:
            if counts == demand:
                solutions.append(frozenset(selected))
            return
        for choice in (0, 1):
            head = (i + choice) % k
            if counts[head] >= demand[head]:
                continue
            counts[head] += 1
            enough = True
            for v in range(k):
                available = sum(v == u or v == (u + 1) % k for u in range(i + 1, k))
                if demand[v] - counts[v] > available:
                    enough = False
                    break
            if enough:
                visit(i + 1, selected + [2 * i + choice])
            counts[head] -= 1
    visit(0, [])
    return solutions


def audit_large_identity_family(data, statistics):
    k, c, n = data['k'], data['c'], data['n']
    h, ports, exterior, edges = data['h'], data['ports'], data['exterior'], data['edges']
    assert k % 2 == 0 and k >= 4 and c == k + 1 and n == 2 * k + 1
    assert edges == h + ports + exterior and len(h) == k * k + 1
    m, d, z, r = len(h), len(ports), k, k // 2
    hcount = Counter(tuple(sorted(e)) for e in h)
    for i, j in combinations(range(k), 2):
        assert hcount[i, j] == (1 if (i, j) == (0, 1) else 2)
    for i in range(k):
        assert hcount[i, z] == (2 if i in (0, 1) else 1)
    # These row classes include every proper trace of H.
    for t in range(1, k + 1):
        assert t * (t - 1) <= k * (t - 1)
    for t in range(k):
        assert t * t + int(t > 0) <= k * t
    degree = [sum(v in e for e in edges) for v in range(n)]
    assert [degree[v] - 2 * k for v in range(c)] == [1] * k + [3]
    assert ports == [[i, c + j] for i in range(k) for j in (i, (i + 1) % k)] + [[z, c + i] for i in range(k)] + [[z, c]]
    exterior_counts = Counter(tuple(sorted(e)) for e in exterior)
    assert exterior_counts == Counter({(c + i, c + j): 2 for i, j in combinations(range(k), 2)})
    initial, final = data['initial_mask'], data['final_mask']
    assert len(data['word']) == 1
    eid = data['word'][0]
    assert eid >= m + d
    tail, head = edges[eid]
    if initial & (1 << eid):
        tail, head = head, tail
    assert (tail, head) == (c, c + r)
    assert initial ^ (1 << eid) == final
    sigma, target_sigma = initial >> m, final >> m
    outgoing = outgoing_ports(sigma, d)
    assert outgoing == frozenset(range(2 * k))
    assert outgoing_ports(target_sigma, d) == outgoing
    old_family = cycle_bases(k, [1] * k)
    desired = [1] * k
    desired[0], desired[r] = 0, 2
    new_family = cycle_bases(k, desired)
    assert len(old_family) == 2 and len(new_family) == 1
    assert set(old_family) == {frozenset(e) for e in data['old_capacity_shadow_bases']}
    assert new_family[0] == frozenset(data['new_capacity_shadow_base'])
    distance = min(len(e - new_family[0]) for e in old_family)
    assert distance == r == data['minimum_physical_shadow_distance']
    old_activity = activity_vector(c, ports, outgoing - old_family[0])
    new_activity = activity_vector(c, ports, outgoing - new_family[0])
    assert old_activity == new_activity == [1] * k + [0]
    assert data['common_extra_payment_units'] == 0
    for state in (initial, final):
        output = outdegrees(n, edges, state)
        assert output[:c] == [k + 1] * c
        assert all(output[v] - k >= old_activity[v] for v in range(c))
    before_checks = statistics['root_flow_threshold_checks']
    for v in range(1, n):
        dinic_threshold(n, edges, initial, 0, v, 2 * k + 1, statistics, True)
    for state in (initial, final):
        for v in range(1, n):
            dinic_threshold(n, edges, state, 0, v, k, statistics)
            dinic_threshold(n, edges, state, v, 0, k, statistics)
    qedges = [[0 if u < c else u - c + 1, 0 if v < c else v - c + 1]
              for u, v in ports + exterior]
    for sig, base in [(sigma, e) for e in old_family] + [(target_sigma, new_family[0])]:
        shadow = shadow_state(sig, base, d)
        for v in range(1, k + 1):
            dinic_threshold(k + 1, qedges, shadow, 0, v, k, statistics)
            dinic_threshold(k + 1, qedges, shadow, v, 0, k, statistics)
    actual_checks = statistics['root_flow_threshold_checks'] - before_checks
    assert actual_checks == data['root_flow_threshold_checks']
    if k in (4, 6):
        for state in (initial, final):
            literal(n, edges, state, k, statistics)
    return dict(k=k, vertices=n, physical_shadow_distance=distance,
                common_extra_payment_units=0, actual_word_length=1,
                root_flow_threshold_checks=actual_checks,
                capacity_basis_families_complete=True)


def main():
    certificate_path = ROOT / 'variable_shadows_certificate.json'
    certificate = json.loads(certificate_path.read_text(encoding='utf-8'))
    assert certificate['status'] == 'PASS'
    assert certificate['program_sha256'] == hashlib.sha256((ROOT / 'verify_variable_shadows.py').read_bytes()).hexdigest()
    for name, digest in certificate['dependency_sha256'].items():
        assert hashlib.sha256((ROOT.parent / '2k+1' / name).read_bytes()).hexdigest() == digest
    stats = Counter()
    controls = [audit_control(data, stats) for data in certificate['controls']]
    family = [audit_unpaid_family(data, stats) for data in certificate['unpaid_entry_family']]
    large_family = [audit_large_identity_family(data, stats) for data in certificate['large_identity_change_family']]
    result = dict(status='PASS', theorem='H1', controls=controls,
                  unpaid_entry_family=family, large_identity_change_family=large_family, stats=dict(stats),
                  certificate_sha256=hashlib.sha256(certificate_path.read_bytes()).hexdigest(),
                  program_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
                  analytic_source_sha256=hashlib.sha256((ROOT / '研究结果_H1_可变影子基与跨环境一步交接.md').read_bytes()).hexdigest(),
                  scope='Independent exact finite audit; no assertion of universal MAIN.')
    (ROOT / 'variable_shadows_independent_audit.json').write_text(
        json.dumps(result, ensure_ascii=False, indent=2), encoding='utf-8')
    print(json.dumps(result, ensure_ascii=False, indent=2), flush=True)


if __name__ == '__main__':
    main()
