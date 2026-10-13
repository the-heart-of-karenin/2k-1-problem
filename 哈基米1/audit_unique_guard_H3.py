"""Independent H3 audit. No import of a constructor, path selector, or archive.

Literal directed cuts are counted from physical arcs. Enumeration may reuse a
degree profile; saved word prefixes separately reuse only identical full masks.
Large family inputs use all directed root pairs and undirected root flows.
"""
from collections import Counter, deque
from pathlib import Path
import hashlib
import json

ROOT = Path(__file__).resolve().parent


def directed(edges, bits):
    result = []
    for i, (u, v) in enumerate(edges):
        result.append((v, u) if bits & (1 << i) else (u, v))
    return result


def outdegrees(n, aa):
    ans = [0]*n
    for tail, head in aa:
        ans[tail] += 1
    return tuple(ans)


def literal_out(aa, s):
    return sum(1 for tail, head in aa if s & (1 << tail) and not s & (1 << head))


def literal_rows(n, aa, counts, name):
    counts[name] += (1 << n)-2
    return [literal_out(aa, s) for s in range(1, (1 << n)-1)]


def reach(aa, sources, forbidden=()):
    bad, seen = set(forbidden), set(sources)
    todo = list(sources)
    while todo:
        u = todo.pop()
        for tail, head in aa:
            if tail == u and head not in bad and head not in seen:
                seen.add(head)
                todo.append(head)
    return seen


def flow(n, arcs, source, target, limit):
    graph = [[] for _ in range(n)]
    for u, v in arcs:
        graph[u].append([v, 1, len(graph[v])])
        graph[v].append([u, 0, len(graph[u])-1])
    total = 0
    while total < limit:
        levels = [-1]*n
        levels[source] = 0
        todo = deque([source])
        while todo:
            u = todo.popleft()
            for v, cap, back in graph[u]:
                if cap and levels[v] == -1:
                    levels[v] = levels[u]+1
                    todo.append(v)
        if levels[target] < 0:
            return total
        ptr = [0]*n
        def push(u, amount):
            if u == target:
                return amount
            while ptr[u] < len(graph[u]):
                item = graph[u][ptr[u]]
                v, cap, back = item
                if cap and levels[v] == levels[u]+1:
                    got = push(v, min(amount, cap))
                    if got:
                        item[1] -= got
                        graph[v][back][1] += got
                        return got
                ptr[u] += 1
            return 0
        while total < limit:
            got = push(source, limit-total)
            if not got:
                break
            total += got
    return total


def full_flow(n, aa, k, counts):
    for v in range(1, n):
        for s, t in ((0, v), (v, 0)):
            assert flow(n, aa, s, t, k) >= k
            counts['directed_root_flows'] += 1


def audit_control(item, counts):
    k, c, n, h, outer, sigma = (item[key] for key in ('k', 'c', 'n', 'h', 'outer', 'sigma'))
    edges, m = h+outer, len(h)
    core, whole = (1 << c)-1, (1 << n)-1
    outside = whole ^ core
    assert item['m'] == m and item['q'] == m-k*(c-1) > 0
    for s in range(1, core):
        e = sum(1 for u, v in h if s & (1 << u) and s & (1 << v))
        assert e <= k*(s.bit_count()-1)
        counts['sd_subset_rows'] += 1
    und = []
    for s in range(1, whole):
        und.append(sum(1 for u, v in edges if bool(s & (1 << u)) != bool(s & (1 << v))))
    counts['literal_undirected_cut_rows'] += whole-1
    assert min(und) == item['minimum_cut'] >= 2*k+1
    qe = [(0 if u < c else u-c+1, 0 if v < c else v-c+1) for u, v in outer]
    qa = directed(qe, sigma)
    assert min(literal_rows(n-c+1, qa, counts, 'literal_quotient_cut_rows')) >= k
    assert outdegrees(n-c+1, qa)[0] == k+1
    targets = {outer[eid][0] for eid, (tail, head) in enumerate(qa) if tail == 0}
    deg = [sum(v in e for e in edges) for v in range(n)]
    mu = [deg[v]-2*k for v in range(c)]
    profile_rows, legal = {}, []
    for hm in range(1 << m):
        aa = directed(edges, hm | sigma << m)
        out = outdegrees(n, aa)
        if any(t < k or t > deg[v]-k for v, t in enumerate(out)):
            continue
        if out not in profile_rows:
            profile_rows[out] = literal_rows(n, aa, counts, 'literal_enumeration_profile_cut_rows')
        if min(profile_rows[out]) >= k:
            legal.append(hm)
    assert hashlib.sha256(json.dumps(legal).encode()).hexdigest() == item['legal_internal_masks_sha256']
    assert len(legal) == item['stats']['legal_physical_states']
    counts['enumerated_legal_physical_states'] += len(legal)
    expected, guard_data = set(), {}
    seen_profiles = set()
    for hm in legal:
        aa = directed(edges, hm | sigma << m)
        out = outdegrees(n, aa)
        a = [out[v]-k for v in range(c)]
        if out not in guard_data:
            family = {u: [] for u in range(c) if a[u] > 0}
            for s, value in enumerate(profile_rows[out], 1):
                if value == k and s & core not in (0, core) and s & outside not in (0, outside):
                    for u in family:
                        if s & (1 << u):
                            family[u].append(s)
            intersections = {}
            for u, ss in family.items():
                if ss:
                    meet = whole
                    for s in ss:
                        meet &= s
                    assert profile_rows[out][meet-1] == k
                    trace = meet & core
                    assert a[u] == 1 and sum(a[v] for v in range(c) if trace & (1 << v)) == 1
                    assert sum(1 for p, q in h if trace & (1 << p) and trace & (1 << q)) == k*(trace.bit_count()-1)
                    assert all(not (meet & (1 << v)) or trace & (1 << p)
                               for p, v in outer if p < c <= v)
                    intersections[u] = meet
            guard_data[out] = family, intersections
        family, intersections = guard_data[out]
        for x in targets:
            if a[x] > 0:
                continue
            expected.add((hm, x))
            excluded = [u for u, meet in intersections.items() if not (meet & (1 << x))]
            assert len(excluded) <= 1
            if out not in seen_profiles:
                counts['guard_profile_target_checks'] += 1
            counts['guard_physical_state_target_checks'] += 1
        seen_profiles.add(out)
    words = {(word['initial_internal_mask'], word['target_endpoint']): word for word in item['words']}
    residuals = {(word['initial_internal_mask'], word['target_endpoint']): word for word in item['residuals']}
    assert len(words) == len(item['words']) and len(residuals) == len(item['residuals'])
    assert not words.keys() & residuals.keys() and words.keys() | residuals.keys() == expected
    actual_masks = set()
    def check_actual(bits):
        counts['actual_mask_prefix_visits'] += 1
        if bits not in actual_masks:
            assert min(literal_rows(n, directed(edges, bits), counts, 'literal_actual_physical_cut_rows')) >= k
            actual_masks.add(bits)
    for (hm, x), record in words.items():
        bits = hm | sigma << m
        source_arcs = directed(edges, bits)
        a = [t-k for t in outdegrees(n, source_arcs)[:c]]
        donor, vertices = record['donor'], record['path_vertices']
        assert vertices[0] == donor and vertices[-1] == x and len(set(vertices)) == len(vertices)
        assert len(record['physical_word']) == len(vertices)-1 <= c-1
        assert a[donor] > 0 and all(a[v] < mu[v] for v in vertices[1:])
        check_actual(bits)
        for j, eid in enumerate(record['physical_word']):
            assert 0 <= eid < m and source_arcs[eid] == (vertices[j], vertices[j+1])
            bits ^= 1 << eid
            check_actual(bits)
        assert bits == record['final_full_mask'] and outdegrees(n, directed(edges, bits))[x] == k+1
        counts['conditional_entry_words'] += 1
        counts['conditional_entry_flips'] += len(record['physical_word'])
        counts['positive_unsaturated_frontier_words'] += any(a[v] > 0 for v in vertices[1:])
    for (hm, x), record in residuals.items():
        bits = hm | sigma << m
        aa = directed(edges, bits)
        out = outdegrees(n, aa)
        a = [out[v]-k for v in range(c)]
        family, intersections = guard_data[out]
        u, shore = record['sole_guarded_positive'], record['minimal_guard_shore']
        assert a[u] == mu[u] == 1 and shore == intersections[u]
        assert (shore & core).bit_count() >= 2 and not (shore & (1 << x))
        assert set(intersections) == {u}
        free = {v for v in range(c) if a[v] > 0 and v != u}
        assert free and x in reach(aa[:m], free) and x not in reach(aa[:m], free, [u])
        counts['residual_saturated_gate_pairs'] += 1
    counts['unique_actual_physical_masks'] += len(actual_masks)
    counts['finite_controls'] += 1


def audit_family(item, counts):
    k, c, n, h, outer, sigma = (item[key] for key in ('k', 'c', 'n', 'h', 'outer', 'sigma'))
    assert c >= k+3 and n == c+2 and len(h) == k*(c-1)+1
    assert h == [[i, i+1] for i in range(c-1) for _ in range(k)]+[[c-1, 0]]
    edges, m = h+outer, len(h)
    initial = sigma << m
    source_arcs = directed(edges, initial)
    a = [t-k for t in outdegrees(n, source_arcs)[:c]]
    mu = [sum(v in e for e in edges)-2*k for v in range(c)]
    assert mu == [1]*c and a == [1, 1]+[0]*(c-2)
    guard = sum(1 << v for v in range(1, c-1)) | (1 << c)
    assert guard == item['source_guard_shore'] and literal_out(source_arcs, guard) == k
    assert outdegrees(n, source_arcs)[1] == k+1
    assert sum(head == 1 for tail, head in source_arcs) == k
    assert c-1 not in reach(source_arcs[:m], {0}, [1])
    assert not (guard & (1 << (c-1)))
    qe = [(0 if u < c else u-c+1, 0 if v < c else v-c+1) for u, v in outer]
    assert min(literal_rows(3, directed(qe, sigma), counts, 'literal_quotient_cut_rows')) >= k
    g = item['family_target_outer_eid']
    assert min(literal_rows(3, directed(qe, sigma ^ (1 << g)), counts, 'literal_quotient_cut_rows')) == k-1
    shadow = next(eid for eid, (u, v) in enumerate(outer) if u == 1 and v == c)
    assert min(literal_rows(3, directed(qe, sigma ^ (1 << shadow)), counts, 'literal_quotient_cut_rows')) >= k
    if n <= 12:
        for s in range(1, (1 << n)-1):
            assert sum(1 for u, v in edges if bool(s & (1 << u)) != bool(s & (1 << v))) >= 2*k+1
            counts['literal_undirected_cut_rows'] += 1
    else:
        ua = [(u, v) for edge in edges for u, v in (edge, edge[::-1])]
        for v in range(1, n):
            assert flow(n, ua, 0, v, 2*k+1) >= 2*k+1
            counts['undirected_root_flows'] += 1
    bits = initial
    assert len(item['physical_word']) == c-1
    for j in range(c):
        aa = directed(edges, bits)
        if n <= 12:
            assert min(literal_rows(n, aa, counts, 'literal_family_physical_cut_rows')) >= k
        else:
            full_flow(n, aa, k, counts)
        assert [t-k for t in outdegrees(n, aa)[:c]] == item['core_prefix_profiles'][j]
        if j < c-1:
            eid = item['physical_word'][j]
            assert 0 <= eid < m
            bits ^= 1 << eid
    assert bits == item['final_full_mask'] and outdegrees(n, directed(edges, bits))[c-1] == k+1
    bad_first = initial ^ (1 << item['blocked_first_edge'])
    assert literal_out(directed(edges, bad_first), item['blocked_first_shore']) == k-1
    bad_end = initial
    for eid in item['forbidden_guard_donor_word']:
        bad_end ^= 1 << eid
    assert bad_end == item['forbidden_guard_donor_final_mask']
    assert literal_out(directed(edges, bad_end), guard) == k-1
    counts['single_packet_countercontrols'] += 1
    counts['family_relay_words'] += 1
    counts['family_relay_flips'] += c-1


def run():
    data_path = ROOT / 'unique_guard_H3_certificate.json'
    data = json.loads(data_path.read_text(encoding='utf-8'))
    assert data['status'] == 'PASS'
    counts = Counter()
    for item in data['finite_controls']:
        audit_control(item, counts)
        print(json.dumps(dict(control=item['name'], checked=True)), flush=True)
    for item in data['saturated_gate_family_controls']:
        audit_family(item, counts)
        print(json.dumps(dict(family=item['name'], checked=True)), flush=True)
    for key in ('legal_physical_states', 'conditional_entry_words', 'conditional_entry_flips',
                'residual_saturated_gate_pairs', 'positive_unsaturated_frontier_words'):
        audit_key = 'enumerated_legal_physical_states' if key == 'legal_physical_states' else key
        assert counts[audit_key] == data['stats'][key]
    rejected = json.loads((ROOT/'trapped_ports_H3_probe.json').read_text(encoding='utf-8'))
    k, c, n, h, outer, sigma = (rejected[key] for key in ('k', 'c', 'n', 'h', 'outer', 'sigma'))
    qe = [(0 if u < c else u-c+1, 0 if v < c else v-c+1) for u, v in outer]
    bad = [(s, literal_out(directed(qe, sigma), s)) for s in range(1, (1 << (n-c+1))-1)]
    bad = [[s, value] for s, value in bad if value < k]
    assert bad == rejected['quotient_bad_outcuts'] == [[7, 1]]
    source = directed(h+outer, rejected['source_internal_mask'] | sigma << len(h))
    assert literal_out(source, 127) == 1
    counts['rejected_illegal_quotient_candidates'] += 1
    result = dict(status='PASS', certificate_sha256=hashlib.sha256(data_path.read_bytes()).hexdigest(),
                  auditor_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(), stats=dict(counts),
                  method='literal physical cuts and independently built root flows; no constructor import',
                  limitations='finite scope only; exploratory random screen totals are not independently replayed')
    (ROOT/'unique_guard_H3_independent_audit.json').write_text(json.dumps(result, indent=2), encoding='utf-8')
    print(json.dumps(result), flush=True)


if __name__ == '__main__':
    run()
