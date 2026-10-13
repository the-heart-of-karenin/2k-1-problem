"""Supplemental independent literal-cut audit, with no constructor import."""
from collections import Counter
from pathlib import Path
import hashlib
import json

ROOT = Path(__file__).resolve().parent


def orientation(edges, bits):
    return [(v, u) if bits & (1 << eid) else (u, v) for eid, (u, v) in enumerate(edges)]


def rows(n, arcs, counts, category):
    result = []
    for s in range(1, (1 << n)-1):
        result.append(sum(1 for u, v in arcs if s & (1 << u) and not s & (1 << v)))
    counts[category] += len(result)
    return result


def run():
    path = ROOT / 'unlock_pair_H3_certificate.json'
    data = json.loads(path.read_text(encoding='utf-8'))
    assert data['status'] == 'PASS'
    original = json.loads((ROOT/'unique_guard_H3_certificate.json').read_text(encoding='utf-8'))
    assert data['H3_certificate_sha256'] == hashlib.sha256((ROOT/'unique_guard_H3_certificate.json').read_bytes()).hexdigest()
    residual_sources = {item['name']: {(r['initial_internal_mask'], r['target_endpoint'])
                        for r in item['residuals']} for item in original['finite_controls']}
    counts = Counter()
    for item in data['controls']:
        k, c, n, h, outer, sigma = (item[key] for key in ('k', 'c', 'n', 'h', 'outer', 'sigma'))
        m, edges = len(h), h+outer
        qe = [(0 if u < c else u-c+1, 0 if v < c else v-c+1) for u, v in outer]
        qmemo = {}
        def qrows(bits):
            if bits not in qmemo:
                qmemo[bits] = rows(n-c+1, orientation(qe, bits), counts, 'literal_quotient_cut_rows')
            return qmemo[bits]
        assert min(qrows(sigma)) >= k
        qa = orientation(qe, sigma)
        root_g = [eid for eid, (u, v) in enumerate(qa) if u == 0]
        ext_h = [eid for eid, (u, v) in enumerate(outer) if u >= c and v >= c]
        expected = {(h_id, g_id) for g_id in root_g if min(qrows(sigma ^ (1 << g_id))) < k
                    for h_id in ext_h if min(qrows(sigma ^ (1 << h_id))) >= k
                    and min(qrows(sigma ^ (1 << h_id) ^ (1 << g_id))) >= k}
        assert {tuple(pair) for pair in item['pairs']} == expected
        checked, seen = set(), set()
        def check_actual(bits):
            counts['physical_prefix_visits'] += 1
            if bits not in seen:
                assert min(rows(n, orientation(edges, bits), counts, 'literal_actual_physical_cut_rows')) >= k
                seen.add(bits)
        for word in item['words']:
            hm, h_id, g_id = (word[key] for key in ('initial_internal_mask', 'external_outer_eid', 'target_outer_eid'))
            assert (h_id, g_id) in expected
            key = (hm, h_id, g_id)
            assert key not in checked
            checked.add(key)
            xx = outer[g_id][0]
            bits = hm | sigma << m
            initial = orientation(edges, bits)
            before = sum(u == xx for u, v in initial)
            w = word['physical_word']
            assert w[-2:] == [m+h_id, m+g_id] and all(0 <= eid < m for eid in w[:-2])
            assert len(w) <= c+1
            check_actual(bits)
            for eid in w:
                bits ^= 1 << eid
                check_actual(bits)
            assert bits == word['final_full_mask']
            assert bits >> m == sigma ^ (1 << h_id) ^ (1 << g_id)
            assert sum(u == 0 for u, v in orientation(qe, bits >> m)) == k
            counts['actual_unlock_words'] += 1
            counts['actual_unlock_flips'] += len(w)
            counts['unpaid_source_unlock_words'] += before == k
        for omitted in item['omitted']:
            hm, h_id, g_id = (omitted[key] for key in ('initial_internal_mask', 'external_outer_eid', 'target_outer_eid'))
            assert (h_id, g_id) in expected and (hm, outer[g_id][0]) in residual_sources[item['name']]
            assert (hm, h_id, g_id) not in checked
            checked.add((hm, h_id, g_id))
            counts['outside_conditional_entry_cases'] += 1
        source_masks = {hm for hm, h_id, g_id in checked}
        assert len(source_masks) == item['source_profile_representatives']
        assert len(checked) == len(source_masks)*len(expected)
        def outvector(bits):
            aa = orientation(edges, bits)
            return tuple(sum(u == v for u, w in aa) for v in range(n))
        representative_profiles = {outvector(hm | sigma << m) for hm in source_masks}
        assert len(representative_profiles) == len(source_masks)
        deg = [sum(v in edge for edge in edges) for v in range(n)]
        profile_status = {}
        for hm in range(1 << m):
            bits = hm | sigma << m
            out = outvector(bits)
            if any(out[v] < k or out[v] > deg[v]-k for v in range(n)):
                continue
            if out not in profile_status:
                profile_status[out] = min(rows(n, orientation(edges, bits), counts,
                                              'literal_enumeration_profile_cut_rows')) >= k
        assert representative_profiles == {out for out, good in profile_status.items() if good}
        counts['controls'] += 1
        counts['physical_commercial_unlock_pairs'] += len(expected)
        counts['source_profile_representatives'] += len(source_masks)
        counts['unique_actual_physical_masks'] += len(seen)
        print(json.dumps(dict(control=item['name'], checked=True)), flush=True)
    for key, value in data['stats'].items():
        assert counts[key] == value
    report = dict(status='PASS', stats=dict(counts),
                  certificate_sha256=hashlib.sha256(path.read_bytes()).hexdigest(),
                  auditor_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
                  scope=data['scope'], method='independent direct physical cut counts; no constructor import')
    (ROOT/'unlock_pair_H3_independent_audit.json').write_text(json.dumps(report, indent=2), encoding='utf-8')
    print(json.dumps(report), flush=True)


if __name__ == '__main__':
    run()
