"""Physical [H preparation, exterior h, root g] controls for H3.3.

Select one actual source per legal degree profile; do not claim all-source
enumeration for this supplemental certificate. H3 structural enumeration is
separate and unchanged.
"""
from collections import Counter
from pathlib import Path
import hashlib
import json
from verify_unique_guard_H3 import Cuts, arcs_of, degree_vector

ROOT = Path(__file__).resolve().parent


def run():
    source_path = ROOT / 'unique_guard_H3_certificate.json'
    source = json.loads(source_path.read_text(encoding='utf-8'))
    totals, controls = Counter(), []
    for item in source['finite_controls']:
        k, c, n, h, outer, sigma = (item[key] for key in ('k', 'c', 'n', 'h', 'outer', 'sigma'))
        m, edges = len(h), h+outer
        full = Cuts(n, edges, k)
        qe = [(0 if u < c else u-c+1, 0 if v < c else v-c+1) for u, v in outer]
        quotient = Cuts(n-c+1, qe, k)
        qa = arcs_of(qe, sigma)
        outgoing = [eid for eid, (tail, head) in enumerate(qa) if tail == 0]
        external = [eid for eid, (u, v) in enumerate(outer) if u >= c and v >= c]
        pairs = [(h_id, g_id) for g_id in outgoing if not quotient.legal(sigma ^ (1 << g_id))
                 for h_id in external if quotient.legal(sigma ^ (1 << h_id))
                 and quotient.legal(sigma ^ (1 << h_id) ^ (1 << g_id))]
        if not pairs:
            continue
        reps = {}
        for hm in range(1 << m):
            out = degree_vector(n, arcs_of(edges, hm | sigma << m))
            if any(out[v] < k or out[v] > full.degree[v]-k for v in range(n)):
                continue
            if min(full.rows(out)) >= k:
                reps.setdefault(out, hm)
        entry = {(r['initial_internal_mask'], r['target_endpoint']): r for r in item['words']}
        residual = {(r['initial_internal_mask'], r['target_endpoint']): r for r in item['residuals']}
        words, omitted = [], []
        for out, hm in reps.items():
            for h_id, g_id in pairs:
                x = outer[g_id][0]
                if out[x] > k:
                    prep = []
                    branch = 'already_paid'
                elif (hm, x) in entry:
                    prep = entry[hm, x]['physical_word']
                    branch = entry[hm, x]['branch']
                else:
                    assert (hm, x) in residual
                    omitted.append(dict(initial_internal_mask=hm, external_outer_eid=h_id,
                                        target_outer_eid=g_id, reason='sole_saturated_gate_outside_conditional_entry'))
                    totals['outside_conditional_entry_cases'] += 1
                    continue
                word = prep+[m+h_id, m+g_id]
                assert len(word) <= c+1 and all(0 <= eid < m for eid in prep)
                bits = hm | sigma << m
                for eid in word:
                    bits ^= 1 << eid
                    assert full.legal(bits)
                assert bits >> m == sigma ^ (1 << h_id) ^ (1 << g_id)
                words.append(dict(initial_internal_mask=hm, external_outer_eid=h_id,
                                  target_outer_eid=g_id, branch=branch, physical_word=word,
                                  final_full_mask=bits))
                totals['actual_unlock_words'] += 1
                totals['actual_unlock_flips'] += len(word)
                totals['unpaid_source_unlock_words'] += out[x] == k
        totals['controls'] += 1
        totals['physical_commercial_unlock_pairs'] += len(pairs)
        totals['source_profile_representatives'] += len(reps)
        controls.append(dict(**{key: item[key] for key in ('name', 'k', 'c', 'n', 'h', 'outer', 'sigma')},
                             pairs=pairs, words=words, omitted=omitted,
                             source_profile_representatives=len(reps)))
    result = dict(status='PASS', scope='one physical source per complete degree profile, all qualifying h/g pairs in saved controls',
                  stats=dict(totals), controls=controls,
                  H3_certificate_sha256=hashlib.sha256(source_path.read_bytes()).hexdigest(),
                  program_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest())
    (ROOT / 'unlock_pair_H3_certificate.json').write_text(json.dumps(result, indent=2), encoding='utf-8')
    print(json.dumps(dict(status=result['status'], stats=result['stats'])), flush=True)


if __name__ == '__main__':
    run()
