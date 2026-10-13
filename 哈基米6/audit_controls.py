"""Independent all-shore replay from physical endpoints, without constructor import."""
from pathlib import Path
from hashlib import sha256
from collections import Counter
import json
import time

ROOT = Path(__file__).resolve().parent


def tables(n, edges):
    multiplicity = [[0]*n for _ in range(n)]
    for e in edges:
        u, v = e['u'], e['v']
        assert 0 <= u < n and 0 <= v < n and u != v
        multiplicity[u][v] += 1
        multiplicity[v][u] += 1
    total = 1 << n
    internal, size = [0]*total, [0]*total
    for mask in range(1, total):
        bit = mask & -mask
        v, rest = bit.bit_length()-1, mask ^ bit
        count, x = 0, rest
        while x:
            b = x & -x
            count += multiplicity[v][b.bit_length()-1]
            x ^= b
        internal[mask] = internal[rest]+count
        size[mask] = size[rest]+1
    return dict(n=n, internal=internal, size=size, edges=edges)


def degree(frame, physical_mask, heads=False):
    d = [0]*frame['n']
    for i, e in enumerate(frame['edges']):
        u, v = e['u'], e['v']
        if (physical_mask >> i) & 1:
            u, v = v, u
        d[v if heads else u] += 1
    return d


def cut_values(frame, physical_mask, literal_counter):
    d = degree(frame, physical_mask)
    total = 1 << frame['n']
    tail_sum, out = [0]*total, [0]*total
    for shore in range(1, total):
        bit = shore & -shore
        v, rest = bit.bit_length()-1, shore ^ bit
        tail_sum[shore] = tail_sum[rest]+d[v]
        out[shore] = tail_sum[shore]-frame['internal'][shore]
    assert out[-1] == 0
    literal_counter[0] += total-2
    return out


def original_literal_edge_sum(frame, mask, shore):
    ans = 0
    for i, e in enumerate(frame['edges']):
        u, v = e['u'], e['v']
        if (mask >> i) & 1:
            u, v = v, u
        ans += bool((shore >> u) & 1) and not bool((shore >> v) & 1)
    return ans


def core_mask(edges, physical_mask):
    selected = [i for i, e in enumerate(edges) if e['kind'] == 'H']
    return sum(((physical_mask >> i) & 1) << j for j, i in enumerate(selected))


def eulerian_core(core, mask, k):
    return degree(core, mask) == [k]*core['n']


def quotient_frame(control):
    nc = control['n_core']
    qe = []
    for e in control['edges']:
        if e['kind'] == 'H':
            continue
        convert = lambda v: 0 if v < nc else v-nc+1
        qe.append(dict(u=convert(e['u']), v=convert(e['v'])))
    return tables(control['n_vertices']-nc+1, qe)


def check(control):
    started = time.perf_counter()
    k, nc, nv, edges = (control[x] for x in ['k', 'n_core', 'n_vertices', 'edges'])
    assert len({e['id'] for e in edges}) == len(edges)
    full, core, background = (tables(nv, edges),
                             tables(nc, [e for e in edges if e['kind'] == 'H']),
                             tables(nv, [e for e in edges if e['kind'] == 'E']))
    rows, scalar_rows = [0], 0
    assert len(core['edges']) == k*nc
    for shore in range(1, (1 << nc)-1):
        assert core['internal'][shore] <= k*(core['size'][shore]-1)
    undirected_degree = [a+b for a, b in zip(degree(full, 0), degree(full, 0, True))]
    dsum = [0]*(1 << nv)
    undirected_min = len(edges)
    for shore in range(1, (1 << nv)-1):
        bit, rest = shore & -shore, shore ^ (shore & -shore)
        dsum[shore] = dsum[rest]+undirected_degree[bit.bit_length()-1]
        undirected_min = min(undirected_min, dsum[shore]-2*full['internal'][shore])
    assert undirected_min == control['expected_undirected_strength'] >= 2*k+1
    background_out = cut_values(background, 0, rows)
    f = [len(edges)]*(1 << nc)
    for shore in range(1, (1 << nv)-1):
        trace = shore & ((1 << nc)-1)
        if 0 < trace < (1 << nc)-1:
            f[trace] = min(f[trace], background_out[shore])
    beta = min(f[1:-1])
    assert beta == control['expected_beta']
    core_ud = [a+b for a, b in zip(degree(core, 0), degree(core, 0, True))]
    csums = [0]*(1 << nc)
    mincut_f, mincuts = len(edges), []
    for shore in range(1, (1 << nc)-1):
        bit = shore & -shore
        csums[shore] = csums[shore ^ bit]+core_ud[bit.bit_length()-1]
        delta = csums[shore]-2*core['internal'][shore]
        assert delta >= 2*k
        if delta == 2*k:
            mincuts.append(shore)
            mincut_f = min(mincut_f, f[shore])
    qframe = quotient_frame(control)
    qo = cut_values(qframe, 0, rows)
    assert min(qo[1:-1]) >= k
    qrout, qrin = degree(qframe, 0)[0], degree(qframe, 0, True)[0]
    assert qrout == control['expected_quotient_root_out']
    assert qrin == control['expected_quotient_root_in']
    assert all(not (e['u'] >= nc and e['v'] >= nc) for e in edges)
    assert nv-nc == 3 and qrout >= 3*k and qrin >= 3*k
    if 'dense_cut_vertices' in control:
        shore = sum(1 << v for v in control['dense_cut_vertices'])
        comp = ((1 << nv)-1) ^ shore
        assert full['internal'][shore] > k*(full['size'][shore]-1)
        assert full['internal'][comp] > k*(full['size'][comp]-1)
    source, target, word = (control[x] for x in ['source_mask', 'target_mask', 'word'])
    core_source = core_mask(edges, source)
    core_source_out = cut_values(core, core_source, rows)
    source_strength = min(core_source_out[1:-1])
    assert source_strength == control['expected_source_internal_strength']
    if control['mode'] == 'conditional_entry_and_exact_eulerian_alignment':
        assert beta >= 1 and source_strength+beta >= k
    if control['mode'] == 'mincut_supply_eulerian_alignment':
        assert beta == 0 and mincut_f >= 1
    if control['mode'] == 'condition_gap_and_one_actual_bridge':
        assert beta == 1 and source_strength+beta < k
        gap_trace = sum(1 << v for v in control['deficient_core_trace'])
        assert core_source_out[gap_trace] == 0 and f[gap_trace] >= k
    e_positions = [i for i, e in enumerate(edges) if e['kind'] == 'E']
    expected_e_bits = sum(((source >> i) & 1) << i for i in e_positions)
    mask, full_min, visits, masks, prefix_core_strength = source, len(edges), 0, set(), []
    sequence = [None]+word
    for letter in sequence:
        if letter is not None:
            assert 0 <= letter < len(edges) and edges[letter]['kind'] == 'H'
            mask ^= 1 << letter
        assert sum(((mask >> i) & 1) << i for i in e_positions) == expected_e_bits
        actual = cut_values(full, mask, rows)
        minimum = min(actual[1:-1])
        assert minimum >= k, (control['name'], visits, mask, minimum)
        full_min = min(full_min, minimum)
        # Scalar endpoint summation on every state, with several distinct shores.
        for shore in [1, (1 << nc)-1, 1 << nc,
                      sum(1 << v for v in range(0, nv, 2))]:
            assert actual[shore] == original_literal_edge_sum(full, mask, shore)
            scalar_rows += 1
        co = cut_values(core, core_mask(edges, mask), rows)
        prefix_core_strength.append(min(co[1:-1]))
        masks.add(mask)
        visits += 1
    assert mask == target
    if control['mode'] == 'condition_gap_and_one_actual_bridge':
        assert prefix_core_strength[-1] == control['expected_target_internal_strength']
    else:
        assert eulerian_core(core, core_mask(edges, target), k)
        # Independently validate each claimed macro as a simple directed cycle.
        start = source
        for i in word[:control['normalization_letters']]:
            start ^= 1 << i
        assert eulerian_core(core, core_mask(edges, start), k)
        flattened = []
        for cycle in control['cycle_batches']:
            actual_arcs = []
            for i in cycle:
                e = edges[i]
                u, v = e['u'], e['v']
                if (start >> i) & 1:
                    u, v = v, u
                actual_arcs.append((u, v))
            assert len({u for u, _ in actual_arcs}) == len(cycle)
            for j, (u, v) in enumerate(actual_arcs):
                assert v == actual_arcs[(j+1) % len(cycle)][0]
            for i in cycle:
                start ^= 1 << i
            assert eulerian_core(core, core_mask(edges, start), k)
            flattened.extend(cycle)
        assert flattened == word[control['normalization_letters']:] and start == target
    counts = Counter(word)
    helpers = [i for i, count in counts.items() if count and not ((source ^ target) >> i) & 1]
    for i in helpers:
        assert counts[i] % 2 == 0 and ((mask >> i) & 1) == ((source >> i) & 1)
    # Replay the inverse as physical masks; every state is recomputed, not merged by degree.
    for i in reversed(word):
        mask ^= 1 << i
        actual = cut_values(full, mask, rows)
        assert min(actual[1:-1]) >= k
        visits += 1
    assert mask == source
    return dict(name=control['name'], status='PASS', beta=beta,
                min_background_on_core_mincuts=mincut_f, core_mincuts=len(mincuts),
                source_internal_strength=source_strength,
                target_internal_strength=prefix_core_strength[-1],
                complete_original_min_strength=full_min,
                undirected_min_strength=undirected_min,
                physical_letters=len(word), state_visits=visits,
                distinct_physical_masks=len(masks), complete_directed_cut_rows=rows[0],
                original_complete_directed_cut_rows=visits*((1 << nv)-2),
                endpoint_sum_crosschecks=scalar_rows,
                exact_returned_helpers=[edges[i]['id'] for i in helpers],
                all_non_H_identities_frozen=True,
                quotient_has_no_near_orientation_by_three_leaf_argument=True,
                non_OSP_checked='dense_cut_vertices' in control,
                elapsed_seconds=round(time.perf_counter()-started, 3))


def main():
    cert_path = ROOT/'controls_certificate.json'
    certificate = json.loads(cert_path.read_text(encoding='utf-8'))
    assert not certificate['regularization_used']
    assert not certificate['orientation_component_search_used']
    controls = []
    for c in certificate['controls']:
        result = check(c)
        controls.append(result)
        print(json.dumps(result, ensure_ascii=False), flush=True)
    output = dict(status='PASS', main_status='OPEN', constructor_imported=False,
                  orientation_component_search_used=False, regularization_used=False,
                  masks_merged_by_degree=False, ito_general_algorithm_implemented=False,
                  certificate_sha256=sha256(cert_path.read_bytes()).hexdigest(),
                  source_sha256=sha256(Path(__file__).read_bytes()).hexdigest(),
                  controls=controls,
                  total_complete_directed_cut_rows=sum(c['complete_directed_cut_rows'] for c in controls),
                  total_original_complete_directed_cut_rows=sum(c['original_complete_directed_cut_rows'] for c in controls),
                  total_physical_letters=sum(c['physical_letters'] for c in controls))
    (ROOT/'controls_independent_audit.json').write_text(
        json.dumps(output, ensure_ascii=False, indent=2), encoding='utf-8')
    print(json.dumps(dict(status='PASS', rows=output['total_complete_directed_cut_rows'],
                         letters=output['total_physical_letters'])), flush=True)


if __name__ == '__main__':
    main()
