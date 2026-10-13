"""Construct selected physical controls; no orientation-component search."""
from pathlib import Path
from hashlib import sha256
import json

ROOT = Path(__file__).resolve().parent


def edge(edges, label, u, v, kind):
    assert u != v
    edges.append(dict(id=label, u=u, v=v, kind=kind))
    return len(edges)-1


def prime_family(k=2, n=13):
    edges = []
    for j in range(1, k+1):
        for v in range(n):
            edge(edges, f'H_{j}_{v}', v, (v+j) % n, 'H')
    a, b, w = n, n+1, n+2
    h = n//2
    for v in range(n):
        if v < h:
            edge(edges, f'E_b_{v}', b, v, 'E')
            edge(edges, f'E_a_{v}', v, a, 'E')
        else:
            edge(edges, f'E_a_{v}', a, v, 'E')
            edge(edges, f'E_b_{v}', v, b, 'E')
    for v in range(2*k+1):
        u, z = (w, v) if v < k else (v, w)
        edge(edges, f'E_w_{v}', u, z, 'E')
    word = [0]
    cycle_batches = []
    for j in range(1, k+1):
        v, cycle = 0, []
        for _ in range(n):
            cycle.append((j-1)*n+v)
            v = (v+j) % n
        assert v == 0 and len(set(cycle)) == n
        cycle_batches.append(cycle)
        word.extend(cycle)
    return dict(name='prime_far_only_non_eulerian_entry', k=k, n_core=n,
                n_vertices=n+3, edges=edges, source_mask=1,
                target_mask=(1 << (k*n))-1, word=word,
                mode='conditional_entry_and_exact_eulerian_alignment',
                normalization_letters=1, cycle_batches=cycle_batches,
                expected_beta=1, expected_source_internal_strength=k-1,
                expected_undirected_strength=2*k+1,
                expected_quotient_root_out=n+k+1,
                expected_quotient_root_in=n+k,
                dense_cut_vertices=list(range(h))+[a])


def cycle_decomposition(edges, n):
    remaining = {i for i, e in enumerate(edges) if e['kind'] == 'H'}
    cycles = []
    while remaining:
        first = min(remaining)
        vertices, seen, walk = [edges[first]['u']], {edges[first]['u']: 0}, []
        current = vertices[0]
        while True:
            choices = [i for i in remaining if edges[i]['u'] == current]
            assert choices
            i = min(choices)
            walk.append(i)
            current = edges[i]['v']
            if current in seen:
                cycle = walk[seen[current]:]
                assert len(set(cycle)) == len(cycle)
                remaining.difference_update(cycle)
                cycles.append(cycle)
                break
            seen[current] = len(vertices)
            vertices.append(current)
    return cycles


def mincut_only_control():
    k, n = 2, 8
    a, b, w = 8, 9, 10
    edges = []
    for i in range(4):
        for j in range(4):
            u, v = (i, 4+j) if (j-i) % 4 < 2 else (4+j, i)
            edge(edges, f'H_{i}_{j}', u, v, 'H')
    for v in range(n):
        z = a if v < 4 else b
        edge(edges, f'E_to_{v}', v, z, 'E')
        edge(edges, f'E_from_{v}', z, v, 'E')
    for i, (u, v) in enumerate([(w, 0), (w, 1), (2, w), (3, w), (0, w)]):
        edge(edges, f'E_w_{i}', u, v, 'E')
    cycles = cycle_decomposition(edges, n)
    return dict(name='zero_beta_but_all_core_mincuts_paid', k=k, n_core=n,
                n_vertices=n+3, edges=edges, source_mask=0,
                target_mask=(1 << 16)-1,
                word=[i for cycle in cycles for i in cycle],
                mode='mincut_supply_eulerian_alignment', normalization_letters=0,
                cycle_batches=cycles, expected_beta=0,
                expected_source_internal_strength=k,
                expected_undirected_strength=5,
                expected_quotient_root_out=11, expected_quotient_root_in=10)


def complementary_cut_gap(base):
    edges, n, h = base['edges'], base['n_core'], base['n_core']//2
    source = 0
    for i, e in enumerate(edges):
        if e['kind'] != 'H':
            continue
        u, v = e['u'], e['v']
        if (u < h) != (v < h):
            preferred_u, preferred_v = (u, v) if u >= h else (v, u)
        else:
            lo, hi = sorted((u, v))
            assert hi-lo in (1, 2)
            preferred_u, preferred_v = (lo, hi) if hi-lo == 1 else (hi, lo)
        if (preferred_u, preferred_v) != (u, v):
            source |= 1 << i
    cross = next(i for i, e in enumerate(edges)
                 if e['kind'] == 'H' and (e['u'] < h) != (e['v'] < h))
    return dict(name='legal_ambient_source_below_split_strength', k=2,
                n_core=n, n_vertices=base['n_vertices'], edges=edges,
                source_mask=source, target_mask=source ^ (1 << cross), word=[cross],
                mode='condition_gap_and_one_actual_bridge',
                expected_beta=1, expected_source_internal_strength=0,
                expected_target_internal_strength=1,
                expected_undirected_strength=5,
                expected_quotient_root_out=base['expected_quotient_root_out'],
                expected_quotient_root_in=base['expected_quotient_root_in'],
                deficient_core_trace=list(range(h)))


def main():
    base = prime_family()
    controls = [base, mincut_only_control(), complementary_cut_gap(base)]
    certificate = dict(status='CONSTRUCTED', main_status='OPEN',
                       regularization_used=False,
                       source_sha256=sha256(Path(__file__).read_bytes()).hexdigest(),
                       scope='Three selected controls of analytic mechanisms; not universal state search',
                       ito_general_algorithm_implemented=False,
                       orientation_component_search_used=False, controls=controls)
    (ROOT/'controls_certificate.json').write_text(
        json.dumps(certificate, ensure_ascii=False, indent=2), encoding='utf-8')
    print(json.dumps(dict(status='CONSTRUCTED', controls=len(controls),
                         word_lengths=[len(c['word']) for c in controls])))


if __name__ == '__main__':
    main()
