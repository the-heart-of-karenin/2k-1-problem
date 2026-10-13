"""Independently check the full physical graph, connector, macro, and exact return."""
from pathlib import Path
from hashlib import sha256
from collections import Counter
import json

ROOT = Path(__file__).resolve().parent
cp = ROOT/'borrow_control_certificate.json'
c = json.loads(cp.read_text(encoding='utf-8'))
edges, k, nc, nv = c['edges'], c['k'], c['n_core'], c['n_vertices']
assert len({e['id'] for e in edges}) == len(edges)
assert not c['regularization_used'] and not c['orientation_component_search_used']


def endpoints(e, i, mask):
    return (e['v'], e['u']) if (mask >> i) & 1 else (e['u'], e['v'])


def graph_tables(number, indices):
    multiplicity = [[0]*number for _ in range(number)]
    degrees = [0]*number
    for i in indices:
        e = edges[i]
        u, v = e['u'], e['v']
        assert u != v and 0 <= u < number and 0 <= v < number
        multiplicity[u][v] += 1
        multiplicity[v][u] += 1
        degrees[u] += 1
        degrees[v] += 1
    total = 1 << number
    inside, sizes, degree_sum = [0]*total, [0]*total, [0]*total
    for s in range(1, total):
        bit = s & -s
        v, rest = bit.bit_length()-1, s ^ bit
        x, additional = rest, 0
        while x:
            b = x & -x
            additional += multiplicity[v][b.bit_length()-1]
            x ^= b
        inside[s] = inside[rest]+additional
        sizes[s] = sizes[rest]+1
        degree_sum[s] = degree_sum[rest]+degrees[v]
    return dict(number=number, indices=indices, inside=inside, sizes=sizes,
                degrees=degrees, degree_sum=degree_sum)


def outcuts(frame, mask):
    degree = [0]*frame['number']
    for i in frame['indices']:
        u, v = endpoints(edges[i], i, mask)
        degree[u] += 1
    total = 1 << frame['number']
    sums, out = [0]*total, [0]*total
    for s in range(1, total):
        b = s & -s
        sums[s] = sums[s ^ b]+degree[b.bit_length()-1]
        out[s] = sums[s]-frame['inside'][s]
    assert out[-1] == 0
    return degree, out


h_ids = [i for i, e in enumerate(edges) if e['kind'] == 'H']
e_ids = [i for i, e in enumerate(edges) if e['kind'] == 'E']
full = graph_tables(nv, list(range(len(edges))))
core = graph_tables(nc, h_ids)
background = graph_tables(nv, e_ids)
assert len(h_ids) == k*nc and core['degrees'] == [2*k]*nc
assert full['degrees'][:nc] == [2*k+1]*nc
for s in range(1, (1 << nc)-1):
    assert core['inside'][s] <= k*(core['sizes'][s]-1)
ud_min = min(full['degree_sum'][s]-2*full['inside'][s]
             for s in range(1, (1 << nv)-1))
assert ud_min == c['expected_undirected_strength']
assert len({tuple(sorted((e['u'], e['v']))) for e in edges}) == len(edges)

# Independent quotient counts. This graph has one nuclear-root parallel star.
def q_counts(mask):
    r_out, r_in = 0, 0
    for i in e_ids:
        u, v = endpoints(edges[i], i, mask)
        assert (u < nc) != (v < nc)
        r_out += u < nc
        r_in += v < nc
    return r_out, r_in


source, target, word = c['source_mask'], c['target_mask'], c['word']
assert q_counts(source) == (c['expected_quotient_root_out'], c['expected_quotient_root_in'])
assert min(q_counts(source)) > k+1
_, background_out = outcuts(background, source)
f = [len(edges)]*(1 << nc)
for s in range(1, (1 << nv)-1):
    trace = s & ((1 << nc)-1)
    if 0 < trace < (1 << nc)-1:
        f[trace] = min(f[trace], background_out[s])
beta = min(f[1:-1])
assert beta == c['expected_beta'] == 0
mincut_f = min(f[s] for s in range(1, (1 << nc)-1)
               if core['degree_sum'][s]-2*core['inside'][s] == 2*k)
assert mincut_f == 0

# The advertised balanced-after-contraction certificate is checked from its own arcs.
positions = c['connector_positions']
connector_mask = c['connector_orientation_mask']
outdegree, indegree = [0]*nv, [0]*nv
successors = [[] for _ in range(nv)]
for i in positions:
    assert i in e_ids
    u, v = endpoints(edges[i], i, connector_mask)
    outdegree[u] += 1
    indegree[v] += 1
    successors[u].append(v)
assert outdegree[nc:] == indegree[nc:]
assert sum(outdegree[:nc]) == sum(indegree[:nc])
reachable, queue = {c['root_anchor']}, [c['root_anchor']]
for u in queue:
    for v in successors[u]:
        if v not in reachable:
            reachable.add(v)
            queue.append(v)
circle = c['directed_core_cycle']
arcs = [endpoints(edges[i], i, source) for i in circle]
assert arcs[0][0] == c['root_anchor']
assert len({u for u, _ in arcs}) == len(circle)
for j, (u, v) in enumerate(arcs):
    assert v == arcs[(j+1) % len(arcs)][0] and u in reachable

prefix_mask = source
for i in c['commercial_prefix']:
    assert i in e_ids
    prefix_mask ^= 1 << i
    assert min(q_counts(prefix_mask)) >= k
for i in positions:
    assert ((prefix_mask >> i) & 1) == ((connector_mask >> i) & 1)
assert word == c['commercial_prefix']+circle+list(reversed(c['commercial_prefix']))

# Every advertised circle letter is illegal at the initial actual state.
initial_illegal = []
for i in circle:
    _, out = outcuts(full, source ^ (1 << i))
    assert min(out[1:-1]) < k
    initial_illegal.append(edges[i]['id'])

rows, states, scalar_checks, masks, mask = 0, 0, 0, set(), source
full_min, core_min = len(edges), len(h_ids)
for i in [None]+word:
    if i is not None:
        mask ^= 1 << i
    _, out = outcuts(full, mask)
    _, hc = outcuts(core, mask)
    assert min(out[1:-1]) >= k
    assert min(q_counts(mask)) >= k
    full_min = min(full_min, min(out[1:-1]))
    core_min = min(core_min, min(hc[1:-1]))
    for s in [1, 3, (1 << nc)-1, 1 << nc, (1 << 0)+(1 << nc)]:
        counted = 0
        for j, e in enumerate(edges):
            u, v = endpoints(e, j, mask)
            counted += bool((s >> u) & 1) and not bool((s >> v) & 1)
        assert counted == out[s]
        scalar_checks += 1
    rows += (1 << nv)-2
    states += 1
    masks.add(mask)
assert mask == target
assert all(((source ^ target) >> i) & 1 == 0 for i in e_ids)
assert outcuts(core, source)[0] == outcuts(core, target)[0] == [k]*nc
counts = Counter(word)
assert all(counts[i] == 1 for i in circle)
for i in e_ids:
    assert counts[i] % 2 == 0
for i in reversed(word):
    mask ^= 1 << i
    _, out = outcuts(full, mask)
    assert min(out[1:-1]) >= k
    rows += (1 << nv)-2
    states += 1
assert mask == source

result = dict(status='PASS', main_status='OPEN', constructor_imported=False,
              regularization_used=False, orientation_component_search_used=False,
              physical_masks_merged_by_degree=False,
              certificate_sha256=sha256(cp.read_bytes()).hexdigest(),
              source_sha256=sha256(Path(__file__).read_bytes()).hexdigest(),
              physical_letters=len(word), state_visits=states,
              distinct_physical_masks=len(masks), original_complete_directed_cut_rows=rows,
              scalar_endpoint_checks=scalar_checks, beta=beta,
              min_background_on_core_mincuts=mincut_f,
              original_min_strength=full_min, smallest_prefix_core_strength=core_min,
              undirected_strength=ud_min,
              all_nuclear_vertices_have_critical_degree=True,
              initial_circle_single_flips_illegal=initial_illegal,
              quotient_initial_both_far=True, connector_quotient_balanced=True,
              connector_reaches_entire_circle=True, every_non_circle_identity_returned=True,
              scope='One explicit five-letter macro; no universal balanced-certificate existence claim')
(ROOT/'borrow_control_independent_audit.json').write_text(
    json.dumps(result, ensure_ascii=False, indent=2), encoding='utf-8')
print(json.dumps(result, ensure_ascii=False))
