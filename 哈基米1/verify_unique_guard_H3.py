"""H3 finite physical-word certificate, separate from exploratory screens."""
from collections import Counter, deque
from pathlib import Path
import hashlib
import json

ROOT = Path(__file__).resolve().parent


def arcs_of(edges, mask):
    return [(v, u) if mask >> eid & 1 else (u, v) for eid, (u, v) in enumerate(edges)]


def degree_vector(n, arcs):
    out = [0]*n
    for u, v in arcs:
        out[u] += 1
    return tuple(out)


class Cuts:
    def __init__(self, n, edges, k):
        self.n, self.edges, self.k = n, edges, k
        self.degree = [sum(v in edge for edge in edges) for v in range(n)]
        adj = [[0]*n for _ in range(n)]
        for u, v in edges:
            adj[u][v] += 1
            adj[v][u] += 1
        self.inside = [0]*(1 << n)
        for s in range(1, 1 << n):
            u = (s & -s).bit_length()-1
            rest = s ^ (1 << u)
            self.inside[s] = self.inside[rest]+sum(adj[u][v] for v in range(n) if rest >> v & 1)
        self.cache = {}

    def rows(self, out):
        out = tuple(out)
        if out not in self.cache:
            sums = [0]*(1 << self.n)
            for s in range(1, (1 << self.n)-1):
                u = (s & -s).bit_length()-1
                sums[s] = sums[s ^ (1 << u)]+out[u]
            self.cache[out] = [sums[s]-self.inside[s] for s in range(1, (1 << self.n)-1)]
        return self.cache[out]

    def legal(self, mask):
        return min(self.rows(degree_vector(self.n, arcs_of(self.edges, mask)))) >= self.k

    def undirected_minimum(self):
        deg_rows = self.rows(self.degree)
        return min(value-self.inside[s] for s, value in enumerate(deg_rows, 1))


def path(c, arcs, sources, target, allowed):
    parent, todo = {u: None for u in sources}, deque(sorted(sources))
    while todo:
        u = todo.popleft()
        if u == target:
            word, vertices = [], [u]
            while parent[u] is not None:
                p, eid = parent[u]
                word.append(eid)
                vertices.append(p)
                u = p
            return list(reversed(word)), list(reversed(vertices))
        for eid, (tail, head) in enumerate(arcs):
            if tail == u and allowed >> head & 1 and head not in parent:
                parent[head] = (u, eid)
                todo.append(head)
    return None


def guards(c, n, k, a, rr):
    core, whole = (1 << c)-1, (1 << n)-1
    outside = whole ^ core
    result = {u: [] for u in range(c) if a[u] > 0}
    for s, value in enumerate(rr, 1):
        if value == k and s & core not in (0, core) and s & outside not in (0, outside):
            for u in result:
                if s >> u & 1:
                    result[u].append(s)
    intersection = {}
    for u, ss in result.items():
        if ss:
            total = whole
            for s in ss:
                total &= s
            intersection[u] = total
    return result, intersection


def verify_control(control, totals):
    k, c, h, outer, sigma = (control[key] for key in ('k', 'c', 'h', 'outer', 'sigma'))
    n, m = max(max(e) for e in h+outer)+1, len(h)
    full, core = Cuts(n, h+outer, k), Cuts(c, h, k)
    assert m > k*(c-1)
    assert all(core.inside[s] <= k*(s.bit_count()-1) for s in range(1, (1 << c)-1))
    minimum = full.undirected_minimum()
    assert minimum >= 2*k+1
    qe = [(0 if u < c else u-c+1, 0 if v < c else v-c+1) for u, v in outer]
    qcuts = Cuts(n-c+1, qe, k)
    assert qcuts.legal(sigma)
    qarcs = arcs_of(qe, sigma)
    assert sum(tail == 0 for tail, head in qarcs) == k+1
    targets = sorted({outer[eid][0] for eid, (tail, head) in enumerate(qarcs) if tail == 0})
    base = degree_vector(n, arcs_of(outer, sigma))
    profiles = {}
    for hm in range(1 << m):
        hv = degree_vector(c, arcs_of(h, hm))
        profiles.setdefault(hv, []).append(hm)
    legal, words, residuals, local = [], [], [], Counter()
    mu = [full.degree[v]-2*k for v in range(c)]
    for hv, masks in profiles.items():
        out = tuple(base[v]+(hv[v] if v < c else 0) for v in range(n))
        if any(out[v] < k or out[v] > full.degree[v]-k for v in range(n)):
            continue
        rr = full.rows(out)
        if min(rr) < k:
            continue
        legal.extend(masks)
        a = [out[v]-k for v in range(c)]
        guard, intersections = guards(c, n, k, a, rr)
        assert sum(a) == m-k*(c-1)+1
        for u, s in intersections.items():
            trace, z = s & ((1 << c)-1), s >> c
            assert rr[s-1] == k and z not in (0, (1 << (n-c))-1)
            assert a[u] == 1 and sum(a[v] for v in range(c) if trace >> v & 1) == 1
            assert core.inside[trace] == k*(trace.bit_count()-1)
            assert all(not (z >> (v-c) & 1) or trace >> w & 1
                       for w, v in outer if w < c <= v)
        local['legal_profiles'] += 1
        for x in targets:
            if a[x] > 0:
                local['already_positive_physical_pairs'] += len(masks)
                continue
            excluded = [u for u, s in intersections.items() if not (s >> x & 1)]
            assert len(excluded) <= 1
            local['low_profile_target_pairs'] += 1
            local['excluded_guard_profile_target_pairs'] += bool(excluded)
            containing = [u for u, s in intersections.items() if s >> x & 1]
            for hm in masks:
                harcs = arcs_of(h, hm)
                if containing:
                    donor = min(containing)
                    answer = path(c, harcs, {donor}, x, intersections[donor] & ((1 << c)-1))
                    branch = 'guard_intersection_contains_target'
                    assert answer
                else:
                    free = {u for u in guard if not guard[u]}
                    assert free
                    supply = path(c, harcs, free, x, (1 << c)-1)
                    assert supply
                    allowed = (1 << c)-1
                    if excluded and mu[excluded[0]] == 1:
                        allowed ^= 1 << excluded[0]
                    answer = path(c, harcs, free, x, allowed)
                    branch = 'unguarded_supply_with_unsaturated_frontiers'
                local['low_physical_state_target_pairs'] += 1
                if answer is None:
                    u = excluded[0]
                    trace = intersections[u] & ((1 << c)-1)
                    assert a[u] == mu[u] == 1 and trace.bit_count() >= 2
                    residuals.append(dict(initial_internal_mask=hm, target_endpoint=x,
                                          sole_guarded_positive=u, minimal_guard_shore=intersections[u],
                                          unrestricted_supply_word=supply[0]))
                    local['residual_saturated_gate_pairs'] += 1
                    continue
                word, vertices = answer
                donor = vertices[0]
                assert a[donor] > 0 and all(a[v] < mu[v] for v in vertices[1:])
                assert len(word) <= c-1
                tight = [s for s, value in enumerate(rr, 1) if value == k]
                assert all(all(not (s >> donor & 1) or s >> v & 1 for s in tight)
                           for v in vertices[1:])
                current = hm | sigma << m
                for eid in word:
                    current ^= 1 << eid
                    assert full.legal(current)
                assert degree_vector(n, arcs_of(h+outer, current))[x] == k+1
                words.append(dict(initial_internal_mask=hm, target_endpoint=x, branch=branch,
                                  donor=donor, physical_word=word, path_vertices=vertices,
                                  final_full_mask=current))
                local['conditional_entry_words'] += 1
                local['conditional_entry_flips'] += len(word)
                local['positive_unsaturated_frontier_words'] += any(a[v] > 0 for v in vertices[1:])
    legal.sort()
    assert legal
    local['legal_physical_states'] = len(legal)
    totals.update(local)
    return dict(**control, n=n, m=m, q=m-k*(c-1), minimum_cut=minimum,
                legal_internal_masks_sha256=hashlib.sha256(json.dumps(legal).encode()).hexdigest(),
                stats=dict(local), words=words, residuals=residuals)


def family(k, c):
    assert k >= 2 and c >= k+3
    z, w = c, c+1
    h = [(i, i+1) for i in range(c-1) for _ in range(k)]+[(c-1, 0)]
    outer, incoming = [], []
    def ports(u, v, copies, reverse=False):
        for _ in range(copies):
            if reverse:
                incoming.append(len(outer))
            outer.append((u, v))
    ports(0, w, 1)
    ports(0, w, k-1, True)
    ports(1, z, 1)
    for i in range(2, c-1):
        ports(i, z, 1, True)
    first_target_port = len(outer)
    ports(c-1, w, k-1)
    ports(c-1, w, 1, True)
    outer += [(w, z)]*(k+1)
    sigma = sum(1 << eid for eid in incoming)
    return dict(name=f'saturated_gate_k{k}_n{c}', k=k, c=c, h=h, outer=outer, sigma=sigma,
                family_target_outer_eid=first_target_port)


def family_word(control):
    k, c, h, outer, sigma = (control[key] for key in ('k', 'c', 'h', 'outer', 'sigma'))
    edges, m, n = h+outer, len(h), c+2
    word = [k, 0]+[k*i for i in range(2, c-1)]
    mask = sigma << m
    mu = [sum(v in edge for edge in edges)-2*k for v in range(c)]
    assert mu == [1]*c
    profiles = []
    for j in range(len(word)+1):
        a = [t-k for t in degree_vector(n, arcs_of(edges, mask))[:c]]
        assert sum(a) == 2 and all(t in (0, 1) for t in a) and sum(a[1:c-1]) >= 1
        profiles.append(a)
        if j < len(word):
            mask ^= 1 << word[j]
    guard = sum(1 << v for v in range(1, c-1)) | (1 << c)
    source = arcs_of(edges, sigma << m)
    def outgoing(arcs, shore):
        return sum(bool(shore >> u & 1) and not bool(shore >> v & 1) for u, v in arcs)
    assert outgoing(source, guard) == k
    bad_first = outgoing(arcs_of(edges, (sigma << m) ^ 1), ((1 << n)-1) ^ (1 << 1))
    assert bad_first == k-1
    suffix = [k*i for i in range(1, c-1)]
    naive_end = sigma << m
    for eid in suffix:
        naive_end ^= 1 << eid
    assert outgoing(arcs_of(edges, naive_end), guard) == k-1
    return dict(**control, n=n, m=m, q=1, initial_internal_mask=0,
                target_endpoint=c-1, source_guard_shore=guard, physical_word=word,
                final_full_mask=mask, core_prefix_profiles=profiles,
                blocked_first_edge=0, blocked_first_shore=((1 << n)-1) ^ (1 << 1),
                forbidden_guard_donor_word=suffix, forbidden_guard_donor_final_mask=naive_end,
                single_packet_entry_exists=False)


def run():
    archived = json.loads((ROOT / 'root_entry_H2_certificate.json').read_text(encoding='utf-8'))
    controls = [{key: item[key] for key in ('name', 'k', 'c', 'h', 'outer', 'sigma')}
                for item in archived['finite_controls']]
    screen = json.loads((ROOT / 'unshadowed_entry_H3_screen.json').read_text(encoding='utf-8'))
    controls += [dict(name=f'no_shadow_screen_{i}', **{key: item[key]
                  for key in ('k', 'c', 'h', 'outer', 'sigma')}) for i, item in enumerate(screen['examples'])]
    witness = json.loads((ROOT / 'unshadowed_entry_H3_zero_vertex_screen.json').read_text(encoding='utf-8'))['failure']
    controls.append(dict(name='positive_unsaturated_frontier', **{key: witness[key]
                        for key in ('k', 'c', 'h', 'outer', 'sigma')}))
    controls += [family(2, 5), family(2, 7), family(3, 6)]
    totals, finite = Counter(), []
    for item in controls:
        finite.append(verify_control(item, totals))
        print(json.dumps(dict(control=item['name'], stats=finite[-1]['stats'])), flush=True)
    families = [family_word(family(k, c)) for k, c in [(2, 5), (3, 6), (7, 10), (20, 23), (50, 53)]]
    result = dict(status='PASS', scope='finite checks of H3 structure and physical words; universal proofs in H3 note',
                  program_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
                  input_H2_certificate_sha256=hashlib.sha256((ROOT/'root_entry_H2_certificate.json').read_bytes()).hexdigest(),
                  stats=dict(totals), finite_controls=finite, saturated_gate_family_controls=families)
    (ROOT / 'unique_guard_H3_certificate.json').write_text(json.dumps(result, indent=2), encoding='utf-8')
    print(json.dumps(dict(status=result['status'], stats=result['stats'], family_controls=len(families))), flush=True)


if __name__ == '__main__':
    run()
