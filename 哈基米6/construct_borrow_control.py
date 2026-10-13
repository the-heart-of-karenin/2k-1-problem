"""Construct the analytic five-letter borrowed-background control."""
from pathlib import Path
from hashlib import sha256
import json

ROOT = Path(__file__).resolve().parent
k, n, r = 2, 13, 13
edges = []
for i in range(n):
    edges.append(dict(id=f'H_step1_{i}', u=i, v=(i+1) % n, kind='H'))
for i in range(n):
    edges.append(dict(id=f'H_step2_{i}', u=(i+2) % n, v=i, kind='H'))
for i in range(n):
    u, v = (i, r) if i in [3, 4, 5, 6, 7] else (r, i)
    edges.append(dict(id=f'E_port_{i}', u=u, v=v, kind='E'))
helper = 2*n
cycle = [0, 1, n]
word = [helper]+cycle+[helper]
cert = dict(status='CONSTRUCTED', main_status='OPEN',
            source_sha256=sha256(Path(__file__).read_bytes()).hexdigest(),
            regularization_used=False, orientation_component_search_used=False,
            k=k, n_core=n, n_vertices=n+1, edges=edges,
            source_mask=0, target_mask=sum(1 << i for i in cycle),
            word=word, commercial_prefix=[helper], directed_core_cycle=cycle,
            root_anchor=0,
            connector_positions=[2*n, 2*n+3, 2*n+1, 2*n+2],
            connector_orientation_mask=1 << helper,
            expected_beta=0, expected_undirected_strength=5,
            expected_quotient_root_out=5, expected_quotient_root_in=8,
            scope='One supplied balanced certificate on a critical-degree far state; not certificate-existence proof')
(ROOT/'borrow_control_certificate.json').write_text(
    json.dumps(cert, ensure_ascii=False, indent=2), encoding='utf-8')
print(json.dumps(dict(status='CONSTRUCTED', letters=len(word))))
