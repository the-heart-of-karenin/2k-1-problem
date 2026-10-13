"""Seal completed research artifacts and verify preserved dependency hashes."""
from pathlib import Path
import hashlib
import json

ROOT = Path(__file__).resolve().parent
SOURCE = ROOT.parent / '2k+1'


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def run():
    previous = json.loads((ROOT/'研究检查点_2026-10-11_H2.json').read_text(encoding='utf-8'))
    for name, digest in previous['output_sha256'].items():
        assert sha(ROOT/name) == digest, ('H2 archive changed', name)
    for name, digest in previous['dependencies_sha256'].items():
        assert sha(SOURCE/name) == digest, ('source dependency changed', name)
    # Preserve the exact original exploratory program corresponding to its hash.
    current = (ROOT/'probe_unshadowed_entry_H3.py').read_text(encoding='utf-8')
    old = current.replace("allowed &= ~sum(1 << v for v in range(c)\n                                       if a[v] == deg[v]-2*k and v != donor)",
                          "allowed &= ~sum(1 << v for v in range(c) if a[v] > 0 and v != donor)")
    old = old.replace("                  allowed_frontiers='originally_unsaturated_core_vertices',\n", '')
    old_bytes = old.encode('utf-8')
    historic = json.loads((ROOT/'unshadowed_entry_H3_zero_vertex_screen.json').read_text(encoding='utf-8'))
    assert hashlib.sha256(old_bytes).hexdigest() == historic['program_sha256']
    (ROOT/'probe_unshadowed_entry_H3_零前沿旧版.py.txt').write_bytes(old_bytes)
    names = ['unique_guard_H3_certificate.json', 'unique_guard_H3_independent_audit.json',
             'unlock_pair_H3_certificate.json', 'unlock_pair_H3_independent_audit.json']
    reports = {name: json.loads((ROOT/name).read_text(encoding='utf-8')) for name in names}
    assert all(report['status'] == 'PASS' for report in reports.values())
    for cert_name, audit_name in [(names[0], names[1]), (names[2], names[3])]:
        assert reports[audit_name]['certificate_sha256'] == sha(ROOT/cert_name)
    artifacts = names+['研究结果_H3_唯一饱和守卫与双单位接力.md',
                      'verify_unique_guard_H3.py', 'audit_unique_guard_H3.py',
                      'verify_unlock_pair_H3.py', 'audit_unlock_pair_H3.py',
                      'probe_trapped_ports_H3.py', 'trapped_ports_H3_probe.json',
                      'probe_unshadowed_entry_H3.py', 'unshadowed_entry_H3_screen.json',
                      'unshadowed_entry_H3_zero_vertex_screen.json',
                      'probe_unshadowed_entry_H3_零前沿旧版.py.txt',
                      'probe_saturated_guard_H3.py', 'saturated_guard_H3_architecture_screen.json']
    checkpoint = dict(
        date='2026-10-11', main_status='OPEN', general_SD_contraction_status='OPEN',
        H3_analytic_status='PROVED under stated hypotheses',
        H3_main_verification='PASS', H3_independent_verification='PASS',
        H3_unlock_pair_verification='PASS', H3_unlock_pair_independent_verification='PASS',
        advances=[
            'At R=k+1, at most one positive mixed-guard point excludes a fixed zero-surplus outgoing core endpoint',
            'A guard intersection containing the target, or an unguarded path with unsaturated frontiers, gives <=n-1 H flips',
            'Remaining one-packet obstruction is a sole saturated guard point a=mu=1 dominating every other positive-to-target path; guard trace has >=2 vertices',
            'An arbitrary-k k-fold-path control realizes this obstruction, but a two-unit relay of n-1 physical H flips succeeds',
            'Any commercial exterior unlock pair [h,g] lifts if the physical g endpoint is first prepared; H3 conditional entry supplies this from arbitrary sources outside the residual gate'
        ],
        not_claimed=[
            'General root-k+1 internal entry through every saturated guard',
            'General no-shadow exit',
            'Connectivity of every frozen non-H fibre',
            'A single-packet path for every outgoing endpoint',
            'MAIN or general SD contraction'
        ],
        next_attack='Two-unit service through the unique saturated gate with simultaneous control of newly tight mixed cuts and a terminating measure',
        other_remaining=['General R>=k+2 entry', 'Root minimum >k', 'Other no-shadow unlock supply', 'Global termination'],
        finite_constructor=reports[names[0]]['stats'], finite_independent=reports[names[1]]['stats'],
        unlock_pair_constructor=reports[names[2]]['stats'], unlock_pair_independent=reports[names[3]]['stats'],
        rejected_candidate=dict(file='trapped_ports_H3_probe.json', reason='quotient shore mask 7 has outgoing 1<k=2; no legal expansion'),
        exploratory_screen=dict(file='unshadowed_entry_H3_screen.json', status='FINITE_SCREEN_ONLY',
                                independently_replayed=False),
        preserved_H2_outputs_and_source_dependencies='All recorded SHA256 values verified unchanged',
        dependencies_sha256={'研究结果_H2_指定降根端口的任意源态入口.md':sha(ROOT/'研究结果_H2_指定降根端口的任意源态入口.md'),
                             '2k+1/研究结果94_严格稠密核小边界实际收缩_2026-10-08.md':
                             sha(SOURCE/'研究结果94_严格稠密核小边界实际收缩_2026-10-08.md')},
        output_sha256={name: sha(ROOT/name) for name in artifacts})
    (ROOT/'研究检查点_2026-10-11_H3.json').write_text(json.dumps(checkpoint, ensure_ascii=False, indent=2), encoding='utf-8')
    inventory = {p.name:dict(bytes=p.stat().st_size, sha256=sha(p))
                 for p in sorted(ROOT.iterdir(), key=lambda p:p.name)
                 if p.is_file() and p.name != '资料文件清单_SHA256.json'}
    (ROOT/'资料文件清单_SHA256.json').write_text(json.dumps(inventory, ensure_ascii=False, indent=2), encoding='utf-8')
    print(json.dumps(dict(status='PASS', checkpoint='研究检查点_2026-10-11_H3.json', files=len(inventory),
                          preserved_H2_and_source=True), ensure_ascii=False))


if __name__ == '__main__':
    run()
