"""Save the branch frontier; do not register or alter primary research sources."""
from pathlib import Path
from hashlib import sha256
from datetime import datetime
from zoneinfo import ZoneInfo
import json

ROOT = Path(__file__).resolve().parent
PRIMARY = ROOT.parent/'2k+1'


def digest(path):
    return sha256(path.read_bytes()).hexdigest()


def main():
    audit = json.loads((ROOT/'controls_independent_audit.json').read_text(encoding='utf-8'))
    borrow = json.loads((ROOT/'borrow_control_independent_audit.json').read_text(encoding='utf-8'))
    integrity = json.loads((ROOT/'source_integrity.json').read_text(encoding='utf-8'))
    assert audit['status'] == borrow['status'] == integrity['status'] == 'PASS'
    assert audit['certificate_sha256'] == digest(ROOT/'controls_certificate.json')
    assert audit['source_sha256'] == digest(ROOT/'audit_controls.py')
    assert borrow['certificate_sha256'] == digest(ROOT/'borrow_control_certificate.json')
    assert borrow['source_sha256'] == digest(ROOT/'audit_borrow_control.py')
    sources = ['README.md',
               '研究结果172候选_背景割供给与高层欧拉入口_2026-10-13.md',
               '研究结果172候选_续_商平衡背景与单圈准确借还_2026-10-13.md',
               '研究发散_无近层商与零背景割障碍_2026-10-13.md',
               'construct_controls.py', 'audit_controls.py',
               'controls_certificate.json', 'controls_independent_audit.json',
               'construct_borrow_control.py', 'audit_borrow_control.py',
               'borrow_control_certificate.json', 'borrow_control_independent_audit.json',
               'check_source_integrity.py', 'source_integrity.json', Path(__file__).name]
    state = dict(
        date='2026-10-13', last_updated_local=datetime.now(ZoneInfo('Asia/Shanghai')).isoformat(),
        work_directory=str(ROOT), user_directly_authorized_sibling_work_directory=True,
        main_status='OPEN', regularization_used=False,
        latest_formally_recorded_primary_result=171, next_primary_result=172,
        candidate_result=172, candidate_document=262, candidate_registered_in_primary=False,
        status='CONDITIONAL_GENERAL_ENTRANCE_AND_ACCURATE_CIRCLE_RETURN_PROVED_UNIVERSAL_SUPPLY_OPEN',
        read_primary_current_record='研究探索172_指定端口删除的刚性割链_2026-10-13.md',
        primary_formal_state_sha256=digest(PRIMARY/'研究推进状态_2026-10-13_结果171.json'),
        proved_conditionally={
            '172.1': 'q=k；冻结背景β>=s>=1、当前核内至少k-s弧强时，真实H-only入口到任意指定欧拉H；界k n^3+m_H，s=k时直接差异翻。',
            '172.2': '每份H的2k最小割岸均f>=1时，任意两欧拉H代表冻结背景逐圈准确合流；不要求全部trace β>=1。',
            '172.3': '商平衡非H证书从圈起点到达全部圈点，且商实际词已供应时，执行商前缀、反圈、倒放商前缀；全部辅助准确返回，界2|W|+|J|。'},
        proof_inputs={
            'internal_augmentation': 'Ito et al. arXiv:2110.11585 Theorem 1；已核对作者PDF。',
            'eulerian_completion': '主线research_global_scope.md §2/2.1全局物理多面体整数性，商平衡固定子图+剩余1/2分数完成。',
            'commercial_path': '172.3须实际给定商词/具体商连通性/较小MAIN；不存在免费静态入口。'},
        general_obstructions={
            'no_universal_near_state': '根删后的t块分划给根出入>=k t-e(P)。三个独立外点的任意规模简单非OSP阈值族，指定SD核商没有任何近层定向。',
            'split_budget_not_automatic': '任意素数n>=13的k2同族存在完整2强、β=1、内部强度0的源；互补割供给不能推出两个统一最小值相加达k。',
            'balanced_certificate_not_universal': 'k平行圈加一根端口族的所有有向简单H圈均全支撑；每核点背景度1，商平衡到达证书不存在，而圈内拓扑序交错仍合法。'},
        not_proved=['任意far源到欧拉H', '全部单向零背景面的无条件宏步',
                    '任意背景的欧拉代表环境合流', '一般商平衡证书供给',
                    '任意far冻结纤维', 'AC', 'MAIN'],
        finite_controls={
            'original_controls': 3, 'borrow_control': 1,
            'forward_physical_letters': audit['total_physical_letters']+borrow['physical_letters'],
            'complete_original_directed_cut_rows': audit['total_original_complete_directed_cut_rows']+borrow['original_complete_directed_cut_rows'],
            'audits': ['controls_independent_audit.json', 'borrow_control_independent_audit.json'],
            'status': 'PASS', 'no_orientation_component_search': True,
            'general_ito_algorithm_implemented': False,
            'universal_quantifiers_from_analysis_and_cited_theorems_not_samples': True},
        primary_preservation=integrity,
        further_run_stopped=True,
        stop_reason='已有一般条件机制，但从任意源获得供给/商平衡证书仍无普遍动态终止；一般反证排除把证书强加为必要条件。不扩大有限分类或重启大搜索。',
        source_hashes={name: digest(ROOT/name) for name in sources})
    (ROOT/'研究续接_2026-10-13.json').write_text(
        json.dumps(state, ensure_ascii=False, indent=2), encoding='utf-8')
    print(json.dumps(dict(status='PASS', candidate=172, primary_latest=171,
                         primary_sources_preserved=integrity['registered_sources_unchanged'],
                         letters=state['finite_controls']['forward_physical_letters'],
                         original_rows=state['finite_controls']['complete_original_directed_cut_rows'],
                         main_status='OPEN')))


if __name__ == '__main__':
    main()
