"""Write this directory's handoff and provenance without changing the original research."""
from datetime import datetime, timedelta, timezone
import hashlib
import json
from pathlib import Path

ROOT = Path(__file__).resolve().parent
MAIN = ROOT.parent / "2k+1"


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main():
    main_state_path = MAIN / "研究续接_2026-10-13_结果172进行中.json"
    main_state = json.loads(main_state_path.read_text(encoding="utf-8-sig"))
    audit_path = ROOT / "residual_width_audit.json"
    audit = json.loads(audit_path.read_text(encoding="utf-8"))
    assert audit["status"] == "PASS"
    assert audit["controls_sha256"] == digest(ROOT / "residual_width_controls.json")
    artifact_names = [
        "README.md",
        "研究结果172候选_余量阈值以下的残余宽度与原割唯一实现_2026-10-13.md",
        "研究报告_一般推广与下一执行关口_2026-10-13.md",
        "build_residual_width_controls.py", "audit_residual_width_controls.py",
        "residual_width_controls.json", "residual_width_audit.json",
        "record_research_checkpoint.py",
    ]
    source_names = [
        "研究启动必读_方法与停止规则_2026-10-12.md",
        "研究续接_2026-10-13_结果172进行中.json",
        "研究结果170_双单位入守卫与任意端口尾准备_2026-10-12.md",
        "研究结果171_最大余量核的最小割递归与通用商代表_2026-10-13.md",
        "研究探索172_高层代表入口与静态近核选择障碍_2026-10-13.md",
        "研究探索172_最小割窄面与回路构造保持_2026-10-13.md",
        "研究探索172_指定端口删除的刚性割链_2026-10-13.md",
        "研究结果101_严格核内平行束合流与全部副本供给_2026-10-09.md",
    ]
    state = {
        "date": "2026-10-13",
        "recorded_local": datetime.now(timezone(timedelta(hours=8))).isoformat(timespec="seconds"),
        "status": "GENERAL_STRUCTURAL_EXTENSION_AND_SHARP_FAR_AUGMENTATION_OBSTRUCTION_RECORDED",
        "main_status": "OPEN", "regularization_used": False,
        "candidate_result": 172, "candidate_document": 262,
        "original_formal_registration_changed": False,
        "latest_formally_recorded_result_observed": main_state["latest_formally_recorded_result"],
        "original_main_state_last_updated": main_state["last_updated_local"],
        "new_files_directory_authorized_by_latest_user": "哈基米7",
        "no_original_research_files_written_by_this_run": True,
        "proof": artifact_names[1], "route_report": artifact_names[2],
        "general_results": [
            "任意SD余量q、任意合法商高度：min(mu_sigma(X),q)=min(min_Z delta_G(X+Z)-2k,q)。",
            "mu<q的原割完成及两向有向极小完成均唯一，物理支撑随合法商历史固定。",
            "q>=2：mu=1 iff某原2k+1最小割具有该核trace；固定核根后层状，最多2|C|-3份无向split。",
            "指定非H身份g商删后仍k强：任意q>=1的删g零宽岸准确来自跨g的原临界割，唯一完整岸组成链，长度<=|C|-1。",
            "受保护E-g弱分量的实际首次g提升接口，可用旧5静态删g扩张推广到所有诱导SD余量；较小MAIN/具体P连通和当前分量k强仍是条件。",
        ],
        "sharp_general_obstructions": [
            "q=1可在原lambda=2k+2、双向far商态出现mu=1虚拟窄面；同一图两份far商态mu可为1和2。",
            "mu=2<q的唯一原割完成可以交叉，不能把所有低宽度岸当层状。",
            "任意k>=2,t>=k的双端口奇圈：lambda=2k+2、商双向far、全部mu>=2，冻结外部的全严格残余目标仍因核点总出度差1而不存在。",
        ],
        "audit": {
            "status": audit["status"], "prescribed_cases": len(audit["cases"]),
            "literal_directed_full_cut_rows": audit["literal_directed_full_cut_rows"],
            "literal_undirected_full_cut_rows": audit["literal_undirected_full_cut_rows"],
            "constructor_not_imported_by_auditor": True,
            "universal_quantifiers_from_analytic_proof": True,
            "orientation_state_enumeration": False,
        },
        "background_search_started": False, "subagents_spawned": False,
        "not_proved": [
            "任意far源到Eulerian H或近层", "任意源的无条件端口准备", "一般冻结纤维连通",
            "动态获得受保护E-g弱分量", "AC构造保持", "AC", "MAIN",
        ],
        "next_general_method_obligation": "原割树/链的实际支付与宽割保护同一宏步完成，并给辅助归还及严格终止；或提出承担完整背景阈值和物理提升的归约。",
        "stop_rule_applied": "没有新的无条件执行/归约机制，未转为树形、链长、核点数或余量上限的有限分类。",
        "resume_required_read": [
            "../2k+1/研究启动必读_方法与停止规则_2026-10-12.md",
            "该启动必读指向的最新主线状态", artifact_names[1], artifact_names[2],
        ],
        "artifact_sha256": {name: digest(ROOT / name) for name in artifact_names},
        "read_only_sources_sha256_at_checkpoint": {name: digest(MAIN / name) for name in source_names},
    }
    target = ROOT / "研究续接_哈基米7_2026-10-13.json"
    target.write_text(json.dumps(state, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")
    print(json.dumps({"status": state["status"], "main_status": state["main_status"],
                      "candidate_result": state["candidate_result"], "audit": state["audit"]["status"]}))


if __name__ == "__main__":
    main()
