"""Record this independent workspace without editing the original frontier."""
from pathlib import Path
import hashlib
import json

OUT = Path(__file__).resolve().parent
audit = json.loads((OUT / "protective_environment_independent_audit.json").read_text(encoding="utf-8"))
assert audit["status"] == "PASS"
new_audit = json.loads((OUT / "synchronized_lobes_independent_audit.json").read_text(encoding="utf-8"))
assert new_audit["status"] == "PASS"
assert hashlib.sha256((OUT / "synchronized_lobes_certificate.json").read_bytes()).hexdigest() == new_audit["certificate_sha256"]
references = json.loads((OUT / "参考入口源_SHA256.json").read_text(encoding="utf-8"))
mutable_entries = {
    "2k+1/研究启动必读_方法与停止规则_2026-10-12.md",
    "2k+1/研究续接_2026-10-13_结果172进行中.json",
}
entry_updates = []
unchanged = 0
for name, sha in references.items():
    current = hashlib.sha256((OUT.parent / name).read_bytes()).hexdigest()
    if current == sha:
        unchanged += 1
    else:
        assert name in mutable_entries, f"A proof/reference source changed: {name}"
        entry_updates.append({"path": name, "initial_sha256": sha,
                              "current_sha256": current})

original_state = json.loads((OUT.parent / "2k+1/研究推进状态_2026-10-13_结果171.json").read_text(encoding="utf-8"))
for name, sha in original_state["source_hashes"].items():
    assert hashlib.sha256((OUT.parent / "2k+1" / name).read_bytes()).hexdigest() == sha
latest_state = json.loads((OUT.parent / "2k+1/研究续接_2026-10-13_结果172进行中.json").read_text(encoding="utf-8"))
assert latest_state["latest_formally_recorded_result"] == 171
new_record = "2k+1/" + latest_state["current_derivation_record"]
entry_note = {
    "date_local": "2026-10-13",
    "mutable_entry_updates": entry_updates,
    "latest_additional_record_read": new_record,
    "latest_record_sha256": hashlib.sha256((OUT.parent / new_record).read_bytes()).hexdigest(),
    "result171_registered_source_hashes_checked": len(original_state["source_hashes"]),
    "result171_registered_sources_unchanged": True,
    "original_frontier": 171,
    "interpretation": "The live startup entries advanced during this work; their initial snapshots remain preserved and are not mislabeled as unchanged. All this task's writes remain in 哈基米5.",
}
(OUT / "共享入口更新核对_2026-10-13.json").write_text(
    json.dumps(entry_note, ensure_ascii=False, indent=2), encoding="utf-8")

files = [
    "研究结果172候选_保护子环境与无近层商图_2026-10-13.md",
    "README.md", "verify_protective_environment.py",
    "audit_protective_environment.py", "record_checkpoint.py",
    "protective_environment_certificate.json",
    "protective_environment_independent_audit.json", "参考入口源_SHA256.json",
    "共享入口更新核对_2026-10-13.json",
    "研究结果172候选补充_多瓣同步阈值与全部高层合流_2026-10-13.md",
    "verify_synchronized_lobes.py", "audit_synchronized_lobes.py",
    "synchronized_lobes_certificate.json", "synchronized_lobes_independent_audit.json",
]
state = {
    "date_local": "2026-10-13", "timezone": "Asia/Shanghai",
    "workspace": str(OUT),
    "main_status": "OPEN", "regularization_used": False,
    "original_formal_frontier": 171, "original_formal_document": 261,
    "independent_candidate_result": 172, "independent_candidate_document": 262,
    "registered_in_original_number_table": False,
    "candidate_subresults": ["172.1", "172.2", "172.3", "172.4"],
    "status": "SYNCHRONIZED_LOBE_ALL_HEIGHT_FIBRES_AND_HISTORY_LIFTING_PROVED_GENERAL_ENTRANCE_OPEN",
    "startup_required_read": "../2k+1/研究启动必读_方法与停止规则_2026-10-12.md",
    "startup_latest_state_read": "../2k+1/研究续接_2026-10-13_结果172进行中.json",
    "current_record": "研究结果172候选补充_多瓣同步阈值与全部高层合流_2026-10-13.md",
    "previous_record": files[0],
    "latest_shared_record_read": new_record,
    "proven_conditional_interface": [
        "Any H-only word legal on a physical subenvironment containing all H, with the full commercial orientation frozen and legal, is legal on the original G.",
        "For maximal surplus q=k, a currently legal near protective subenvironment supplies exact H-only confluence and entry from a globally far source to any Eulerian H representative.",
        "For k=2 the protective near slice confluence works for every induced SD surplus by 171.2.",
        "Given MAIN(G/C), existence of a near protective subenvironment replaces existence of a near full commercial state for confluence of all Eulerian H canonical extensions.",
        "172.3: arbitrary induced SD q>=1, arbitrary k,n,lobe count and port multiplicities; each actual lobe internally k-strong, each core vertex has the same d_i ports to lobe i, and all S_i(C)/d_i belong to a common integer unit interval. Then all mixed cuts are protected by the point box and the entire frozen H fibre is exactly connected in <=(n+1)m_H flips.",
        "For q=k under 172.3, every actual far source can enter any specified Eulerian H representative, then follow arbitrary legal commercial histories without the synchronization condition.",
        "172.4: any given legal commercial history whose prefixes retain the actual lobe protection and synchronization can be lifted letter-for-letter to an arbitrary specified legal end extension, with only H preparations inserted.",
        "The arbitrary-k two-lobe source outside all natural protective slices is repaired by two actual H reversals; no external identity changes are required for this family.",
    ],
    "general_obstructions": [
        "For every k>=2,t>=2, a simple nonOSP graph with a maximal-surplus clique core and t clique lobes has full commercial root out/in >=kt in every legal orientation; thus it has no near root state.",
        "For every k>=2, a legal source in the two-lobe family can restrict illegally to both natural protective lobes, with core vertex out k-1 in each.",
        "For every k>=2, a k-parallel cycle on 2k+2 vertices with two uniform singleton lobes, S totals k and k+2, has a legal commercial orientation and a point-box H assignment whose mixed cut has out k-1. Without synchronized thresholds the box characterization is false; not a MAIN counterexample.",
    ],
    "not_claimed": [
        "universal supply of a currently legal protective subenvironment",
        "arbitrary far-source entry to Eulerian H",
        "all high frozen fibres connected", "AC", "MAIN",
        "new MAIN proof for the illustrative graph family",
        "actual synchronization from every initially unsynchronized source",
        "universal supply of individually k-strong lobes",
        "uniform port geometry for arbitrary original graphs",
    ],
    "audit_status": audit["status"], "audit_counts": audit["counts"],
    "synchronized_lobes_audit_status": new_audit["status"],
    "synchronized_lobes_audit_counts": new_audit["counts"],
    "synchronized_lobes_constructed_branches": new_audit["constructed_branch_counts"],
    "reference_sources_unchanged": unchanged,
    "mutable_entry_updates": entry_updates,
    "result171_registered_sources_unchanged": True,
    "all_426_formal_sources_reaudited": False,
    "orientation_component_enumeration": False,
    "new_background_search_started": False,
    "stop_rule_applied": True,
    "stop_position": "General all-height synchronization theorem and actual interval words completed; no universal source entry to its current protection/synchronization conditions. No finite case expansion.",
    "next_general_obligation": "An actual macrostep synchronizing lobe port thresholds from arbitrary sources while protecting all mixed cuts, with a global termination principle; or an entry mechanism handling nonuniform ports and lobes not currently k-strong.",
    "source_hashes": {name: hashlib.sha256((OUT / name).read_bytes()).hexdigest()
                      for name in files},
}
(OUT / "研究续接_哈基米5_2026-10-13.json").write_text(
    json.dumps(state, ensure_ascii=False, indent=2), encoding="utf-8")
print(json.dumps({"status": "RECORDED", "candidate": 172,
                  "new_subresults": ["172.3", "172.4"],
                  "original_frontier": 171, "main_status": "OPEN",
                  "reference_hashes_unchanged": unchanged,
                  "mutable_entry_updates": len(entry_updates)}, ensure_ascii=False))
