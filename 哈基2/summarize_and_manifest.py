from pathlib import Path
from hashlib import sha256
import json

BASE = Path(__file__).resolve().parent
d = json.loads((BASE / "exact_results.json").read_text(encoding="utf-8"))
a = json.loads((BASE / "independent_audit.json").read_text(encoding="utf-8"))
b = json.loads((BASE / "external_budget_results.json").read_text(encoding="utf-8"))
c = json.loads((BASE / "nonosp_budget_results.json").read_text(encoding="utf-8"))
assert a["status"] == b["status"] == c["status"] == "PASS"
for name, expected in a["sha256"].items():
    assert sha256((BASE / name).read_bytes()).hexdigest() == expected, name
assert sha256((BASE / "check_external_budget.py").read_bytes()).hexdigest() == b["source_sha256"]
for name, expected in c["sha256"].items():
    assert sha256((BASE / name).read_bytes()).hexdigest() == expected, name
fixture = json.loads((BASE / "nonosp_source_input.json").read_text(encoding="utf-8"))
assert sha256(Path(fixture["source"]).read_bytes()).hexdigest() == fixture["source_sha256"]
review_path = BASE / "review_results.json"
if review_path.exists():
    review = json.loads(review_path.read_text(encoding="utf-8"))
    assert review["status"] == "PASS"
    for name, expected in review["sha256"].items():
        assert sha256((BASE / name).read_bytes()).hexdigest() == expected, name

graphs = d["graphs"]
report = ["# 精确实验报告", "", "2026-10-11。以下为指定输入的有限核验，不是MAIN的普遍证明。", "",
          "## 1. 完整主枚举", "",
          f"十个指定图合计遍历 {sum(g['orientations_examined'] for g in graphs):,} 份物理方向，得到 {sum(g['vertex_legal'] for g in graphs):,} 份顶点合法态及 {sum(g['fully_legal'] for g in graphs):,} 份完整合法态。各输入的完整合法图均为一个分量。平行边按列表位置分别计身份。", "",
          "| 输入名 | n | k | m | λ | 顶点合法 | 完整合法 | 坏区域数 | 最大坏区域 | 无一步修复的坏态 |",
          "|---|---:|---:|---:|---:|---:|---:|---:|---:|---:|"]
for g in graphs:
    report.append(f"| {g['name']} | {g['n']} | {g['k']} | {g['m']} | {g['lambda']} | {g['vertex_legal']:,} | {g['fully_legal']:,} | {g['bad_components']} | {g['largest_bad_component']:,} | {g['bad_vertices_without_legal_neighbor']:,} |")
report += ["", "主程序使用严格的稀疏侧省略规则：若一个岸X满足e(X)≤k(|X|−1)，顶点出入度下界已经同时保护该岸的出入割。因此只有两侧均严格稠密的割需要额外检查；程序逐个顶点子集建立这一准确行集。它不是抽样检查割。", "",
           "## 2. 根封顶下降候选", "",
           "候选允许全部边实际准备，要求从当前根高度r到静态最小值η，并且每个前缀根高度不超过r。没有要求高度逐步单调、根星固定或保持目标外边中途不动。", "",
           f"共 {sum(g['root_cap_queries'] for g in graphs):,} 份根态查询无失败，其中 {sum(g['root_cap_nontrivial_queries'] for g in graphs):,} 份查询的封顶值严格低于该根全局最高层。最高层的查询因已知当前输入整体连通而自动成立，不能作为相同强度的证据。", "",
           "后续审查确认：上述十图所有根的η均等于k，没有覆盖η>k根下降。新补的四图检验与可信度调整见[审查实验说明](审查实验说明_2026-10-11.md)及[路线审查报告](路线审查报告_2026-10-11.md)。", "",
           "主方法是按高度激活合法物理状态及其真实单翻邻边，记录每个诱导分量能够达到的最小高度。正则2k+1度根只有两层，较高层封顶是完整环境，此类根不纳入主候选计数。", "",
           f"独立程序重做五个m≤18输入的全部割和连通分量，并用全部η层作为多源进行封顶洪泛，核对 {sum(t['root_cap_queries'] for t in a['audits']):,} 份查询，其中 {sum(t['root_cap_nontrivial_queries'] for t in a['audits']):,} 份为非最高层查询。m>18输入的完整枚举数量由C++主实现承担，没有声称它们全部由第二实现重复。", "",
           "## 3. 过强断言的物理见证", ""]
h = graphs[0]["hamming_trap"]
report += [f"K6、k=2：源位码 {h['start']}，目标位码 {h['target']}，Hamming差异 {h['hamming']}；源态中每份目标差异身份都被阻挡。完整最短词为 `{h['shortest_word']}`，长度 {len(h['shortest_word'])}。身份0临时借用并归还。全部前缀的完整割及最短距离由独立实现核对。这是目标身份限制失败，不是原题反例。", "",
           "八点two_dense_K4_odd和十点two_K5_with_matching给顶点合法、割非法、没有任何一步完整合法修复的状态。源位码分别8383210、33476531；独立证书逐份重算所有物理邻居的最小出割。它否定一步修复入口，支持研究整个坏区域。", "",
           "root_shadow_control_k2：源位码3867、根指出4，所有当前outgoing根身份均不可翻回；词 `[8, 0, 9, 1]` 先动非根身份，根高度依次4、4、3、3、2，全割合法。它是148控制的本轮独立重核，不登记成新结果。", "",
           "## 4. η>k的外部预算", "",
           f"六点OSP控制：k={b['k']}、q={b['q']}、η={b['eta']}、j={b['j']}，没有R=k层。穷尽1000份最小层商签名及32份内部物理方向，检查 {b['vertex_legal_internal_assignments']:,} 份顶点合法内部方向，全为完整合法；重算 {b['identity_rows']:,} 条四角恒等式。", "",
           f"端口部分只抽取明确的 {b['paid_signature_sample']} 份签名，检查 {b['paid_port_cubes']:,} 份满足扣款条件的端口立方体、{b['paid_cube_states']:,} 份状态；合计 {b['full_outcut_rows']:,} 行完整出割，保存 {len(b['words'])} 份准确返回词。这是账本控制，六点输入原本已在OSP可解范围内。", "",
           f"20点非OSP控制：读取146的一份实际源态，k=2、λ=5、q=1、η=3、j=1。全部 {c['identity_rows']:,} 行四角恒等式通过；筛选全部7份incoming身份的子集，得到 {c['activity_sets_satisfying_B3']} 组满足B3的活动集合。四份选定立方体的 {c['distinct_physical_prefix_states_full_cut_checked']} 份不同物理前缀，及原始源态，合计重算 {c['full_cut_rows']:,} 行完整割，全部合法；四份六步词准确归还活动端口。", "",
           "B2是起点的精确合法条件。后续审查修正B3的量词：固定内部方向、要求任意排列全部前缀合法时，B3连同核点容量及终商态是必要且充分条件；若只要求某个顺序，B3仅充分。新四点见证及删弧等价见路线审查报告。两项原实验都没有证明任意源态能够实际进入满足扣款条件的profile域。", "",
           "## 5. 重跑与材料边界", "",
           "从本文件所在目录运行：", "", "```powershell", "g++ -std=c++20 -O3 -march=native -Wall -Wextra exact_routes.cpp -o exact_routes.exe", ".\\exact_routes.exe exact_results.json", "python verify_exact.py", "python check_external_budget.py", "python check_nonosp_budget.py", "python summarize_and_manifest.py", "```", "",
           "编译时工作目录设为本目录，使用ASCII文件名，避免部分Windows编译器的Unicode输出路径问题。Python程序只需标准库；本轮没有安装额外依赖。", "",
           "位码约定：exact_results中bit1表示边列表存储的u→v；nonosp_budget中bit1表示反转保存的初始有向弧。不要跨证书直接复用整数位码。", "",
           "完整主枚举只覆盖上述十个输入；20点程序只覆盖指定源态及所列活动集合/立方体。解析正文承担一般账本结论，有限计数不外推任意k、任意图阶或一般MAIN。", ""]
(BASE / "精确实验报告_2026-10-11.md").write_text("\n".join(report), encoding="utf-8")

source_names = ["README.md", "原定理综合研究与唯一剩余接口.md", "研究接续与工作约定_2026-10-07.md",
                "research_path_only_universal_reduction_2026-10-07.md",
                "research_interval_frozen_peeling_components_2026-10-07.md",
                "研究结果123_核心交接的双紧岸完全刻画与最小割树_2026-10-10.md",
                "研究结果146_共同根紧层的树缺额与非OSP核供给反例_2026-10-10.md",
                "研究结果148_极小坏岸祖先与逐端口共同保护_2026-10-10.md",
                "研究深思记录_2026-10-10_全局供给与根极值.md",
                "sd_global_anchor_independent_audit_2026-10-10.json"]
sources = []
for name in source_names:
    p = BASE.parent / "2k+1" / name
    sources.append({"path": str(p), "bytes": p.stat().st_size, "sha256": sha256(p.read_bytes()).hexdigest()})
outputs = [{"name": p.name, "bytes": p.stat().st_size, "sha256": sha256(p.read_bytes()).hexdigest()}
           for p in sorted(BASE.iterdir(), key=lambda p: p.name)
           if p.is_file() and p.name != "研究资料清单_SHA256.json"]
manifest = {"date": "2026-10-11", "folder": str(BASE), "main_status": "OPEN",
            "sources_read_only": sources, "outputs": outputs,
            "note": "Manifest excludes itself; source hashes record the files used, not an independent re-audit of every old proof."}
(BASE / "研究资料清单_SHA256.json").write_text(json.dumps(manifest, ensure_ascii=False, indent=2), encoding="utf-8")
print("reports and source/output hashes verified", len(outputs), flush=True)
