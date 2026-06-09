# DOCTRINE — 终局战役：Ch13 / Ch35 / Ch36 → 40/40

日期：2026-06-09。分支 `zinan-overnight`（canonical，superset of main）。
uisai1 离线；build server = uisai2（git 经 Mac 中继）。
0 个真 sorry——三章的"开放"全部是条件式定理的命名残差 Prop；战役目标 = 把残差逐一变成无条件定理。

## 总目标（一句话）

把 Ch13、Ch35、Ch36 的全部残差关成 clean-3 无条件定理，使全书 40/40 通过 audit（0 sorry / 0 axiom / 全 repo build / #print axioms 干净 / 语义忠实）。

## 编排原则

三章数学内核相互独立 → 三线并行（一文件一写者）。Codex/Opus worker 在 uisai2 跑 `lake env lean` 自检；我做连接组织 + 独立复核 + commit。ChatGPT Pro（pbook channel）承担 Ch13 手术与 Ch36 移植的前沿设计轮。每条 avenue 干到 terminal verdict（成功 / 反例 / 严格证伪），不估时、不中途换道。

---

## Ch13（spherical SZ / FoldedFlatCutTransport）——真残差：fold 分支的 endpt ≤ endpt

**已判死**：支撑线路线的 interior-exclusion（exfalso）核心思想不可修复（FFCT10/15/16 三个同族假残差，全部 kernel-anchored）。FFCT9–15 平面引擎保留为独立定理，退出临界路径。
**正确方向**（RUN_LOG 2026-06-09 再续）：折叠缩短端距——在 stuck 点从 `stuckAtK_betweenness`/`flat_eq` 的折平数据 + SameSides/JointLe **真证** `endpt A ≤ endpt B`，不再排除。

- **(a) 折点吸收手术（主攻）**：折平时 A 在顶点 k 处退化 ≅ 少一顶点的 (n−1)-臂 A′（边长 sideLen k−1 ± sideLen k 视折向合并）；对 A′ 用已证 hinge 单调机器归纳得 endpt A′ = endpt A ≤ endpt B。
  前置：数值验证不等式方向在折叠构型族上恒成立（含 FFCT16 反例那类构型）。
  Terminal：`fold_branch_endpt_le` 无条件 clean-3，FoldedFlatCutTransport 全消费链重新接线 → Ch13 headline 无条件。
- **(b) TailFoldBetweenness 式数据提取**：若 (a) 的"合并边长"在球面上不闭合（spherical 三角不等式障碍），改走 tail 分支同款：从 Gram 符号 + ShortArc 数据直接走 `tail_witness_of_betweenness_inputs` 的内部版。
- **(c) ChatGPT Pro 设计轮**：(a)(b) 任一卡死即派 pbook 深想轮（带 FFCT16 反例 + stuckAtKData 字段全文），要"有限可查步骤地图"。
- **Fallback**：把 fold 分支单独隔离为一个新命名残差 + 证明其余全链无条件（诚实 CONDITIONAL-honest 收口），明确标注——仅当 (a)(b)(c) 全部有书面 terminal verdict。

## Ch35（Thomassen / 离散 Jordan，count route）——残差 2 个

`ZinanCh35CountRoute.lean`（11 个结果 clean-3）已把拓扑侧归约到唯一计数残差；torus anchor 证实计数 conjecturally genus-free。

- **(a) hsplits 计数界（主攻）**：`concatLen Ls + 2 ≤ 2·card(actualSplitFinset C Ls) + 2·C.len`。
  攻法 = 对每个 `faceCorr₂` 轨道做 run-decomposition（cutCapPhi2 逐点表：cap-entry iff φd ∈ {p_j,q_j}），seam-local SameCycle 证书沿 canonical cycle-list word；**注意 orchestrator 修正**：s ≥ (concatLen+2−2len)/2 可超过 len，split 必须同时从 ordinary-dart runs 取（K₄-sphere 要 4 > 3）。
  Terminal：hsplits 无条件 → count route 闭合。
- **(b) EndpointCapLink**（gateCompat' 连通侧，独立残差）：与 (a) 并行派 worker；图论性质，纯组合。
- **(c) 若 (a) 的证书构造卡死**：退回 stepDelta 望远镜的逐步守恒不等式（每步 split 计数下界），在 `ForcedSplits` 词上归纳。
- **Fallback**：sphere-only 版本（genus 0 假设显式化）诚实收口 + torus anchor 留作 conjecture 注记。

## Ch36（Art Gallery / 简单多边形 winding）——单一 Jordan 内核

残差图已收敛到一个内核（四个等价形式）：`EarCutData.earDeletedExterior` ≡ RayCrossingAlternation ≡ EarDeletedWindingZero ≡ LocalJumpSeed。

- **(a) mono_theta 移植（主攻，残差图推荐）**：把 `ZinanFFCT9.mono_theta` 的单调 branch-cut 角移到位置向量 (∂P − x)，按 crossTau 排序；eSign 交替由单调挤出（ray-direction genericity 公理已排掉 antipodal care-point）。
  Bricks（顺序）：① `thetaPos` def + 单调引理；② 交替引理；③ 经已证桥 `windCross_mem_of_alternation → earDeletedExterior_of_seed` 接线。
  Terminal：earDeletedExterior 无条件 → artGallery_strict_attach 链条闭合。
- **(b) 若 mono_theta 在位置向量上不单调**（反例出现）：换 RayCrossingAlternation 形式直接做平面 ray-crossing 奇偶（同一内核的组合形式，不需要 winding API）。
- **(c) (B) 复解析战役**（Homotopy.Lifting + Cauchy + ear-escape）：已设计未启动，greenfield winding API——仅当 (a)(b) 都有 terminal verdict 才启动。
- **附带（非临界）**：ExtAngleRealSumPm2Pi（Umlaufsatz ±2π，纯 ℝ，ear-clip 归纳）——有空闲 worker 时派。
- **已知死路（勿碰）**：EarHalfPlaneContainment（机器证伪，reflex band）；InteriorOddSeed as stated（≡ allConvex，reflex 处假）。

---

## Step 0（开跑即做）

1. 本地 zinan-overnight（tip 1a29fc8）push 到 origin；同步 uisai2。
2. uisai2 工作树清理（untracked FFCT14/15/16 与 git 对齐）。
3. 三个 worker 文件命名空间预分配：Ch13 → `ZinanFFCT17+`，Ch35 → `ZinanCh35Split*`，Ch36 → `ZinanCh36Theta*`；Audit.lean 接线由我统一做。

## 全局 Terminal

40/40：全 repo `lake build` EXIT 0，三章 headline `#print axioms` = {propext, Classical.choice, Quot.sound}，语义审查（§3.1 C 组）三章各过一轮独立对抗复核。
