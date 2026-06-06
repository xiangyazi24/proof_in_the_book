# DOCTRINE — 全书 formalization 收官(36/40 → 40/40)

主目标:四个开放章节(09, 13, 35, 36)全部以 0-sorry、axioms={propext, Classical.choice, Quot.sound}、
非 fragment 的 headline 定理关闭。

## Ch35(主攻,引擎几乎齐装)
(a) F 计数 NumCyclesCutPhi2:genus-free 路线(pbook a249330d 设计中)或应用层 genus-0 注入。
    终态:cutCapMap2_F 无条件 ⟹ jordan_simple_cycle2 ⟹ Separates。
    已证:抽象链定理×2、纯圈引理、双因子装配、SeamDecomposition⟹计数。
(b) witness 应用层:SidesReach2 + FragmentCompatible2 从近三角剖分结构(面=三角形枚举)discharge。
(c) 删除链定向数据:FanIncidenceData / MergedOuterArcData / DeletedOuterBoundary——同族 Jordan 定向,
    候选:从(a)(b)的同套机制或补充 fan-certificate 字段。
(d) 装配:f11 JordanOracle discharge → thomassen 主定理 → f13–16 bridge → 书面五色推论。
fallback:若 genus-free 路线终不可形式化,Separates 经由(b)的 witness + 连通性矛盾仍可绕过 F 等式
(witness ⟹ connected ⟹ chi'≤2 与 chi'=chi+(F'−F)…需 F'≥F+2 下界——记为待验证支线)。

## Ch09
(e) pearl 角度分类(pearlclass 在跑:截面机制 + SectorSum 对接)。
(f) Bricard 条件组装:pearl_lemma + 分类 + TetDihedral 具体值 + Chapter09 代数层 → headline
    (正四面体与等体积立方体不可等剖分)。TetVolume 已证供体积归一。

## Ch36
(g) parity round-2 基础层(polyparity 在跑)→ A3/A4 scaffold discharge → EarTriangulation 存在
    → artGallery_strict。
## Ch13
(h) WeakConvexArm 识别定理(多边形 B 层)→ cauchy_arm 点级;球面 arm + vertex-link 基底设计
    (pbook 后续回合)。

终止条件:每章 headline `#print axioms` clean-3 + AUDIT.md 计入。
