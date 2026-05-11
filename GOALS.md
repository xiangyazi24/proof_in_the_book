# /goal 长期执行目标（Proofs in THE BOOK 全书 Lean 形式化）

## 1. 终极目标

把 `ProofsInTheBook/Chapter01.lean` 到 `ProofsInTheBook/Chapter40.lean` 全部完成为
**按书籍原命题的 Lean 形式化证明**，并保持章节定义、定理语义和证明路径都可复核。

## 2. 硬规则（不可违反）

1. 不能以 `sorry`、`admit`、`by sorry` 结束任何目标。
2. 不能以 `theorem ... : True := by ...` 作为完成状态。
3. 不能只通过“统一类型”占位（例如把不同章节都改成 `Nat.Infinite {p : ℕ // p.Prime}`）。
4. 不能删除或抹平书内结构（例如把多个命题合并为单个不相干结论）。
5. 每次与 webapp 结对时，一次只发 1~2 个定理任务，避免一次堆积过多问题。

`/goal` 的“完成”只在满足上面 5 条后才计入。

## 3. 真实完成标准

章级验收标准：
- 本章的定理声明与书内目标一致，语义非平凡。
- 无 `sorry`/`admit`/`by sorry`。
- 该章文件至少包含一条非平凡、可追溯的 proof term（不可是“无关紧要统一结论”）。
- 有对应提交记录，且该提交可在 `Changelog.md` 中追踪。

全书验收标准：
- 40 章按顺序都满足章级标准。
- 全书无章节级语义退化（不能用同一结论替代不同章节）。
- 全书可复现提交序列，且每次小步完成后都有 push。

## 4. `/goal` 执行协议（固定）

```bash
bash scripts/goal next                # 选定当前待处理章节
bash scripts/goal run --chapter N --max 2
bash scripts/goal check N
bash scripts/goal mark N done
bash scripts/goal report
```

执行要求：
1. 每次只针对明确的定理名下发。
2. webapp 回传后立即落地到对应 Lean 文件。
3. 先局部检查，再 `git commit`，再 `git push`，最后更新 `WebappTasks.md` 与 `Changelog.md`。
4. 任何卡住点至少说明 3 次尝试方向（而不是改成占位）。

## 5. 书目顺序任务（40 章）

01 质数无穷多（六个证明）  
02 Bertrand 猜想  
03 二项式系数几乎不可能是幂  
04 两平方和表示  
05 二次互反律  
06 有限除环是域  
07 无理数构造与性质  
08 计算 \(\pi^2/6\)  
09 Hilbert 第三问题  
10 平面直线与图分解  
11 Slope 问题  
12 Euler 公式的三个应用  
13 Cauchy 刚性  
14 切触单纯形  
15 大点集含钝角  
16 Borsuk 猜想  
17 集合、函数与连续统假设  
18 不等式专题  
19 基本代数定理  
20 方形与奇数个三角形  
21 Pólya 多项式定理  
22 Littlewood–Offord 引理  
23 cotangent 与 Herglotz 技巧  
24 Buffon 针  
25 鸽巢与重数计数  
26 矩形镶嵌  
27 有穷集合的三大定理  
28 洗牌问题  
29 格点路径与行列式  
30 Cayley 树数  
31 恒等式与构造计数  
32 Latin 方阵补全  
33 Dinitz 问题  
34 平面图五色定理  
35 博物馆警卫问题  
36 Turán 图论  
37 误码通信  
38 Kneser 图染色  
39 朋友与政客  
40 概率让计数更容易

## 6. 阶段计划

Goal-01：重置进度（恢复真实章节语义）  
Goal-02：建立稳定的 `/goal` 节奏（每轮 1~2 题）  
Goal-03：完成 01–10 章  
Goal-04：完成 11–20 章  
Goal-05：完成 21–30 章  
Goal-06：完成 31–40 章  
Goal-07：全书语义审计 + 最终交付  

## 7. 风险控制

- 若 webapp 多次未返回或返回不可验证内容，及时告知并请求重提问；超 2 轮仍未解决则考虑升级到 extend 或 pro extend 模式。
- 若出现“似乎全书都能 `check` 但语义明显相同”现象，立即回滚当轮改动并按书重建命题。
- 对外部资料的引理/定理可复用，但不能替代书内证明路径本体的语义目标。
