# /goal 长期执行手册（Proofs in THE BOOK 全书形式化）

目标是把整本书 40 章做成可核验的 Lean 形式化。任何“完成”都必须代表真正的数学推导，而不是占位。

## 全局目标

- 在 `ProofsInTheBook/Chapter01.lean` 到 `ProofsInTheBook/Chapter40.lean` 中完成每一条书内命题。
- 反对 `sorry` 作为最终结果。
- 反对 `theorem ... : True := ...`、`:= by trivial`、`:= by aesop`、`:= by decide` 作为主要完成方案。
- `webapp` 返回要可替换到对应定理位点，且与书中论断语义一致。
- 每批次机械改动后做可追踪的 `commit + push`，记录到 `Changelog.md` 与 `WebappTasks.md`。

## 目标序列（40 章）

01 质数无穷多（六个证明）  
02 Bertrand 猜想  
03 二项式系数几乎不可能是幂  
04 两平方和表示  
05 二次互反律  
06 有限除环是域  
07 无理数构造与性质  
08 计算 $\pi^2/6$  
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

## 真实完成标准（硬规则）

- 章级标准：`bash scripts/goal check <N>` 必须返回 `sorry=0` 且 `true-stub=0`。  
- 局部标准：书中定理声明不能仍是平凡占位，必须保留能反映命题内容的证明代码。  
- 工程标准：对应章节有至少一次可追踪提交，并在 `Changelog.md` 记载本轮完成内容与测试状态。  
- 全书标准：`bash scripts/goal check all` 完全清零 TODO，`bash scripts/goal build` 可通过。

## /goal 执行流程（默认 instant）

1. `bash scripts/goal report` 看阶段和剩余任务。  
2. `bash scripts/goal next` 取下一个章节。  
3. `bash scripts/goal run [--chapter N] [--max M]`（M=1~2）产出问题列表。  
4. 给 webapp 下发：文件、定理名、缺失目标、建议 proof 风格。  
5. 回收后直接替换对应定理。  
6. `bash scripts/goal check <N>` 验证本章清零。  
7. `bash scripts/goal mark <N> done`，写入 `WebappTasks.md`，记录 `Changelog`，并 commit + push。  
8. 重复步骤 2~7。

## 阶段规划

- Goal-01：重启状态，恢复真实待做题目。  
- Goal-02：任务链路与通信稳定（日志、窗口、频道）。  
- Goal-03：01–10 章完成。  
- Goal-04：11–20 章完成。  
- Goal-05：21–30 章完成。  
- Goal-06：31–40 章完成。  
- Goal-07：全书收敛、最终清单发布。

## 运行规则

- 一轮任务默认 1~2 条，避免问答堆积。  
- 频道名固定 `dm-codex`。  
- 频道/窗口若异常先修复通信再继续推进。  
- webapp 回应失败超过 2 轮后切到 `extend` 并提前告诉你。  

## 任务指令汇总

- `goal init`：初始化状态。  
- `goal stage`：查看阶段和当前章节。  
- `goal next`：查看下一个未完成章节。  
- `goal run [--chapter N] [--max M]`：生成一轮任务。  
- `goal check [all|N]`：检查剩余 `sorry` 与 `True` 占位。  
- `goal mark <N> done`：章节完成入账。  
- `goal build`：构建检测。  
- `goal report`：总体汇总。  

