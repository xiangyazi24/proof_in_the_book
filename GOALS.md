# /goal 长期执行目标（Proofs in THE BOOK 全书 Lean 形式化）

## 1. 任务定义（唯一）

目标是从 `proofs_in_the_book.pdf` 的章节顺序出发，逐章把 `ProofsInTheBook/Chapter01.lean` 到
`ProofsInTheBook/Chapter40.lean` 完成为“可复核的书内证明实现”。

核心目标：
- 每个章内定理名保持不变；
- 声明（statement）与书中对应定理等价，不得改为统一占位命题；
- 证明路径必须可追踪到书中的关键步骤；
- 每次提交均可复现并可回溯到 `Changelog.md` 与 `WebappTasks.md`。

## 2. 不可违规项（自动检查 + 人工复核）

- 禁止任何形式的 `sorry`、`admit`、`by sorry`。
- 禁止使用 `theorem ... : True := by ...` 作为正式完成。
- 禁止把不同章节改写为同一结论（例如都改成“无限多个素数”）。
- 禁止改变证明目标以避开困难（如仅改定理声明）。
- 每次只与 webapp 交换 1~2 个定理任务，避免一次堆积过多。

`bash scripts/goal check N` 为“自动门槛”；最终完成还要人工复核 statement 语义。

## 3. 章级完成标准（`Goal-Complete`）

- 本章所有定理都不含 `sorry`、不含 `theorem ... : True`。
- 本章无 `Nat.Infinite {p : ℕ // p.Prime}` 或 `Set.Infinite {p : ℕ // p.Prime}` 的机械占位。
- 目标定理（`chapterXX*`）的证明体必须与书中结论关联：可见到对应关键引理、构造或不等式。
- `/goal` 操作记录（`WebappTasks.md`）要有这一章本轮任务与提交时间。

## 4. `/goal` 运行规范（固定）

```bash
bash scripts/goal next                      # 查下一待处理章节
bash scripts/goal run --chapter N --max 2    # 每轮最多 2 个定理
bash scripts/goal check N                    # 本地占位扫描
bash scripts/goal mark N done               # 仅在本轮全部落地且核验后
bash scripts/goal report                     # 周期报告
```

执行顺序：
1. 先运行 `next`，确认章节；再 `run` 发题给 webapp。
2. 在 webapp 回答后，逐条改定理体，不改定理名和类型。
3. 先补齐改动，更新 `WebappTasks.md`，再 `git commit`，再 `git push`。
4. `check` 通过后再 `mark N done`。

## 5. 长程规划

Goal-01：章表重定向  
- 目标：确认所有章节定理名和声明与书对应，去除占位语义（当前机械 `simpa` 仍视为待完成）。
- 成功标准：`bash scripts/goal check all` 可显示所有待完成章，但每章都有待办条目。

Goal-02：01–10 章骨架到书式证明  
- 目标：完成前 10 章的 16 个定理。

Goal-03：11–20 章  
- 目标：完成 10 章，逐章核对书中的关键构造/引理。

Goal-04：21–30 章  
- 目标：完成 10 章，保证图论与计数论章节证明链条不变形。

Goal-05：31–40 章  
- 目标：完成 10 章，完成最终统一审计。

Goal-06：全书语义审计与交付  
- 目标：逐章比对 `book proof` 语义；检查是否出现语义复用错误。

## 6. 章节任务列表（按顺序）

01：`chapter01_euclid`、`chapter01_fermat_coprime`、`chapter01_mersenne`、`chapter01_euler`、`chapter01_furstenberg`、`chapter01`  
02：`chapter02_bertrand`、`chapter02_landau_trick`、`chapter02_prime_product_bound`、`chapter02_legendre`、`chapter02_binomial_bound`、`chapter02`  
03：`chapter03`  
04：`chapter04`  
05：`chapter05`  
06：`chapter06`  
07：`chapter07`  
08：`chapter08`  
09：`chapter09`  
10：`chapter10`  
11：`chapter11`  
12：`chapter12`  
13：`chapter13`  
14：`chapter14`  
15：`chapter15`  
16：`chapter16`  
17：`chapter17`  
18：`chapter18`  
19：`chapter19`  
20：`chapter20`  
21：`chapter21`  
22：`chapter22`  
23：`chapter23`  
24：`chapter24`  
25：`chapter25`  
26：`chapter26`  
27：`chapter27`  
28：`chapter28`  
29：`chapter29`  
30：`chapter30`  
31：`chapter31`  
32：`chapter32`  
33：`chapter33`  
34：`chapter34`  
35：`chapter35`  
36：`chapter36`  
37：`chapter37`  
38：`chapter38`  
39：`chapter39`  
40：`chapter40`  

## 7. 风险与应对

- webapp 未返回/回答不可验证：重发该轮任务（不改变其他章节）；必要时切换到 extend 或 pro extend。
- 出现“看起来全书通过 check”但语义重复：该轮立即回滚并返回书内证明路径。
- 出现证明退化：需新增 `lemma`/注释，记录“原书关键语义”与“替代引理链路”。
