# `/goal` 长期执行目标（全书 Lean formalization）

## 1. 总目标

把 `ProofsInTheBook/` 的 40 章全部改为：

- 按《Proofs from THE BOOK》原定理命名或语义对应命名写出 Lean 语句；
- 每条定理都使用书中的证明路线（不允许“替换成`Nat.Infinite {p : ℕ // p.Prime}`”这类语义迁移）；
- 通过 `/goal` 自动检查和人工语义复核后稳定完成；
- 全部任务要连续可追踪：`instant` / `extend` 之间可切换，但不得阻塞 `/goal` 流转。

## 2. 书级完成标准（每章）

- `bash scripts/goal check N` 返回：
  - `sorry=0`
  - `true-stub=0`
  - `placeholder=0`
- 该章声明和子定理名存在于 `scripts/goal` 报告出的任务集合中；
- 本轮目标必须与书章标题对齐（见章节清单）；
- `/goal mark N done` 后立即提交并 push，且在 `WebappTasks.md`、`Changelog.md` 写明本轮完成项和通信状态（含窗口/模式）。

## 3. 执行纪律（硬约束）

- 每轮只做 1–2 个任务：
  - `bash scripts/goal run --chapter N --max 2`
- 每轮只改本轮任务相关文件；
- 先 `bash scripts/goal check N`；若不通过，暂停本轮并回到本地修正；
- 第三次失败后，向我汇报并申请切到 `extend` 或 `pro extend`；
- 每轮必须在 `WebappTasks.md` 记录“请求→返回”，并用 `Changelog.md`记录时间戳级别变更；
- 任何提交必须包含：
  - 修改的 `ProofsInTheBook/ChapterXX.lean`；
  - 若是任务流转更新，`WebappTasks.md` 与 `Changelog.md` 对应追加条目。

## 4. 全书执行里程碑

- M0 统一语义对齐：逐章清理“占位语义”并绑定书章标题。
- M1 章节级基线（01–10）：完成已分拆子目标的 01–03；其余 04–10 转为书命题+主定理。
- M2 结构统一（11–20）：每章至少保留一本体证明结构的关键子目标再汇总到 `chapterXX`。
- M3 结构统一（21–30）：同 M2。
- M4 汇总收口（31–40）：完成语义一致性抽检（标题/命题方向/证明策略）。
- M5 终检：`bash scripts/goal check all` 显示 `DONE:40/40` 且附一轮人工抽检日志。

## 5. 全书任务清单（按书章节）

### Part A：01–10
1. `Chapter01.lean`：`chapter01_euclid`, `chapter01_fermat_coprime`, `chapter01_mersenne`, `chapter01_euler`, `chapter01_furstenberg`, `chapter01`
2. `Chapter02.lean`：`chapter02_bertrand`, `chapter02_landau_trick`, `chapter02_prime_product_bound`, `chapter02_legendre`, `chapter02_binomial_bound`, `chapter02`
3. `Chapter03.lean`：`chapter03_sylvester`, `chapter03_binomials_coefficients_never_powers`, `chapter03`
4. `Chapter04.lean`：`chapter04`（two-square representation chapter goal）
5. `Chapter05.lean`：`chapter05`（quadratic reciprocity chapter goal）
6. `Chapter06.lean`：`chapter06`（finite division rings to fields chapter goal）
7. `Chapter07.lean`：`chapter07`（irrationality chapter goal）
8. `Chapter08.lean`：`chapter08`（Basel sum chapter goal）
9. `Chapter09.lean`：`chapter09`（Hilbert third problem chapter goal）
10. `Chapter10.lean`：`chapter10`（lines/graph decompositions chapter goal）

### Part B：11–20
11. `Chapter11.lean`：`chapter11`
12. `Chapter12.lean`：`chapter12`
13. `Chapter13.lean`：`chapter13`
14. `Chapter14.lean`：`chapter14`
15. `Chapter15.lean`：`chapter15`
16. `Chapter16.lean`：`chapter16`
17. `Chapter17.lean`：`chapter17`
18. `Chapter18.lean`：`chapter18`
19. `Chapter19.lean`：`chapter19`
20. `Chapter20.lean`：`chapter20`

### Part C：21–30
21. `Chapter21.lean`：`chapter21`
22. `Chapter22.lean`：`chapter22`
23. `Chapter23.lean`：`chapter23`
24. `Chapter24.lean`：`chapter24`
25. `Chapter25.lean`：`chapter25`
26. `Chapter26.lean`：`chapter26`
27. `Chapter27.lean`：`chapter27`
28. `Chapter28.lean`：`chapter28`
29. `Chapter29.lean`：`chapter29`
30. `Chapter30.lean`：`chapter30`

### Part D：31–40
31. `Chapter31.lean`：`chapter31`
32. `Chapter32.lean`：`chapter32`
33. `Chapter33.lean`：`chapter33`
34. `Chapter34.lean`：`chapter34`
35. `Chapter35.lean`：`chapter35`
36. `Chapter36.lean`：`chapter36`
37. `Chapter37.lean`：`chapter37`
38. `Chapter38.lean`：`chapter38`
39. `Chapter39.lean`：`chapter39`
40. `Chapter40.lean`：`chapter40`

## 6. 里程碑命令（固定）

```bash
bash scripts/goal next
bash scripts/goal run --chapter N --max 2
bash scripts/goal check N
bash scripts/goal mark N done
bash scripts/goal report
```

- `next`：查找下一待做章节；
- `run`：生成本轮 1–2 个任务；
- `check`：确认入场门槛；
- `mark`：每次提交前后要成对执行；
- `report`：每 2–3 轮做一次全局里程碑复盘。 
