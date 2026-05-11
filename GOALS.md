# 全书长期目标（Formalization Goal）

## 目标

在 `~/repos/proof_in_the_book` 中完成全书 40 章按书重建的 Lean 形式化：

- 章节声明不得替换（`theorem` 名称和声明体不变）
- 机械化证明不可代替书上证明：`chapterNN` 的任务是“按书题意重写其对应证明”，而不是把所有章都留在
  `apply Set.infinite_coe_iff.mp; exact Nat.infinite_setOf_prime` 这类骨架上
- `/goal` 统一以 `sorry / true-stub / placeholder` 为完成判定；placeholder 必须覆盖：
  - 命题直接是 `Infinite {p : ℕ // p.Prime}` 但用固定骨架直接闭合
  - `to_subtype`、`simpa using Nat.infinite_setOf_prime` 等机械闭合
- 所有工作需 commit + push 供 webapp 读取

## 全局验收标准

章节 `N` 完成条件：

1. `bash scripts/goal check N`
2. 输出必须是：`sorry=0`, `true-stub=0`, `placeholder=0`
3. 本轮只允许修改对应章节任务，不允许改动其他章节声明
4. 提交并 push，更新 `Changelog.md`
5. 通过后执行 `bash scripts/goal mark N done`

全书完成标准：

1. `bash scripts/goal check all`
2. 输出 `DONE:40/40`
3. 所有 01–40 任务顺序已按文件顺序完成并可追溯

## 执行节奏（固定）

每轮只改 1–2 个目标（防止碎片化）：

1. `bash scripts/goal run --chapter N --max 2`
2. 将脚本输出的任务完整提交给 `dm-codex`
3. 在本地按 webapp 回复替换证明体（不改声明）
4. `bash scripts/goal check N`
5. `bash scripts/goal mark N done`（仅当阶段清零）

连续 3 次失败或卡住时暂停，先回报并评估切到 `extend` / `pro extend`。

## 阶段（按章节）

- 阶段 A：01–03
  - 目标：任务派发稳定，子命题拆分与总目标声明同步
- 阶段 B：01–10
- 阶段 C：11–20
- 阶段 D：21–30
- 阶段 E：31–40
- 阶段 F：全书收敛（全局清零）

里程碑：

- M0：01 可持续派发、Webapp 回传与本地落库通路稳定
- M1：`01` 全部通过
- M2：`01–10` 全部通过
- M3：`01–20` 全部通过
- M4：`01–30` 全部通过
- M5：`01–40` 全部通过
- M6：`check all = DONE:40/40`

## 全书执行清单（固定顺序）

1. Chapter 01 `chapter01_euclid`
2. Chapter 01 `chapter01_fermat_coprime`
3. Chapter 01 `chapter01_mersenne`
4. Chapter 01 `chapter01_euler`
5. Chapter 01 `chapter01_furstenberg`
6. Chapter 01 `chapter01`
7. Chapter 02 `chapter02_bertrand`
8. Chapter 02 `chapter02_landau_trick`
9. Chapter 02 `chapter02_prime_product_bound`
10. Chapter 02 `chapter02_legendre`
11. Chapter 02 `chapter02_binomial_bound`
12. Chapter 02 `chapter02`
13. Chapter 03 `chapter03_sylvester`
14. Chapter 03 `chapter03_binomials_coefficients_never_powers`
15. Chapter 03 `chapter03`
16. Chapter 04 `chapter04`
17. Chapter 05 `chapter05`
18. Chapter 06 `chapter06`
19. Chapter 07 `chapter07`
20. Chapter 08 `chapter08`
21. Chapter 09 `chapter09`
22. Chapter 10 `chapter10`
23. Chapter 11 `chapter11`
24. Chapter 12 `chapter12`
25. Chapter 13 `chapter13`
26. Chapter 14 `chapter14`
27. Chapter 15 `chapter15`
28. Chapter 16 `chapter16`
29. Chapter 17 `chapter17`
30. Chapter 18 `chapter18`
31. Chapter 19 `chapter19`
32. Chapter 20 `chapter20`
33. Chapter 21 `chapter21`
34. Chapter 22 `chapter22`
35. Chapter 23 `chapter23`
36. Chapter 24 `chapter24`
37. Chapter 25 `chapter25`
38. Chapter 26 `chapter26`
39. Chapter 27 `chapter27`
40. Chapter 28 `chapter28`
41. Chapter 29 `chapter29`
42. Chapter 30 `chapter30`
43. Chapter 31 `chapter31`
44. Chapter 32 `chapter32`
45. Chapter 33 `chapter33`
46. Chapter 34 `chapter34`
47. Chapter 35 `chapter35`
48. Chapter 36 `chapter36`
49. Chapter 37 `chapter37`
50. Chapter 38 `chapter38`
51. Chapter 39 `chapter39`
52. Chapter 40 `chapter40`

## 任务语义备忘（禁止列表）

- 禁止以 `by trivial`、`: True`、`sorry` 收口
- 禁止 `simpa using Nat.infinite_setOf_prime.to_subtype`、`exact Nat.infinite_setOf_prime.to_subtype` 作为书命题主结论
- 禁止把多个书命题塞进一个占位命题

## 文件映射

- 任务源：`WebappTasks.md`
- 执行脚本：`scripts/goal`
- 状态记录：`.proof_goals_state`
- 版本记录：`Changelog.md`
