# `/goal` 长期执行目标（全书 Lean 形式化）

## 1. 任务总目标

在 `ProofsInTheBook/` 中把《Proofs from THE BOOK》1–40 章按书中的证明步骤完整写成 Lean。目标是：每章都用“书的命题”与“书的证明结构”替换占位，每章最终可被 `/goal` 体系判定完成并通过人工语义审查。

## 2. 完成定义（Goal-Complete）

一章 `N` 判定完成时必须同时满足：
- `bash scripts/goal check N` 显示 `sorry=0`、`true-stub=0`、`placeholder=0`。
- 该章不出现“语义迁移式替代”，即：当前声明语义不能用“无限质数”这类通用命题替代书中目标。
- 至少有 1 段注释说明本章对应书中的关键分解（反证、构造、界估计、归纳、组合计数、几何变换之一）。
- `bash scripts/goal mark N done` 后立即提交并 push，且在 `WebappTasks.md` 与 `Changelog.md` 记录本轮输入/输出。

## 3. 强制流程（不可变）

- `/goal run --chapter N --max 2` 的输出即为本轮要解决的任务集，单轮仅 1–2 个定理。
- `bash scripts/goal run` 之外不改本轮外的文件；不要求的文件禁止改动。
- `bash scripts/goal check N` 是每轮入场门槛，失败则暂停当前轮。
- 单轮失败三次及以上，调用你决定是否从 `instant` 切到 `extend` 或 `pro extend`。
- 任何 `commit` 必须包含本轮 `goal` 任务文件、`WebappTasks.md`、`Changelog.md` 对应条目。

## 4. 全书路线

### M0 统一对齐（当前阶段）
- 先对每章的定理语义做一次对齐，清理掉 `chapter03` 以外的 `Nat.Infinite` 迁移式占位。
- 目标是建立“书命题优先、结构可读”的统一基线。

### M1 数论基础（01–10）
- 01–02 的分拆定理先完善，再以 03 继续补齐二项式部分子命题。
- 04–10 每章从 `chapterXX` 单定理转为“书命题子目标 + 主定理”结构。

### M2 核心代数几何与离散（11–20）
- 每章保留原有章节声明，并在主定理下补齐书中的中间命题或构造性子引理。

### M3 组合图论与概率入口（21–30）
- 每章都保留书目标的原始方向，避免“借助其他命题直接 exact”。

### M4 收口（31–40）
- 进行全书语义抽检：逐章比对书名与定理方向，查重复命题复用、同名重用、弱化证明。

### M5 全书闭环
- `bash scripts/goal check all` 为 `DONE:40/40`，且手工复核确认每章都按书目标。

## 5. 章序与目标文件

1. `ProofsInTheBook/Chapter01.lean`：`chapter01_euclid`, `chapter01_fermat_coprime`, `chapter01_mersenne`, `chapter01_euler`, `chapter01_furstenberg`, `chapter01`
2. `ProofsInTheBook/Chapter02.lean`：`chapter02_bertrand`, `chapter02_landau_trick`, `chapter02_prime_product_bound`, `chapter02_legendre`, `chapter02_binomial_bound`, `chapter02`
3. `ProofsInTheBook/Chapter03.lean`：`chapter03_sylvester`（Sylvester 证明风格）、`chapter03_binomial_never_power`（或对应书中 near-power 定理的 Lean 命名）、`chapter03`
4. `ProofsInTheBook/Chapter04.lean`：`chapter04`
5. `ProofsInTheBook/Chapter05.lean`：`chapter05`
6. `ProofsInTheBook/Chapter06.lean`：`chapter06`
7. `ProofsInTheBook/Chapter07.lean`：`chapter07`
8. `ProofsInTheBook/Chapter08.lean`：`chapter08`
9. `ProofsInTheBook/Chapter09.lean`：`chapter09`
10. `ProofsInTheBook/Chapter10.lean`：`chapter10`
11. `ProofsInTheBook/Chapter11.lean`：`chapter11`
12. `ProofsInTheBook/Chapter12.lean`：`chapter12`
13. `ProofsInTheBook/Chapter13.lean`：`chapter13`
14. `ProofsInTheBook/Chapter14.lean`：`chapter14`
15. `ProofsInTheBook/Chapter15.lean`：`chapter15`
16. `ProofsInTheBook/Chapter16.lean`：`chapter16`
17. `ProofsInTheBook/Chapter17.lean`：`chapter17`
18. `ProofsInTheBook/Chapter18.lean`：`chapter18`
19. `ProofsInTheBook/Chapter19.lean`：`chapter19`
20. `ProofsInTheBook/Chapter20.lean`：`chapter20`
21. `ProofsInTheBook/Chapter21.lean`：`chapter21`
22. `ProofsInTheBook/Chapter22.lean`：`chapter22`
23. `ProofsInTheBook/Chapter23.lean`：`chapter23`
24. `ProofsInTheBook/Chapter24.lean`：`chapter24`
25. `ProofsInTheBook/Chapter25.lean`：`chapter25`
26. `ProofsInTheBook/Chapter26.lean`：`chapter26`
27. `ProofsInTheBook/Chapter27.lean`：`chapter27`
28. `ProofsInTheBook/Chapter28.lean`：`chapter28`
29. `ProofsInTheBook/Chapter29.lean`：`chapter29`
30. `ProofsInTheBook/Chapter30.lean`：`chapter30`
31. `ProofsInTheBook/Chapter31.lean`：`chapter31`
32. `ProofsInTheBook/Chapter32.lean`：`chapter32`
33. `ProofsInTheBook/Chapter33.lean`：`chapter33`
34. `ProofsInTheBook/Chapter34.lean`：`chapter34`
35. `ProofsInTheBook/Chapter35.lean`：`chapter35`
36. `ProofsInTheBook/Chapter36.lean`：`chapter36`
37. `ProofsInTheBook/Chapter37.lean`：`chapter37`
38. `ProofsInTheBook/Chapter38.lean`：`chapter38`
39. `ProofsInTheBook/Chapter39.lean`：`chapter39`
40. `ProofsInTheBook/Chapter40.lean`：`chapter40`

## 6. 里程碑验收与命令

```bash
bash scripts/goal next
bash scripts/goal run --chapter N --max 2
bash scripts/goal check N
bash scripts/goal mark N done
bash scripts/goal report
```

- `next` 只用于选择待做章节。
- `run` 负责产生一问一答的任务最小包。
- `mark` 前后必须提交并 push。
