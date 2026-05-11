# `/goal` 长期执行目标（全书 Lean 形式化）

本文件是 `/goal` 脚本的“执行目标文件”，目标是把
`ProofsInTheBook/` 的 40 章全部改为按书证明确切结构的 Lean 证明。

## 0. 约束与完成标准

- 只通过 `/goal` 检查结果决定章节完成（不接受手工口头确认）。
- 每章在 `/goal check N` 的三项计数都必须为 0：
  - `sorry`
  - `true-stub`
  - `placeholder`
- 禁止以“替换命题本身”收束：
  - 章节主命题不能直接写成 `Nat.Infinite {p : ℕ // p.Prime}` 作为结论收尾。
  - `simpa using Nat.infinite_setOf_prime.to_subtype` 仅可作为辅助定理，不可作为书命题主结论。
- 每个章节必须至少保留一条对应书命题主声明（如 `chapter03`）。
- `/goal` 每轮只处理 **1–2 个未完成定理**。
- 连续 3 次失败（同一轮 3 次）必须暂停并向我说明，必要时切到 extend/pro extend。

## 1. `/goal` 固定执行流程

1. `bash scripts/goal run --chapter N --max 2`
2. 对 Webapp 回传的目标按“声明不变、替换证明体”实现。
3. 我方本地把回传结果应用后，必要时做最小结构性清理。
4. `bash scripts/goal check N`，确认 0/0/0 后再继续。
5. `bash scripts/goal mark N done`。
6. 每完成一个 `chapter` 都提交并 push，确保 Webapp 可见。
7. 每次阶段转换后执行 `bash scripts/goal report`，我会在对话中记录里程碑。

## 2. 阶段计划

- 阶段 A：初始化与第一轮任务
  - 目标：启动 `goal`，确认 01–03 的书目标命名和提交流程稳定。
- 阶段 B：第 1 段（01–10）
  - 目标：完成并通过 01–10 的 check。
- 阶段 C：第 2 段（11–20）
- 阶段 D：第 3 段（21–30）
- 阶段 E：第 4 段（31–40）
- 阶段 F：全书收敛（`check all` = `DONE:40/40`）。

## 3. 全书任务清单（固定执行顺序）

- Chapter 01 `chapter01_euclid`
- Chapter 01 `chapter01_fermat_coprime`
- Chapter 01 `chapter01_mersenne`
- Chapter 01 `chapter01_euler`
- Chapter 01 `chapter01_furstenberg`
- Chapter 01 `chapter01`
- Chapter 02 `chapter02_bertrand`
- Chapter 02 `chapter02_landau_trick`
- Chapter 02 `chapter02_prime_product_bound`
- Chapter 02 `chapter02_legendre`
- Chapter 02 `chapter02_binomial_bound`
- Chapter 02 `chapter02`
- Chapter 03 `chapter03_sylvester`
- Chapter 03 `chapter03_binomials_coefficients_never_powers`
- Chapter 03 `chapter03`
- Chapter 04 `chapter04`
- Chapter 05 `chapter05`
- Chapter 06 `chapter06`
- Chapter 07 `chapter07`
- Chapter 08 `chapter08`
- Chapter 09 `chapter09`
- Chapter 10 `chapter10`
- Chapter 11 `chapter11`
- Chapter 12 `chapter12`
- Chapter 13 `chapter13`
- Chapter 14 `chapter14`
- Chapter 15 `chapter15`
- Chapter 16 `chapter16`
- Chapter 17 `chapter17`
- Chapter 18 `chapter18`
- Chapter 19 `chapter19`
- Chapter 20 `chapter20`
- Chapter 21 `chapter21`
- Chapter 22 `chapter22`
- Chapter 23 `chapter23`
- Chapter 24 `chapter24`
- Chapter 25 `chapter25`
- Chapter 26 `chapter26`
- Chapter 27 `chapter27`
- Chapter 28 `chapter28`
- Chapter 29 `chapter29`
- Chapter 30 `chapter30`
- Chapter 31 `chapter31`
- Chapter 32 `chapter32`
- Chapter 33 `chapter33`
- Chapter 34 `chapter34`
- Chapter 35 `chapter35`
- Chapter 36 `chapter36`
- Chapter 37 `chapter37`
- Chapter 38 `chapter38`
- Chapter 39 `chapter39`
- Chapter 40 `chapter40`

## 4. 里程碑与验收

- M0：`/goal run` 在 01 起不再下发“直接 `simpa using Nat.infinite_setOf_prime.to_subtype` 的替代任务。
- M1：01–10 全部 `check` 通过。
- M2：11–20 全部 `check` 通过。
- M3：21–30 全部 `check` 通过。
- M4：31–40 全部 `check` 通过。
- M5：`bash scripts/goal check all` 显示 `DONE:40/40`。

## 5. 章节与书标题对照（仅用于任务语义）

- Chapter 01: Six proofs of the infinity of primes
- Chapter 02: Bertrand's postulate
- Chapter 03: Binomial coefficients are (almost) never powers
- Chapter 04: Representing numbers as sums of two squares
- Chapter 05: The law of quadratic reciprocity
- Chapter 06: Every finite division ring is a field
- Chapter 07: Some irrational numbers
- Chapter 08: Three times pi^2 / 6
- Chapter 09: Hilbert's third problem: decomposing polyhedra
- Chapter 10: Lines in the plane and decompositions of graphs
- Chapter 11: The slope problem
- Chapter 12: Three applications of Euler's formula
- Chapter 13: Cauchy's rigidity theorem
- Chapter 14: Touching simplices
- Chapter 15: Every large point set has an obtuse angle
- Chapter 16: Borsuk's conjecture
- Chapter 17: Sets, functions, and the continuum hypothesis
- Chapter 18: In praise of inequalities
- Chapter 19: The fundamental theorem of algebra
- Chapter 20: One square and an odd number of triangles
- Chapter 21: A theorem of Pólya on polynomials
- Chapter 22: On a lemma of Littlewood and Offord
- Chapter 23: Cotangent and the Herglotz trick
- Chapter 24: Buffon's needle problem
- Chapter 25: Pigeon-hole and double counting
- Chapter 26: Tiling rectangles
- Chapter 27: Three famous theorems on finite sets
- Chapter 28: Shuffling cards
- Chapter 29: Lattice paths and determinants
- Chapter 30: Cayley's formula for the number of trees
- Chapter 31: Identities versus bijections
- Chapter 32: Completing Latin squares
- Chapter 33: The Dinitz problem
- Chapter 34: Five-coloring plane graphs
- Chapter 35: How to guard a museum
- Chapter 36: Turan's graph theorem
- Chapter 37: Communicating without errors
- Chapter 38: The chromatic number of Kneser graphs
- Chapter 39: Of friends and politicians
- Chapter 40: Probability makes counting (sometimes) easy
