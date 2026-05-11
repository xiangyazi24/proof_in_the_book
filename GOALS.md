# `/goal` 长期执行目标（全书 Lean formalization 重启版）

## 1. 目标定义（唯一）

把 `ProofsInTheBook/` 中 40 章改写为《Proofs from THE BOOK》对应章节的形式化版本：

- 逐章采用书中的定理陈述（章节语义与书名对齐）。
- 逐步写出书中的证明路径；不允许用与书结论不等价的“占位替换”收尾。
- `/goal` 只处理书级证明任务，不处理流程管理之外的技巧性重构。

## 2. 硬性完成标准（每章）

一个章节在 `scripts/goal check N` 中必须满足：

- `sorry = 0`
- `true-stub = 0`
- `placeholder = 0`

并且该章必须包含与书证明链条一致的关键主命题与子命题定义。

## 3. 禁止行为（硬规则）

以下写法在目标定理层面一律不视为完成：

- 目标语句直接或间接写成 `Nat.Infinite {p : ℕ // p.Prime}`。
- 目标使用 `simpa using Nat.infinite_setOf_prime.to_subtype` 等“直接替换”收束。
- `by` 块里无实质内容或以数学语义转译代替书上结论。

可接受的 `Nat.infinite_setOf_prime` 用法：

- 作为章节证明中的辅助 lemma。
- 不得取代对应章节的书级主定理。

## 4. `/goal` 流程（每轮固定）

每一轮只处理 1–2 个任务，全部依照以下顺序执行：

1. `bash scripts/goal run --chapter N --max 2`
2. 对每个任务写 Lean 证明代码。
3. `bash scripts/goal check N`
4. 通过后：`bash scripts/goal mark N done`
5. 及时提交并 push。

失败规则：

- 当单轮任务第三次连续未过检查，向我报告并申请切 `extend` 或 `pro extend`。
- 任务失败时先停止该轮，不能跳题。

## 5. 书章目标清单（40 章）

### Part 1：01–10
- 01: `chapter01_euclid`, `chapter01_fermat_coprime`, `chapter01_mersenne`, `chapter01_euler`, `chapter01_furstenberg`, `chapter01`
- 02: `chapter02_bertrand`, `chapter02_landau_trick`, `chapter02_prime_product_bound`, `chapter02_legendre`, `chapter02_binomial_bound`, `chapter02`
- 03: `chapter03_sylvester`, `chapter03_binomials_coefficients_never_powers`, `chapter03`
- 04: `chapter04`
- 05: `chapter05`
- 06: `chapter06`
- 07: `chapter07`
- 08: `chapter08`
- 09: `chapter09`
- 10: `chapter10`

### Part 2：11–20
- 11: `chapter11`
- 12: `chapter12`
- 13: `chapter13`
- 14: `chapter14`
- 15: `chapter15`
- 16: `chapter16`
- 17: `chapter17`
- 18: `chapter18`
- 19: `chapter19`
- 20: `chapter20`

### Part 3：21–30
- 21: `chapter21`
- 22: `chapter22`
- 23: `chapter23`
- 24: `chapter24`
- 25: `chapter25`
- 26: `chapter26`
- 27: `chapter27`
- 28: `chapter28`
- 29: `chapter29`
- 30: `chapter30`

### Part 4：31–40
- 31: `chapter31`
- 32: `chapter32`
- 33: `chapter33`
- 34: `chapter34`
- 35: `chapter35`
- 36: `chapter36`
- 37: `chapter37`
- 38: `chapter38`
- 39: `chapter39`
- 40: `chapter40`

每个章节必须至少包含一个“书名对应的命题主声明”。

## 6. 里程碑（硬约束）

- M0：第一轮后 `goal` 只保留书命题，不包含占位证明。
- M1：01–10 全部 `check` 无警告。
- M2：11–20 全部 `check` 无警告。
- M3：21–30 全部 `check` 无警告。
- M4：31–40 全部 `check` 无警告。
- M5：`bash scripts/goal check all` 显示 `DONE:40/40`。

里程碑时执行 `bash scripts/goal report`，输出给我并记录。

## 7. 章节到书标题映射（执行对齐）

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
