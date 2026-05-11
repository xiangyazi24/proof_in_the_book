# /goal 长期执行手册（Proofs in THE BOOK）

本文件是“全书长期执行目标”，用于指导 40 章逐步完成**真实 Lean 形式化**（不是 `: True` 占位）。它与 `scripts/goal` 协同，支持长时间重复推进。

## 总目标

- 在 `ProofsInTheBook/Chapter01.lean` 到 `ProofsInTheBook/Chapter40.lean` 中，把书中每个目标语句都补齐为非平凡数学定理。
- 保证证明来自可核验的 Lean 代码，不依赖 `by trivial`、`by aesop`、`sorry` 作为最终解。
- `/goal` 流程持续循环：本地机械工作 + webapp 交互证明分工，要求全程 commit + push 可见。

## 关键约束（硬规则）

- 任何章节只在 `goal` 允许的任务单中推进，单轮不超过 2 条。
- 每轮问题必须明确：文件名、定理名、命题上下文、希望的 proof style（优先直接 replacement）。
- 不再接受“章节名显示完成但仍是 `: True` / `trivial`”的完成；必须消除 `sorry` 且 theorem 类型需与书面命题一致。
- 每个 webapp 回答必须可直接编译替换；不能有草率宏证明（除非可被逐步展开并验证）。
- 本地与 webapp 的结果以 commit 为单位可追溯：`WebappTasks.md` 记录问题，提交记录记录每次收敛。

## 长期状态机（固定 8 阶段）

- **Goal-00 复位**：回到真实形式化起点，移除本轮误用的占位（`trivial`）并清零阶段标记。
- **Goal-01 工程稳态**：任务链条完整（脚本、通信、提交与日志可复现）。
- **Goal-02 定理切分**：每章的可交付子问题按 `theorem` 级别可追踪。
- **Goal-03 章 1..10 完成**：每章任务清零、代码可编译、形成提交批次。
- **Goal-04 章 11..20 完成**：同上。
- **Goal-05 章 21..30 完成**：同上。
- **Goal-06 章 31..40 完成**：同上。
- **Goal-07 全书收敛**：无 `sorry`，全书至少一次 `lake build` 通过。

## 章节级执行循环（固定流程）

1. `bash scripts/goal next`：锁定下一个未完成章节（含未解 `sorry`）。
2. `bash scripts/goal run [--chapter N] [--max M]`：选出本轮 1~2 个可下发问题。
3. 发给 webapp，channel 固定 `dm-codex`；等待 `task_id`，并将 `time-window` + 问题内容补录到 `WebappTasks.md`。
4. 回收后，应用补丁并本地核验：
   - `bash scripts/goal check <chapter>`
   - （必要时）`bash scripts/goal build`
5. 证明通过后：`bash scripts/goal mark <N> done`，并立即 commit + push。
6. 每轮结束前，记录 `Changelog.md` 条目，注明“本轮完成的数学定理 + 验证结果”。

## 真实完成标准（章级）

- `bash scripts/goal check N` 不再出现 `sorry`。
- 章节文件中每个定理都不再是 `: True` 的占位（若某定理仍是平凡形式需重写）。
- 该章能在本地构建环境中通过类型检查（至少对应导入树可编译）。
- 已对该章提交至少一次 commit，且与 `WebappTasks.md` 与 `Changelog.md` 成对出现。

## 全书完成标准（Goal-07）

- 40 章全部过 `bash scripts/goal check all`，无 `sorry`。
- `bash scripts/goal build` 通过。
- 生成一份最终收敛清单（最后一条 changelog）说明：未完结证明、已知缺口、依赖外部库版本。

## 每日工作约束（你我执行）

- 默认保持 `instant`，当 webapp 连续 2 次超时或无法返回可用 proof，切到 `extend` 并告知我。
- 一问一答：若有可用，保守每轮 1~2 条；必要时可加到 2 条。
- 每次本地提交前，先确认通信不再卡在频道名漂移（以 `dm-codex` 为准）。

## 文档与归档

- `ProofsInTheBook.lean`：总入口。
- `ProofsInTheBook/ChapterXX.lean`：章节主文件。
- `COMMUNICATION_PROTOCOL.md`：沟通协议。
- `WebappTasks.md`：轮次提问记录。
- `Changelog.md`：结果收敛日志。
- `scripts/goal`：执行引擎。

## /goal 命令清单

- `goal init`：重置状态。
- `goal stage`：显示阶段。
- `goal next`：显示下一个待完成章节。
- `goal run [--chapter N] [--max M]`：生成本轮提问清单（默认 1~2 条）。
- `goal check [all|N]`：扫描剩余 `sorry`。
- `goal mark <N> done`：手工完成章节账目。
- `goal build`：执行基础构建检查。
- `goal report`：阶段汇总（DONE/TODO + state）。

## 启动规则（重启时执行）

1. `.proof_goals_state` 清空到初始态：`goal=defined`，`current_chapter=1`，移除 chapter 完成标记。
2. 章节文件中的 `by trivial`、`aesop`（若作为占位）先回退为 `sorry`，恢复机械任务状态。
3. 运行 `bash scripts/goal report`，确认 `current_chapter` 在 1 附近，`TODO` 非 0，即可正式派发。
