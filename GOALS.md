# /goal 长期执行手册（Proofs in THE BOOK）

这份文件定义的是“全书持续化执行目标”，不是某一章的数学目标。它和 `scripts/goal` 联动，支持循环推进 1..40 章。

## 总目标
- 在仓库中把《Proofs from THE BOOK》40 章的占位定理从 `sorry` 全部替换为 Lean 证明。
- 每轮保持本地机械工作与 webapp 的重负载证明分工闭环。

## /goal 长期状态机（固定 7 阶段）
- **Goal-01 工程稳态**：构建与任务追踪可复现。
- **Goal-02 任务切分**：每章可独立派发的子问题。
- **Goal-03 1..10 章完成**：每章完成并提交。
- **Goal-04 11..20 章完成**：每章完成并提交。
- **Goal-05 21..30 章完成**：每章完成并提交。
- **Goal-06 31..40 章完成**：每章完成并提交。
- **Goal-07 全书收敛**：全局无 `sorry` 且构建通过。

## 长期执行循环（每轮）
1. `bash scripts/goal next`：找出下一个未完成章节（包含 `sorry`）。
2. `bash scripts/goal run`：输出这一轮建议问题清单（最多 2 个问题）与要发送的内容。
3. 你把问题按“1~2条”发给 webapp。
4. 回收后，执行：
   - `bash scripts/goal check <chapter>`：确认剩余 `sorry`。
   - （可选）`bash scripts/goal build`：校验本地构建。
5. `bash scripts/goal mark <chapter> done`：手工记账阶段进度。
6. 每次本地更新后：**立即** `commit + push`。

## 工程阶段验收条件

### Goal-01 可执行条件
- `scripts/goal check all` 可运行。
- `lake env lean` 至少能够打开根模块。
- `COMMUNICATION_PROTOCOL.md` 记录 `dm-codex` 通道协议。

### Goal-02 任务切分条件
- 每章都存在固定入口定理（`chapterNN : True`）与子命题。
- 每个章节至少有 1 个可追踪任务。
- `WebappTasks.md` 以每轮 1~2 项提问。

### 每章完成条件（Goal-03~06）
- 对应 `ProofsInTheBook/ChapterXX.lean` 中不存在 `sorry`。
- 对应章节 `goal check XX` 显示 0。
- 本轮变更已 `commit + push`。

### Goal-07 全书收敛条件
- `bash scripts/goal check all` 无 TODO。
- `bash scripts/goal build` 通过（或至少关键构建命令无失败）。
- 形成“完成清单”提交。

## 目录与职责
- 总入口：`ProofsInTheBook.lean`
- 章节文件：`ProofsInTheBook/Chapter01.lean` ~ `ProofsInTheBook/Chapter40.lean`
- 通信协议：`COMMUNICATION_PROTOCOL.md`
- 任务文件：`WebappTasks.md`
- 执行脚本：`scripts/goal`

## /goal 命令对照（建议）
- `goal init`：重置/初始化执行状态。
- `goal stage`：显示当前执行阶段。
- `goal next`：显示下一个未完成章节。
- `goal run [--chapter N] [--max M]`：输出本轮 1~2 个具体任务。
- `goal check [N|all]`：查看未完成 `sorry`。
- `goal mark <N> done`：标记里程碑。
- `goal build`：执行本地基础构建检查。
- `goal report`：汇总当前完成率。
