# GOALS for Proofs in THE BOOK Lean Formalization

## 长期目标
- 2026-05-11 至少完成《Proofs from THE BOOK》40 章全部 formalization。
- 每章以可复用的定理名、可验证脚本和可追溯任务状态完成。

## 里程碑（Goal 1-7）

### Goal 1：工程稳态（2-3 次迭代）
- `lakefile.lean` 可复现构建。
- `ProofsInTheBook.lean` 能稳定导入 1..40 章。
- `scripts/goal check all` 返回可执行指标。
- 与 `dm-codex` 通道通信协议写入 `COMMUNICATION_PROTOCOL.md`。

### Goal 2：全书任务剖分（1 次迭代）
- 每章 1 个根定理 + N 个子定理（初始建议 5-6 个）占位。
- 所有定理命名、文件与章节对应（`ChapterNN`）。
- Webapp 任务以 `WebappTasks.md` 以每轮 1-2 项方式派发。

### Goal 3：1..10 章完成（核心）
- 每章 1 次 end-to-end 回合：
  - 本地更新占位 => 提交 => 推送。
  - webapp 回填 `sorry`。
  - 本地 `scripts/goal check NN == 0`。

### Goal 4：11..20 章完成
- 同上。

### Goal 5：21..30 章完成
- 同上。

### Goal 6：31..40 章完成
- 同上。

### Goal 7：全书收敛
- `scripts/goal check all` 显示 0 TODO。
- 生成最终整书证明记录（提交日志 + 完成清单）。

## 执行规则（配合 `goal`）
- 每完成一次本地更新（包括任务派发和结果合并）都 `commit + push`。
- `goal next` 返回下一个待做章节。
- 每次 webapp 询问一次不超过 2 项。
- 章完成条件：
  - 该章节文件中不存在 `sorry`。
  - 提交信息包含章节与子定理项。

## `goal` 命令对照
- `goal next`：定位下一个有 `sorry` 的章节
- `goal check <NN>`：查看某章剩余 `sorry` 数
- `goal check` 或 `goal check all`：检查全书待办
- `goal mark <NN> done`：手工标记里程碑（用于短期阻塞或已确认草案）
- `goal report`：阶段性汇总

## 执行建议（每轮）
1. 本地选一章（例如 goal next）。
2. 派发 1-2 个 webapp 任务（`WebappTasks.md` 追加）。
3. 回收并核验后运行 `goal check <NN>`。
4. `goal report` 记录状态。
5. `commit + push`。
