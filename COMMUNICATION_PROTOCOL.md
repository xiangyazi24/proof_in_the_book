# Communication Protocol with ChatGPT Webapp (chatgpt-bridge)

Purpose
- Keep this repository collaboration workflow stable for Lean proof outsourcing.

Transport
- Local bridge server: `http://localhost:8801`
- API endpoints:
  - `POST /api/ask` : submit a task
  - `GET /api/pending?channel=<channel>` : webapp side polls for work
  - `POST /api/respond/{task_id}` : webapp posts answer
  - `GET /api/result/{task_id}` : poll answer from caller
  - `GET /api/status` : check backlog and active channels
  - `GET /api/channels` : active channel list

Preferred Channel for this repo
- Historical channel: `dm-codex`
- Current active bridge channel for this run: `ssem`

Send/Receive workflow (1-2 questions at a time)
1. From local: call bridge to submit one compact question.
2. Record the task id in `BRIDGE_TASKS.md` or `WebappTasks.md`.
3. If active delivery is unavailable, poll `GET /api/result/{id}` until
   `completed`, `failed`, or an explicit timeout is recorded.
4. If active delivery is available, do not block on polling; continue local
   organization work and process delivered responses when they arrive.
5. Apply returned patch or theorem proof updates if valid.
6. Commit and push immediately after local updates.

Why this was used
- Keeps one question per round short enough for quick handoff.
- Avoids stale channel bleed between tabs in latest fix.

Example CLI (if using wrapper)
- `CHATGPT_CHANNEL_GUARD=0 ./ask-chatgpt.sh --channel ssem "Your question here"`

Note
- This repo uses mechanical + formal split:
  - Local side prepares Lean skeleton / orchestration files.
  - Webapp solves hard proofs and returns `sorry`-to-proof replacements.
