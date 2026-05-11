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
- `dm-codex`

Send/Receive workflow (1-2 questions at a time)
1. From local: call bridge to submit one compact question.
2. Wait for task id and monitor `GET /api/result/{id}`.
3. Apply returned patch or theorem proof updates if valid.
4. Commit and push immediately after local updates.

Why this was used
- Keeps one question per round short enough for quick handoff.
- Avoids stale channel bleed between tabs in latest fix.

Example CLI (if using wrapper)
- `./ask-chatgpt.sh --channel dm-codex "Your question here"`

Note
- This repo uses mechanical + formal split:
  - Local side prepares Lean skeleton / orchestration files.
  - Webapp solves hard proofs and returns `sorry`-to-proof replacements.
