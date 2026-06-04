# CHAPTER 11 / Parameterized sweep lemmas

I hit a blocker before editing code further.

What I tried:
1. Read current `Chapter11.lean` around line 7320: only `sweepLabelingAt`, `shiftedSortedAngleAt`, `interEventAngleAt`, and the first 4 mirror lemmas are present.
2. Compared with existing un-parameterized lemmas (`interEventAngle_lt_sortedAngle`, `sortedAngle_lt_interEventAngle_succ`, etc.) and tried to mirror them with `shiftedSortedAngleAt`.
3. Inspected recent commit history; current branch has no implementations for these `_at` lemmas yet.
4. Reviewed assumptions: the user’s template asks adding the same `hlow / hhigh` pair to many `_at` lemmas.

Blocker:
- With current `shiftedSortedAngleAt` definition (`+π` on wrap), lemmas such as
  `interEventAngleAt_le_start_add_pi` / `shiftedSortedAngleAt_lt_interEventAngleAt_succ` seem not derivable from only
  `hlow : ∀ d, d.angle - π < θ₀` and `hhigh : ∀ d, θ₀ < d.angle` for arbitrary `s : Fin r`.
- Counterexample pattern: take direction angles sorted e.g. `[-1.4, -1.0, 1.0]`, choose `θ₀ < -1.4`, `s = 1`, then a wrapped `shiftedSortedAngleAt` value is `angle + π` and can exceed `θ₀ + π`, breaking the final-interval bound needed for those lemmas.

Decision needed:
- Are the requested `_at` lemmas intended to include extra hypotheses tying `s` to `θ₀` (so these properties hold), or should the `shiftedSortedAngleAt`/`interEventAngleAt` definitions be adjusted further (e.g., additional case split or changed start-angle indexing) so those lemmas are true for all `s`?
- Please confirm the intended additional assumption(s) for the first five order lemmas, especially `interEventAngleAt_le_start_add_pi` / `shiftedSortedAngleAt_lt_interEventAngleAt_succ`.
