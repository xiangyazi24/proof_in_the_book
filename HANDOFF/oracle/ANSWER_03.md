# ANSWER_03 — Triage: most of spark's batch C is dead code

## TL;DR

I just grepped — three of spark's four batch C lemmas have **zero downstream uses** in your
current Chapter11.lean. Just delete them. Only `only_event_between_interEventAnglesAt` is
referenced (inside your `mono_at_eventAt` at line ~8093, via the call at line 8120), so it
needs to be fixed or rewritten.

Reference table:

| Lemma | Defined at | Used downstream? | Action |
|---|---|---|---|
| `shiftedSortedAngleAt_mono` | 7750 | check if used inside `only_event_between`'s proof; if not → **delete** |
| `only_event_between_interEventAnglesAt` | 7781 | YES (line 8120 in mono_at_eventAt) | **rewrite from scratch** |
| `no_tie_from_start_to_interEventAt` | 7896 | none | **delete** |
| `sweepLabelingAt_inj_at_interEvent` | 7936 | none | **delete** |

(I ran `rg -n "lemma_name" ProofsInTheBook/Chapter11.lean` for each — the three marked
"delete" only show their own def-site.)

Run `rg -n "shiftedSortedAngleAt_mono" ProofsInTheBook/Chapter11.lean` and check — if it
appears only at line 7750 and inside `only_event_between_interEventAnglesAt`'s proof body
(7781-7931), you can inline or fix it as part of the rewrite. If it doesn't appear inside
that proof either, delete it.

## API answers

- **`Fin.strictMono_iff_lt_succ`**: EXISTS in Mathlib. Multiple places in Mathlib itself use
  it (Composition.lean, SimplicialSet/*, LinearAlgebra/Basis/Flag.lean). Signature:
  `Fin.strictMono_iff_lt_succ : StrictMono f ↔ ∀ i : Fin n, f (Fin.castSucc i) < f i.succ`.
  Spark's invocations are fine — the failures are elsewhere (e.g. `_` argument).

- **`Nat.le_sub_of_lt`**: DOES NOT EXIST in this form. Mathlib variants:
  - `Nat.le_sub_of_add_le : k + m ≤ n → k ≤ n - m`
  - `Nat.lt_sub_iff_add_lt : a < b - c ↔ a + c < b` (when c ≤ b)
  - `Nat.sub_lt_iff_lt_add` and friends
  - **Easiest fix: replace with `by omega`.** `omega` handles all linear Nat arithmetic
    including subtraction, and is what the rest of this codebase already uses.

## Rewrite of `only_event_between_interEventAnglesAt`

Spark expanded the non-_at version (60 lines) to 150 lines because of mishandled wrap.
The clean structure: case on wrap, in each case reduce to a numerical bounds argument
using `sortedAngleAt_strictMono`. **No need to chain through labeled points.**

Skeleton (adapt to your exact statement signature):

```lean
section
set_option maxHeartbeats 600000 in
theorem only_event_between_interEventAnglesAt
    {points : Finset Point2} {k : ℕ}
    (hcard : points.card = 2 * k)
    (hne : (directionsDeterminedBy points).Nonempty)
    (θ₀ : ℝ) (s : Fin (directionsDeterminedBy points).card)
    (hlow  : ∀ d ∈ directionsDeterminedBy points, d.angle - Real.pi < θ₀)
    (hhigh : ∀ d ∈ directionsDeterminedBy points, θ₀ < d.angle)
    (hgap  : ∀ t : Fin (directionsDeterminedBy points).card,
              t.val < s.val → sortedAngleAt points t < θ₀)
    (j : Fin (directionsDeterminedBy points).card)
    (a b : Fin (2 * k))
    (hab : a ≠ b)
    (θ : ℝ)
    (hθ_icc : θ ∈ Set.Icc
      (interEventAngleAt points hne θ₀ s ⟨j.val, by omega⟩)
      (interEventAngleAt points hne θ₀ s ⟨j.val + 1, by omega⟩))
    (hθ_ne : θ ≠ shiftedSortedAngleAt points hne s j) :
    orientedLevel θ ((sweepLabelingAt hcard θ₀).point a) ≠
      orientedLevel θ ((sweepLabelingAt hcard θ₀).point b) := by
  -- Strategy: show θ avoids every direction angle mod π, then apply
  -- orientedLevel_ne_of_ne_mod_pi.
  intro htie
  set L := sweepLabelingAt hcard θ₀
  have hpq : L.point a ≠ L.point b := fun h => hab (L.point_injective h)
  have hdir_mem : direction (L.point a) (L.point b) ∈ directionsDeterminedBy points :=
    L.direction_mem hab
  -- Three cases of the wrap pattern.
  by_cases hcase_unwrapped : s.val + j.val + 1 < (directionsDeterminedBy points).card
  · -- Fully unwrapped: both shiftedSortedAngleAt(s, j) and shiftedSortedAngleAt(s, j+1)
    -- equal raw sortedAngleAt indices.
    sorry
  by_cases hcase_midwrap : s.val + j.val < (directionsDeterminedBy points).card
  · -- Wrap at j+1: shiftedSortedAngleAt(s, j+1) = sortedAngleAt(0) + π.
    -- d.angle ∈ [0, π) and shiftedSortedAngleAt(s, j) ≥ d.angle by upper bound
    -- of the largest sortedAngle; combine.
    sorry
  · -- Fully wrapped: shiftedSortedAngleAt(s, j) = sortedAngleAt(s+j-r) + π ≥ π.
    -- d.angle < π, immediate contradiction with θ ≥ shiftedSortedAngleAt(s, j) > d.angle.
    sorry
end
```

Each `sorry` is 10-15 lines of bounded numerical work using `sortedAngleAt_strictMono` and
`sortedAngleAt_lt_pi`. Total ~80 lines.

**OR** — if you want a much shorter route and `only_event_between_interEventAnglesAt` is
**only** called once (line 8120), inline its content into the call site using your
`interEventAngleAt_ne_direction_angle` approach. Then delete the named lemma entirely.
This is the cleanest path because it converges with the numerical structure you already
got working in `inj_at_interEventAngleAt`.

## My recommendation

Do this in order:

1. **Delete** `no_tie_from_start_to_interEventAt`, `sweepLabelingAt_inj_at_interEvent`,
   and `shiftedSortedAngleAt_mono` (if not internally used).
2. Check the single use of `only_event_between_interEventAnglesAt` at line 8120 inside
   `mono_at_eventAt`. **If it's exactly the kind of argument that `interEventAngleAt_ne_direction_angle`
   already handles**, inline the proof there and delete `only_event_between_interEventAnglesAt`.
3. Otherwise rewrite `only_event_between_interEventAnglesAt` per the skeleton above.
4. Remote build, see what survives.

Don't fix spark's broken code line-by-line — it has structural problems in all 3 lt_trichotomy
branches and the patch surface is larger than a rewrite.

Go.
