# ANSWER_01 — Don't case-split on θ < π vs θ ≥ π. Use `orientedLevel_ne_of_ne_mod_pi`.

## TL;DR

Neither Option A nor Option B as you framed them. There's a **third option** that's much cleaner:

> Bypass `orientedLevel_injective_at_non_direction_angle` (which forces `0 ≤ θ < π`).
> Use `orientedLevel_ne_of_ne_mod_pi` (line 6915) directly — it's the **mod-π version** that
> doesn't restrict θ to [0, π).

No π case split needed. Your `hlow`/`hhigh` hypotheses on θ₀ already give the required range
on θ = interEventAngleAt(j).

## Why no case split

`orientedLevel_ne_of_ne_mod_pi` requires (for each pair p ≠ q with direction d):

  `(d.angle - π < θ)  ∧  (θ < d.angle + π)  ∧  (θ ≠ d.angle)`

From your existing hypotheses:

- `hlow : ∀ d ∈ dirs, d.angle - Real.pi < θ₀`
- `hhigh : ∀ d ∈ dirs, θ₀ < d.angle`
- `startAngle_le_interEventAngleAt`: `θ₀ ≤ θ`
- `interEventAngleAt_le_start_add_pi`: `θ ≤ θ₀ + π`

Combining:
- `d.angle - π < θ₀ ≤ θ`             → first bound
- `θ ≤ θ₀ + π < d.angle + π`         → second bound

Both bounds hold **independent of whether θ < π or θ ≥ π**. The "wrap" makes the angle larger
but always within π of every direction angle. That's exactly what mod-π injectivity wants.

## Why not Option A (subtract π, apply [0,π) lemma)

`orientedLevel (θ - π) p = -orientedLevel θ p` (sign flip via `orientedLevel_add_pi`), so
injectivity IS preserved under θ → θ - π. But this forces you to:
- case-split on whether θ ≥ π
- reprove the no-direction-angle hypothesis at the shifted θ - π
- handle the wrap-crossing case where the shifted angle becomes negative

All avoidable.

## Why not Option B as you described

Your Option B is on the right track but you anchored it to `only_event_between_interEventAnglesAt`,
which gives "θ ≠ shiftedSortedAngleAt at all events j' ≠ j". That's a sweep-event condition.

What you actually need is "θ ≠ d.angle for every direction d ∈ dirs", which is the **direction**
condition, not the **event** condition. They're related but not the same.

## Concrete proof skeleton

```lean
private theorem inj_at_interEventAngleAt
    {points : Finset Point2} {k : ℕ}
    (hcard : points.card = 2 * k)
    (hne : (directionsDeterminedBy points).Nonempty)
    (θ₀ : ℝ) (s : Fin (directionsDeterminedBy points).card)
    (hlow  : ∀ d ∈ directionsDeterminedBy points, d.angle - Real.pi < θ₀)
    (hhigh : ∀ d ∈ directionsDeterminedBy points, θ₀ < d.angle)
    (hgap  : ∀ t : Fin (directionsDeterminedBy points).card,
              t.val < s.val → sortedAngleAt points t < θ₀)
    (j : Fin ((directionsDeterminedBy points).card + 1)) :
    Function.Injective (fun a : Fin (2 * k) =>
      orientedLevel (interEventAngleAt points hne θ₀ s j)
        ((sweepLabelingAt hcard θ₀).point a)) := by
  set L := sweepLabelingAt hcard θ₀
  set θ := interEventAngleAt points hne θ₀ s j with hθ_def
  -- range bounds on θ
  have hθ_lo : θ₀ ≤ θ :=
    startAngle_le_interEventAngleAt (points := points) hne θ₀ s hlow hhigh hgap j
  have hθ_hi : θ ≤ θ₀ + Real.pi :=
    interEventAngleAt_le_start_add_pi (points := points) hne θ₀ s hlow hhigh hgap j
  -- per-pair argument via orientedLevel_ne_of_ne_mod_pi
  intro a b hab
  by_contra hne_ab
  have ha_ne_b : a ≠ b := fun h => by subst h; exact hne_ab rfl
  have hpq : L.point a ≠ L.point b := fun h => ha_ne_b (L.point_injective h)
  have hdir_mem : direction (L.point a) (L.point b) ∈ directionsDeterminedBy points :=
    L.direction_mem ha_ne_b
  -- range relative to this particular direction
  have hd_lo : (direction (L.point a) (L.point b)).angle - Real.pi < θ := by
    have := hlow _ hdir_mem
    linarith
  have hd_hi : θ < (direction (L.point a) (L.point b)).angle + Real.pi := by
    have := hhigh _ hdir_mem
    linarith
  -- the no-tie condition: θ ≠ this direction's angle
  -- This is the ONE thing you still owe: prove θ avoids every direction angle.
  -- For corner j (j = 0 or j = card), θ = θ₀ or θ₀ + π, both excluded by hlow/hhigh strict.
  -- For middle j, use the fact that θ = genericAngleBetween two shifted sortedAngleAts
  -- and any direction's sortedAngleAt is one of the events; show θ falls strictly between.
  have hθ_ne : θ ≠ (direction (L.point a) (L.point b)).angle := by
    -- this is where only_event_between_interEventAnglesAt-style argument lives
    sorry  -- TODO: prove via case-split on j corner vs middle
  exact orientedLevel_ne_of_ne_mod_pi hpq hd_lo hd_hi hθ_ne hab
```

The `sorry` for `hθ_ne` is the only real content. For middle j it follows from
`interEventAngleAt_lt_shiftedSortedAngle` + `shiftedSortedAngleAt_lt_interEventAngleAt_succ`
applied at the index where the direction's sortedAngleAt sits. For corner j (0 and card),
θ = θ₀ or θ₀ + π and both `hlow`/`hhigh` are strict so the inequality is immediate.

## On your question (3): when can interEventAngleAt(j) ≥ π for non-corner j?

Yes, it can — when `α + β ≥ π` where α = sortedAngleAt(unwrapped index), β = sortedAngleAt(wrapped index, before adding π). In the cross-event case (j-1 unwrapped, j wrapped), interEventAngleAt(j) = (α + β + π) / 2, which is ≥ π exactly when α + β ≥ π.

This is why I rejected Option A — the shifted angle θ - π in that case becomes (α + β - π)/2 ∈ [0, π/2), and the lower bound argument relative to sortedAngleAt(j-1) = α becomes "(α+β-π)/2 > α - π" which is α+β-π > 2α-2π, i.e. β > α - π — trivially true but you've lost the connection to your original sweep bounds.

The mod-π approach sidesteps this entirely because it works in the (d.angle - π, d.angle + π) window for **each direction d**, not in a fixed [0, π) interval.

## What to do next

1. Implement the skeleton above, leaving `hθ_ne` as a separate lemma you can iterate on.
2. For `hθ_ne`, write a helper:
   ```
   private theorem interEventAngleAt_ne_direction_angle
       ... (d : Direction) (hd : d ∈ directionsDeterminedBy points) :
       interEventAngleAt points hne θ₀ s j ≠ d.angle
   ```
   Case on j = 0 (use `interEventAngleAt_zero` + `hhigh`),
   case on j = card (use `interEventAngleAt_last` + `hlow` shifted by π),
   middle case (use the strict bounds from `_lt_shiftedSortedAngle` + `_lt_..._succ`).
3. Remote build, iterate.
4. If `hθ_ne` for the middle case gets ugly, file a follow-up question — it's the only genuinely
   nontrivial piece.

Good luck.
