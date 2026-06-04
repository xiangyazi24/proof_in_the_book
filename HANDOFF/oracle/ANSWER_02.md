# ANSWER_02 — Option X (extract + heartbeats), with Option Y as backup

## Recommendation: Option X (extract, raise heartbeats)

Option X gets you unblocked fastest. The timeout is elaboration-level
(`mem_directionsDeterminedBy` → `point_surjective_on` × 2 →
`only_event_between_interEventAnglesAt` produces a huge nested proof term
that the elaborator chews through every time it's used in context). Extracting
the proof into a `private theorem` compiles it **once** at the namespace level,
where you can also give it an explicit heartbeat allowance.

```lean
section
set_option maxHeartbeats 1000000 in
private theorem interEventAngleAt_ne_direction_angle
    {points : Finset Point2} {k : ℕ}
    (hcard : points.card = 2 * k)
    (hne : (directionsDeterminedBy points).Nonempty)
    (θ₀ : ℝ) (s : Fin (directionsDeterminedBy points).card)
    (hlow  : ∀ d ∈ directionsDeterminedBy points, d.angle - Real.pi < θ₀)
    (hhigh : ∀ d ∈ directionsDeterminedBy points, θ₀ < d.angle)
    (hgap  : ∀ t : Fin (directionsDeterminedBy points).card,
              t.val < s.val → sortedAngleAt points t < θ₀)
    (j : Fin ((directionsDeterminedBy points).card + 1))
    (d : Direction) (hd : d ∈ directionsDeterminedBy points) :
    interEventAngleAt points hne θ₀ s j ≠ d.angle := by
  -- your current `hθ_ne` proof body goes here, untouched
  sorry
end
```

Then in `inj_at_interEventAngleAt`, replace the inline `hθ_ne` with:

```lean
  have hθ_ne : θ ≠ (direction (L.point a) (L.point b)).angle :=
    interEventAngleAt_ne_direction_angle hcard hne θ₀ s hlow hhigh hgap j _ hdir_mem
```

The `set_option maxHeartbeats 1000000 in` is local to that one lemma; it does
not affect the rest of the file. Standard pattern for elaboration-heavy proofs
(cf. `feedback_native_decide_heartbeats` in the project lessons).

Try this first. If it still times out at 1M heartbeats (unusual), bump to 0
(unlimited) on just that lemma. Don't put 0 at file scope — that hides genuine
runaway proofs.

## Option Y for completeness (numerical, harder but cleaner)

If you want to ditch the labeled-points + existentials chain entirely, here's
the math. Let `k` be the index of `d` in `sortedAngles`, so
`sortedAngleAt points k = d.angle`, and split on `j`:

**Case j = 0**: `interEventAngleAt(0) = θ₀` and `hhigh d hd : θ₀ < d.angle`,
so `θ₀ ≠ d.angle`. Immediate.

**Case j = r** (the upper corner): `interEventAngleAt(r) = θ₀ + π` and
`hlow d hd : d.angle - π < θ₀`, i.e., `d.angle < θ₀ + π`. So `θ₀ + π ≠ d.angle`.
Immediate.

**Case j = m + 1, m ∈ [0, r-1)** (middle, the real work):
By def, `interEventAngleAt(m+1) = genericAngleBetween(shiftedSortedAngleAt(s, m),
shiftedSortedAngleAt(s, m+1))`, which sits strictly between the two
shifted-sorted angles. So:
```
shiftedSortedAngleAt(s, m) < interEventAngleAt(m+1) < shiftedSortedAngleAt(s, m+1)
```

Assume for contradiction `interEventAngleAt(m+1) = d.angle = sortedAngleAt(k)`.
Three sub-cases on the wrap pattern at index `m`:

- **Fully unwrapped (s + m + 1 < r)**:
  `shiftedSortedAngleAt(s, m)   = sortedAngleAt(s+m)`
  `shiftedSortedAngleAt(s, m+1) = sortedAngleAt(s+m+1)`
  So `sortedAngleAt(s+m) < sortedAngleAt(k) < sortedAngleAt(s+m+1)`.
  By `sortedAngleAt_strictMono`, `s+m < k < s+m+1`, impossible.

- **Mid-wrap (s + m < r = s + m + 1)**:
  `shiftedSortedAngleAt(s, m)   = sortedAngleAt(r-1)`     (largest direction angle)
  `shiftedSortedAngleAt(s, m+1) = sortedAngleAt(0) + π`
  Lower bound: `sortedAngleAt(r-1) < sortedAngleAt(k)`. But `r-1` is the max
  index of `sortedAngleAt`, so `sortedAngleAt(k) ≤ sortedAngleAt(r-1)` by
  monotonicity (or by `sortedAngleAt_lt_pi` if `k = r-1` is excluded).
  Contradiction.

- **Fully wrapped (s + m ≥ r)**:
  `shiftedSortedAngleAt(s, m)   = sortedAngleAt(s+m - r) + π`,
  i.e., `≥ π`.
  Lower bound becomes `π ≤ shiftedSortedAngleAt(s, m) < sortedAngleAt(k) = d.angle`.
  But `d.angle < π` (since `d` is a direction and `Direction.angle_lt_pi`).
  Contradiction.

This is ~40 lines of case-split, each sub-case 8-12 lines. Cleaner than the
labeled-point chain but more code than Option X.

## Picking which

- If your Option X works after extraction + raised heartbeats → **ship it**.
  The labeled-point approach is fine when it elaborates; the issue was just
  inlining cost.
- If Option X still times out at 1M, go Option Y — the numeric proof has a
  smaller proof term.
- Don't try to be clever and mix; pick one structure.

## Quick win: also try

If the `mem_directionsDeterminedBy → point_surjective_on` unpacking is where
the time goes, an even smaller extraction works: pull the unpacking into a
named term `have direction_witness := ...` BEFORE the long branching, so
elaboration finishes it once and reuses the term. Then `only_event_between`
is the only remaining cost. This is sometimes enough without the maxHeartbeats
bump.

Go.
