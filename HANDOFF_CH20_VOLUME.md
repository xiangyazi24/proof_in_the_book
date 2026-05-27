# HANDOFF — Ch20 Monsky: volume(convexHull {a,b,c}) = realTriangleArea

**From:** Claude Code (opus-4-7), session 2026-05-26
**To:** Fresh CC session on `~/repos/proof_in_the_book`
**Baseline:** commit `ef91815` (main, 0 sorry / 0 axiom)

## Goal

Prove for any `a b c : ℝ × ℝ`:

```lean
theorem volume_convexHull_triangle :
    MeasureTheory.volume (convexHull ℝ ({a, b, c} : Set (ℝ × ℝ))) =
      ENNReal.ofReal (realTriangleArea a b c)
```

This is the missing **measure-theoretic bridge** for the Ch20 Monsky proof.
With it in hand, the geometric dissection-cover argument (currently the only
remaining gap to discharge the `MonskyCertificate` escape in `chapter20`)
becomes tractable: a real triangulation of the unit square gives n triangles
covering [0,1]² with disjoint interiors; sum of `realTriangleArea`s = 1; and
combined with the equal-area hypothesis (each = 1/n) we connect to the
rainbow-triangle area contradiction already proven (lines 402-434, 522-625).

## What's already done in `ProofsInTheBook/Chapter20.lean`

Read these to anchor (all build-verified, 0 sorry / 0 axiom):

- `doubleArea_eq_det_fin_two` — doubleArea = 2x2 det of edge vectors.
- `realTriangleArea_eq_half_abs_det` — area = |det|/2.
- Structural lemmas: `doubleArea_translate`, `doubleArea_zero_left`,
  `doubleArea_eq_zero_left_sub`, `doubleArea_swap_right` (antisym),
  `doubleArea_cycle`, `doubleArea_eq_zero_iff_collinear`,
  `realTriangleArea_translate / _swap_right / _cycle`.
- `triangleAffine a b c (st : ℝ × ℝ) := a + st.1 • (b - a) + st.2 • (c - a)` —
  the affine parametrization. Vertex-image simp lemmas done.
- `triangleAffine_eq_combo` — parametrization = (1-s-t)•a + s•b + t•c.
- `filled2Simplex` set + `filled2Simplex_mem_iff`.
- **Forward direction proven**: `triangleAffine_mem_convexHull` +
  `triangleAffine_image_subset_convexHull`.

## What's needed (three bricks + glue)

### Brick 1: `volume_filled2Simplex = ENNReal.ofReal (1/2)`

The 2-D Lebesgue measure of the filled standard 2-simplex.

**Pitfall I hit:** Mathlib's `regionBetween f g s` uses an **open** interval
`Ioo (f x) (g x)` for the y-component, not `Icc`. So
`filled2Simplex = regionBetween 0 (fun s => 1-s) (Icc 0 1)` is FALSE as set
equality — they differ by the measure-zero boundary `{p.2 = 0}` (and
`{p.2 = 1 - p.1}`).

**Two clean routes:**

(a) **measure-congr route**: prove `filled2Simplex` and the regionBetween
    differ by a null set (the boundary edges), then use
    `MeasureTheory.measure_congr` to transfer the volume. The boundary edges
    are `ℝ × {0}` and a graph of a continuous function, both measure zero in
    `volume.prod volume`.

(b) **direct Fubini route**: skip regionBetween entirely. Use
    `MeasureTheory.Measure.volume_eq_prod` to rewrite volume as
    `volume.prod volume`, then `MeasureTheory.Measure.prod_apply` with a
    `MeasurableSet filled2Simplex` proof (provable via `measurability` since
    the set is a finite intersection of closed half-spaces in continuous
    coords). The inner slice is `Set.Icc 0 (1 - s)` of volume `ENNReal.ofReal
    (1 - s)`. Then `∫⁻ s in Set.Icc 0 1, ENNReal.ofReal (1-s)` =
    `ENNReal.ofReal (∫ s in 0..1, (1-s))` = `ENNReal.ofReal (1/2)`. Compute
    via `intervalIntegral.integral_sub`, `intervalIntegral.integral_const`,
    `intervalIntegral.integral_id`.

Route (b) is more direct; I'd try it first.

**Namespace corrections from my failed attempts:**
- `regionBetween` is at top level, NOT `MeasureTheory.regionBetween`.
- The product-volume lemma is `MeasureTheory.Measure.volume_eq_prod`.
- The integral lemma is `MeasureTheory.volume_regionBetween_eq_integral`
  (not just `volume_...`).

### Brick 2: convex-hull reverse direction

Prove `convexHull ℝ ({a, b, c} : Set (ℝ × ℝ)) ⊆ triangleAffine a b c '' filled2Simplex`.

Combined with the existing `triangleAffine_image_subset_convexHull` forward
direction, this gives the set equality:

```lean
theorem convexHull_eq_triangleAffine_image (a b c : ℝ × ℝ) :
    convexHull ℝ ({a, b, c} : Set (ℝ × ℝ)) =
      triangleAffine a b c '' filled2Simplex
```

**Mathlib API to use:** `Set.Finite.convexHull_eq` for a finite set, which
characterizes convex hull as the set of `Finset.centerMass` images. For the
3-point set `{a, b, c}` (possibly with repeated elements), the cleanest is
probably:

- `convexHull_eq_image_combination` (if it exists), OR
- Unfold via `Set.Finite.convexHull_eq` + handle the index Finset
  (which may have 1, 2, or 3 elements depending on repetitions).

Given a point `p = α•a + β•b + γ•c` with α,β,γ ≥ 0, α+β+γ = 1, set
`s = β, t = γ`. Then `1 - s - t = α ≥ 0`, so `(s, t) ∈ filled2Simplex`.
And `triangleAffine a b c (s, t) = (1-s-t)•a + s•b + t•c = p`.

The challenge is the **Mathlib unwrapping**: getting from `p ∈ convexHull ℝ
{a, b, c}` to an explicit `(α, β, γ)` form. May need:
- `mem_convexHull` characterization in `Mathlib.Analysis.Convex.Hull`
- `convexHull_eq` in `Mathlib.Analysis.Convex.Combination`

### Brick 3: glue via `addHaar_image_linearMap`

The final step:

```lean
volume (convexHull ℝ {a, b, c})
  = volume (triangleAffine a b c '' filled2Simplex)            -- Brick 2
  = volume (M '' filled2Simplex)  where M = the linear part    -- translation invariance
  = ENNReal.ofReal |LinearMap.det M| * volume filled2Simplex   -- addHaar_image_linearMap
  = ENNReal.ofReal |doubleArea a b c| * ENNReal.ofReal (1/2)   -- doubleArea_eq_det_fin_two + Brick 1
  = ENNReal.ofReal (|doubleArea a b c| / 2)
  = ENNReal.ofReal (realTriangleArea a b c)
```

The linear part: define a `LinearMap` version of `triangleAffine` minus the
translation. Specifically:

```lean
noncomputable def triangleEdgeMap (a b c : ℝ × ℝ) : (ℝ × ℝ) →ₗ[ℝ] (ℝ × ℝ) :=
  { toFun := fun st => st.1 • (b - a) + st.2 • (c - a)
    map_add' := ...
    map_smul' := ... }
```

Then `triangleAffine a b c st = a + triangleEdgeMap a b c st`, so
`triangleAffine a b c '' S = a +ᵥ (triangleEdgeMap a b c '' S)`.

**Mathlib lemmas:**
- `MeasureTheory.Measure.addHaar_image_linearMap` (in
  `Mathlib/MeasureTheory/Measure/Lebesgue/EqHaar.lean:300`) gives
  `μ (f '' s) = ENNReal.ofReal |LinearMap.det f| * μ s`.
- Translation invariance: `Measure.measure_preimage_add` or
  `MeasureTheory.Measure.add_addHaar` — adding a constant doesn't change
  Lebesgue measure. Variant: `Set.image (· + v) s = v +ᵥ s` and Lebesgue is
  add-left-invariant.
- `LinearMap.det (triangleEdgeMap a b c) = doubleArea a b c`: prove via
  `LinearMap.det_toMatrix` with `Basis.finTwoProd` (standard basis of ℝ × ℝ),
  matrix is `!![b.1-a.1, c.1-a.1; b.2-a.2, c.2-a.2]`, det = doubleArea (use
  `doubleArea_eq_det_fin_two` from `c609eef`).

Mathlib volume on `ℝ × ℝ` IS `IsAddHaarMeasure` — check `instance` declarations
in `Mathlib/MeasureTheory/Measure/Lebesgue/EqHaar.lean` and product instances.

## Workflow notes (READ FIRST)

- **Remote build only**, never local on the mini (will OOM):
  ```
  /Users/huangx/.openclaw/workspace/scripts/remote-build.sh proof_in_the_book
  ```
  Single-file mode `--file ProofsInTheBook/Chapter20.lean` only works if all
  deps are prebuilt (Mathlib is cached on uisai1).
- A new `import` (e.g. importing Archive) requires full `lake build` to
  trigger building the new dep.
- After each lemma compiles, **commit promptly** in the codex micro-commit
  style. Whitespace check: `git diff --check` before commit.
- `nohup ... > /tmp/foo.log 2>&1 &` for builds to survive SSH disconnects.
- Codex (codex-ssem tmux session) was the long-running grinder on this repo
  before — currently dormant; user redirected to CC. **Stay off Ch22 and
  Ch39 (TuckerLemmaCore.lean)** — those are codex's live targets, collision
  risk if codex resumes.
- The repo policy is **zero sorry / zero axiom** in the library (files
  under `ProofsInTheBook/`). Never commit a sorry. Scratch files at top
  level (`scratch_*.lean`) are NOT in the lib build and CAN hold drafts.
- Chinese / English mixing in commit messages OK; user prefers concise.

## Why I'm handing off rather than continuing

I (current session) pushed 4 build-verified Ch20 commits today (det bridge,
structural lemmas, parametrization+forward, listed at top). Attempted Brick
1 via the `regionBetween` route and hit the open-interval pitfall + several
namespace name corrections across 4 failed build iterations. The right path
(direct Fubini OR measure_congr) requires fresher focus on Mathlib's measure
API than I have left in this session. Reverted cleanly to `ef91815`.

Fresh session should land all three bricks in a few hours of focused work.
