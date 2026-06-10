import ProofsInTheBook.ZinanFFCT25
import ProofsInTheBook.SphericalCore

/-!
# `ZinanFFCT26` — the Chapter 13 B1 Gram-sign extraction: the derivative-algebra layer

This module implements the *worker / needs-care* bricks of the B1 Gram-sign extraction design
(`HANDOFF/design-rounds/ch13-b1-gram-extraction.md`).  These are the algebraic and one-variable
calculus facts that the master assembly (`hβ`/`hα` extraction, normalization, `StuckAtKData`
construction) consumes.  Nothing here uses the heavy convex-geometry machinery; everything is
self-contained over `E3 = EuclideanSpace ℝ (Fin 3)` with `cross`, `det3`, and the Rodrigues `rot`.

## Bricks delivered

* **Brick 1** `det3_cross_expansion` — the triple product against a cross product:
  `det3 x y (k × w) = ⟪x,k⟫⟪y,w⟫ − ⟪x,w⟫⟪y,k⟫`.  (Route: `inner_cross_eq_det3` + `cross_cross`
  Binet–Cauchy, or directly via coordinates.)
* **Brick 4** `det3_axis_cross_eq_neg_gram` — the axis-incident specialization
  `det3 x y (y × w) = −(⟪x,w⟫ − ⟪x,y⟫⟪w,y⟫)` for a *unit* `y`.  This is the literal `-hβ` form.
* **Brick 2a** `hasDerivAt_rot` — `d/dθ rot k θ v = k × rot k θ v` for a unit axis `k`,
  proved by differentiating the explicit cos/sin Rodrigues form term by term and collapsing the
  derivative to `cross k (rot k θ v)` via `cross_cross` and `cross_self`.
* **Brick 2b** `hasDerivAt_mixedSupport` — composing brick 2a with the (third-slot linear) map
  `z ↦ det3 x y z`, giving `HasDerivAt (mixedSupport A ij) (det3 x y (k × wθ)) θ`.
* **Brick 3** `deriv_nonpos_of_left_nonneg_zero` — a self-contained one-sided extremum lemma:
  if `f ≥ 0` on `[0,δ]` and `f δ = 0`, then `f' (δ) ≤ 0`.  Proved by the difference-quotient
  filter argument (no fragile one-sided Mathlib API).
* **Brick 8** `shortArc_axis_opened_tail` — the opened last edge stays a short arc: rotating the
  tail about the (fixed) axis preserves `ShortArc (axis) (tail)`.

Two non-vacuity guards (`example`s) are included.

No `sorry`, `axiom`, `admit`, or `native_decide`.
-/

noncomputable section
open scoped RealInnerProductSpace
open ProofsInTheBook.SphericalKernel ProofsInTheBook.SphericalArm
open ProofsInTheBook.SphericalRotation ProofsInTheBook.SphericalCore
open ProofsInTheBook.ZinanFFCT10

namespace ProofsInTheBook.ZinanFFCT26

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000

/-! ## Brick 1 — the triple product against a cross product

`det3 x y (k × w) = ⟪x,k⟫ * ⟪y,w⟫ − ⟪x,w⟫ * ⟪y,k⟫`.

Route: `det3 x y z = ⟪x, y × z⟫` (the landed `inner_cross_eq_det3`), then
`y × (k × w) = ⟪y,w⟫ • k − ⟪y,k⟫ • w` (the landed `cross_cross` BAC–CAB rule), then expand the
inner products. -/

/-- **(Brick 1) Triple-product–cross expansion.**
`det3 x y (k × w) = ⟪x,k⟫⟪y,w⟫ − ⟪x,w⟫⟪y,k⟫`. -/
theorem det3_cross_expansion (x y k w : E3) :
    det3 x y (cross k w)
      = (⟪x, k⟫ : ℝ) * (⟪y, w⟫ : ℝ) - (⟪x, w⟫ : ℝ) * (⟪y, k⟫ : ℝ) := by
  rw [← inner_cross_eq_det3, cross_cross, inner_sub_right, real_inner_smul_right,
    real_inner_smul_right]
  ring

/-! ## Brick 4 — the axis-incident `-hβ` form

Taking `k := y` (a unit `S²` point) in brick 1 and using `⟪y,y⟫ = 1`. -/

/-- **(Brick 4) Axis-incident derivative is `-hβ`.**  For a unit vector `y`,
`det3 x y (y × w) = −(⟪x,w⟫ − ⟪x,y⟫⟪w,y⟫)`, the negated Gram quantity `hβ`. -/
theorem det3_axis_cross_eq_neg_gram {x w : E3} {y : E3} (hy : (⟪y, y⟫ : ℝ) = 1) :
    det3 x y (cross y w)
      = - ((⟪x, w⟫ : ℝ) - (⟪x, y⟫ : ℝ) * (⟪w, y⟫ : ℝ)) := by
  rw [det3_cross_expansion, hy, mul_one, real_inner_comm y w]
  ring

/-- The `S²`-flavoured form: for sphere points coerced into `E3`, `⟪y,y⟫ = 1` automatically. -/
theorem det3_axis_cross_eq_neg_gram_S2 (x w : E3) (y : S2) :
    det3 x (y : E3) (cross (y : E3) w)
      = - ((⟪x, w⟫ : ℝ) - (⟪x, (y : E3)⟫ : ℝ) * (⟪w, (y : E3)⟫ : ℝ)) :=
  det3_axis_cross_eq_neg_gram (S2.inner_self y)

/-! ## Brick 2a — the Rodrigues derivative

`d/dθ rot k θ v = k × rot k θ v` for a unit axis `k`.  Differentiate the explicit form
`rot k θ v = cos θ • v + sin θ • (k×v) + ((1−cos θ)⟪k,v⟫) • k` term by term, then identify the
result with `cross k (rot k θ v)` via `cross_cross` (`k×(k×v) = ⟪k,v⟫•k − v` for unit `k`) and
`cross_self` (`k×k = 0`). -/

/-- The explicit derivative value of the Rodrigues form (no axis identity collapse yet). -/
private theorem hasDerivAt_rot_explicit (k v : E3) (θ : ℝ) :
    HasDerivAt (fun t : ℝ => rot k t v)
      (-(Real.sin θ) • v + Real.cos θ • cross k v
        + (Real.sin θ * (⟪k, v⟫ : ℝ)) • k) θ := by
  -- term 1: cos t • v
  have h1 : HasDerivAt (fun t : ℝ => Real.cos t • v) ((-Real.sin θ) • v) θ :=
    (Real.hasDerivAt_cos θ).smul_const v
  -- term 2: sin t • (k × v)
  have h2 : HasDerivAt (fun t : ℝ => Real.sin t • cross k v) (Real.cos θ • cross k v) θ :=
    (Real.hasDerivAt_sin θ).smul_const (cross k v)
  -- term 3: ((1 - cos t) * ⟪k,v⟫) • k
  have hscal : HasDerivAt (fun t : ℝ => (1 - Real.cos t) * (⟪k, v⟫ : ℝ))
      (Real.sin θ * (⟪k, v⟫ : ℝ)) θ := by
    have hc : HasDerivAt (fun t : ℝ => 1 - Real.cos t) (Real.sin θ) θ := by
      have := (Real.hasDerivAt_cos θ).const_sub 1
      simpa using this
    simpa using hc.mul_const (⟪k, v⟫ : ℝ)
  have h3 : HasDerivAt (fun t : ℝ => ((1 - Real.cos t) * (⟪k, v⟫ : ℝ)) • k)
      ((Real.sin θ * (⟪k, v⟫ : ℝ)) • k) θ := hscal.smul_const k
  have hsum := (h1.add h2).add h3
  -- the function is exactly `rot k · v`
  simpa only [rot_apply, neg_smul] using hsum

/-- **(Brick 2a) Rodrigues derivative.**  For a unit axis `k`,
`HasDerivAt (fun t => rot k t v) (k × rot k θ v) θ`. -/
theorem hasDerivAt_rot {k : E3} (hk : ‖k‖ = 1) (θ : ℝ) (v : E3) :
    HasDerivAt (fun t : ℝ => rot k t v) (cross k (rot k θ v)) θ := by
  have hkk : (⟪k, k⟫ : ℝ) = 1 := by rw [real_inner_self_eq_norm_sq, hk]; norm_num
  -- collapse cross k (rot k θ v) to the explicit derivative value
  have hcollapse :
      cross k (rot k θ v)
        = -(Real.sin θ) • v + Real.cos θ • cross k v + (Real.sin θ * (⟪k, v⟫ : ℝ)) • k := by
    have hkkv : cross k (cross k v) = (⟪k, v⟫ : ℝ) • k - v := by
      rw [cross_cross, hkk, one_smul]
    have hckk : cross k k = 0 := cross_self k
    rw [rot_apply, cross_add_right, cross_add_right, cross_smul_right, cross_smul_right,
      cross_smul_right, hkkv, hckk, smul_zero]
    -- now a pure module identity
    rw [smul_sub]
    module
  rw [hcollapse]
  exact hasDerivAt_rot_explicit k v θ

/-! ## Brick 2b — the mixed-support derivative

`mixedSupport A ij θ = det3 x y (rot k θ tail)` with `x = A ij.1`, `y = A ij.2`,
`k = openAxis A`, `tail = A (Fin.last (n+1))`.  Compose brick 2a with the third-slot–linear map
`z ↦ det3 x y z` (the landed `det3_add_right` / `det3_smul_right`).  We expand `det3 x y z` into a
finite sum of coordinate products and differentiate coordinatewise — the robust route mirroring
`continuous_mixedSupport`. -/

/-- `z ↦ det3 x y z` has the derivative `det3 x y z'` whenever `z` has derivative `z'`:  the map is
linear in `z`, expanded coordinatewise. -/
theorem hasDerivAt_det3_third {x y : E3} {g : ℝ → E3} {g' : E3} {θ : ℝ}
    (hg : HasDerivAt g g' θ) :
    HasDerivAt (fun t : ℝ => det3 x y (g t)) (det3 x y g') θ := by
  -- coordinate derivatives of g (project with the coordinate CLM `EuclideanSpace.proj`)
  have hg0 : HasDerivAt (fun t : ℝ => g t 0) (g' 0) θ :=
    (EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin 3)).hasFDerivAt.comp_hasDerivAt θ hg
  have hg1 : HasDerivAt (fun t : ℝ => g t 1) (g' 1) θ :=
    (EuclideanSpace.proj (𝕜 := ℝ) (1 : Fin 3)).hasFDerivAt.comp_hasDerivAt θ hg
  have hg2 : HasDerivAt (fun t : ℝ => g t 2) (g' 2) θ :=
    (EuclideanSpace.proj (𝕜 := ℝ) (2 : Fin 3)).hasFDerivAt.comp_hasDerivAt θ hg
  -- det3 x y z = x0*(y1*z2 - y2*z1) - x1*(y0*z2 - y2*z0) + x2*(y0*z1 - y1*z0)
  have hterm0 : HasDerivAt
      (fun t : ℝ => x 0 * (y 1 * g t 2 - y 2 * g t 1))
      (x 0 * (y 1 * g' 2 - y 2 * g' 1)) θ :=
    (((hg2.const_mul (y 1)).sub (hg1.const_mul (y 2))).const_mul (x 0))
  have hterm1 : HasDerivAt
      (fun t : ℝ => x 1 * (y 0 * g t 2 - y 2 * g t 0))
      (x 1 * (y 0 * g' 2 - y 2 * g' 0)) θ :=
    (((hg2.const_mul (y 0)).sub (hg0.const_mul (y 2))).const_mul (x 1))
  have hterm2 : HasDerivAt
      (fun t : ℝ => x 2 * (y 0 * g t 1 - y 1 * g t 0))
      (x 2 * (y 0 * g' 1 - y 1 * g' 0)) θ :=
    (((hg1.const_mul (y 0)).sub (hg0.const_mul (y 1))).const_mul (x 2))
  have hsum := (hterm0.sub hterm1).add hterm2
  -- unfold det3 on both the function and the derivative value
  simpa only [det3] using hsum

/-- **(Brick 2b) Mixed-support derivative.**  For a unit axis `k = openAxis A`,
`HasDerivAt (mixedSupport A ij) (det3 (A ij.1) (A ij.2) (k × rot k θ (A (Fin.last (n+1))))) θ`. -/
theorem hasDerivAt_mixedSupport {n : ℕ} (A : Fin (n + 1 + 1) → S2)
    (ij : Fin (n + 1 + 1) × Fin (n + 1 + 1)) (θ : ℝ) :
    HasDerivAt (mixedSupport A ij)
      (det3 (A ij.1 : E3) (A ij.2 : E3)
        (cross (openAxis A : E3)
          (rot (openAxis A : E3) θ (A (Fin.last (n + 1)) : E3)))) θ := by
  have hrot := hasDerivAt_rot (openAxis A).2 θ (A (Fin.last (n + 1)) : E3)
  have h := hasDerivAt_det3_third (x := (A ij.1 : E3)) (y := (A ij.2 : E3)) hrot
  -- `mixedSupport A ij` is definitionally this composition
  exact h

/-! ## Brick 3 — the one-sided extremum sign

If `f ≥ 0` on `[0,δ]` and `f δ = 0`, then the derivative at `δ` is `≤ 0`.  We avoid the fragile
one-sided Mathlib API and run the difference-quotient filter argument directly: `HasDerivAt` gives
`(f t − f δ) / (t − δ) → f'` as `t → δ`; restricting to `t < δ` in `[0,δ]`, each quotient is
`≤ 0` (numerator `≥ 0`, denominator `< 0`), so the limit `f' ≤ 0`. -/

/-- **(Brick 3) One-sided extremum sign.**  If `0 < δ`, `f` has derivative `f'` at `δ`,
`f θ ≥ 0` for all `θ ∈ [0,δ]`, and `f δ = 0`, then `f' ≤ 0`. -/
theorem deriv_nonpos_of_left_nonneg_zero {f : ℝ → ℝ} {δ f' : ℝ}
    (hδ : 0 < δ) (hderiv : HasDerivAt f f' δ)
    (hleft : ∀ θ, θ ∈ Set.Icc 0 δ → 0 ≤ f θ) (hzero : f δ = 0) :
    f' ≤ 0 := by
  -- restrict the derivative to the left interval `Set.Iio δ`
  have hslope : HasDerivWithinAt f f' (Set.Iio δ) δ := hderiv.hasDerivWithinAt
  -- the slope of `f` at `δ` tends to `f'` along `𝓝[Iio δ \ {δ}] δ`
  have htend : Filter.Tendsto (slope f δ) (nhdsWithin δ (Set.Iio δ \ {δ})) (nhds f') :=
    hasDerivWithinAt_iff_tendsto_slope.mp hslope
  -- `Iio δ \ {δ} = Iio δ` since `δ ∉ Iio δ`
  have hset : Set.Iio δ \ {δ} = Set.Iio δ := by
    ext t; simp only [Set.mem_diff, Set.mem_Iio, Set.mem_singleton_iff]
    constructor
    · exact fun h => h.1
    · exact fun h => ⟨h, ne_of_lt h⟩
  rw [hset] at htend
  -- the punctured-left neighbourhood is nontrivial (`δ` is not isolated from the left)
  haveI : (nhdsWithin δ (Set.Iio δ)).NeBot := nhdsWithin_Iio_neBot (le_refl δ)
  -- the slope is eventually `≤ 0`: for `t < δ` close to `δ`, `t ∈ [0,δ]` so `f t ≥ 0`,
  -- and `slope f δ t = (f t − f δ)/(t − δ) = f t /(t − δ) ≤ 0` (numerator ≥ 0, denom < 0).
  have heventually : ∀ᶠ t in nhdsWithin δ (Set.Iio δ), slope f δ t ≤ 0 := by
    -- the left half-open interval `(0, δ)` is a neighbourhood of `δ` within `Iio δ`
    have hmem : Set.Ioo 0 δ ∈ nhdsWithin δ (Set.Iio δ) := by
      apply mem_nhdsWithin.2
      refine ⟨Set.Ioi 0, isOpen_Ioi, hδ, ?_⟩
      intro t ht
      exact ⟨ht.1, ht.2⟩
    filter_upwards [hmem] with t ht
    have htlt : t < δ := ht.2
    have htge : (0 : ℝ) ≤ t := le_of_lt ht.1
    have hft : 0 ≤ f t := hleft t ⟨htge, le_of_lt htlt⟩
    -- slope f δ t = (f t − f δ) / (t − δ)
    rw [slope_def_field, hzero, sub_zero]
    -- numerator f t ≥ 0, denominator t − δ < 0 ⟹ quotient ≤ 0
    have hden : t - δ < 0 := by linarith
    exact div_nonpos_of_nonneg_of_nonpos hft (le_of_lt hden)
  exact le_of_tendsto htend heventually

/-! ## Brick 8 — the opened last edge stays a short arc

Rotating the tail about the (fixed) axis preserves `ShortArc (axis) (tail)`.  We prove `rotS2`
preserves `ShortArc` (both conjuncts via the injectivity of `rot`), then use that the axis is fixed
by its own rotation (`rot_axis`). -/

/-- Rotation is injective on `E3`: `rot k θ` is norm-preserving and additive, so `rot k θ u =
rot k θ v → u = v`. -/
theorem rot_injective {k : E3} (hk : ‖k‖ = 1) (θ : ℝ) {u v : E3}
    (h : rot k θ u = rot k θ v) : u = v := by
  have hz : rot k θ (u - v) = 0 := by rw [rot_sub, h, sub_self]
  have : ‖u - v‖ = 0 := by rw [← norm_rot hk θ (u - v), hz, norm_zero]
  exact sub_eq_zero.mp (norm_eq_zero.mp this)

/-- `rot k θ (-v) = -(rot k θ v)`. -/
theorem rot_neg (k : E3) (θ : ℝ) (v : E3) : rot k θ (-v) = -(rot k θ v) := by
  rw [show (-v) = (-1 : ℝ) • v by module, rot_smul]; module

/-- **`rotS2` preserves `ShortArc`.**  Both endpoints are rotated by the same unit-axis rotation,
which is injective and commutes with negation, so neither equality nor antipodality is created. -/
theorem shortArc_rotS2 (k : S2) (θ : ℝ) {p q : S2} (h : ShortArc p q) :
    ShortArc (rotS2 k θ p) (rotS2 k θ q) := by
  refine ⟨?_, ?_⟩
  · -- not equal: rot injective
    intro he
    apply h.1
    have : rot (k : E3) θ (p : E3) = rot (k : E3) θ (q : E3) := by
      have := congrArg (Subtype.val) he; simpa only [rotS2_coe] using this
    exact S2.ext (rot_injective k.2 θ this)
  · -- not antipodal: (rot p) = -(rot q) ⟹ rot p = rot (-q) ⟹ p = -q
    intro he
    apply h.2
    have he' : rot (k : E3) θ (p : E3) = rot (k : E3) θ (-(q : E3)) := by
      rw [rot_neg]
      simpa only [rotS2_coe] using he
    exact rot_injective k.2 θ he'

/-- **(Brick 8) The opened last edge stays short.**  The axis vertex is fixed by the opening
rotation, and the tail vertex is rotated, so if the original last edge `(axis, tail)` is a short
arc, so is the opened edge `(axis, rot tail)`.  Stated against the `openArm` vocabulary: the axis is
`openArm A θ ⟨n,_⟩ = A ⟨n,_⟩` (fixed) and the tail is `openArm A θ (Fin.last (n+1))`. -/
theorem shortArc_axis_opened_tail {n : ℕ} (A : Fin (n + 1 + 1) → S2) (θ : ℝ)
    (hshort : ShortArc (A ⟨n, by omega⟩) (A (Fin.last (n + 1)))) :
    ShortArc (openArm A θ ⟨n, by omega⟩) (openArm A θ (Fin.last (n + 1))) := by
  -- axis is fixed
  have haxis : openArm A θ (⟨n, by omega⟩ : Fin (n + 1 + 1)) = A ⟨n, by omega⟩ :=
    openArm_fixed A θ (le_refl n)
  -- tail is the rotated tail; openAxis A = A ⟨n,_⟩
  have htail : openArm A θ (Fin.last (n + 1)) = rotS2 (openAxis A) θ (A (Fin.last (n + 1))) :=
    openArm_last A θ
  rw [haxis, htail]
  -- rewrite the fixed axis as `rotS2 (openAxis A) θ (openAxis A)` (axis fixed by its rotation)
  have hfix : (A (⟨n, by omega⟩ : Fin (n + 1 + 1))) = rotS2 (openAxis A) θ (openAxis A) := by
    apply S2.ext
    rw [rotS2_coe]
    show (openAxis A : E3) = rot (openAxis A : E3) θ (openAxis A : E3)
    rw [rot_axis (openAxis A).2]
  -- now both endpoints are rotations of (openAxis A) and (A last)
  have hbase : ShortArc (openAxis A) (A (Fin.last (n + 1))) := by
    have : openAxis A = A (⟨n, by omega⟩ : Fin (n + 1 + 1)) := rfl
    rw [this]; exact hshort
  rw [hfix]
  exact shortArc_rotS2 (openAxis A) θ hbase

/-! ## Non-vacuity guards -/

/-- Guard for brick 3 (non-vacuity): `f := fun θ => δ − θ` satisfies all hypotheses of
`deriv_nonpos_of_left_nonneg_zero` (it is `≥ 0` on `[0,δ]`, vanishes at `δ`, derivative `−1`), and
the lemma indeed concludes the (true) `−1 ≤ 0`. -/
example (δ : ℝ) (hδ : 0 < δ) : (-1 : ℝ) ≤ 0 := by
  have hderiv : HasDerivAt (fun θ : ℝ => δ - θ) (-1) δ := by
    simpa using (hasDerivAt_id δ).const_sub δ
  refine deriv_nonpos_of_left_nonneg_zero hδ hderiv ?_ (by simp)
  intro θ hθ
  have := hθ.2; simpa using (by linarith : (0 : ℝ) ≤ δ - θ)

/-- Guard for brick 1: at the standard basis triple `det3 e0 e1 (e0 × e1) = +1` (since
`e0 × e1 = e2` and `det3 e0 e1 e2 = 1`).  Computed by the brick-1 expansion + `inner` coordinates,
norm_num — no `decide`. -/
example :
    det3 (!₂[1, 0, 0] : E3) (!₂[0, 1, 0] : E3) (cross (!₂[1, 0, 0] : E3) (!₂[0, 1, 0] : E3)) = 1 := by
  rw [det3_cross_expansion, inner_eq_coord, inner_eq_coord, inner_eq_coord, inner_eq_coord]
  simp

end ProofsInTheBook.ZinanFFCT26
