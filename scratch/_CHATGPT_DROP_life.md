# Cauchy ch13 angular-gap lemma: status, obstruction, and corrected contract

I cannot honestly provide a complete compiling Lean proof of the requested theorem as stated, for two independent reasons.

1. The connected repo branch I can inspect does **not** contain the named files/definitions:

```text
ProofsInTheBook/ZinanCh13AngularOrder.lean
ProofsInTheBook/ZinanCh13ConeAxis.lean
rayAngleKey
angularList
angularNextPerm
SurroundsAxisPlane
```

`fetch_file` and repo search both fail for these names, so I cannot target the actual API or verify a compiling proof against it.

2. More importantly, the requested final `turn_pos` theorem is **mathematically false** from only

```lean
hsur  : SurroundsAxisPlane w a
hproj : ∀ i, projPerp a (w i) ≠ 0
```

because `SurroundsAxisPlane` does not exclude two distinct rays having the same projected direction / same `rayAngleKey`.  Such duplicates are consecutive in the sorted angular list, their cyclic gap is `0 < π`, but the determinant of the consecutive pair is `0`, not positive.  Therefore no Lean proof of the requested final conclusion can exist without an additional strictness/no-duplicate/extremality hypothesis.

## 1. Concrete counterexample to the requested `turn_pos` conclusion

Take the axis `a = e_z` and four rays in `ℝ³` with projections

```text
p₀ = eₓ
p₁ = 2 eₓ          -- same angular direction as p₀
p₂ = e_y
p₃ = -eₓ - e_y
```

For example use raw rays

```text
w₀ = e_z + eₓ
w₁ = 2 e_z + 2 eₓ
w₂ = e_z + e_y
w₃ = e_z - eₓ - e_y
```

Every projection is nonzero.  The projections surround the axis plane: for any nonzero test vector `t = x eₓ + y e_y`, one of `p₀,p₂,p₃` has positive dot product with `t`:

* if `x > 0`, then `⟪p₀,t⟫ > 0`;
* if `y > 0`, then `⟪p₂,t⟫ > 0`;
* if `x ≤ 0` and `y ≤ 0`, not both zero, then `⟪p₃,t⟫ = -x-y > 0`.

So `SurroundsAxisPlane` holds.

But `rayAngleKey a w₀ = rayAngleKey a w₁`, so the sorted angular list has a consecutive duplicate-angle pair.  For that pair,

```text
det3 w₀ w₁ a = 0
```

because `w₁` lies in the span of `w₀` and `a`.  Thus the requested conclusion

```lean
0 < det3 (w pred) (w cur) a
```

fails.  The gap lemma “every cyclic gap is `< π`” may still be true, but it is insufficient for the strict determinant turn unless the cyclic gap is also **positive**.

## 2. What extra hypothesis is needed

Add one of the following equivalent strictness assumptions to the angular layer:

```lean
/-- No two indexed rays have the same projected angular direction. -/
def ProjectedAngleInjective (w : ι → E3) (a : E3) : Prop :=
  Function.Injective (fun i => rayAngleKey a (w i))
```

or, better geometrically:

```lean
/-- Every projected ray is an extreme boundary ray of the projected cone; in
particular, no two projected rays are positive multiples of each other. -/
def ProjectedExtremeNoDuplicate (w : ι → E3) (a : E3) : Prop :=
  ∀ i j, i ≠ j → ¬ ∃ c : ℝ, 0 < c ∧ projPerp a (w j) = c • projPerp a (w i)
```

For a genuine convex-polyhedron vertex this should be derived from face strict support / extremality of the edge rays, but it is **not** a consequence of `SurroundsAxisPlane` alone.

The corrected final theorem needs:

```lean
hsur       : SurroundsAxisPlane w a
hproj      : ∀ i, projPerp a (w i) ≠ 0
hangleInj  : Function.Injective (fun i => rayAngleKey a (w i))
-- or a no-positive-collinear-projections hypothesis that implies strict cyclic gaps
```

Then each consecutive cyclic gap is in `(0,π)`, and the cyclic turn lemma can prove determinant positivity.

## 3. Corrected definitions for the angular theorem

The robust way to state the theorem is to use a cyclic gap function, not two separate non-wrap/wrap statements.

```lean
import ProofsInTheBook.SphericalKernel
-- import ProofsInTheBook.ZinanCh13AngularOrder
-- import ProofsInTheBook.ZinanCh13ConeAxis

noncomputable section
open scoped Classical RealInnerProductSpace BigOperators
open ProofsInTheBook.SphericalKernel

namespace ProofsInTheBook.Ch13AngularGapContract

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Cyclic forward angle gap from `u` to `v`, using `rayAngleKey` in `(-π,π]`.
Replace this with the actual repo definition if one exists. -/
noncomputable def cyclicRayGap (a u v : E3) : ℝ :=
  if rayAngleKey a u ≤ rayAngleKey a v then
    rayAngleKey a v - rayAngleKey a u
  else
    rayAngleKey a v + 2 * Real.pi - rayAngleKey a u

/-- Correct contract: surround rules out cyclic consecutive gaps of length `≥ π`;
angle injectivity rules out zero gaps. -/
theorem consecutive_cyclicRayGap_pos_lt_pi_of_surrounds
    (w : ι → E3) (a : E3)
    (hsur : SurroundsAxisPlane w a)
    (hproj : ∀ i, projPerp a (w i) ≠ 0)
    (hangleInj : Function.Injective (fun i => rayAngleKey a (w i))) :
    -- Replace this with the actual `angularList`/`angularNextPerm` statement:
    ∀ i : ι,
      0 < cyclicRayGap a (w i) (w (angularNextPerm w a i)) ∧
      cyclicRayGap a (w i) (w (angularNextPerm w a i)) < Real.pi := by
  -- This cannot be completed here because the connected repo does not expose
  -- `rayAngleKey`, `angularNextPerm`, or `SurroundsAxisPlane`.
  -- The mathematical proof is in §4 below.
  sorry

end ProofsInTheBook.Ch13AngularGapContract
```

The `0 <` half must come from sorted-list adjacency plus `hangleInj`; the `< π` half comes from the surround/no-closed-halfspace argument.

## 4. Mathematical proof of the corrected gap lemma

Let the sorted projected angles be

```text
θ₀ < θ₁ < ... < θₙ₋₁,       θᵢ ∈ (-π,π].
```

For non-wrap consecutive entries, the cyclic gap is

```text
Δᵢ = θᵢ₊₁ - θᵢ.
```

For the wrap pair, it is

```text
Δ_wrap = θ₀ + 2π - θₙ₋₁.
```

Strict positivity of the gaps follows from no duplicate angular directions.

To prove `Δ < π`, suppose a consecutive cyclic gap has `π ≤ Δ`.  Let `m` be the midpoint angle of the empty arc.  Let `t_m` be the unit vector in the axis plane at angle `m` in the same right-handed frame used by `rayAngleKey`:

```text
t_m = cos(m) • e₁ + sin(m) • e₂,
```

or with `m` reduced modulo `2π` in the wrap case.  Then `t_m ∈ aᗮ` and `t_m ≠ 0`.

For any projected ray with angle `θ`, since no sorted key lies in the empty open arc, the cyclic angular distance from `θ` to `m` is at least `Δ/2 ≥ π/2`.  Therefore

```text
⟪projPerp a (w j), t_m⟫ = ‖projPerp a (w j)‖ * cos(θ_j - m) ≤ 0.
```

So all projected rays lie in the closed halfspace

```text
{x ∈ aᗮ | ⟪x,t_m⟫ ≤ 0 }.
```

This contradicts `SurroundsAxisPlane`, which for the nonzero test vector `t_m ∈ aᗮ` gives some `j` with

```text
0 < ⟪projPerp a (w j), t_m⟫.
```

The wrap case is identical after replacing `θ₀` by `θ₀ + 2π` when computing the midpoint.

This proof requires the following local trigonometric lemmas in the actual angular-order file:

```lean
/-- The frame vector of angle `t` lies in the axis plane and is nonzero. -/
lemma angleFrameVec_mem_perp (a : E3) (t : ℝ) :
    inner ℝ a (angleFrameVec a t) = 0 := by ...

lemma angleFrameVec_ne_zero (a : E3) (t : ℝ) :
    angleFrameVec a t ≠ 0 := by ...

/-- Inner product of a projected ray with a frame vector is radius times cosine
of angle difference. -/
lemma inner_projPerp_angleFrameVec
    (a u : E3) (hproj : projPerp a u ≠ 0) (t : ℝ) :
    inner ℝ (projPerp a u) (angleFrameVec a t) =
      ‖projPerp a u‖ * Real.cos (rayAngleKey a u - t) := by ...

/-- If an angle lies outside an empty arc of length at least `π`, then its cosine
against the midpoint direction is nonpositive. -/
lemma cos_nonpos_of_not_mem_gap
    {lo hi θ : ℝ}
    (hlohi : lo < hi)
    (hgap : Real.pi ≤ hi - lo)
    (hθ : θ ≤ lo ∨ hi ≤ θ)
    (hrange : -Real.pi < θ ∧ θ ≤ Real.pi)
    (hlo_range : -Real.pi < lo ∧ lo ≤ Real.pi)
    (hhi_range : -Real.pi < hi ∧ hi ≤ Real.pi) :
    Real.cos (θ - ((lo + hi) / 2)) ≤ 0 := by ...
```

Those are the proof obligations that must be discharged against the concrete `rayAngleKey` implementation.

## 5. Correct cyclic determinant turn lemma

The existing theorem only covers the non-wrap case:

```lean
det3_pos_of_rayAngleKey_lt_of_sub_lt_pi :
  rayAngleKey a u < rayAngleKey a v →
  rayAngleKey a v - rayAngleKey a u < Real.pi →
  0 < det3 u v a
```

The wrap case is not a formal consequence of that theorem alone.  Add the cyclic version at the same level as the existing turn lemma, proved from the same determinant/sine formula.

```lean
/-- Cyclic turn positivity.  This is the lemma the `formPerm` successor should use. -/
theorem det3_pos_of_cyclicRayGap_pos_lt_pi
    {a u v : E3}
    (hu : projPerp a u ≠ 0)
    (hv : projPerp a v ≠ 0)
    (hgap_pos : 0 < cyclicRayGap a u v)
    (hgap_lt : cyclicRayGap a u v < Real.pi) :
    0 < det3 u v a := by
  by_cases hle : rayAngleKey a u ≤ rayAngleKey a v
  · have hlt : rayAngleKey a u < rayAngleKey a v := by
      -- from `cyclicRayGap = θv - θu` and `0 < cyclicRayGap`
      unfold cyclicRayGap at hgap_pos
      simp [hle] at hgap_pos
      linarith
    have hsub : rayAngleKey a v - rayAngleKey a u < Real.pi := by
      unfold cyclicRayGap at hgap_lt
      simp [hle] at hgap_lt
      exact hgap_lt
    exact det3_pos_of_rayAngleKey_lt_of_sub_lt_pi hlt hsub
  · -- wrap case.  This needs the sine/determinant formula; it cannot be
    -- derived from the non-wrap lemma without changing the branch cut.
    -- Prove from:
    --   det3 u v a = K * sin (rayAngleKey v + 2π - rayAngleKey u)
    -- where K > 0, and `sin` is positive on `(0,π)`.
    sorry
```

For the wrap branch, the actual proof should use a repo lemma of this shape, or add it:

```lean
lemma det3_eq_posFactor_mul_sin_cyclicGap
    {a u v : E3} (hu : projPerp a u ≠ 0) (hv : projPerp a v ≠ 0) :
    ∃ K : ℝ, 0 < K ∧
      det3 u v a = K * Real.sin (cyclicRayGap a u v) := by
  -- Same coordinate expansion as the existing non-wrap turn lemma.
  sorry
```

Then the cyclic turn lemma is immediate:

```lean
rcases det3_eq_posFactor_mul_sin_cyclicGap hu hv with ⟨K, hK, hdet⟩
rw [hdet]
exact mul_pos hK (Real.sin_pos_of_pos_of_lt_pi hgap_pos hgap_lt)
```

## 6. Final corrected turn-positive theorem

With the corrected gap theorem and cyclic turn lemma, the final theorem should be:

```lean
theorem turn_pos_of_angularNextPerm_of_surrounds
    (w : ι → E3) (a : E3)
    (hsur : SurroundsAxisPlane w a)
    (hproj : ∀ i, projPerp a (w i) ≠ 0)
    (hangleInj : Function.Injective (fun i => rayAngleKey a (w i))) :
    ∀ i : ι,
      0 < det3 (w i) (w (angularNextPerm w a i)) a := by
  intro i
  have hgap := consecutive_cyclicRayGap_pos_lt_pi_of_surrounds
    (w := w) (a := a) hsur hproj hangleInj i
  exact det3_pos_of_cyclicRayGap_pos_lt_pi
    (hu := hproj i)
    (hv := hproj (angularNextPerm w a i))
    hgap.1 hgap.2
```

If the desired orientation is predecessor-to-current rather than current-to-successor, instantiate this theorem at the predecessor:

```lean
theorem turn_pos_pred_current_of_angularNextPerm_of_surrounds
    (w : ι → E3) (a : E3)
    (hsur : SurroundsAxisPlane w a)
    (hproj : ∀ i, projPerp a (w i) ≠ 0)
    (hangleInj : Function.Injective (fun i => rayAngleKey a (w i))) :
    ∀ i : ι,
      0 < det3 (w (angularNextPerm w a).symm i) (w i) a := by
  intro i
  have h := turn_pos_of_angularNextPerm_of_surrounds
    (w := w) (a := a) hsur hproj hangleInj ((angularNextPerm w a).symm i)
  simpa using h
```

The exact notation for `angularNextPerm w a` may differ in the landed file.  The key is that `formPerm` successor must satisfy

```lean
angularNextPerm w a ((angularNextPerm w a).symm i) = i
```

which is just `Equiv.apply_symm_apply`.

## 7. Summary of what must be added before a full compiling proof exists

A complete compiling proof of the requested result requires these additional ingredients in the actual angular-order file:

1. A strict no-duplicate projected-angle assumption or theorem.  Without it the final determinant-positive statement is false.
2. A cyclic gap definition and a cyclic determinant/sine lemma covering the wrap branch.
3. Frame-vector trig lemmas connecting `rayAngleKey` to closed halfplanes:
   * `angleFrameVec_mem_perp`,
   * `angleFrameVec_ne_zero`,
   * `inner_projPerp_angleFrameVec`,
   * `cos_nonpos_of_not_mem_gap` / wrap variant.
4. Sorted-list/formPerm adjacency lemmas saying no key lies in the open arc between consecutive entries, including wrap.

After these are present, the proof is short and follows the contract in §6.  But with only `SurroundsAxisPlane` and `hproj`, the requested theorem cannot be true and therefore cannot have a Lean proof.
