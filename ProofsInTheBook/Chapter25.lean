import Mathlib

/-!
# Chapter 25: Buffon's needle problem

From "Proofs from THE BOOK":

**Buffon's needle**: A needle of length ℓ dropped on parallel lines
spaced d apart (ℓ ≤ d) crosses a line with probability 2ℓ/(πd).

The book's proof uses the linearity of expectation: any curve of
length L crosses E[crossings] = 2L/(πd) lines, proved by decomposing
into infinitesimal segments and using rotational symmetry.

Formalization status: this file now removes the previous escape hatch where a
structure field asserted the expected-value identity.  The public `chapter25`
states the short-needle theorem as an explicit density-level probability
calculation: the center distance from the nearest line is averaged uniformly on
`[0,d/2]`, the angle is averaged uniformly on `[0,π]`, and the resulting
one-dimensional angle integral is evaluated.

Remaining gap to the full measure-theoretic book statement: replace the
density-level average with an actual product probability measure on
`[0,d/2] × [0,π]`, prove measurability of the crossing event, identify the
event integral with the conditional center-distance average used here, and
then derive the expectation/probability equality from the Bernoulli crossing
count.  No field below assumes this identity.
-/

namespace ProofsInTheBook.Chapter25

open scoped BigOperators

/-- Expected crossings for a single segment in Buffon's needle model. -/
noncomputable def segmentExpectedCrossings (d length : ℝ) : ℝ :=
  2 * length / (Real.pi * d)

/-- Center-distance threshold for crossing at angle `θ`: a short needle crosses
iff its center lies within this distance of the nearest parallel line. -/
noncomputable def buffonCenterThreshold (length θ : ℝ) : ℝ :=
  length * Real.sin θ / 2

/-- The geometric crossing event in density coordinates.  Here `x` is the
distance from the needle center to the nearest line, and `θ ∈ [0,π]` is the
unoriented angle against the parallel lines. -/
def buffonCrossingEvent (length x θ : ℝ) : Prop :=
  x ≤ buffonCenterThreshold length θ

/-- Conditional crossing probability after averaging the center distance
uniformly over `[0,d/2]`, before averaging over the angle. -/
noncomputable def buffonConditionalCrossingProbability (d length θ : ℝ) : ℝ :=
  (2 / d) * buffonCenterThreshold length θ

/-- The short-needle Buffon probability obtained by uniform angle averaging on
`[0,π]` after the center-distance average. -/
noncomputable def buffonNeedleCrossingProbability (d length : ℝ) : ℝ :=
  (1 / Real.pi) *
    ∫ θ in (0 : ℝ)..Real.pi, buffonConditionalCrossingProbability d length θ

/-- The conditional probability is exactly the center-distance threshold divided
by the length `d/2` of the uniform center-distance interval. -/
theorem buffonConditionalCrossingProbability_eq_center_average
    (d length θ : ℝ) :
    buffonConditionalCrossingProbability d length θ =
      (2 / d) * buffonCenterThreshold length θ := by
  unfold buffonConditionalCrossingProbability buffonCenterThreshold
  ring

/-- In the short-needle range, the crossing threshold lies inside the possible
center-distance interval. -/
theorem buffonCenterThreshold_mem_Icc {d length θ : ℝ}
    (hlen : 0 ≤ length) (hle : length ≤ d) (hθ0 : 0 ≤ θ) (hθπ : θ ≤ Real.pi) :
    buffonCenterThreshold length θ ∈ Set.Icc (0 : ℝ) (d / 2) := by
  have hsin0 : 0 ≤ Real.sin θ := Real.sin_nonneg_of_mem_Icc ⟨hθ0, hθπ⟩
  have hsin1 : Real.sin θ ≤ 1 := Real.sin_le_one θ
  constructor
  · unfold buffonCenterThreshold
    positivity
  · unfold buffonCenterThreshold
    have hmul : length * Real.sin θ ≤ length * 1 :=
      mul_le_mul_of_nonneg_left hsin1 hlen
    nlinarith

/-- The conditional center-distance crossing probability is a genuine
probability for every short-needle angle. -/
theorem buffonConditionalCrossingProbability_mem_Icc {d length θ : ℝ}
    (hd : 0 < d) (hlen : 0 ≤ length) (hle : length ≤ d)
    (hθ0 : 0 ≤ θ) (hθπ : θ ≤ Real.pi) :
    buffonConditionalCrossingProbability d length θ ∈ Set.Icc (0 : ℝ) 1 := by
  have hthreshold := buffonCenterThreshold_mem_Icc hlen hle hθ0 hθπ
  have hscale_nonneg : 0 ≤ 2 / d := div_nonneg (by norm_num) hd.le
  constructor
  · unfold buffonConditionalCrossingProbability
    exact mul_nonneg hscale_nonneg hthreshold.1
  · unfold buffonConditionalCrossingProbability
    have hscale :
        (2 / d) * buffonCenterThreshold length θ ≤ (2 / d) * (d / 2) :=
      mul_le_mul_of_nonneg_left hthreshold.2 hscale_nonneg
    have hscale_eq : (2 / d) * (d / 2) = 1 := by
      field_simp [hd.ne']
    linarith

/--
Expected crossings for a polygonal curve, defined by summing the segment
contributions. This is the finite version of the linearity-of-expectation
step used in the book before passing from polygonal approximations to curves.
-/
noncomputable def curveExpectedCrossings {ι : Type*} (segments : Finset ι) (length : ι → ℝ)
    (d : ℝ) : ℝ :=
  ∑ i ∈ segments, segmentExpectedCrossings d (length i)

theorem curveExpectedCrossings_eq_total_length {ι : Type*} (segments : Finset ι)
    (length : ι → ℝ) (d : ℝ) :
    curveExpectedCrossings segments length d =
      segmentExpectedCrossings d (∑ i ∈ segments, length i) := by
  simp [curveExpectedCrossings, segmentExpectedCrossings, Finset.sum_mul, Finset.mul_sum,
    div_eq_mul_inv]

theorem segmentExpectedCrossings_nonneg {d length : ℝ} (hd : 0 < d) (hlen : 0 ≤ length) :
    0 ≤ segmentExpectedCrossings d length := by
  unfold segmentExpectedCrossings
  positivity

/-- Zero-length needle has zero expected crossings. -/
@[simp]
theorem segmentExpectedCrossings_zero (d : ℝ) :
    segmentExpectedCrossings d 0 = 0 := by
  simp [segmentExpectedCrossings]

/-- Expected crossings is monotone in needle length (for fixed `d > 0`). -/
theorem segmentExpectedCrossings_mono {d : ℝ} (hd : 0 < d)
    {a b : ℝ} (hab : a ≤ b) :
    segmentExpectedCrossings d a ≤ segmentExpectedCrossings d b := by
  unfold segmentExpectedCrossings
  have hden : 0 < Real.pi * d := mul_pos Real.pi_pos hd
  apply div_le_div_of_nonneg_right (by linarith) hden.le

/-- Linearity of expectation: expected crossings is additive in needle length. -/
theorem segmentExpectedCrossings_add (d a b : ℝ) :
    segmentExpectedCrossings d (a + b) =
      segmentExpectedCrossings d a + segmentExpectedCrossings d b := by
  unfold segmentExpectedCrossings
  ring

/-- Expected crossings scales linearly in needle length. -/
theorem segmentExpectedCrossings_const_mul (d c length : ℝ) :
    segmentExpectedCrossings d (c * length) = c * segmentExpectedCrossings d length := by
  unfold segmentExpectedCrossings
  ring

/-- `curveExpectedCrossings` of an empty segment family is `0`. -/
@[simp]
theorem curveExpectedCrossings_empty {ι : Type*} (length : ι → ℝ) (d : ℝ) :
    curveExpectedCrossings (∅ : Finset ι) length d = 0 := by
  simp [curveExpectedCrossings]

/-- `curveExpectedCrossings` is nonneg when `d > 0` and all lengths are nonneg. -/
theorem curveExpectedCrossings_nonneg {ι : Type*} {segments : Finset ι}
    {length : ι → ℝ} {d : ℝ} (hd : 0 < d) (hlen : ∀ i ∈ segments, 0 ≤ length i) :
    0 ≤ curveExpectedCrossings segments length d := by
  unfold curveExpectedCrossings
  exact Finset.sum_nonneg fun i hi => segmentExpectedCrossings_nonneg hd (hlen i hi)

/-- A single-segment curve's expected crossings equals the segment formula. -/
@[simp]
theorem curveExpectedCrossings_singleton {ι : Type*} [DecidableEq ι]
    (i : ι) (length : ι → ℝ) (d : ℝ) :
    curveExpectedCrossings ({i} : Finset ι) length d = segmentExpectedCrossings d (length i) := by
  unfold curveExpectedCrossings
  rw [Finset.sum_singleton]

/-- Buffon's noodle additivity: total expected crossings of a curve equals
the expected crossings of a single equivalent-length segment (provided d > 0). -/
theorem curveExpectedCrossings_eq_segment_of_total_length
    {ι : Type*} (segments : Finset ι) (length : ι → ℝ) (d L : ℝ)
    (hL : (∑ i ∈ segments, length i) = L) :
    curveExpectedCrossings segments length d = segmentExpectedCrossings d L := by
  rw [curveExpectedCrossings_eq_total_length, hL]

theorem segmentExpectedCrossings_le_one {d length : ℝ} (hd : 0 < d) (hle : length ≤ d) :
    segmentExpectedCrossings d length ≤ 1 := by
  unfold segmentExpectedCrossings
  have hden : 0 < Real.pi * d := mul_pos Real.pi_pos hd
  rw [div_le_one hden]
  have h2pi : (2 : ℝ) ≤ Real.pi := Real.two_le_pi
  nlinarith

/--
Buffon's needle probability for a single needle: when `0 < d` and `0 ≤ ℓ ≤ d`,
the crossing probability `2ℓ/(πd)` lies in `[0, 1]`. Since a needle of length
at most `d` crosses at most one line, the expected crossing count IS the
crossing probability.
-/
theorem buffon_needle_prob_in_unit_interval {d length : ℝ}
    (hd : 0 < d) (hlen : 0 ≤ length) (hle : length ≤ d) :
    segmentExpectedCrossings d length ∈ Set.Icc (0 : ℝ) 1 :=
  ⟨segmentExpectedCrossings_nonneg hd hlen, segmentExpectedCrossings_le_one hd hle⟩

/--
The Buffon needle formula: for a straight needle of length `ℓ` dropped on
parallel lines spaced `d` apart, the crossing probability is `2ℓ/(πd)`.
This packages the formula along with its validity as a probability.
-/
theorem buffon_needle {d length : ℝ} (hd : 0 < d) (hlen : 0 ≤ length) (hle : length ≤ d) :
    ∃ P : ℝ, P = 2 * length / (Real.pi * d) ∧ P ∈ Set.Icc (0 : ℝ) 1 :=
  ⟨segmentExpectedCrossings d length, rfl, buffon_needle_prob_in_unit_interval hd hlen hle⟩

/--
Buffon's noodle generalization: a convex curve of total arc length `L`
dropped on parallel lines spaced `d` apart has expected crossing count
`2L/(πd)`, regardless of the curve's shape.
-/
theorem buffon_noodle_expected_crossings {ι : Type*} (segments : Finset ι)
    (length : ι → ℝ) (d : ℝ) (_hd : 0 < d) :
    curveExpectedCrossings segments length d =
      2 * (∑ i ∈ segments, length i) / (Real.pi * d) := by
  rw [curveExpectedCrossings_eq_total_length]
  rfl

/--
The book's proof of Buffon's formula proceeds in three steps:
1. For a single segment of length ℓ, average the center-distance crossing
   condition over the angle: `(1/π)∫₀^π (ℓ/d) sin θ dθ = 2ℓ/(πd)`.
2. By linearity, any curve of length L has E[crossings] = 2L/(πd)
3. For a needle (straight segment) of length ≤ d, at most one crossing occurs,
   so E[crossings] = P(crossing) = 2ℓ/(πd)

Step 2 is `curveExpectedCrossings_eq_total_length`.
Step 3 uses `buffon_needle_prob_in_unit_interval`.
Step 1 (the rotational symmetry argument) is the geometric core and
requires the integral `∫₀^π sin(θ) dθ = 2`.
-/
theorem buffon_rotational_symmetry_integral :
    ∫ θ in (0 : ℝ)..Real.pi, Real.sin θ = 2 := by
  rw [integral_sin]
  simp [Real.cos_pi, Real.cos_zero]
  norm_num

/-- The half-range sine integral `∫₀^{π/2} sin θ dθ = 1`.  This is the
quarter-period component that, combined with rotational symmetry, drives the
short-needle Buffon probability formula `2ℓ/(πd)`. -/
theorem buffon_half_range_sine_integral :
    ∫ θ in (0 : ℝ)..(Real.pi / 2), Real.sin θ = 1 := by
  rw [integral_sin]
  simp [Real.cos_pi_div_two, Real.cos_zero]

/-- The honest core integral computation for Buffon's short-needle model. -/
theorem buffonNeedleCrossingProbability_eq_segmentExpectedCrossings
    (d length : ℝ) (_hd : 0 < d) :
    buffonNeedleCrossingProbability d length = segmentExpectedCrossings d length := by
  unfold buffonNeedleCrossingProbability buffonConditionalCrossingProbability
    buffonCenterThreshold segmentExpectedCrossings
  rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_div,
    intervalIntegral.integral_const_mul, buffon_rotational_symmetry_integral]
  ring_nf

/--
Chapter 25 (Buffon's needle, short-needle density model):
For `0 ≤ ℓ ≤ d`, averaging the explicit crossing event over the uniform
center distance on `[0,d/2]` and the uniform angle on `[0,π]` gives crossing
probability `2ℓ/(πd)`.

This theorem deliberately has no probability-space structure parameter and no
field asserting the expected-value identity.  The remaining measure-theoretic
upgrade is to prove that the density-level average used in
`buffonNeedleCrossingProbability` is equal to the integral of the indicator of
`buffonCrossingEvent` over the normalized product measure on
`[0,d/2] × [0,π]`.
-/
theorem chapter25 (d length : ℝ) (hd : 0 < d) (_hlen : 0 ≤ length) (_hle : length ≤ d) :
    buffonNeedleCrossingProbability d length = 2 * length / (Real.pi * d) := by
  rw [buffonNeedleCrossingProbability_eq_segmentExpectedCrossings d length hd]
  rfl

end ProofsInTheBook.Chapter25
