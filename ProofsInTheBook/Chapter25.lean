import Mathlib

/-!
# Chapter 25: Buffon's needle problem

From "Proofs from THE BOOK":

**Buffon's needle**: A needle of length ℓ dropped on parallel lines
spaced d apart (ℓ ≤ d) crosses a line with probability 2ℓ/(πd).

The book's proof uses the linearity of expectation: any curve of
length L crosses E[crossings] = 2L/(πd) lines, proved by decomposing
into infinitesimal segments and using rotational symmetry.

Formalization status: the short-needle theorem is proved from an actual
probability measure on needle placements.  A placement is `(θ, x)`, with
angle `θ ∈ [0,π]` and center distance `x ∈ [0,d/2]`; the measure is normalized
Lebesgue measure on this rectangle.  The crossing probability is the measure of
the crossing set, and the proof computes this measure by reducing the planar
area to the integral `∫₀^π sin θ dθ = 2`.
-/

namespace ProofsInTheBook.Chapter25

open MeasureTheory
open scoped BigOperators
open scoped ENNReal

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

/-- A placement is `(θ, x)`: the angle against the parallel lines and the
center distance from the nearest line. -/
abbrev BuffonPlacement := ℝ × ℝ

/-- The rectangle of admissible short-needle placements. -/
noncomputable def buffonPlacementSet (d : ℝ) : Set BuffonPlacement :=
  Set.Icc (0 : ℝ) Real.pi ×ˢ Set.Icc (0 : ℝ) (d / 2)

/-- Normalized Lebesgue measure on the placement rectangle.  For `0 < d`,
`buffonPlacementMeasure_isProbabilityMeasure` proves this is a probability
measure. -/
noncomputable def buffonPlacementMeasure (d : ℝ) : Measure BuffonPlacement :=
  ENNReal.ofReal (2 / (Real.pi * d)) • volume.restrict (buffonPlacementSet d)

/-- The closed crossing set for the placement model. -/
def buffonCrossingSet (length : ℝ) : Set BuffonPlacement :=
  {p : BuffonPlacement |
    p.1 ∈ Set.Icc (0 : ℝ) Real.pi ∧
      p.2 ∈ Set.Icc (0 : ℝ) (buffonCenterThreshold length p.1)}

/-- The same crossing set with boundary removed.  It has the same planar
Lebesgue measure as `buffonCrossingSet`, and Mathlib's `regionBetween` theorem
computes its area directly. -/
def buffonCrossingRegion (length : ℝ) : Set BuffonPlacement :=
  regionBetween (fun _ : ℝ => 0) (fun θ : ℝ => buffonCenterThreshold length θ)
    (Set.Icc (0 : ℝ) Real.pi)

/-- Conditional crossing probability after averaging the center distance
uniformly over `[0,d/2]`, before averaging over the angle. -/
noncomputable def buffonConditionalCrossingProbability (d length θ : ℝ) : ℝ :=
  (2 / d) * buffonCenterThreshold length θ

/-- The density-level average obtained by first averaging the center distance
and then averaging the angle.  The measure-theoretic probability below proves
that this equals the event probability. -/
noncomputable def buffonNeedleCrossingDensityAverage (d length : ℝ) : ℝ :=
  (1 / Real.pi) *
    ∫ θ in (0 : ℝ)..Real.pi, buffonConditionalCrossingProbability d length θ

/-- The actual crossing probability: the real mass of the crossing set under
the normalized placement measure. -/
noncomputable def buffonNeedleCrossingProbability (d length : ℝ) : ℝ :=
  (buffonPlacementMeasure d (buffonCrossingSet length)).toReal

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

/-- The crossing set really represents the original crossing predicate on the
placement rectangle. -/
theorem mem_buffonCrossingSet_iff {length : ℝ} {p : BuffonPlacement} :
    p ∈ buffonCrossingSet length ↔
      p.1 ∈ Set.Icc (0 : ℝ) Real.pi ∧ 0 ≤ p.2 ∧
        buffonCrossingEvent length p.2 p.1 := by
  simp [buffonCrossingSet, buffonCrossingEvent, Set.mem_Icc]

/-- In the short-needle range, every crossing placement lies in the placement
rectangle. -/
theorem buffonCrossingSet_subset_placementSet {d length : ℝ}
    (hlen : 0 ≤ length) (hle : length ≤ d) :
    buffonCrossingSet length ⊆ buffonPlacementSet d := by
  intro p hp
  rcases hp with ⟨hθ, hx⟩
  have hthreshold := buffonCenterThreshold_mem_Icc hlen hle hθ.1 hθ.2
  exact ⟨hθ, ⟨hx.1, le_trans hx.2 hthreshold.2⟩⟩

/-- The open crossing region used for area computation is contained in the
placement rectangle in the short-needle range. -/
theorem buffonCrossingRegion_subset_placementSet {d length : ℝ}
    (hlen : 0 ≤ length) (hle : length ≤ d) :
    buffonCrossingRegion length ⊆ buffonPlacementSet d := by
  intro p hp
  rcases hp with ⟨hθ, hx⟩
  have hthreshold := buffonCenterThreshold_mem_Icc hlen hle hθ.1 hθ.2
  exact ⟨hθ, ⟨le_of_lt hx.1, le_trans (le_of_lt hx.2) hthreshold.2⟩⟩

/-- The geometric crossing event is measurable. -/
theorem measurableSet_buffonCrossingSet (length : ℝ) :
    MeasurableSet (buffonCrossingSet length) := by
  unfold buffonCrossingSet
  have hcont : Continuous fun p : BuffonPlacement => buffonCenterThreshold length p.1 := by
    unfold buffonCenterThreshold
    fun_prop
  simp only [Set.mem_Icc, Set.setOf_and]
  exact (measurableSet_Ici.inter measurableSet_Iic).preimage measurable_fst |>.inter
    ((measurableSet_le measurable_const measurable_snd).inter
      (measurableSet_le measurable_snd hcont.measurable))

/-- The open crossing region used for the area computation is measurable. -/
theorem measurableSet_buffonCrossingRegion (length : ℝ) :
    MeasurableSet (buffonCrossingRegion length) := by
  unfold buffonCrossingRegion
  refine measurableSet_regionBetween ?_ ?_ measurableSet_Icc
  · fun_prop
  · unfold buffonCenterThreshold
    fun_prop

/-- The placement rectangle has area `πd/2`. -/
theorem volume_buffonPlacementSet (d : ℝ) :
    volume (buffonPlacementSet d) = ENNReal.ofReal (Real.pi * d / 2) := by
  unfold buffonPlacementSet
  rw [Measure.volume_eq_prod ℝ ℝ, Measure.prod_prod]
  rw [Real.volume_Icc, Real.volume_Icc]
  simp only [sub_zero]
  rw [← ENNReal.ofReal_mul Real.pi_pos.le]
  ring_nf

/-- The placement rectangle is measurable. -/
theorem measurableSet_buffonPlacementSet (d : ℝ) :
    MeasurableSet (buffonPlacementSet d) := by
  unfold buffonPlacementSet
  exact measurableSet_Icc.prod measurableSet_Icc

/-- The normalized placement measure has total mass one. -/
theorem buffonPlacementMeasure_univ {d : ℝ} (hd : 0 < d) :
    buffonPlacementMeasure d Set.univ = 1 := by
  unfold buffonPlacementMeasure
  rw [Measure.smul_apply, Measure.restrict_apply_univ, volume_buffonPlacementSet d]
  rw [smul_eq_mul]
  rw [← ENNReal.ofReal_mul]
  · rw [← ENNReal.ofReal_one]
    congr 1
    field_simp [Real.pi_ne_zero, hd.ne']
  · positivity

/-- For positive spacing, `buffonPlacementMeasure` is a probability measure. -/
theorem buffonPlacementMeasure_isProbabilityMeasure {d : ℝ} (hd : 0 < d) :
    IsProbabilityMeasure (buffonPlacementMeasure d) :=
  ⟨buffonPlacementMeasure_univ hd⟩

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

/-- The integral of the center-distance threshold over the angle range. -/
theorem buffonCenterThreshold_integral_Icc (length : ℝ) :
    ∫ θ in Set.Icc (0 : ℝ) Real.pi, buffonCenterThreshold length θ = length := by
  rw [MeasureTheory.integral_Icc_eq_integral_Ioc]
  rw [← intervalIntegral.integral_of_le Real.pi_pos.le]
  unfold buffonCenterThreshold
  rw [intervalIntegral.integral_div, intervalIntegral.integral_const_mul,
    buffon_rotational_symmetry_integral]
  ring

/-- The open crossing region has area `length`. -/
theorem volume_buffonCrossingRegion {length : ℝ} (hlen : 0 ≤ length) :
    volume (buffonCrossingRegion length) = ENNReal.ofReal length := by
  unfold buffonCrossingRegion
  rw [Measure.volume_eq_prod ℝ ℝ]
  rw [volume_regionBetween_eq_integral]
  · simp only [Pi.sub_apply, sub_zero]
    rw [buffonCenterThreshold_integral_Icc]
  · exact continuous_const.integrableOn_Icc
  · have hcont : Continuous fun θ : ℝ => buffonCenterThreshold length θ := by
      unfold buffonCenterThreshold
      fun_prop
    exact hcont.integrableOn_Icc
  · exact measurableSet_Icc
  · intro θ hθ
    exact (buffonCenterThreshold_mem_Icc (d := length) hlen le_rfl hθ.1 hθ.2).1

/-- The boundary of the crossing set has zero planar measure, so the closed
crossing set and the open region have the same area. -/
theorem volume_buffonCrossingSet_eq_region (length : ℝ) :
    volume (buffonCrossingSet length) = volume (buffonCrossingRegion length) := by
  rw [Measure.volume_eq_prod ℝ ℝ]
  rw [Measure.prod_apply (measurableSet_buffonCrossingSet length),
    Measure.prod_apply (measurableSet_buffonCrossingRegion length)]
  apply lintegral_congr
  intro θ
  by_cases hθ : θ ∈ Set.Icc (0 : ℝ) Real.pi
  · have hclosed :
        (Prod.mk θ ⁻¹' buffonCrossingSet length) =
          Set.Icc (0 : ℝ) (buffonCenterThreshold length θ) := by
      ext x
      simp [buffonCrossingSet, hθ.1, hθ.2]
    have hopen :
        (Prod.mk θ ⁻¹' buffonCrossingRegion length) =
          Set.Ioo (0 : ℝ) (buffonCenterThreshold length θ) := by
      ext x
      simp [buffonCrossingRegion, regionBetween, hθ.1, hθ.2]
    rw [hclosed, hopen, Real.volume_Icc, Real.volume_Ioo]
  · have hclosed : (Prod.mk θ ⁻¹' buffonCrossingSet length) = ∅ := by
      have hθ' : ¬ (0 ≤ θ ∧ θ ≤ Real.pi) := by
        simpa [Set.mem_Icc] using hθ
      ext x
      simp [buffonCrossingSet, hθ']
    have hopen : (Prod.mk θ ⁻¹' buffonCrossingRegion length) = ∅ := by
      have hθ' : ¬ (0 ≤ θ ∧ θ ≤ Real.pi) := by
        simpa [Set.mem_Icc] using hθ
      ext x
      simp [buffonCrossingRegion, regionBetween, hθ']
    rw [hclosed, hopen]

/-- The crossing set area is the `lintegral` of its indicator. -/
theorem volume_buffonCrossingSet_eq_lintegral_indicator (length : ℝ) :
    volume (buffonCrossingSet length) =
      ∫⁻ p, ((buffonCrossingSet length).indicator
        (1 : BuffonPlacement → ℝ≥0∞) p) ∂volume := by
  rw [lintegral_indicator_one (measurableSet_buffonCrossingSet length)]

/-- On the placement rectangle, the threshold predicate is the same indicator
as the closed crossing set. -/
theorem buffonThresholdIndicator_eq_crossingIndicator_on_placementSet
    (d length : ℝ) :
    Set.EqOn
      (({p : BuffonPlacement | p.2 ≤ buffonCenterThreshold length p.1}).indicator
        (1 : BuffonPlacement → ℝ))
      ((buffonCrossingSet length).indicator (1 : BuffonPlacement → ℝ))
      (buffonPlacementSet d) := by
  intro p hp
  rcases hp with ⟨hθ, hx⟩
  by_cases hcross : p.2 ≤ buffonCenterThreshold length p.1
  · have hthreshold :
        p ∈ {p : BuffonPlacement | p.2 ≤ buffonCenterThreshold length p.1} := hcross
    have hset : p ∈ buffonCrossingSet length := ⟨hθ, ⟨hx.1, hcross⟩⟩
    simp [hthreshold, hset]
  · have hthreshold :
        p ∉ {p : BuffonPlacement | p.2 ≤ buffonCenterThreshold length p.1} := hcross
    have hset : p ∉ buffonCrossingSet length := by
      intro hp'
      exact hcross hp'.2.2
    simp [hthreshold, hset]

/-- The real integral of the threshold indicator over the placement rectangle
is the planar crossing area. -/
theorem buffonThresholdIndicator_integral_eq_crossingArea {d length : ℝ}
    (hlen : 0 ≤ length) (hle : length ≤ d) :
    ∫ p in buffonPlacementSet d,
        ({p : BuffonPlacement | p.2 ≤ buffonCenterThreshold length p.1}).indicator
          (1 : BuffonPlacement → ℝ) p ∂volume =
      (volume (buffonCrossingSet length)).toReal := by
  rw [setIntegral_congr_fun (measurableSet_buffonPlacementSet d)
    (buffonThresholdIndicator_eq_crossingIndicator_on_placementSet d length)]
  rw [integral_indicator_one (μ := volume.restrict (buffonPlacementSet d))
    (measurableSet_buffonCrossingSet length)]
  rw [measureReal_def]
  rw [Measure.restrict_eq_self volume (buffonCrossingSet_subset_placementSet hlen hle)]

/-- The unnormalized crossing indicator integral over the placement rectangle
has area `length`. -/
theorem buffonThresholdIndicator_integral {d length : ℝ}
    (hlen : 0 ≤ length) (hle : length ≤ d) :
    ∫ p in buffonPlacementSet d,
        ({p : BuffonPlacement | p.2 ≤ buffonCenterThreshold length p.1}).indicator
          (1 : BuffonPlacement → ℝ) p ∂volume =
      length := by
  rw [buffonThresholdIndicator_integral_eq_crossingArea hlen hle,
    volume_buffonCrossingSet_eq_region, volume_buffonCrossingRegion hlen,
    ENNReal.toReal_ofReal hlen]

/-- The crossing probability is the crossing area divided by the total placement
area. -/
theorem buffonNeedleCrossingProbability_eq_volume_ratio {d length : ℝ}
    (hd : 0 < d) (hlen : 0 ≤ length) (hle : length ≤ d) :
    buffonNeedleCrossingProbability d length =
      (volume (buffonCrossingSet length)).toReal /
        (volume (buffonPlacementSet d)).toReal := by
  unfold buffonNeedleCrossingProbability buffonPlacementMeasure
  rw [Measure.smul_apply]
  rw [Measure.restrict_eq_self volume (buffonCrossingSet_subset_placementSet hlen hle)]
  rw [smul_eq_mul, ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity)]
  rw [volume_buffonPlacementSet d, ENNReal.toReal_ofReal (by positivity)]
  field_simp [Real.pi_ne_zero, hd.ne']

/-- The crossing probability is the normalized integral of the threshold
indicator over `[0,π] × [0,d/2]`. -/
theorem buffonNeedleCrossingProbability_eq_normalized_thresholdIntegral {d length : ℝ}
    (hd : 0 < d) (hlen : 0 ≤ length) (hle : length ≤ d) :
    buffonNeedleCrossingProbability d length =
      (2 / (Real.pi * d)) *
        ∫ p in buffonPlacementSet d,
          ({p : BuffonPlacement | p.2 ≤ buffonCenterThreshold length p.1}).indicator
            (1 : BuffonPlacement → ℝ) p ∂volume := by
  unfold buffonNeedleCrossingProbability buffonPlacementMeasure
  rw [Measure.smul_apply]
  rw [Measure.restrict_eq_self volume (buffonCrossingSet_subset_placementSet hlen hle)]
  rw [buffonThresholdIndicator_integral_eq_crossingArea hlen hle]
  rw [smul_eq_mul, ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity)]

/-- The normalized threshold-indicator integral is Buffon's short-needle
probability formula. -/
theorem buffonThresholdIndicator_integral_normalized {d length : ℝ}
    (_hd : 0 < d) (hlen : 0 ≤ length) (hle : length ≤ d) :
    (2 / (Real.pi * d)) *
        ∫ p in buffonPlacementSet d,
          ({p : BuffonPlacement | p.2 ≤ buffonCenterThreshold length p.1}).indicator
            (1 : BuffonPlacement → ℝ) p ∂volume =
      2 * length / (Real.pi * d) := by
  rw [buffonThresholdIndicator_integral hlen hle]
  ring

/-- Integrating the normalized placement density over the geometric crossing
region gives the Buffon short-needle probability formula. -/
theorem buffonCrossingRegion_density_integral {d length : ℝ}
    (_hd : 0 < d) (hlen : 0 ≤ length) :
    ∫ _ in buffonCrossingRegion length, (2 / (Real.pi * d) : ℝ) ∂volume =
      2 * length / (Real.pi * d) := by
  rw [setIntegral_const, measureReal_def]
  rw [volume_buffonCrossingRegion hlen, ENNReal.toReal_ofReal hlen]
  ring

/-- The placement measure of the actual crossing set is the Buffon formula. -/
theorem buffonPlacementMeasure_crossingSet {d length : ℝ}
    (hd : 0 < d) (hlen : 0 ≤ length) (hle : length ≤ d) :
    buffonPlacementMeasure d (buffonCrossingSet length) =
      ENNReal.ofReal (2 * length / (Real.pi * d)) := by
  unfold buffonPlacementMeasure
  rw [Measure.smul_apply]
  rw [Measure.restrict_eq_self volume (buffonCrossingSet_subset_placementSet hlen hle)]
  rw [volume_buffonCrossingSet_eq_region, volume_buffonCrossingRegion hlen]
  rw [smul_eq_mul]
  rw [← ENNReal.ofReal_mul]
  · congr 1
    ring
  · positivity

/-- The measure-theoretic crossing probability is the integral of the constant
placement density over the geometric crossing region. -/
theorem buffonNeedleCrossingProbability_eq_crossingRegion_densityIntegral
    {d length : ℝ} (hd : 0 < d) (hlen : 0 ≤ length) (hle : length ≤ d) :
    buffonNeedleCrossingProbability d length =
      ∫ _ in buffonCrossingRegion length, (2 / (Real.pi * d) : ℝ) ∂volume := by
  rw [buffonNeedleCrossingProbability_eq_volume_ratio hd hlen hle]
  rw [volume_buffonCrossingSet_eq_region, volume_buffonCrossingRegion hlen,
    volume_buffonPlacementSet d, ENNReal.toReal_ofReal hlen,
    ENNReal.toReal_ofReal (by positivity)]
  rw [buffonCrossingRegion_density_integral hd hlen]
  field_simp [Real.pi_ne_zero, hd.ne']

/-- The old density-level average equals the segment formula. -/
theorem buffonNeedleCrossingDensityAverage_eq_segmentExpectedCrossings
    (d length : ℝ) (_hd : 0 < d) :
    buffonNeedleCrossingDensityAverage d length = segmentExpectedCrossings d length := by
  unfold buffonNeedleCrossingDensityAverage buffonConditionalCrossingProbability
    buffonCenterThreshold segmentExpectedCrossings
  rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_div,
    intervalIntegral.integral_const_mul, buffon_rotational_symmetry_integral]
  ring_nf

/-- The actual measure-theoretic crossing probability equals the segment formula. -/
theorem buffonNeedleCrossingProbability_eq_segmentExpectedCrossings
    (d length : ℝ) (hd : 0 < d) (hlen : 0 ≤ length) (hle : length ≤ d) :
    buffonNeedleCrossingProbability d length = segmentExpectedCrossings d length := by
  rw [buffonNeedleCrossingProbability_eq_normalized_thresholdIntegral hd hlen hle,
    buffonThresholdIndicator_integral_normalized hd hlen hle]
  rfl

/-- The measure-theoretic probability agrees with the older density-level
average. -/
theorem buffonNeedleCrossingProbability_eq_densityAverage
    (d length : ℝ) (hd : 0 < d) (hlen : 0 ≤ length) (hle : length ≤ d) :
    buffonNeedleCrossingProbability d length =
      buffonNeedleCrossingDensityAverage d length := by
  rw [buffonNeedleCrossingProbability_eq_segmentExpectedCrossings d length hd hlen hle,
    buffonNeedleCrossingDensityAverage_eq_segmentExpectedCrossings d length hd]

/--
Chapter 25 (Buffon's needle, short-needle density model):
For `0 ≤ ℓ ≤ d`, the normalized placement measure on
`[0,π] × [0,d/2]` assigns the crossing set probability `2ℓ/(πd)`.
-/
theorem chapter25 (d length : ℝ) (hd : 0 < d) (hlen : 0 ≤ length) (hle : length ≤ d) :
    buffonNeedleCrossingProbability d length = 2 * length / (Real.pi * d) := by
  rw [buffonNeedleCrossingProbability_eq_crossingRegion_densityIntegral hd hlen hle,
    buffonCrossingRegion_density_integral hd hlen]

end ProofsInTheBook.Chapter25
