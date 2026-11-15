import Agafonov.Kamae1973.CompactBernoulliNormality
import Mathlib.MeasureTheory.Measure.Portmanteau
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Topology.MetricSpace.ProperSpace

/-!
# Empirical frequencies and portmanteau convergence

Continuous-observable convergence implies convergence of frequencies for sets with
null boundary. This is the empirical-measure form of the portmanteau step in
Kamae (1973), Section 1, pp. 121–124.
-/

namespace Agafonov.Kamae1973

open scoped ENNReal Topology
open MeasureTheory Filter

/-- The empirical probability measure of the first N points of a sequence. -/
noncomputable def empiricalPointMeasure {Y : Type*} [MeasurableSpace Y]
    (y : ℕ → Y) (N : ℕ) : Measure Y :=
  ((N : ℝ≥0∞)⁻¹) • ∑ i ∈ Finset.range N, Measure.dirac (y i)

/-- An empirical point measure with a nonempty sample is a probability measure.
Kamae (1973), Section 1. -/
theorem empiricalPointMeasure_isProbabilityMeasure {Y : Type*} [MeasurableSpace Y]
    (y : ℕ → Y) {N : ℕ} (hN : N ≠ 0) :
    IsProbabilityMeasure (empiricalPointMeasure y N) := by
  constructor
  rw [empiricalPointMeasure, Measure.smul_apply]
  simp [hN]

private theorem empiricalPointMeasure_integral {Y : Type*} [MeasurableSpace Y]
    [MeasurableSingletonClass Y] (y : ℕ → Y) {N : ℕ} (hN : N ≠ 0)
    (F : Y → ℝ) (hF : Measurable F) :
    (∫ x, F x ∂empiricalPointMeasure y N) =
      (∑ i ∈ Finset.range N, F (y i)) / (N : ℝ) := by
  rw [empiricalPointMeasure, integral_smul_measure, integral_finsetSum_measure]
  · simp [integral_dirac, div_eq_mul_inv, ENNReal.toReal_inv, hN]
  · intro i hi
    exact (integrable_dirac (hF.aestronglyMeasurable)).integrable

private theorem empiricalPointMeasure_apply {Y : Type*} [MeasurableSpace Y]
    (y : ℕ → Y) {N : ℕ} (hN : N ≠ 0)
    (E : Set Y) (hE : MeasurableSet E) :
    (empiricalPointMeasure y N) E =
      ((N : ℝ≥0∞)⁻¹) * (((Finset.range N).filter (fun i => y i ∈ E)).card : ℝ≥0∞) := by
  rw [empiricalPointMeasure, Measure.smul_apply]
  simp [Measure.dirac_apply', hE, Finset.sum_boole]

private theorem measurableSet_of_null_frontier
    {Y : Type*} [TopologicalSpace Y] [MeasurableSpace Y]
    [OpensMeasurableSpace Y] (E : Set Y)
    (hE : (frontier E).Null) : MeasurableSet E := by
  have hfront : MeasurableSet (frontier E) := isClosed_frontier.measurableSet
  have hdiff : MeasurableSet (E \ interior E) :=
    hfront.mono (by
      intro x hx
      exact ⟨subset_closure hx.1, hx.2⟩)
  have hdecomp : interior E ∪ (E \ interior E) = E :=
    union_sdiff_cancel interior_subset
  rw [← hdecomp]
  exact isOpen_interior.measurableSet.union hdiff

private theorem empiricalProbabilityMeasures_tendsto
    {Y : Type*} [MeasurableSpace Y] [TopologicalSpace Y]
    [OpensMeasurableSpace Y] [HasOuterApproxClosed Y]
    (μ : Measure Y) [IsProbabilityMeasure μ] (y : ℕ → Y)
    (hy : ∀ F : Y → ℝ, Continuous F →
      Tendsto (fun N : ℕ =>
        (∑ i ∈ Finset.range N, F (y i)) / (N : ℝ)
        ) atTop (𝓝 (∫ x, F x ∂μ))) :
    Tendsto
      (fun N : ℕ =>
        (⟨empiricalPointMeasure y (N + 1),
          empiricalPointMeasure_isProbabilityMeasure y (Nat.succ_ne_zero N)⟩ :
          ProbabilityMeasure Y))
      atTop (𝓝 (⟨μ, inferInstance⟩ : ProbabilityMeasure Y)) := by
  apply ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mpr
  intro f
  have h := (hy f f.continuous).comp (tendsto_add_atTop_nat 1)
  convert h using 1
  · funext N
    exact (empiricalPointMeasure_integral y (Nat.succ_ne_zero N)
      f f.continuous.measurable).symm

/-- Continuous-test convergence gives convergence of empirical frequencies on every
set whose frontier is null. This is the portmanteau theorem for empirical point
measures (Kamae (1973), Section 1, pp. 121–124). -/
open Classical in
theorem empiricalFrequency_tendsto_of_null_frontier
    {Y : Type*} [MetricSpace Y] [CompactSpace Y] [MeasurableSpace Y] [BorelSpace Y]
    (μ : Measure Y) [IsProbabilityMeasure μ] (y : ℕ → Y)
    (hy : ∀ F : Y → ℝ, Continuous F →
      Tendsto (fun N : ℕ =>
        (∑ i ∈ Finset.range N, F (y i)) / (N : ℝ)
        ) atTop (𝓝 (∫ x, F x ∂μ)))
    (E : Set Y) (hE : μ (frontier E) = 0) :
    Tendsto
      (fun N : ℕ =>
        (((Finset.range N).filter (fun i => y i ∈ E)).card : ℝ) / (N : ℝ))
      atTop (𝓝 (μ E).toReal) := by
  have hmeas : MeasurableSet E :=
    measurableSet_of_measurable_frontier E isClosed_frontier.measurableSet
  let μlim : ProbabilityMeasure Y := ⟨μ, inferInstance⟩
  let μseq : ℕ → ProbabilityMeasure Y := fun N =>
    ⟨empiricalPointMeasure y (N + 1),
      empiricalPointMeasure_isProbabilityMeasure y (Nat.succ_ne_zero N)⟩
  have hweak : Tendsto μseq atTop (𝓝 μlim) := by
    exact empiricalProbabilityMeasures_tendsto μ y hy
  have hport :=
    ProbabilityMeasure.tendsto_measure_of_null_frontier_of_tendsto'
      hweak hE
  have hreal :=
    (ENNReal.tendsto_toReal (measure_ne_top μ E)).comp hport
  have hshift :
      Tendsto
        (fun N : ℕ =>
          (((Finset.range (N + 1)).filter (fun i => y i ∈ E)).card : ℝ) /
            ((N + 1 : ℕ) : ℝ))
        atTop (𝓝 (μ E).toReal) := by
    apply hreal.congr'
    filter_upwards [] with N
    rw [empiricalPointMeasure_apply y (Nat.succ_ne_zero N) E hmeas]
    simp [μseq, ENNReal.toReal_mul, ENNReal.toReal_inv,
      Nat.cast_ne_zero.mpr (Nat.succ_ne_zero N)]
  exact (tendsto_add_atTop_iff_nat 1).1 hshift

/-- Compact-window frequencies converge to their Bernoulli product probabilities.
This is the finite-window portmanteau consequence of Kamae (1973), Section 1. -/
open Classical in
theorem compactNormal_windowFrequency_tendsto
    {X : Type*} [MetricSpace X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
    (P : Measure X) [IsProbabilityMeasure P] (ξ : ℕ → X)
    (hξ : IsCompactNormal P ξ) (r : ℕ) (E : Set (Fin r → X))
    (hE : Measure.pi (fun _ : Fin r => P) (frontier E) = 0) :
    Tendsto
      (fun N : ℕ =>
        (((Finset.range N).filter (fun i => compactWindow ξ i r ∈ E)).card : ℝ) /
          (N : ℝ))
      atTop
      (𝓝 ((Measure.pi (fun _ : Fin r => P) E).toReal)) := by
  apply empiricalFrequency_tendsto_of_null_frontier
    (Measure.pi (fun _ : Fin r => P))
    (fun i => compactWindow ξ i r)
  · intro F hF
    exact hξ r F hF
  · exact E
  · exact hE

/-- Selected-coordinate frequencies converge to their one-coordinate marginal.
This is the length-one portmanteau consequence of Kamae (1973), Section 1. -/
open Classical in
theorem compactCollective_frequency_tendsto
    {X : Type*} [MetricSpace X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
    (P : Measure X) [IsProbabilityMeasure P] (ξ : ℕ → X) (τ : ℕ → ℕ)
    (hξ : IsCompactCollective P ξ τ) (E : Set X)
    (hE : P (frontier E) = 0) :
    Tendsto
      (fun N : ℕ =>
        (((Finset.range N).filter (fun i => ξ (τ i) ∈ E)).card : ℝ) / (N : ℝ))
      atTop (𝓝 (P E).toReal) := by
  apply empiricalFrequency_tendsto_of_null_frontier P
    (fun i => ξ (τ i))
  · intro F hF
    exact hξ F hF
  · exact E
  · exact hE

#print axioms Agafonov.Kamae1973.empiricalPointMeasure_isProbabilityMeasure
#print axioms Agafonov.Kamae1973.empiricalFrequency_tendsto_of_null_frontier
#print axioms Agafonov.Kamae1973.compactNormal_windowFrequency_tendsto
#print axioms Agafonov.Kamae1973.compactCollective_frequency_tendsto

end Agafonov.Kamae1973
