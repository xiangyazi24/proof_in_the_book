import Agafonov.Kamae1973.Statements
import Mathlib.Probability.ProductMeasure
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Topology.MetricSpace.ProperSpace
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic

namespace Agafonov.Kamae1973
open Filter Topology MeasureTheory
open scoped BigOperators ENNReal
def compactShift {X : Type*} (ξ : ℕ → X) (i : ℕ) : ℕ → X :=
  fun j => ξ (i + j)
def compactWindow {X : Type*} (ξ : ℕ → X) (i r : ℕ) : Fin r → X :=
  fun j => ξ (i + j.val)
noncomputable def IsCompactNormal
    {X : Type*} [MetricSpace X] [CompactSpace X]
    [MeasurableSpace X] [BorelSpace X]
    (P : Measure X) [IsProbabilityMeasure P] (ξ : ℕ → X) : Prop :=
  ∀ (r : ℕ) (F : (Fin r → X) → ℝ), Continuous F →
    Tendsto (fun N : ℕ =>
      (∑ i ∈ Finset.range N, F (compactWindow ξ i r)) / (N : ℝ))
      atTop (𝓝 (∫ w : Fin r → X, F w ∂(Measure.pi (fun _ : Fin r => P))))
noncomputable def IsCompactCollective
    {X : Type*} [MetricSpace X] [CompactSpace X]
    [MeasurableSpace X] [BorelSpace X]
    (P : Measure X) [IsProbabilityMeasure P]
    (ξ : ℕ → X) (τ : ℕ → ℕ) : Prop :=
  ∀ F : X → ℝ, Continuous F →
    Tendsto (fun N : ℕ =>
      (∑ i ∈ Finset.range N, F (ξ (τ i))) / (N : ℝ))
      atTop (𝓝 (∫ x : X, F x ∂P))
end Agafonov.Kamae1973
