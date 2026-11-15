import Agafonov.Kamae1973.Statements
import Mathlib.Probability.ProductMeasure
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Topology.MetricSpace.ProperSpace
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic

/-!
# Bernoulli normality for compact metric alphabets

The compact-metric formulation of normality and the four conditions in
Kamae (1973), Section 1 and Theorem 4 (pp. 121–124, 147).
Normality is expressed by continuous finite-window averages and, equivalently,
by continuous observables on the countable sequence space.
-/

namespace Agafonov.Kamae1973

open Filter Topology MeasureTheory
open scoped BigOperators ENNReal

/-- Shift a sequence to the window starting at `i`.
This is the shift used in Kamae (1973), Section 1. -/
def compactShift {X : Type*} (ξ : ℕ → X) (i : ℕ) : ℕ → X :=
  fun j => ξ (i + j)

/-- The length-`r` word starting at `i` in a sequence.
This is the finite block observable of Kamae (1973), Section 1. -/
def compactWindow {X : Type*} (ξ : ℕ → X)
    (i r : ℕ) : Fin r → X :=
  fun j => ξ (i + j.val)

/-- A Borel measure is concentrated at a single point.
This is the nondegeneracy exclusion in Kamae (1973), Theorem 4. -/
def IsDiracMeasure {X : Type*} [MeasurableSpace X]
    (P : Measure X) : Prop :=
  ∃ x : X, P = Measure.dirac x

/-- Bernoulli normality tested on every continuous finite-window observable.
The target law is the finite marginal of the Bernoulli product measure
from Kamae (1973), Section 1 (pp. 121–124). -/
noncomputable def IsCompactNormal
    {X : Type*} [MetricSpace X] [CompactSpace X]
    [MeasurableSpace X] [BorelSpace X]
    (P : Measure X) [IsProbabilityMeasure P]
    (ξ : ℕ → X) : Prop :=
  ∀ (r : ℕ) (F : (Fin r → X) → ℝ), Continuous F →
    Tendsto
      (fun N : ℕ =>
        (∑ i ∈ Finset.range N, F (compactWindow ξ i r)) / (N : ℝ))
      atTop
      (𝓝 (∫ w : Fin r → X, F w ∂(Measure.pi (fun _ : Fin r => P))))

/-- Weak Bernoulli normality tested on continuous observables of the full
sequence space, corresponding to the empirical orbit measures in
Kamae (1973), Section 1 (pp. 121–124). -/
noncomputable def IsCompactWeakNormal
    {X : Type*} [MetricSpace X] [CompactSpace X]
    [MeasurableSpace X] [BorelSpace X]
    (P : Measure X) [IsProbabilityMeasure P]
    (ξ : ℕ → X) : Prop :=
  ∀ F : (ℕ → X) → ℝ, Continuous F →
    Tendsto
      (fun N : ℕ =>
        (∑ i ∈ Finset.range N, F (compactShift ξ i)) / (N : ℝ))
      atTop
      (𝓝 (∫ ω : ℕ → X, F ω ∂
        (Measure.infinitePi (fun _ : ℕ => P))))

/-- The selected single-letter empirical averages converge to the letter law,
the collective condition of Kamae (1973), Theorem 4. -/
noncomputable def IsCompactCollective
    {X : Type*} [MetricSpace X] [CompactSpace X]
    [MeasurableSpace X] [BorelSpace X]
    (P : Measure X) [IsProbabilityMeasure P]
    (ξ : ℕ → X) (τ : ℕ → ℕ) : Prop :=
  ∀ F : X → ℝ, Continuous F →
    Tendsto
      (fun N : ℕ =>
        (∑ i ∈ Finset.range N, F (ξ (τ i))) / (N : ℝ))
      atTop (𝓝 (∫ x : X, F x ∂P))

/-- Every normal sequence is collective under selection.
Kamae (1973), Theorem 4, Condition 1. -/
noncomputable def ConditionOneCompact
    {X : Type*} [MetricSpace X] [CompactSpace X]
    [MeasurableSpace X] [BorelSpace X]
    (P : Measure X) [IsProbabilityMeasure P] (τ : ℕ → ℕ) : Prop :=
  ∀ ξ : ℕ → X, IsCompactNormal P ξ → IsCompactCollective P ξ τ

/-- Selection preserves Bernoulli normality.
Kamae (1973), Theorem 4, Condition 2. -/
noncomputable def ConditionTwoCompact
    {X : Type*} [MetricSpace X] [CompactSpace X]
    [MeasurableSpace X] [BorelSpace X]
    (P : Measure X) [IsProbabilityMeasure P] (τ : ℕ → ℕ) : Prop :=
  ∀ ξ : ℕ → X, IsCompactNormal P ξ →
    IsCompactNormal P (fun n => ξ (τ n))

/-- The image of the normal sequences under selection equals the entire
set of normal sequences. Kamae (1973), Theorem 4, Condition 3. -/
noncomputable def ConditionThreeCompact
    {X : Type*} [MetricSpace X] [CompactSpace X]
    [MeasurableSpace X] [BorelSpace X]
    (P : Measure X) [IsProbabilityMeasure P] (τ : ℕ → ℕ) : Prop :=
  {η : ℕ → X | ∃ ξ : ℕ → X,
      IsCompactNormal P ξ ∧ η = fun n => ξ (τ n)} =
    {η : ℕ → X | IsCompactNormal P η}

/-- The binary indicator of the selector is completely deterministic.
Kamae (1973), Theorem 4, Condition 4. -/
def ConditionFourCompact (τ : ℕ → ℕ) : Prop :=
  ConditionFour τ

#print axioms Agafonov.Kamae1973.compactShift
#print axioms Agafonov.Kamae1973.compactWindow
#print axioms Agafonov.Kamae1973.IsDiracMeasure
#print axioms Agafonov.Kamae1973.IsCompactNormal
#print axioms Agafonov.Kamae1973.IsCompactWeakNormal
#print axioms Agafonov.Kamae1973.IsCompactCollective
#print axioms Agafonov.Kamae1973.ConditionOneCompact
#print axioms Agafonov.Kamae1973.ConditionTwoCompact
#print axioms Agafonov.Kamae1973.ConditionThreeCompact
#print axioms Agafonov.Kamae1973.ConditionFourCompact

end Agafonov.Kamae1973
