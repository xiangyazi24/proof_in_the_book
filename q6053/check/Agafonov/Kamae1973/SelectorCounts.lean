import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Finset.Interval
import Mathlib.Data.List.OfFn

namespace Agafonov.Kamae1973

open scoped BigOperators

/-- Indicator of the range of a selection function. -/
noncomputable def rangeIndicator (τ : ℕ → ℕ) (k : ℕ) : Bool :=
  @decide (k ∈ Set.range τ) (Classical.propDecidable _)

/-- The Boolean range indicator is true exactly on the selector range. -/
theorem rangeIndicator_eq_true_iff (τ : ℕ → ℕ) (k : ℕ) :
    rangeIndicator τ k = true ↔ k ∈ Set.range τ := by
  classical
  simp [rangeIndicator]

end Agafonov.Kamae1973
