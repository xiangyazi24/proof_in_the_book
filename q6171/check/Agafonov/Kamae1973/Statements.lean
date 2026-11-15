import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
import Mathlib.Order.LiminfLimsup

namespace Agafonov.Kamae1973

open Filter Topology

/-- The growth hypothesis `limsup τ(n)/n < ∞`, in eventual-linear form. -/
def HasLinearGrowth (τ : ℕ → ℕ) : Prop :=
  ∃ C : ℝ, ∀ᶠ n : ℕ in atTop, (τ n : ℝ) ≤ C * (n : ℝ)

end Agafonov.Kamae1973
