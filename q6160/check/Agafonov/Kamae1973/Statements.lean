import Mathlib.Data.Real.Basic
import Mathlib.Data.Set.Basic

namespace Agafonov.Kamae1973

/-- A finite-alphabet letter distribution carrier. -/
def LetterDistribution (b : ℕ) := Fin b → ℝ

/-- Weighted normality, abstracted for the logical interface check. -/
def IsWeightedNormal {b : ℕ}
    (P : LetterDistribution b) (x : ℕ → Fin b) : Prop :=
  True

/-- Selection preserves weighted normality. -/
def ConditionTwo {b : ℕ}
    (P : LetterDistribution b) (τ : ℕ → ℕ) : Prop :=
  ∀ x : ℕ → Fin b,
    IsWeightedNormal P x →
      IsWeightedNormal P (fun n => x (τ n))

/-- Selection maps the set of weighted-normal sequences onto itself. -/
def ConditionThree {b : ℕ}
    (P : LetterDistribution b) (τ : ℕ → ℕ) : Prop :=
  {y : ℕ → Fin b |
      ∃ x : ℕ → Fin b,
        IsWeightedNormal P x ∧ y = fun n => x (τ n)} =
    {y : ℕ → Fin b | IsWeightedNormal P y}

end Agafonov.Kamae1973
