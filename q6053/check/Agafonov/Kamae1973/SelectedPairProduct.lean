import Agafonov.Kamae1973.LocalCorrectionMean

namespace Agafonov.Kamae1973

/-- The selected-clock pair of a shifted letter and capped gap. -/
def selectedPair {b : ℕ} (τ : ℕ → ℕ) (L : ℕ)
    (y : ℕ → Fin b) (j : ℕ) : Fin b × Fin (L + 1) :=
  (y (j + 1), cappedGap τ L j)

end Agafonov.Kamae1973
