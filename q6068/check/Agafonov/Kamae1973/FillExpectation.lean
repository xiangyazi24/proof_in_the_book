import Agafonov.Kamae1973.RandomFillCoordinates

namespace Agafonov.Kamae1973

open scoped BigOperators

noncomputable section

noncomputable def fillWindowExpectation {b q : ℕ}
    (P : LetterDistribution b) (τ : ℕ → ℕ) (y : ℕ → Fin b)
    (i : ℕ) (w : Fin q → Fin b) : ℝ := by
  classical
  exact ∏ r : Fin q,
    if h : i + r.val ∈ Set.range τ then
      if y (Classical.choose h) = w r then 1 else 0
    else P.prob (w r)

end

end Agafonov.Kamae1973
