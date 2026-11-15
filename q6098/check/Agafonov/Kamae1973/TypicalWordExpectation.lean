import Agafonov.Kamae1973.StubBase
import Mathlib.Data.List.TakeDrop

namespace Agafonov.Kamae1973

/-- Number of wholly internal occurrences of a word. -/
def internalOccurrenceCount {b L r : ℕ}
    (u : Fin L → Fin b) (w : Fin r → Fin b) : ℕ :=
  ((Finset.univ : Finset (Fin (L + 1 - r))).filter fun
      (j : Fin (L + 1 - r)) =>
    ((List.ofFn u).drop j.1).take r = List.ofFn w).card

/-- Internal occurrence frequency normalized by the block length. -/
noncomputable def internalFrequency {b L r : ℕ}
    (u : Fin L → Fin b) (w : Fin r → Fin b) : ℝ :=
  (internalOccurrenceCount u w : ℝ) / (L : ℝ)

/-- Simultaneous typicality for all words through resolution `R`. -/
def IsTypicalWord {b : ℕ} (P : LetterDistribution b)
    (L R : ℕ) (β : ℝ) (u : Fin L → Fin b) : Prop :=
  ∀ r : ℕ, 1 ≤ r → r ≤ R →
    ∀ w : Fin r → Fin b,
      |internalFrequency u w - P.wordMass (List.ofFn w)| ≤ β

end Agafonov.Kamae1973
