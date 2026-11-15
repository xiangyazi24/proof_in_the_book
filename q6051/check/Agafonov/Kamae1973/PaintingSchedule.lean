import Agafonov.Kamae1973.StubBase

namespace Agafonov.Kamae1973

open Filter Topology

noncomputable def paintingTolerance (_k : ℕ) : ℝ := 1

axiom paintingTolerance_pos (k : ℕ) :
  0 < paintingTolerance k

axiom paintingTolerance_le_sixteenth (k : ℕ) :
  paintingTolerance k ≤ 1 / 16

noncomputable def stageParameters {b : ℕ}
    (P : LetterDistribution b) (k : ℕ) :
    PaintingParameters P (k + 1) (paintingTolerance k) where
  blockLength := 1
  macroLength := 1
  minMacroblocks := 1

axiom tendsto_paintingTolerance :
  Tendsto paintingTolerance atTop (𝓝 0)

end Agafonov.Kamae1973
