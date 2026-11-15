import Agafonov.Kamae1973.PaintingSchedule

namespace Agafonov.Kamae1973

open Filter Topology

axiom exists_fastProfileEndpoints {b : ℕ}
    (P : LetterDistribution b)
    {t : ℕ → Bool} {S : Set ℕ} {μ : BlockFamily Bool}
    (hprofile : IsLimitProfile t S μ) :
    ∃ N : ℕ → ℕ,
      StrictMono N ∧
      (∀ k, N (k + 1) ∈ S) ∧
      (∀ k, 0 < N k) ∧
      (∀ k,
        finiteLOne
          (empiricalLaw t (N (k + 1))
            (stageParameters P k).blockLength)
          (μ.law (stageParameters P k).blockLength) ≤
            paintingTolerance k / 8) ∧
      (∀ k,
        (N k : ℝ) / (N (k + 1) : ℝ) ≤
          paintingTolerance k / 16) ∧
      (∀ k,
        (stageParameters P k).minMacroblocks ≤
          (N (k + 1) - N k) /
            (stageParameters P k).macroLength) ∧
      (∀ k,
        ((stageParameters P k).macroLength : ℝ) /
            ((N (k + 1) - N k : ℕ) : ℝ) ≤
          paintingTolerance k) ∧
      (∀ k,
        ((stageParameters P k).macroLength : ℝ) / (N k : ℝ) ≤
          paintingTolerance k)

end Agafonov.Kamae1973
