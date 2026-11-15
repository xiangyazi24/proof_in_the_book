import Agafonov.Kamae1973.StubBase

namespace Agafonov.Kamae1973

open Filter Topology

axiom paintedStages_firstMarginal_allPrefixes {b : ℕ}
    (P : LetterDistribution b) (x : ℕ → Fin b)
    (N M : ℕ → ℕ) (hN : StrictMono N)
    (β : ℕ → ℝ) (hβ : Tendsto β atTop (𝓝 0))
    (hratio : Tendsto
      (fun k => (N k : ℝ) / (N (k + 1) : ℝ))
      atTop (𝓝 0))
    (hlook : Tendsto (fun k => (M k : ℝ) / (N k : ℝ))
      atTop (𝓝 0))
    (hprefix : ∀ k s, s ≤ N (k + 1) - N k →
      ∀ r, 1 ≤ r → r ≤ k + 1 →
        ∀ w : Fin r → Fin b,
          |(intervalWordCount x (N k) s (List.ofFn w) : ℝ) -
              (s : ℝ) * P.wordMass (List.ofFn w)| ≤
            4 * β k * (s : ℝ) + M k) :
    IsWeightedNormal P x

end Agafonov.Kamae1973
