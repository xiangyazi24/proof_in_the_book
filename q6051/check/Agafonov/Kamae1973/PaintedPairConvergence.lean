import Agafonov.Kamae1973.StubBase

namespace Agafonov.Kamae1973

open Filter Topology

axiom paintedStages_pairCoordinateConverge {C : Type*}
    [Fintype C] [DecidableEq C]
    (x : ℕ → C) (ν : BlockFamily C)
    (N : ℕ → ℕ) (hN : StrictMono N)
    (β : ℕ → ℝ) (hβ : Tendsto β atTop (𝓝 0))
    (hratio : Tendsto
      (fun k => (N k : ℝ) / (N (k + 1) : ℝ)) atTop (𝓝 0))
    (hstage : ∀ k r, 1 ≤ r → r ≤ k + 1 →
      finiteLOne
        (intervalEmpiricalLaw x (N k) (N (k + 1) - N k) r)
        (ν.law r) ≤ 15 * β k) :
    ∀ r w,
      Tendsto (fun k => empiricalLaw x (N (k + 1)) r w)
        atTop (𝓝 (ν.law r w))

end Agafonov.Kamae1973
