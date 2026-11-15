import Agafonov.Kamae1973.StubBase

namespace Agafonov.Kamae1973

axiom stageLaw_of_prefixLaws {C : Type*}
    [Fintype C] [DecidableEq C]
    (x : ℕ → C) {a N L : ℕ} (q : (Fin L → C) → ℝ)
    (haN : a < N)
    {β : ℝ} (hβ : 0 < β) (hβsmall : β ≤ 1 / 16)
    (hnew : finiteLOne (empiricalLaw x N L) q ≤ β / 8)
    (hratio : (a : ℝ) / (N : ℝ) ≤ β / 16) :
    finiteLOne (intervalEmpiricalLaw x a (N - a) L) q ≤ β

end Agafonov.Kamae1973
