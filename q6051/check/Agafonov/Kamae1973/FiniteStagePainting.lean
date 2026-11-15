import Agafonov.Kamae1973.StubBase

namespace Agafonov.Kamae1973

open scoped BigOperators

axiom exists_finiteStagePainting {b : ℕ}
    (P : LetterDistribution b) (t : ℕ → Bool)
    (μ : BlockFamily Bool) (ν : BlockFamily (Fin b × Bool))
    (a T R : ℕ) {β : ℝ} (hβ : 0 < β)
    (param : PaintingParameters P R β)
    (hT : 0 < T)
    (hmacroblocks :
      param.minMacroblocks ≤ T / param.macroLength)
    (hmacro : (param.macroLength : ℝ) / (T : ℝ) ≤ β)
    (ht :
      finiteLOne
        (intervalEmpiricalLaw t a T param.blockLength)
        (μ.law param.blockLength) ≤ β)
    (hfst : ∀ n : ℕ,
      ν.fst n = fun w : Fin n → Fin b => ∏ i, P.prob (w i))
    (hsnd : ∀ n : ℕ, ν.snd n = μ.law n) :
    ∃ u : Fin T → Fin b,
      (∀ x : ℕ → Fin b, ExtendsInterval a u x →
        ∀ r : ℕ, 1 ≤ r → r ≤ R →
          finiteLOne
            (intervalEmpiricalLaw (fun i => (x i, t i)) a T r)
            (ν.law r) ≤ 15 * β) ∧
      (∀ x : ℕ → Fin b, ExtendsInterval a u x →
        ∀ s : ℕ, s ≤ T →
          ∀ r : ℕ, 1 ≤ r → r ≤ R →
            ∀ w : Fin r → Fin b,
              |(intervalWordCount x a s (List.ofFn w) : ℝ) -
                  (s : ℝ) * P.wordMass (List.ofFn w)| ≤
                4 * β * (s : ℝ) + param.macroLength)

end Agafonov.Kamae1973
