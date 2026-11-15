import Agafonov.Kamae1973.StubBase

namespace Agafonov.Kamae1973

axiom exists_sequence_extending_stages
    {A : Type*} [Nonempty A]
    (N : ℕ → ℕ) (hN : StrictMono N) (filler : A)
    (stage : ∀ k, Fin (N (k + 1) - N k) → A) :
    ∃ x : ℕ → A,
      (∀ n, n < N 0 → x n = filler) ∧
      ∀ k, ExtendsInterval (N k) (stage k) x

end Agafonov.Kamae1973
