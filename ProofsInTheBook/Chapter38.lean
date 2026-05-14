import Mathlib

/-!
# Chapter 38: Communicating without errors

From "Proofs from THE BOOK":

**Shannon's theorem**: The capacity of a binary symmetric channel
with error probability p is C = 1 - H(p), where H is the binary entropy.

The book discusses error-correcting codes, the Hamming bound,
the Singleton bound, and the Gilbert-Varshamov bound.
-/

namespace ProofsInTheBook.Chapter38

/-!
### Unique decoding from Hamming distance

Before the asymptotic capacity statement, coding theory uses the elementary
fact that Hamming balls of radius `t` around codewords are disjoint whenever
the minimum distance is greater than `2t`.
-/

abbrev BinaryWord (n : ℕ) : Type :=
  Fin n → Bool

theorem unique_decode_of_two_mul_radius_lt_distance {n t d : ℕ} {code : Finset (BinaryWord n)}
    (hmin : ∀ c₁ ∈ code, ∀ c₂ ∈ code, c₁ ≠ c₂ → d ≤ hammingDist c₁ c₂)
    (hd : 2 * t < d) {received c₁ c₂ : BinaryWord n}
    (hc₁ : c₁ ∈ code) (hc₂ : c₂ ∈ code)
    (hr₁ : hammingDist c₁ received ≤ t) (hr₂ : hammingDist c₂ received ≤ t) :
    c₁ = c₂ := by
  by_contra hne
  have hdist_lower : d ≤ hammingDist c₁ c₂ := hmin c₁ hc₁ c₂ hc₂ hne
  have hdist_upper : hammingDist c₁ c₂ ≤ 2 * t := by
    have htri : hammingDist c₁ c₂ ≤ hammingDist c₁ received + hammingDist received c₂ :=
      hammingDist_triangle c₁ received c₂
    have hr₂' : hammingDist received c₂ ≤ t := by
      simpa [hammingDist_comm] using hr₂
    nlinarith
  omega

theorem chapter38 {n t d : ℕ} {code : Finset (BinaryWord n)}
    (hmin : ∀ c₁ ∈ code, ∀ c₂ ∈ code, c₁ ≠ c₂ → d ≤ hammingDist c₁ c₂)
    (hd : 2 * t < d) {received c₁ c₂ : BinaryWord n}
    (hc₁ : c₁ ∈ code) (hc₂ : c₂ ∈ code)
    (hr₁ : hammingDist c₁ received ≤ t) (hr₂ : hammingDist c₂ received ≤ t) :
    c₁ = c₂ :=
  unique_decode_of_two_mul_radius_lt_distance hmin hd hc₁ hc₂ hr₁ hr₂

end ProofsInTheBook.Chapter38
