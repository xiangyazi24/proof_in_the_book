import Mathlib

/-!
Chapter 3: Binomial coefficients are (almost) never powers.
-/

namespace ProofsInTheBook.Chapter03

-- Sylvester-style theorem on binomial coefficients.

theorem chapter03_sylvester : ∀ n k : ℕ, n ≥ 2 * k → k > 0 → ∃ p : ℕ, p > k ∧ p.Prime ∧ p ∣ Nat.choose n k := by
  intro n k hn hk
  exact Nat.exists_prime_and_dvd_choose_of_two_mul_le hn hk

-- Binomial coefficients are almost never perfect powers.

theorem chapter03_binomials_coefficients_never_powers :
    ∀ k l m n : ℕ, 2 ≤ l → 4 ≤ k → k ≤ n - 4 → Nat.choose n k ≠ m ^ l := by
  intro k l m n hl hk hkn
  exact Nat.choose_ne_pow_of_two_le hl hk hkn

-- Chapter marker.

theorem chapter03 : ∀ n : ℕ, ∃ p : ℕ, n ≤ p ∧ Nat.Prime p := by
  intro n
  exact Nat.exists_infinite_primes n

end ProofsInTheBook.Chapter03
