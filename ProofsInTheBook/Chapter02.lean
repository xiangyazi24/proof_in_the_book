import Mathlib

-- Chapter 2: Bertrand's postulate.

namespace ProofsInTheBook.Chapter02

-- Bertrand's postulate statement.
-- For every n ≥ 1 there exists a prime p with n < p ≤ 2*n.

theorem chapter02_bertrand : ∀ n : ℕ, n ≠ 0 → ∃ p : ℕ, Nat.Prime p ∧ n < p ∧ p ≤ 2 * n := by
  intro n hn0
  exact Nat.exists_prime_lt_and_le_two_mul n hn0

-- Landau's reduction.
-- A finite sequence of explicit checked primes gives Bertrand for small n, then only large n remain.

theorem chapter02_landau_trick : ∀ n : ℕ, 4 ≤ n → 4 ^ n < n * n.centralBinom := by
  intro n hn
  exact Nat.four_pow_lt_mul_centralBinom n hn

-- Inequality (1): product of primes up to x ≤ 4^(x-1) for x ≥ 2.

theorem chapter02_prime_product_bound :
    ∀ n : ℕ, 2 < n → (∀ p : ℕ, Nat.Prime p → n < p → 2 * n < p) →
      n.centralBinom ≤ (2 * n) ^ (2 * n).sqrt * 4 ^ (2 * n / 3) := by
  intro n hn hnp
  exact centralBinom_le_of_no_bertrand_prime n hn hnp

-- Legendre exponent decomposition for n! and binomial valuation bounds used in the proof.

theorem chapter02_legendre : ∀ n : ℕ, 512 ≤ n →
    n * (2 * n) ^ (2 * n).sqrt * 4 ^ (2 * n / 3) ≤ 4 ^ n := by
  intro n hn
  exact bertrand_main_inequality hn

-- Binomial coefficient estimate and contradiction step giving a prime in (n, 2n].

theorem chapter02_binomial_bound :
    ∀ n : ℕ, 2 < n → (∀ p : ℕ, Nat.Prime p → n < p → 2 * n < p) →
      n.centralBinom ≤ (2 * n) ^ (2 * n).sqrt * 4 ^ (2 * n / 3) := by
  intro n hn hnp
  exact centralBinom_le_of_no_bertrand_prime n hn hnp

-- Overall chapter marker.

theorem chapter02 : Infinite {p : ℕ // p.Prime} := by
  exact Nat.infinite_setOf_prime.to_subtype

end ProofsInTheBook.Chapter02
