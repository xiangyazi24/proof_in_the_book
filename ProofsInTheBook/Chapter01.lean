import Mathlib
import Mathlib.NumberTheory.LucasLehmer

namespace ProofsInTheBook.Chapter01

/--
Chapter 1: Six proofs of the infinity of primes.
-/

theorem chapter01_euclid : Infinite {p : ℕ // p.Prime} := by
  classical
  -- TODO (book-style rewrite): build the set-of-primes finite assumption,
  -- define N as product of all listed primes, and derive contradiction via a prime divisor of N + 1.
  sorry

/--
Second proof via Fermat numbers.
Show that Fermat numbers are pairwise coprime.
-/

theorem chapter01_fermat_coprime :
    ∀ m n : ℕ, m ≠ n → Nat.Coprime (Nat.fermatNumber m) (Nat.fermatNumber n) := by
  -- TODO (book-style rewrite): assume a common prime divisor q of F_m and F_n,
  -- use m≠n to show q divides both 2^(gcd m n)+1 and difference (2^((2^n)) etc.),
  -- then force q=2 and contradict oddness.
  sorry

/--
Third proof via Mersenne numbers.
For n > 1, each Mersenne number has a prime divisor.
-/

theorem chapter01_mersenne : ∀ n : ℕ, 1 < n → ∃ p : ℕ, p.Prime ∧ p ∣ mersenne n := by
  intro n hn
  have hmn : mersenne n ≠ 1 := by
    exact ne_of_gt (lt_of_lt_of_le (by decide) (one_lt_mersenne.2 hn))
  obtain ⟨p, hp, hp'⟩ := Nat.exists_prime_and_dvd hmn
  exact ⟨p, hp, hp'⟩

/--
Fourth proof via Euler-style argument on n! + 1.
-/

theorem chapter01_euler : ∀ n : ℕ, ∃ p : ℕ, p.Prime ∧ p ∣ (n.factorial + 1) := by
  intro n
  have hmn : n.factorial + 1 ≠ 1 := by
    exact ne_of_gt (Nat.succ_lt_succ (Nat.factorial_pos _))
  obtain ⟨p, hp, hp'⟩ := Nat.exists_prime_and_dvd hmn
  exact ⟨p, hp, hp'⟩

/--
Fifth proof via divisors of Fermat numbers.
-/

theorem chapter01_furstenberg : ∀ n : ℕ, ∃ p : ℕ, p.Prime ∧ p ∣ Nat.fermatNumber n := by
  intro n
  refine ⟨Nat.minFac (Nat.fermatNumber n), ?_, Nat.minFac_dvd _⟩
  exact Nat.minFac_prime (ne_of_gt <| lt_of_lt_of_le (by decide) (Nat.three_le_fermatNumber n))

/--
Overall chapter marker.
-/

theorem chapter01 : Infinite {p : ℕ // p.Prime} := by
  exact chapter01_euclid

end ProofsInTheBook.Chapter01
