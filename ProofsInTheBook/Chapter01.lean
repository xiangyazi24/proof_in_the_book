import Mathlib
import Mathlib.NumberTheory.LucasLehmer

namespace ProofsInTheBook.Chapter01

/--
Chapter 1: Six proofs of the infinity of primes.
-/

theorem chapter01_euclid : Infinite {p : ℕ // p.Prime} := by
  classical
  refine infinite_of_forall_exists_gt ?_
  intro q
  let N : ℕ := q.val.factorial + 1
  have hNne : N ≠ 1 := by
    dsimp [N]
    exact Nat.succ_ne_zero q.val.factorial
  obtain ⟨p, hp, hpdvd⟩ := Nat.exists_prime_and_dvd hNne
  refine ⟨⟨p, hp⟩, ?_⟩
  dsimp
  by_contra hle
  have hp_le_q : p ≤ q.val := hle
  have hpdvd_fact : p ∣ q.val.factorial := Nat.dvd_factorial hp.pos hp_le_q
  have hpdvd_one : p ∣ 1 := by
    exact (Nat.dvd_add_iff_right hpdvd_fact).2 hpdvd
  exact hp.not_dvd_one hpdvd_one

/--
Second proof via Fermat numbers.
Show that Fermat numbers are pairwise coprime.
-/

theorem chapter01_fermat_coprime :
    ∀ m n : ℕ, m ≠ n → Nat.Coprime (Nat.fermatNumber m) (Nat.fermatNumber n) := by
  intro m n hmn
  exact Nat.coprime_fermatNumber_fermatNumber hmn

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
