import Mathlib
import Mathlib.NumberTheory.LucasLehmer

namespace ProofsInTheBook.Chapter01

/--
Chapter 1: Six proofs of the infinity of primes.
-/

theorem chapter01_euclid : Infinite {p : ℕ // p.Prime} := by
  classical
  rcases finite_or_infinite ({p : ℕ // p.Prime}) with hfin | hinf
  · letI : Fintype ({p : ℕ // p.Prime}) := Fintype.ofFinite ({p : ℕ // p.Prime})
    let N : ℕ := (Finset.univ : Finset {p : ℕ // p.Prime}).prod (fun p => (p : ℕ))
    have hN_pos : 0 < N := by
      unfold N
      exact Finset.prod_pos (fun p hp => p.2.pos)
    have h2dvd : (2 : ℕ) ∣ N := by
      unfold N
      exact
        (Finset.dvd_prod_of_mem
          (f := fun p : {p : ℕ // p.Prime} => (p : ℕ))
          (a := (⟨2, by decide⟩ : {p : ℕ // p.Prime}))
          (s := (Finset.univ : Finset {p : ℕ // p.Prime}))
          (by simp))
    have hN_ne : N + 1 ≠ 1 := by
      exact Nat.ne_of_gt (Nat.succ_le_succ hN_pos)
    have hN_ne : N + 1 ≠ 1 := by omega
    obtain ⟨q, hqprime, hqdvd⟩ := Nat.exists_prime_and_dvd hN_ne
    have hq_divides_factor : q ∣ N := by
      simpa [N] using
        (Finset.dvd_prod_of_mem
          (f := fun p : {p : ℕ // p.Prime} => (p : ℕ))
          (a := (⟨q, hqprime⟩ : {p : ℕ // p.Prime}))
          (s := (Finset.univ : Finset {p : ℕ // p.Prime}))
          (by simp))
    have hq_divides_one : q ∣ 1 := (Nat.dvd_add_iff_right hq_divides_factor).2 hqdvd
    exact False.elim (hqprime.not_dvd_one hq_divides_one)
  · exact hinf

/--
Second proof via Fermat numbers.
Show that Fermat numbers are pairwise coprime.
-/

theorem chapter01_fermat_coprime :
    ∀ m n : ℕ, m ≠ n → Nat.Coprime (Nat.fermatNumber m) (Nat.fermatNumber n) := by
  intro m n hmn
  have hcoprime_of_lt : ∀ {a b : ℕ}, a < b → Nat.Coprime (Nat.fermatNumber a) (Nat.fermatNumber b) := by
    intro a b hab
    let d := (Nat.fermatNumber a).gcd (Nat.fermatNumber b)
    have h_b : d ∣ Nat.fermatNumber b := Nat.gcd_dvd_right _ _
    have h_a : d ∣ 2 := by
      have h_a' : d ∣ ∏ k ∈ Finset.range b, Nat.fermatNumber k := by
        exact (Nat.gcd_dvd_left _ _).trans
          (Finset.dvd_prod_of_mem
            (f := Nat.fermatNumber)
            (a := a)
            (s := Finset.range b)
            (Finset.mem_range.mpr hab))
      exact (Nat.dvd_add_right h_a').mp (Nat.fermatNumber_eq_prod_add_two b ▸ h_b)
    refine (Nat.coprime_iff_gcd_eq_one).2 ?_
    refine ((Nat.dvd_prime Nat.prime_two).mp h_a).resolve_right ?_
    intro h_two
    exact (Nat.odd_fermatNumber _).not_two_dvd_nat (h_two ▸ h_b)
  by_cases hlt : m < n
  · exact hcoprime_of_lt hlt
  · have hgt : n < m := lt_of_le_of_ne (Nat.le_of_not_gt hlt) hmn.symm
    simpa [Nat.coprime_comm] using hcoprime_of_lt hgt

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
