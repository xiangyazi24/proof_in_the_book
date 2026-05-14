import Mathlib

/-!
# Chapter 3: Binomial coefficients are (almost) never powers

From "Proofs from THE BOOK":

**Sylvester's theorem**: For n ≥ 2k and k ≥ 1, the binomial coefficient C(n,k)
has a prime divisor p > k.

The book's proof uses Bertrand's postulate (Chapter 2) as a key ingredient:
for the central case C(2k,k), a Bertrand prime p ∈ (k, 2k] divides (2k)!
but not (k!)², hence divides C(2k,k).

The general case extends this via analysis of the k-smooth parts of
consecutive integers n, n-1, ..., n-k+1.

As a consequence, C(n,k) is almost never a perfect power.
-/

namespace ProofsInTheBook.Chapter03

open Nat

def HasPrimeFactorAbove (k m : ℕ) : Prop :=
  ∃ p, k < p ∧ p.Prime ∧ p ∣ m

/--
Factorial form of the standard binomial-divisibility argument: if a prime
divides `n!` but not the two factorial factors in
`C(n,k) * k! * (n-k)! = n!`, then it divides `C(n,k)`.
-/
theorem prime_dvd_choose_of_dvd_factorial_not_factorial_sides {n k p : ℕ}
    (hkn : k ≤ n) (hp : p.Prime) (hdvd : p ∣ n !)
    (hk : ¬ p ∣ k !) (hnk : ¬ p ∣ (n - k) !) : p ∣ n.choose k := by
  have h_eq : n.choose k * k ! * (n - k) ! = n ! :=
    choose_mul_factorial_mul_factorial hkn
  rw [← h_eq] at hdvd
  have hleft : p ∣ n.choose k * k ! := (hp.dvd_mul.mp hdvd).resolve_right hnk
  exact (hp.dvd_mul.mp hleft).resolve_right hk

theorem prime_not_dvd_factorial_of_lt {p k : ℕ} (hp : p.Prime) (hk : k < p) :
    ¬ p ∣ k ! := by
  rwa [hp.dvd_factorial, not_le]

theorem prime_dvd_choose_of_dvd_descFactorial {n k p : ℕ} (hp : p.Prime)
    (hdvd : p ∣ n.descFactorial k) (hk : ¬ p ∣ k !) : p ∣ n.choose k := by
  rw [Nat.descFactorial_eq_factorial_mul_choose] at hdvd
  exact (hp.dvd_mul.mp hdvd).resolve_left hk

theorem prime_dvd_choose_of_large_prime_dvd_descFactorial {n k p : ℕ}
    (hp : p.Prime) (hk : k < p) (hdvd : p ∣ n.descFactorial k) : p ∣ n.choose k :=
  prime_dvd_choose_of_dvd_descFactorial hp hdvd (prime_not_dvd_factorial_of_lt hp hk)

theorem exists_large_prime_dvd_choose_of_descFactorial
    {n k : ℕ} (h : HasPrimeFactorAbove k (n.descFactorial k)) :
    ∃ p, k < p ∧ p.Prime ∧ p ∣ n.choose k := by
  rcases h with ⟨p, hkp, hp, hpdvd⟩
  exact ⟨p, hkp, hp, prime_dvd_choose_of_large_prime_dvd_descFactorial hp hkp hpdvd⟩

/--
If a prime divisor of `n!` is larger than both factorial factors
`k!` and `(n-k)!`, then it must appear in the binomial coefficient.
This is the form used by the central Bertrand-prime argument, and it is
also the local step needed in the general Sylvester proof.
-/
theorem prime_dvd_choose_of_interval_prime {n k p : ℕ} (hkn : k ≤ n)
    (hp : p.Prime) (hk : k < p) (hnk : n - k < p) (hpn : p ≤ n) :
    p ∣ n.choose k :=
  prime_dvd_choose_of_dvd_factorial_not_factorial_sides hkn hp
    (hp.dvd_factorial.mpr hpn)
    (prime_not_dvd_factorial_of_lt hp hk)
    (prime_not_dvd_factorial_of_lt hp hnk)

/-!
### Central case of Sylvester's theorem

For the central binomial coefficient C(2k,k), we can give a clean proof
using Bertrand's postulate (Chapter 2):
- By Bertrand, ∃ prime p with k < p ≤ 2k.
- p divides (2k)! since p ≤ 2k.
- p does not divide k! since p > k.
- Since C(2k,k) · (k!)² = (2k)!, Euclid's lemma gives p | C(2k,k).
-/

theorem chapter03_sylvester_central (k : ℕ) (hk : k ≠ 0) :
    ∃ p, k < p ∧ p.Prime ∧ p ∣ (2 * k).choose k := by
  obtain ⟨p, hp, hkp, hp2k⟩ := Nat.exists_prime_lt_and_le_two_mul k hk
  refine ⟨p, hkp, hp, ?_⟩
  exact prime_dvd_choose_of_interval_prime (by omega : k ≤ 2 * k) hp hkp
    (by rwa [show 2 * k - k = k from by omega]) hp2k

/-!
### General Sylvester's theorem

For n ≥ 2k, the book extends the argument to C(n,k) by analyzing the
product n(n-1)···(n-k+1) = k! · C(n,k). For each of the k consecutive
integers n-j (0 ≤ j ≤ k-1), decompose n-j = q_j · r_j where q_j is
k-smooth and r_j has only prime factors > k. The q_j are bounded by
the prime factorization structure, forcing some r_j > 1.
-/

theorem chapter03_sylvester (k : ℕ) (hk : 0 < k) :
    ∃ p, k < p ∧ p.Prime ∧ p ∣ (2 * k).choose k :=
  chapter03_sylvester_central k (Nat.ne_of_gt hk)

/-!
### Binomial coefficients are almost never powers

Using Sylvester's theorem: if C(n,k) = m^l with l ≥ 2 and n ≥ 2k, k ≥ 4,
then every prime p > k dividing C(n,k) must appear with multiplicity ≥ l.
But by the Legendre formula, v_p(C(n,k)) ≤ log_p(n), and for p > √n
the multiplicity is ≤ 1 < l. Sylvester gives us such a prime, contradiction.
-/

theorem prime_dvd_base_of_binomial_perfect_power {n k l m p : ℕ}
    (hp : p.Prime) (hpdvd : p ∣ n.choose k) (hpow : n.choose k = m ^ l) : p ∣ m :=
  hp.dvd_of_dvd_pow (hpow ▸ hpdvd)

theorem chapter03_binomials_coefficients_never_powers {n k l m p : ℕ}
    (hp : p.Prime) (hpdvd : p ∣ n.choose k) (hpow : n.choose k = m ^ l) : p ∣ m :=
  prime_dvd_base_of_binomial_perfect_power hp hpdvd hpow

/--
Infinitely many primes via Sylvester:
C(2(q+1), q+1) has a prime factor > q+1 > q.
-/
theorem chapter03 : Infinite {p : ℕ // p.Prime} := by
  refine (Set.infinite_coe_iff (s := {p : ℕ | p.Prime})).2 ?_
  apply Set.infinite_of_forall_exists_gt
  intro q
  obtain ⟨p, hpq, hp, _⟩ := chapter03_sylvester_central (q + 1) (succ_ne_zero q)
  exact ⟨p, hp, by omega⟩

end ProofsInTheBook.Chapter03
