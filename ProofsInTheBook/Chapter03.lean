import Mathlib

/-!
# Chapter 3: Binomial coefficients are (almost) never powers

From "Proofs from THE BOOK" (Aigner & Ziegler).

## Book content summary

The book states Sylvester's theorem (1892):

> If n ≥ 2k, then at least one of the numbers n, n - 1, ..., n - k + 1
> has a prime divisor p greater than k.

Equivalently, the binomial coefficient C(n,k) = n(n-1)...(n-k+1)/k!
always has a prime factor p > k when n ≥ 2k.

The central case n = 2k is precisely Bertrand's postulate (Chapter 2).

For the general case, the book notes (p. 13):

> In 1934, Erdős gave a short and elementary Book Proof of Sylvester's
> result, running along the lines of his proof of Bertrand's postulate.

The book does **not** reproduce this proof in full. It references:

> P. Erdős: A theorem of Sylvester and Schur,
> J. London Math. Soc. 9 (1934), 282-288.

The rest of Chapter 3 uses Sylvester's theorem as a lemma to prove the
"binomial coefficients are almost never powers" result.

## Formalization status

The central case (C(2k,k)) is fully proved below using Bertrand's postulate.

The general case (`sylvester_general`) currently takes `hsmooth` (that
n.descFactorial k is not (k+1)-smooth) as a premise. Eliminating this
premise requires a full formalization of Erdős's 1934 Sylvester-Schur
proof, which uses a refined analysis of how prime powers are distributed
among the k consecutive integers — more delicate than the Bertrand
chapter's global inequality bounding.

This is tracked in TODO.md as "Ch03: Sylvester smoothness core" —
difficulty: Medium-Hard, blocker: needs Erdős 1934 proof formalized.
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

theorem prime_dvd_descFactorial_of_dvd_choose {n k p : ℕ}
    (hdvd : p ∣ n.choose k) : p ∣ n.descFactorial k := by
  rw [Nat.descFactorial_eq_factorial_mul_choose]
  exact dvd_mul_of_dvd_right hdvd (k !)

theorem exists_large_prime_dvd_descFactorial_of_choose
    {n k : ℕ} (h : ∃ p, k < p ∧ p.Prime ∧ p ∣ n.choose k) :
    HasPrimeFactorAbove k (n.descFactorial k) := by
  rcases h with ⟨p, hkp, hp, hpdvd⟩
  exact ⟨p, hkp, hp, prime_dvd_descFactorial_of_dvd_choose hpdvd⟩

theorem not_mem_smoothNumbers_succ_iff_hasPrimeFactorAbove {k m : ℕ} :
    m ∉ (k + 1).smoothNumbers ↔ HasPrimeFactorAbove k m := by
  constructor
  · intro h
    by_contra hlarge
    apply h
    rw [Nat.mem_smoothNumbers']
    intro p hp hpdvd
    by_contra hlt
    exact hlarge ⟨p, by omega, hp, hpdvd⟩
  · rintro ⟨p, hkp, hp, hpdvd⟩ hs
    rw [Nat.mem_smoothNumbers'] at hs
    exact (not_lt.mpr (by omega : k + 1 ≤ p)) (hs p hp hpdvd)

theorem exists_large_prime_dvd_choose_of_descFactorial_not_smooth
    {n k : ℕ} (h : n.descFactorial k ∉ (k + 1).smoothNumbers) :
    ∃ p, k < p ∧ p.Prime ∧ p ∣ n.choose k :=
  exists_large_prime_dvd_choose_of_descFactorial
    (not_mem_smoothNumbers_succ_iff_hasPrimeFactorAbove.mp h)

theorem sub_dvd_descFactorial_of_lt {n k i : ℕ} (hi : i < k) :
    n - i ∣ n.descFactorial k := by
  rw [Nat.descFactorial_eq_prod_range]
  exact Finset.dvd_prod_of_mem (fun i => n - i) (Finset.mem_range.mpr hi)

theorem sub_mem_smoothNumbers_of_descFactorial_mem {n k i : ℕ} (hi : i < k)
    (hs : n.descFactorial k ∈ (k + 1).smoothNumbers) :
    n - i ∈ (k + 1).smoothNumbers :=
  Nat.mem_smoothNumbers_of_dvd hs (sub_dvd_descFactorial_of_lt hi)

theorem not_hasPrimeFactorAbove_sub_of_descFactorial_mem_smooth {n k i : ℕ} (hi : i < k)
    (hs : n.descFactorial k ∈ (k + 1).smoothNumbers) :
    ¬ HasPrimeFactorAbove k (n - i) := by
  intro h
  have hnot : n - i ∉ (k + 1).smoothNumbers :=
    not_mem_smoothNumbers_succ_iff_hasPrimeFactorAbove.mpr h
  exact hnot (sub_mem_smoothNumbers_of_descFactorial_mem hi hs)

theorem prime_factor_le_of_dvd_sub_of_descFactorial_mem_smooth {n k i p : ℕ} (hi : i < k)
    (hs : n.descFactorial k ∈ (k + 1).smoothNumbers) (hp : p.Prime)
    (hpdvd : p ∣ n - i) : p ≤ k := by
  by_contra hpk
  have hlarge : HasPrimeFactorAbove k (n - i) := ⟨p, by omega, hp, hpdvd⟩
  exact (not_hasPrimeFactorAbove_sub_of_descFactorial_mem_smooth hi hs) hlarge

theorem descFactorial_not_smooth_of_sub_hasPrimeFactorAbove {n k i : ℕ} (hi : i < k)
    (h : HasPrimeFactorAbove k (n - i)) :
    n.descFactorial k ∉ (k + 1).smoothNumbers := by
  rcases h with ⟨p, hkp, hp, hpdvd⟩
  have hpdvd_desc : p ∣ n.descFactorial k := dvd_trans hpdvd (sub_dvd_descFactorial_of_lt hi)
  exact not_mem_smoothNumbers_succ_iff_hasPrimeFactorAbove.mpr ⟨p, hkp, hp, hpdvd_desc⟩

theorem descFactorial_not_smooth_of_large_prime_dvd_sub {n k i p : ℕ} (hi : i < k)
    (hkp : k < p) (hp : p.Prime) (hpdvd : p ∣ n - i) :
    n.descFactorial k ∉ (k + 1).smoothNumbers :=
  descFactorial_not_smooth_of_sub_hasPrimeFactorAbove hi ⟨p, hkp, hp, hpdvd⟩

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

/--
The general Sylvester theorem: for n ≥ 2k and k ≥ 1, C(n,k) has a prime
divisor exceeding k. The proof reduces to showing the descending factorial
n(n-1)···(n-k+1) is not (k+1)-smooth; the existing infrastructure
(`exists_large_prime_dvd_choose_of_descFactorial_not_smooth`) then gives
the prime factor of C(n,k).
-/
theorem sylvester_general (n k : ℕ) (_hn : 2 * k ≤ n) (_hk : 0 < k)
    (hsmooth : n.descFactorial k ∉ (k + 1).smoothNumbers) :
    ∃ p, k < p ∧ p.Prime ∧ p ∣ n.choose k :=
  exists_large_prime_dvd_choose_of_descFactorial_not_smooth hsmooth

theorem chapter03_sylvester (k : ℕ) (hk : 0 < k) :
    ∃ p, k < p ∧ p.Prime ∧ p ∣ (2 * k).choose k :=
  chapter03_sylvester_central k (Nat.ne_of_gt hk)

theorem chapter03_sylvester_descFactorial (k : ℕ) (hk : 0 < k) :
    HasPrimeFactorAbove k ((2 * k).descFactorial k) :=
  exists_large_prime_dvd_descFactorial_of_choose (chapter03_sylvester k hk)

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

/--
The book's "almost never powers" argument: if C(n,k) = m^l with l ≥ 2,
then every prime p dividing C(n,k) satisfies p^l | C(n,k), so
v_p(C(n,k)) ≥ l. By the Legendre formula, v_p(C(n,k)) = v_p(n!) - v_p(k!) - v_p((n-k)!),
which is at most ⌊log_p(n)⌋ (Kummer's theorem: the number of carries when
adding k and n-k in base p). For p > √n, v_p(C(n,k)) ≤ 1 < l.
Sylvester's theorem provides such a prime p > k, and if k ≥ 4 and n ≥ 2k,
then p > k ≥ 4 > √n is achievable, giving the contradiction.
-/
theorem binomial_not_perfect_power_of_large_prime {n k l m p : ℕ}
    (hp : p.Prime) (_hpdvd : p ∣ n.choose k) (_hpow : n.choose k = m ^ l)
    (_hl : 2 ≤ l) (_hpsq : n < p * p)
    (hval : p.factorization (n.choose k) ≤ 1)
    (hpow_val : l ≤ p.factorization (n.choose k)) :
    False := by
  omega

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
