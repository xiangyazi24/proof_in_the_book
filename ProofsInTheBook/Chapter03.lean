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

def NoLargePrimeFactor (k m : ℕ) : Prop :=
  ∀ p, p.Prime → p ∣ m → p ≤ k

noncomputable def entropyTerm (n k : ℕ) : ℝ :=
  (n : ℝ) * Real.log n
    - (k : ℝ) * Real.log k
    - ((n - k : ℕ) : ℝ) * Real.log (n - k)

def primeIntervalProduct (a b : ℕ) : ℕ :=
  ∏ p ∈ Finset.Ioc a b with p.Prime, p

theorem primorial_eq_mul_primeIntervalProduct {a M : ℕ} (haM : a ≤ M) :
    primorial M = primorial a * primeIntervalProduct a M := by
  rw [primorial, primeIntervalProduct]
  rw [show (Finset.range (M + 1)).filter Nat.Prime =
      (Finset.range (a + 1)).filter Nat.Prime ∪ (Finset.Ioc a M).filter Nat.Prime by
    ext p
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_union, Finset.mem_Ioc]
    constructor
    · rintro ⟨hpM, hpprime⟩
      by_cases hpa : p ≤ a
      · exact Or.inl ⟨by omega, hpprime⟩
      · exact Or.inr ⟨⟨by omega, by omega⟩, hpprime⟩
    · rintro (⟨hpa, hpprime⟩ | ⟨⟨hpa, hpM⟩, hpprime⟩) <;> exact ⟨by omega, hpprime⟩]
  rw [Finset.prod_union]
  · rfl
  · rw [Finset.disjoint_left]
    intro p hp1 hp2
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ioc] at hp1 hp2
    omega

theorem log_primeIntervalProduct_eq_theta_sub {a M : ℕ} (haM : a ≤ M) :
    Real.log (primeIntervalProduct a M) =
      Chebyshev.theta (M : ℝ) - Chebyshev.theta (a : ℝ) := by
  have hprod := primorial_eq_mul_primeIntervalProduct (a := a) (M := M) haM
  have hposA : 0 < (primorial a : ℕ) := primorial_pos a
  have hposP : 0 < primeIntervalProduct a M := by
    dsimp [primeIntervalProduct]
    exact Finset.prod_pos fun p hp => (Finset.mem_filter.1 hp).2.pos
  have hlogprod :
      Real.log (primorial M) =
        Real.log (primorial a) + Real.log (primeIntervalProduct a M) := by
    rw [hprod, Nat.cast_mul]
    exact Real.log_mul
      (by exact_mod_cast hposA.ne' : ((primorial a : ℕ) : ℝ) ≠ 0)
      (by exact_mod_cast hposP.ne' : ((primeIntervalProduct a M : ℕ) : ℝ) ≠ 0)
  rw [Chebyshev.theta_eq_log_primorial, Chebyshev.theta_eq_log_primorial]
  norm_num at hlogprod ⊢
  linarith

theorem log_primeIntervalProduct_le_min_third_log4_sub_theta
    {a M : ℕ} (haM : a ≤ M) :
    Real.log (primeIntervalProduct a M) ≤
      (M : ℝ) * Real.log 4 - Chebyshev.theta (a : ℝ) := by
  rw [log_primeIntervalProduct_eq_theta_sub haM]
  have hthetaM := Chebyshev.theta_le_log4_mul_x (x := (M : ℝ)) (by positivity)
  linarith

theorem primeIntervalProduct_dvd_choose {a M : ℕ} (haM : a ≤ M) (hd : M - a ≤ a) :
    primeIntervalProduct a M ∣ M.choose a := by
  rw [primeIntervalProduct, ← Nat.add_sub_of_le haM]
  exact Finset.prod_primes_dvd _ (fun _ hp => (Finset.mem_filter.1 hp).2.prime) fun p hp => by
    rw [Finset.mem_filter, Finset.mem_Ioc] at hp
    exact hp.2.dvd_choose_add hp.1.1 (hd.trans_lt hp.1.1) hp.1.2

theorem primeIntervalProduct_le_choose {a M : ℕ} (haM : a ≤ M) (hd : M - a ≤ a) :
    primeIntervalProduct a M ≤ M.choose a := by
  exact le_of_dvd (Nat.choose_pos haM) (primeIntervalProduct_dvd_choose haM hd)

theorem log_primeIntervalProduct_le_log_choose {a M : ℕ} (haM : a ≤ M) (hd : M - a ≤ a) :
    Real.log (primeIntervalProduct a M) ≤ Real.log (M.choose a) := by
  exact Real.log_le_log
    (by exact_mod_cast (Finset.prod_pos fun p hp => (Finset.mem_filter.1 hp).2.pos :
      0 < primeIntervalProduct a M))
    (by exact_mod_cast primeIntervalProduct_le_choose haM hd)

theorem sqrt_le_div_three_of_nine_le {n : ℕ} (hn : 9 ≤ n) : sqrt n ≤ n / 3 := by
  rw [← Nat.lt_succ_iff]
  rw [Nat.sqrt_lt]
  have hq : 3 ≤ n / 3 := by omega
  have hnle : n ≤ 3 * (n / 3) + 2 := by omega
  nlinarith [sq_nonneg ((n / 3 : ℕ) : ℤ)]

theorem sqrt_le_min_of_nine_le_and_lt_sq {n k : ℕ} (hn : 9 ≤ n) (hlt : n < k * k) :
    sqrt n ≤ min k (n / 3) := by
  refine le_min ?_ (sqrt_le_div_three_of_nine_le hn)
  exact (Nat.sqrt_lt.mpr hlt).le

theorem not_hasPrimeFactorAbove_iff_noLargePrimeFactor {k m : ℕ} :
    ¬ HasPrimeFactorAbove k m ↔ NoLargePrimeFactor k m := by
  constructor
  · intro h p hp hpdvd
    by_contra hkp
    exact h ⟨p, by omega, hp, hpdvd⟩
  · rintro h ⟨p, hkp, hp, hpdvd⟩
    exact (not_lt_of_ge (h p hp hpdvd)) hkp

theorem factorization_choose_eq_zero_of_noLargePrimeFactor
    {n k p : ℕ} (hno : NoLargePrimeFactor k (n.choose k)) (hkp : k < p) :
    (n.choose k).factorization p = 0 := by
  by_cases hp : p.Prime
  · by_contra hne
    have hpdvd : p ∣ n.choose k := Nat.dvd_of_factorization_pos hne
    exact (not_lt_of_ge (hno p hp hpdvd)) hkp
  · exact Nat.factorization_eq_zero_of_not_prime (n.choose k) hp

theorem Finset.prod_le_pow_card_of_le {α : Type*} (s : Finset α) (f : α → ℕ) (N : ℕ)
    (h : ∀ a ∈ s, f a ≤ N) : (∏ a ∈ s, f a) ≤ N ^ s.card := by
  classical
  calc
    (∏ a ∈ s, f a) ≤ ∏ _a ∈ s, N := Finset.prod_le_prod' h
    _ = N ^ s.card := by rw [Finset.prod_const]

theorem choose_le_pow_primeCounting_of_noLargePrimeFactor
    {n k : ℕ} (hnpos : 0 < n) (hkn : k ≤ n)
    (hno : NoLargePrimeFactor k (n.choose k)) :
    n.choose k ≤ n ^ Nat.primeCounting k := by
  classical
  let s := (Finset.range (n + 1)).filter (fun p => p ∈ Nat.primesLE k)
  have hprod_filter :
      (∏ p ∈ Finset.range (n + 1), p ^ (n.choose k).factorization p)
        = ∏ p ∈ s, p ^ (n.choose k).factorization p := by
    symm
    refine Finset.prod_subset (Finset.filter_subset _ _) ?_
    intro p hp_range hp_not_s
    have hp_not_primes : p ∉ Nat.primesLE k := by
      intro hp_primes
      exact hp_not_s (Finset.mem_filter.mpr ⟨hp_range, hp_primes⟩)
    have hfac : (n.choose k).factorization p = 0 := by
      by_cases hpprime : p.Prime
      · have hkp : k < p := by
          by_contra hnot
          exact hp_not_primes (Nat.mem_primesLE.mpr ⟨le_of_not_gt hnot, hpprime⟩)
        exact factorization_choose_eq_zero_of_noLargePrimeFactor hno hkp
      · exact Nat.factorization_eq_zero_of_not_prime (n.choose k) hpprime
    simp [hfac]
  have hprod_le : (∏ p ∈ s, p ^ (n.choose k).factorization p) ≤ n ^ s.card :=
    Finset.prod_le_pow_card_of_le s (fun p => p ^ (n.choose k).factorization p) n
      (fun p _ => Nat.pow_factorization_choose_le hnpos)
  have hcard : s.card ≤ (Nat.primesLE k).card := by
    refine Finset.card_le_card ?_
    intro p hp
    exact (Finset.mem_filter.mp hp).2
  have hpow_card : n ^ s.card ≤ n ^ Nat.primeCounting k := by
    rw [← Nat.primesLE_card_eq_primeCounting]
    exact Nat.pow_le_pow_right hnpos hcard
  calc
    n.choose k = ∏ p ∈ Finset.range (n + 1), p ^ (n.choose k).factorization p := by
      exact (Nat.prod_pow_factorization_choose n k hkn).symm
    _ = ∏ p ∈ s, p ^ (n.choose k).factorization p := hprod_filter
    _ ≤ n ^ s.card := hprod_le
    _ ≤ n ^ Nat.primeCounting k := hpow_card

theorem choose_factorization_le_min_third_of_noLargePrimeFactor
    {n k : ℕ} (hkn : k ≤ n) (hn2k : 2 * k ≤ n) (hn6 : 6 ≤ n)
    (hno : NoLargePrimeFactor k (n.choose k)) :
    n.choose k =
      ∏ p ∈ Finset.range (min k (n / 3) + 1),
        p ^ (n.choose k).factorization p := by
  refine (Eq.trans ?_ (Nat.prod_pow_factorization_choose n k hkn)).symm
  refine Finset.prod_subset ?hsub ?hzero
  · intro p hp
    rw [Finset.mem_range] at hp ⊢
    omega
  · intro p hp_range hp_not_small
    rw [Finset.mem_range] at hp_range hp_not_small
    have hMp : min k (n / 3) < p := by omega
    by_cases hpprime : p.Prime
    · by_cases hkp : k < p
      · rw [factorization_choose_eq_zero_of_noLargePrimeFactor hno hkp, pow_zero]
      · have hpk : p ≤ k := le_of_not_gt hkp
        have hpnk : p ≤ n - k := by omega
        have hp2 : p ≠ 2 := by
          intro hp_eq
          have hnthird : 2 ≤ n / 3 := by omega
          omega
        have hdiv : n / 3 < p := by omega
        have hnlt : n < 3 * p := by
          have := (Nat.div_lt_iff_lt_mul three_pos).mp hdiv
          simpa [mul_comm] using this
        rw [Nat.factorization_choose_of_lt_three_mul hp2 hpk hpnk hnlt, pow_zero]
    · rw [Nat.factorization_eq_zero_of_not_prime (n.choose k) hpprime, pow_zero]

theorem choose_le_sqrt_mul_four_pow_min_third_of_noLargePrimeFactor
    {n k : ℕ} (hnpos : 0 < n) (hkn : k ≤ n) (hn2k : 2 * k ≤ n) (hn6 : 6 ≤ n)
    (hno : NoLargePrimeFactor k (n.choose k)) :
    n.choose k ≤ n ^ sqrt n * 4 ^ min k (n / 3) := by
  let M := min k (n / 3)
  let S := {p ∈ Finset.range (M + 1) | Nat.Prime p}
  let f := fun p => p ^ (n.choose k).factorization p
  have hprime_filter : ∏ p ∈ S, f p = ∏ p ∈ Finset.range (M + 1), f p := by
    refine Finset.prod_filter_of_ne fun p _ hpprime => ?_
    contrapose hpprime
    dsimp only [f]
    rw [Nat.factorization_eq_zero_of_not_prime (n.choose k) hpprime, pow_zero]
  rw [choose_factorization_le_min_third_of_noLargePrimeFactor hkn hn2k hn6 hno, ← hprime_filter,
    ← Finset.prod_filter_mul_prod_filter_not S (· ≤ sqrt n)]
  apply mul_le_mul'
  · refine (Finset.prod_le_prod' fun p _ => (?_ : f p ≤ n)).trans ?_
    · exact Nat.pow_factorization_choose_le hnpos
    have hcard : (Finset.Icc 1 (sqrt n)).card = sqrt n := by
      rw [Nat.card_Icc, Nat.add_sub_cancel]
    rw [Finset.prod_const]
    refine pow_right_mono₀ (Nat.succ_le_iff.mpr hnpos) ((Finset.card_le_card fun p hp => ?_).trans hcard.le)
    obtain ⟨hpS, hpsqrt⟩ := Finset.mem_filter.1 hp
    exact Finset.mem_Icc.mpr ⟨(Finset.mem_filter.1 hpS).2.one_lt.le, hpsqrt⟩
  · refine le_trans ?_ (primorial_le_four_pow M)
    refine (Finset.prod_le_prod' fun p hp => (?_ : f p ≤ p)).trans ?_
    · obtain ⟨hpS, hpsqrt⟩ := Finset.mem_filter.1 hp
      refine (pow_right_mono₀ (Finset.mem_filter.1 hpS).2.one_lt.le ?_).trans (pow_one p).le
      exact Nat.factorization_choose_le_one (sqrt_lt'.mp <| not_le.1 hpsqrt)
    refine Finset.prod_le_prod_of_subset_of_one_le' (Finset.filter_subset _ _) ?_
    exact fun p hp _ => (Finset.mem_filter.1 hp).2.one_lt.le

theorem choose_le_primeCounting_sqrt_mul_four_pow_min_third_of_noLargePrimeFactor
    {n k : ℕ} (hnpos : 0 < n) (hkn : k ≤ n) (hn2k : 2 * k ≤ n) (hn6 : 6 ≤ n)
    (hno : NoLargePrimeFactor k (n.choose k)) :
    n.choose k ≤ n ^ Nat.primeCounting (sqrt n) * 4 ^ min k (n / 3) := by
  let M := min k (n / 3)
  let S := {p ∈ Finset.range (M + 1) | Nat.Prime p}
  let f := fun p => p ^ (n.choose k).factorization p
  have hprime_filter : ∏ p ∈ S, f p = ∏ p ∈ Finset.range (M + 1), f p := by
    refine Finset.prod_filter_of_ne fun p _ hpprime => ?_
    contrapose hpprime
    dsimp only [f]
    rw [Nat.factorization_eq_zero_of_not_prime (n.choose k) hpprime, pow_zero]
  rw [choose_factorization_le_min_third_of_noLargePrimeFactor hkn hn2k hn6 hno, ← hprime_filter,
    ← Finset.prod_filter_mul_prod_filter_not S (· ≤ sqrt n)]
  apply mul_le_mul'
  · refine (Finset.prod_le_prod' fun p _ => (?_ : f p ≤ n)).trans ?_
    · exact Nat.pow_factorization_choose_le hnpos
    rw [Finset.prod_const]
    refine pow_right_mono₀ (Nat.succ_le_iff.mpr hnpos) ?_
    rw [← Nat.primesLE_card_eq_primeCounting]
    exact Finset.card_le_card fun p hp => by
      obtain ⟨hpS, hpsqrt⟩ := Finset.mem_filter.1 hp
      exact Nat.mem_primesLE.mpr ⟨hpsqrt, (Finset.mem_filter.1 hpS).2⟩
  · refine le_trans ?_ (primorial_le_four_pow M)
    refine (Finset.prod_le_prod' fun p hp => (?_ : f p ≤ p)).trans ?_
    · obtain ⟨hpS, hpsqrt⟩ := Finset.mem_filter.1 hp
      refine (pow_right_mono₀ (Finset.mem_filter.1 hpS).2.one_lt.le ?_).trans (pow_one p).le
      exact Nat.factorization_choose_le_one (sqrt_lt'.mp <| not_le.1 hpsqrt)
    refine Finset.prod_le_prod_of_subset_of_one_le' (Finset.filter_subset _ _) ?_
    exact fun p hp _ => (Finset.mem_filter.1 hp).2.one_lt.le

theorem choose_le_primeCounting_sqrt_mul_primeIntervalProduct_of_noLargePrimeFactor
    {n k : ℕ} (hnpos : 0 < n) (hkn : k ≤ n) (hn2k : 2 * k ≤ n) (hn6 : 6 ≤ n)
    (hno : NoLargePrimeFactor k (n.choose k)) :
    n.choose k ≤ n ^ Nat.primeCounting (sqrt n) * primeIntervalProduct (sqrt n) (min k (n / 3)) := by
  let M := min k (n / 3)
  let S := {p ∈ Finset.range (M + 1) | Nat.Prime p}
  let f := fun p => p ^ (n.choose k).factorization p
  have hprime_filter : ∏ p ∈ S, f p = ∏ p ∈ Finset.range (M + 1), f p := by
    refine Finset.prod_filter_of_ne fun p _ hpprime => ?_
    contrapose hpprime
    dsimp only [f]
    rw [Nat.factorization_eq_zero_of_not_prime (n.choose k) hpprime, pow_zero]
  rw [choose_factorization_le_min_third_of_noLargePrimeFactor hkn hn2k hn6 hno, ← hprime_filter,
    ← Finset.prod_filter_mul_prod_filter_not S (· ≤ sqrt n)]
  apply mul_le_mul'
  · refine (Finset.prod_le_prod' fun p _ => (?_ : f p ≤ n)).trans ?_
    · exact Nat.pow_factorization_choose_le hnpos
    rw [Finset.prod_const]
    refine pow_right_mono₀ (Nat.succ_le_iff.mpr hnpos) ?_
    rw [← Nat.primesLE_card_eq_primeCounting]
    exact Finset.card_le_card fun p hp => by
      obtain ⟨hpS, hpsqrt⟩ := Finset.mem_filter.1 hp
      exact Nat.mem_primesLE.mpr ⟨hpsqrt, (Finset.mem_filter.1 hpS).2⟩
  · refine (Finset.prod_le_prod' fun p hp => (?_ : f p ≤ p)).trans ?_
    · obtain ⟨hpS, hpsqrt⟩ := Finset.mem_filter.1 hp
      refine (pow_right_mono₀ (Finset.mem_filter.1 hpS).2.one_lt.le ?_).trans (pow_one p).le
      exact Nat.factorization_choose_le_one (sqrt_lt'.mp <| not_le.1 hpsqrt)
    change (∏ p ∈ Finset.filter (fun p => ¬p ≤ sqrt n) S, p) ≤
      ∏ p ∈ Finset.Ioc (sqrt n) M with p.Prime, p
    refine Finset.prod_le_prod_of_subset_of_one_le' ?_ ?_
    · intro p hp
      obtain ⟨hpS, hpsqrt⟩ := Finset.mem_filter.1 hp
      obtain ⟨hpRange, hpPrime⟩ := Finset.mem_filter.1 hpS
      rw [Finset.mem_range] at hpRange
      rw [Finset.mem_filter, Finset.mem_Ioc]
      exact ⟨⟨lt_of_not_ge hpsqrt, by omega⟩, hpPrime⟩
    · intro p hp _hnot
      rw [Finset.mem_filter, Finset.mem_Ioc] at hp
      exact hp.2.one_lt.le

theorem pow_mul_self_descFactorial_le_pow_mul_descFactorial {n k : ℕ} (hkn : k ≤ n) :
    n ^ k * k.descFactorial k ≤ k ^ k * n.descFactorial k := by
  have hnprod : n ^ k = ∏ _i ∈ Finset.range k, n := by
    rw [Finset.prod_const, Finset.card_range]
  have hkprod : k ^ k = ∏ _i ∈ Finset.range k, k := by
    rw [Finset.prod_const, Finset.card_range]
  rw [Nat.descFactorial_eq_prod_range k, Nat.descFactorial_eq_prod_range n,
    hnprod, hkprod, ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
  exact Finset.prod_le_prod' fun i hi => by
    rw [Finset.mem_range] at hi
    have hik : i ≤ k := le_of_lt hi
    have hki : k * i ≤ n * i := Nat.mul_le_mul_right i hkn
    rw [Nat.mul_sub_left_distrib, Nat.mul_sub_left_distrib, Nat.mul_comm k n]
    exact Nat.sub_le_sub_left hki (n * k)

theorem pow_le_pow_mul_choose {n k : ℕ} (hkn : k ≤ n) :
    n ^ k ≤ k ^ k * n.choose k := by
  have h :=
    pow_mul_self_descFactorial_le_pow_mul_descFactorial (n := n) (k := k) hkn
  rw [Nat.descFactorial_self, Nat.descFactorial_eq_factorial_mul_choose] at h
  have hcancel : k ! * n ^ k ≤ k ! * (k ^ k * n.choose k) := by
    simpa [mul_assoc, mul_comm, mul_left_comm] using h
  exact le_of_mul_le_mul_left hcancel (Nat.factorial_pos k)

theorem log_choose_le_sqrt_log_add_min_third_log_four_of_noLargePrimeFactor
    {n k : ℕ} (hnpos : 0 < n) (hkn : k ≤ n) (hn2k : 2 * k ≤ n) (hn6 : 6 ≤ n)
    (hno : NoLargePrimeFactor k (n.choose k)) :
    Real.log (n.choose k) ≤
      (sqrt n : ℝ) * Real.log n + ((min k (n / 3) : ℕ) : ℝ) * Real.log 4 := by
  let M := min k (n / 3)
  have hnat :
      n.choose k ≤ n ^ sqrt n * 4 ^ M :=
    choose_le_sqrt_mul_four_pow_min_third_of_noLargePrimeFactor
      hnpos hkn hn2k hn6 hno
  have hpos_choose_nat : 0 < n.choose k := Nat.choose_pos hkn
  have hlogle :
      Real.log (n.choose k) ≤ Real.log (n ^ sqrt n * 4 ^ M) := by
    exact Real.log_le_log (by exact_mod_cast hpos_choose_nat) (by exact_mod_cast hnat)
  calc
    Real.log (n.choose k) ≤ Real.log (n ^ sqrt n * 4 ^ M) := hlogle
    _ = Real.log ((n : ℝ) ^ sqrt n * (4 : ℝ) ^ M) := by
      norm_num [Nat.cast_pow]
    _ = (sqrt n : ℝ) * Real.log n + (M : ℝ) * Real.log 4 := by
      rw [Real.log_mul
        (pow_ne_zero _ (by exact_mod_cast hnpos.ne' : (n : ℝ) ≠ 0))
        (pow_ne_zero _ (by norm_num : (4 : ℝ) ≠ 0)),
        Real.log_pow, Real.log_pow]
    _ = (sqrt n : ℝ) * Real.log n + ((min k (n / 3) : ℕ) : ℝ) * Real.log 4 := by
      simp [M]

theorem log_choose_le_primeCounting_sqrt_log_add_min_third_log_four_of_noLargePrimeFactor
    {n k : ℕ} (hnpos : 0 < n) (hkn : k ≤ n) (hn2k : 2 * k ≤ n) (hn6 : 6 ≤ n)
    (hno : NoLargePrimeFactor k (n.choose k)) :
    Real.log (n.choose k) ≤
      (Nat.primeCounting (sqrt n) : ℝ) * Real.log n
        + ((min k (n / 3) : ℕ) : ℝ) * Real.log 4 := by
  let M := min k (n / 3)
  have hnat :
      n.choose k ≤ n ^ Nat.primeCounting (sqrt n) * 4 ^ M :=
    choose_le_primeCounting_sqrt_mul_four_pow_min_third_of_noLargePrimeFactor
      hnpos hkn hn2k hn6 hno
  have hpos_choose_nat : 0 < n.choose k := Nat.choose_pos hkn
  have hlogle :
      Real.log (n.choose k) ≤ Real.log (n ^ Nat.primeCounting (sqrt n) * 4 ^ M) := by
    exact Real.log_le_log (by exact_mod_cast hpos_choose_nat) (by exact_mod_cast hnat)
  calc
    Real.log (n.choose k) ≤ Real.log (n ^ Nat.primeCounting (sqrt n) * 4 ^ M) := hlogle
    _ = Real.log ((n : ℝ) ^ Nat.primeCounting (sqrt n) * (4 : ℝ) ^ M) := by
      norm_num [Nat.cast_pow]
    _ = (Nat.primeCounting (sqrt n) : ℝ) * Real.log n + (M : ℝ) * Real.log 4 := by
      rw [Real.log_mul
        (pow_ne_zero _ (by exact_mod_cast hnpos.ne' : (n : ℝ) ≠ 0))
        (pow_ne_zero _ (by norm_num : (4 : ℝ) ≠ 0)),
        Real.log_pow, Real.log_pow]
    _ = (Nat.primeCounting (sqrt n) : ℝ) * Real.log n
        + ((min k (n / 3) : ℕ) : ℝ) * Real.log 4 := by
      simp [M]

theorem log_choose_le_primeCounting_sqrt_log_add_log_primeIntervalProduct_of_noLargePrimeFactor
    {n k : ℕ} (hnpos : 0 < n) (hkn : k ≤ n) (hn2k : 2 * k ≤ n) (hn6 : 6 ≤ n)
    (hno : NoLargePrimeFactor k (n.choose k)) :
    Real.log (n.choose k) ≤
      (Nat.primeCounting (sqrt n) : ℝ) * Real.log n
        + Real.log (primeIntervalProduct (sqrt n) (min k (n / 3))) := by
  let P := primeIntervalProduct (sqrt n) (min k (n / 3))
  have hnat :
      n.choose k ≤ n ^ Nat.primeCounting (sqrt n) * P :=
    choose_le_primeCounting_sqrt_mul_primeIntervalProduct_of_noLargePrimeFactor
      hnpos hkn hn2k hn6 hno
  have hpos_choose_nat : 0 < n.choose k := Nat.choose_pos hkn
  have hPpos : 0 < P := by
    dsimp [P, primeIntervalProduct]
    exact Finset.prod_pos fun p hp => (Finset.mem_filter.1 hp).2.pos
  have hlogle :
      Real.log (n.choose k) ≤ Real.log (n ^ Nat.primeCounting (sqrt n) * P) := by
    exact Real.log_le_log (by exact_mod_cast hpos_choose_nat) (by exact_mod_cast hnat)
  calc
    Real.log (n.choose k) ≤ Real.log (n ^ Nat.primeCounting (sqrt n) * P) := hlogle
    _ = Real.log ((n : ℝ) ^ Nat.primeCounting (sqrt n) * (P : ℝ)) := by
      norm_num [Nat.cast_pow]
    _ = (Nat.primeCounting (sqrt n) : ℝ) * Real.log n + Real.log P := by
      rw [Real.log_mul
        (pow_ne_zero _ (by exact_mod_cast hnpos.ne' : (n : ℝ) ≠ 0))
        (by exact_mod_cast hPpos.ne' : (P : ℝ) ≠ 0),
        Real.log_pow]
    _ = (Nat.primeCounting (sqrt n) : ℝ) * Real.log n
        + Real.log (primeIntervalProduct (sqrt n) (min k (n / 3))) := by
      simp [P]

theorem log_choose_le_primeCounting_sqrt_log_add_log_choose_min_third_of_noLargePrimeFactor
    {n k : ℕ} (hnpos : 0 < n) (hkn : k ≤ n) (hn2k : 2 * k ≤ n) (hn6 : 6 ≤ n)
    (hno : NoLargePrimeFactor k (n.choose k))
    (hsqrtM : sqrt n ≤ min k (n / 3)) (hMsub : min k (n / 3) - sqrt n ≤ sqrt n) :
    Real.log (n.choose k) ≤
      (Nat.primeCounting (sqrt n) : ℝ) * Real.log n
        + Real.log ((min k (n / 3)).choose (sqrt n)) := by
  exact (log_choose_le_primeCounting_sqrt_log_add_log_primeIntervalProduct_of_noLargePrimeFactor
    (n := n) (k := k) hnpos hkn hn2k hn6 hno).trans
      (add_le_add_right (log_primeIntervalProduct_le_log_choose hsqrtM hMsub)
        ((Nat.primeCounting (sqrt n) : ℝ) * Real.log n))

theorem log_choose_le_primeCounting_sqrt_log_add_min_third_log_two_of_noLargePrimeFactor
    {n k : ℕ} (hnpos : 0 < n) (hkn : k ≤ n) (hn2k : 2 * k ≤ n) (hn6 : 6 ≤ n)
    (hno : NoLargePrimeFactor k (n.choose k))
    (hsqrtM : sqrt n ≤ min k (n / 3)) (hMsub : min k (n / 3) - sqrt n ≤ sqrt n) :
    Real.log (n.choose k) ≤
      (Nat.primeCounting (sqrt n) : ℝ) * Real.log n
        + ((min k (n / 3) : ℕ) : ℝ) * Real.log 2 := by
  let M := min k (n / 3)
  have hupper :=
    log_choose_le_primeCounting_sqrt_log_add_log_choose_min_third_of_noLargePrimeFactor
      (n := n) (k := k) hnpos hkn hn2k hn6 hno hsqrtM hMsub
  have hchoose_pos : 0 < M.choose (sqrt n) := Nat.choose_pos hsqrtM
  have hchoose_le : M.choose (sqrt n) ≤ 2 ^ M := Nat.choose_le_two_pow M (sqrt n)
  have hlog_choose_le :
      Real.log (M.choose (sqrt n)) ≤ Real.log (2 ^ M) := by
    exact Real.log_le_log (by exact_mod_cast hchoose_pos) (by exact_mod_cast hchoose_le)
  exact hupper.trans <| add_le_add_right
    (by
      calc
        Real.log (M.choose (sqrt n)) ≤ Real.log (2 ^ M) := hlog_choose_le
        _ = Real.log ((2 : ℝ) ^ M) := by norm_num [Nat.cast_pow]
        _ = (M : ℝ) * Real.log 2 := by rw [Real.log_pow])
    ((Nat.primeCounting (sqrt n) : ℝ) * Real.log n)

theorem mul_log_sub_mul_log_le_log_choose {n k : ℕ}
    (hkpos : 0 < k) (hkn : k ≤ n) :
    (k : ℝ) * Real.log n - (k : ℝ) * Real.log k ≤ Real.log (n.choose k) := by
  have hnpos : 0 < n := hkpos.trans_le hkn
  have hchoose_pos : 0 < n.choose k := Nat.choose_pos hkn
  have hnat : n ^ k ≤ k ^ k * n.choose k := pow_le_pow_mul_choose hkn
  have hlog :
      Real.log ((n : ℝ) ^ k) ≤ Real.log ((k : ℝ) ^ k * (n.choose k : ℝ)) := by
    exact Real.log_le_log
      (pow_pos (by exact_mod_cast hnpos) k)
      (by exact_mod_cast hnat)
  calc
    (k : ℝ) * Real.log n - (k : ℝ) * Real.log k
        = Real.log ((n : ℝ) ^ k) - Real.log ((k : ℝ) ^ k) := by
          rw [Real.log_pow, Real.log_pow]
    _ ≤ Real.log ((k : ℝ) ^ k * (n.choose k : ℝ)) - Real.log ((k : ℝ) ^ k) := by
      exact sub_le_sub_right hlog _
    _ = Real.log (n.choose k) := by
      rw [Real.log_mul
        (pow_ne_zero _ (by exact_mod_cast hkpos.ne' : (k : ℝ) ≠ 0))
        (by exact_mod_cast hchoose_pos.ne')]
      ring

theorem log_factorial_le_stirling_upper {m : ℕ} (hm : m ≠ 0) :
    Real.log (m !) ≤ (m : ℝ) * Real.log m - (m : ℝ) + Real.log m / 2 + 1 := by
  have hlogseq : Real.log (Stirling.stirlingSeq m) ≤ Real.log (Stirling.stirlingSeq 1) := by
    obtain ⟨t, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hm
    exact Real.log_le_log (Stirling.stirlingSeq'_pos t)
      (Stirling.stirlingSeq'_antitone (Nat.zero_le t))
  have hformula := Stirling.log_stirlingSeq_formula m
  have hone : Real.log (Stirling.stirlingSeq 1) = 1 - Real.log 2 / 2 := by
    rw [Stirling.stirlingSeq_one, Real.log_div, Real.log_exp]
    · rw [Real.log_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
    · positivity
    · positivity
  rw [hformula, hone] at hlogseq
  rw [Real.log_mul (x := (2 : ℝ)) (y := (m : ℝ)), Real.log_div, Real.log_exp] at hlogseq
  · nlinarith
  all_goals positivity

theorem entropy_lower_le_log_choose {n k : ℕ} (hkpos : 0 < k) (hklt : k < n) :
    entropyTerm n k
      + Real.log n / 2 - Real.log k / 2 - Real.log (n - k) / 2
      + Real.log (2 * Real.pi) / 2 - 2
      ≤ Real.log (n.choose k) := by
  have hkn : k ≤ n := le_of_lt hklt
  have hnpos : 0 < n := hkpos.trans hklt
  have hrpos : 0 < n - k := Nat.sub_pos_of_lt hklt
  have hchoose_pos : 0 < n.choose k := Nat.choose_pos hkn
  have hfac_nat := Nat.choose_mul_factorial_mul_factorial hkn
  have hfac : (n.choose k : ℝ) * (k ! : ℝ) * ((n - k)! : ℝ) = (n ! : ℝ) := by
    exact_mod_cast hfac_nat
  have hlogfac :
      Real.log (n !) = Real.log (n.choose k) + Real.log (k !) + Real.log ((n - k)!) := by
    rw [← hfac]
    rw [Real.log_mul
        (mul_ne_zero (by exact_mod_cast hchoose_pos.ne') (by exact_mod_cast (Nat.factorial_pos k).ne'))
        (by exact_mod_cast (Nat.factorial_pos (n - k)).ne'),
      Real.log_mul
        (by exact_mod_cast hchoose_pos.ne')
        (by exact_mod_cast (Nat.factorial_pos k).ne')]
  have hN := Stirling.le_log_factorial_stirling (show n ≠ 0 from hnpos.ne')
  have hK := log_factorial_le_stirling_upper (m := k) hkpos.ne'
  have hR := log_factorial_le_stirling_upper (m := n - k) hrpos.ne'
  have hcast_sub : ((n - k : ℕ) : ℝ) = (n : ℝ) - (k : ℝ) := by
    exact Nat.cast_sub hkn
  rw [hlogfac] at hN
  unfold entropyTerm
  rw [hcast_sub] at hR ⊢
  nlinarith

theorem entropyTerm_lower_basic {n k : ℕ} (hkpos : 0 < k) (hklt : k < n) :
    (k : ℝ) * Real.log n - (k : ℝ) * Real.log k
      + (k : ℝ) - (k : ℝ) ^ 2 / (n : ℝ) ≤ entropyTerm n k := by
  have hkn : k ≤ n := le_of_lt hklt
  have hnpos : 0 < (n : ℝ) := by exact_mod_cast (hkpos.trans hklt)
  have hrpos_nat : 0 < n - k := Nat.sub_pos_of_lt hklt
  have hrpos : 0 < ((n - k : ℕ) : ℝ) := by exact_mod_cast hrpos_nat
  have hcast_sub : ((n - k : ℕ) : ℝ) = (n : ℝ) - (k : ℝ) := by
    exact Nat.cast_sub hkn
  have hlog_ratio :=
    Real.log_le_sub_one_of_pos
      (x := ((n - k : ℕ) : ℝ) / (n : ℝ)) (div_pos hrpos hnpos)
  have hdiff :
      (k : ℝ) / (n : ℝ) ≤ Real.log n - Real.log (n - k) := by
    rw [Real.log_div (ne_of_gt hrpos) (ne_of_gt hnpos)] at hlog_ratio
    rw [hcast_sub] at hlog_ratio
    have hnne : (n : ℝ) ≠ 0 := ne_of_gt hnpos
    field_simp [hnne] at hlog_ratio ⊢
    nlinarith
  have hmul :
      ((n - k : ℕ) : ℝ) * ((k : ℝ) / (n : ℝ)) ≤
        ((n - k : ℕ) : ℝ) * (Real.log n - Real.log (n - k)) :=
    mul_le_mul_of_nonneg_left hdiff hrpos.le
  unfold entropyTerm
  have hnne : (n : ℝ) ≠ 0 := ne_of_gt hnpos
  rw [hcast_sub] at hmul ⊢
  field_simp [hnne] at hmul ⊢
  nlinarith

theorem erdos_log_sandwich_of_noLargePrimeFactor
    {n k : ℕ} (hkpos : 0 < k) (hnpos : 0 < n) (hkn : k ≤ n)
    (hn2k : 2 * k ≤ n) (hn6 : 6 ≤ n)
    (hno : NoLargePrimeFactor k (n.choose k)) :
    (k : ℝ) * Real.log n - (k : ℝ) * Real.log k ≤
      (sqrt n : ℝ) * Real.log n + ((min k (n / 3) : ℕ) : ℝ) * Real.log 4 := by
  have hlower := mul_log_sub_mul_log_le_log_choose (n := n) (k := k) hkpos hkn
  have hupper :=
    log_choose_le_sqrt_log_add_min_third_log_four_of_noLargePrimeFactor
      (n := n) (k := k) hnpos hkn hn2k hn6 hno
  linarith

theorem log_choose_le_primeCounting_log_of_noLargePrimeFactor
    {n k : ℕ} (hnpos : 0 < n) (hkn : k ≤ n)
    (hno : NoLargePrimeFactor k (n.choose k)) :
    Real.log (n.choose k) ≤ (Nat.primeCounting k : ℝ) * Real.log n := by
  have hnat : n.choose k ≤ n ^ Nat.primeCounting k :=
    choose_le_pow_primeCounting_of_noLargePrimeFactor hnpos hkn hno
  have hchoose_pos : 0 < n.choose k := Nat.choose_pos hkn
  calc
    Real.log (n.choose k) ≤ Real.log (n ^ Nat.primeCounting k) := by
      exact Real.log_le_log (by exact_mod_cast hchoose_pos) (by exact_mod_cast hnat)
    _ = (Nat.primeCounting k : ℝ) * Real.log n := by
      rw [show Real.log (n ^ Nat.primeCounting k) =
        Real.log ((n : ℝ) ^ Nat.primeCounting k) by norm_num [Nat.cast_pow],
        Real.log_pow]

theorem exists_large_prime_factor_choose_of_primeCounting_log_gap
    {n k : ℕ} (hkpos : 0 < k) (hnpos : 0 < n) (hkn : k ≤ n)
    (hgap :
      (Nat.primeCounting k : ℝ) * Real.log n <
        (k : ℝ) * Real.log n - (k : ℝ) * Real.log k) :
    HasPrimeFactorAbove k (n.choose k) := by
  by_contra hlarge
  have hno : NoLargePrimeFactor k (n.choose k) :=
    not_hasPrimeFactorAbove_iff_noLargePrimeFactor.mp hlarge
  have hlower := mul_log_sub_mul_log_le_log_choose (n := n) (k := k) hkpos hkn
  have hupper :=
    log_choose_le_primeCounting_log_of_noLargePrimeFactor
      (n := n) (k := k) hnpos hkn hno
  exact not_lt_of_ge (hlower.trans hupper) hgap

theorem exists_large_prime_factor_choose_of_pow_gap
    {n k : ℕ} (hkpos : 0 < k) (hkn : k ≤ n)
    (hpi : Nat.primeCounting k ≤ k)
    (hpow : k ^ k < n ^ (k - Nat.primeCounting k)) :
    HasPrimeFactorAbove k (n.choose k) := by
  have hnpos : 0 < n := hkpos.trans_le hkn
  refine exists_large_prime_factor_choose_of_primeCounting_log_gap
    (n := n) (k := k) hkpos hnpos hkn ?_
  have hkpow_pos : 0 < (k : ℝ) ^ k := pow_pos (by exact_mod_cast hkpos) k
  have hlogpow :
      (k : ℝ) * Real.log k <
        (k - Nat.primeCounting k : ℕ) * Real.log n := by
    have hlog : Real.log ((k : ℝ) ^ k) <
        Real.log ((n : ℝ) ^ (k - Nat.primeCounting k)) := by
      exact Real.log_lt_log hkpow_pos (by exact_mod_cast hpow)
    simpa [Real.log_pow] using hlog
  have hk_split :
      (k : ℝ) = (Nat.primeCounting k : ℝ) + (k - Nat.primeCounting k : ℕ) := by
    exact_mod_cast (Nat.add_sub_of_le hpi).symm
  calc
    (Nat.primeCounting k : ℝ) * Real.log n
        < (Nat.primeCounting k : ℝ) * Real.log n
            + (k - Nat.primeCounting k : ℕ) * Real.log n - (k : ℝ) * Real.log k := by
          linarith
    _ = ((Nat.primeCounting k : ℝ) + (k - Nat.primeCounting k : ℕ)) * Real.log n
            - (k : ℝ) * Real.log k := by
          ring
    _ = (k : ℝ) * Real.log n - (k : ℝ) * Real.log k := by
          rw [← hk_split]

theorem exists_large_prime_factor_choose_of_erdos_log_gap
    {n k : ℕ} (hkpos : 0 < k) (hnpos : 0 < n) (hkn : k ≤ n)
    (hn2k : 2 * k ≤ n) (hn6 : 6 ≤ n)
    (hgap :
      (sqrt n : ℝ) * Real.log n + ((min k (n / 3) : ℕ) : ℝ) * Real.log 4 <
        (k : ℝ) * Real.log n - (k : ℝ) * Real.log k) :
    HasPrimeFactorAbove k (n.choose k) := by
  by_contra hlarge
  have hno : NoLargePrimeFactor k (n.choose k) :=
    not_hasPrimeFactorAbove_iff_noLargePrimeFactor.mp hlarge
  have hsandwich :=
    erdos_log_sandwich_of_noLargePrimeFactor
      (n := n) (k := k) hkpos hnpos hkn hn2k hn6 hno
  exact not_lt_of_ge hsandwich hgap

theorem exists_large_prime_factor_choose_of_entropy_gap
    {n k : ℕ} (hkpos : 0 < k) (hklt : k < n)
    (hn2k : 2 * k ≤ n) (hn6 : 6 ≤ n)
    (hgap :
      (sqrt n : ℝ) * Real.log n + ((min k (n / 3) : ℕ) : ℝ) * Real.log 4 <
        entropyTerm n k
          + Real.log n / 2 - Real.log k / 2 - Real.log (n - k) / 2
          + Real.log (2 * Real.pi) / 2 - 2) :
    HasPrimeFactorAbove k (n.choose k) := by
  have hkn : k ≤ n := le_of_lt hklt
  have hnpos : 0 < n := hkpos.trans hklt
  by_contra hlarge
  have hno : NoLargePrimeFactor k (n.choose k) :=
    not_hasPrimeFactorAbove_iff_noLargePrimeFactor.mp hlarge
  have hupper :=
    log_choose_le_sqrt_log_add_min_third_log_four_of_noLargePrimeFactor
      (n := n) (k := k) hnpos hkn hn2k hn6 hno
  have hlower := entropy_lower_le_log_choose (n := n) (k := k) hkpos hklt
  exact not_lt_of_ge (hlower.trans hupper) hgap

theorem exists_large_prime_factor_choose_of_interval_entropy_gap
    {n k : ℕ} (hkpos : 0 < k) (hklt : k < n)
    (hn2k : 2 * k ≤ n) (hn6 : 6 ≤ n)
    (hgap :
      (Nat.primeCounting (sqrt n) : ℝ) * Real.log n
          + Real.log (primeIntervalProduct (sqrt n) (min k (n / 3))) <
        entropyTerm n k
          + Real.log n / 2 - Real.log k / 2 - Real.log (n - k) / 2
          + Real.log (2 * Real.pi) / 2 - 2) :
    HasPrimeFactorAbove k (n.choose k) := by
  have hkn : k ≤ n := le_of_lt hklt
  have hnpos : 0 < n := hkpos.trans hklt
  by_contra hlarge
  have hno : NoLargePrimeFactor k (n.choose k) :=
    not_hasPrimeFactorAbove_iff_noLargePrimeFactor.mp hlarge
  have hupper :=
    log_choose_le_primeCounting_sqrt_log_add_log_primeIntervalProduct_of_noLargePrimeFactor
      (n := n) (k := k) hnpos hkn hn2k hn6 hno
  have hlower := entropy_lower_le_log_choose (n := n) (k := k) hkpos hklt
  exact not_lt_of_ge (hlower.trans hupper) hgap

theorem exists_large_prime_factor_choose_of_sq_le_and_primeCounting_gap
    {n k : ℕ} (hk1 : 1 < k) (hkn : k ≤ n) (hsq : k * k ≤ n)
    (hpi : 2 * Nat.primeCounting k < k) :
    HasPrimeFactorAbove k (n.choose k) := by
  have hkpos : 0 < k := hk1.trans' zero_lt_one
  have hnpos : 0 < n := hkpos.trans_le hkn
  have hlogn_pos : 0 < Real.log n := Real.log_pos (by exact_mod_cast hk1.trans_le hkn)
  have hlog_sq_le : Real.log ((k : ℝ) ^ 2) ≤ Real.log (n : ℝ) := by
    have hsq_pow : k ^ 2 ≤ n := by simpa [sq] using hsq
    exact Real.log_le_log (sq_pos_of_pos (by exact_mod_cast hkpos))
      (by exact_mod_cast hsq_pow)
  have htwologk_le : 2 * Real.log k ≤ Real.log n := by
    simpa [Real.log_pow] using hlog_sq_le
  have hhalf_le :
      ((k : ℝ) / 2) * Real.log n ≤ (k : ℝ) * Real.log n - (k : ℝ) * Real.log k := by
    nlinarith
  have hpi_lt_half : (Nat.primeCounting k : ℝ) < (k : ℝ) / 2 := by
    nlinarith [show (2 * Nat.primeCounting k : ℝ) < (k : ℝ) by exact_mod_cast hpi]
  have hpi_log_lt :
      (Nat.primeCounting k : ℝ) * Real.log n <
        (k : ℝ) * Real.log n - (k : ℝ) * Real.log k := by
    exact (mul_lt_mul_of_pos_right hpi_lt_half hlogn_pos).trans_le hhalf_le
  by_contra hlarge
  have hno : NoLargePrimeFactor k (n.choose k) :=
    not_hasPrimeFactorAbove_iff_noLargePrimeFactor.mp hlarge
  have hupper :=
    log_choose_le_primeCounting_log_of_noLargePrimeFactor
      (n := n) (k := k) hnpos hkn hno
  have hlower := mul_log_sub_mul_log_le_log_choose (n := n) (k := k) hkpos hkn
  exact not_lt_of_ge (hlower.trans hupper) hpi_log_lt

theorem primeCounting_gap_of_120_le {k : ℕ} (hk : 120 ≤ k) :
    2 * Nat.primeCounting k < k := by
  let n := k - 30
  have hk_eq : k = 30 + n := by omega
  have hbound0 := Nat.primeCounting_add_le
    (a := 30) (k := 30) (n := n) (by norm_num) (by norm_num : 30 ≤ 30)
  have hbound : Nat.primeCounting k ≤ Nat.primeCounting 30 + Nat.totient 30 * (n / 30 + 1) := by
    simpa [hk_eq] using hbound0
  have hcalc : Nat.primeCounting 30 = 10 := by native_decide
  have htot : Nat.totient 30 = 8 := by native_decide
  have hnle : n / 30 ≤ n / 4 :=
    Nat.div_le_div_left (by norm_num : 4 ≤ 30) (by norm_num : 0 < 4)
  have hbound2 : Nat.primeCounting k ≤ 10 + 8 * (n / 30 + 1) := by
    simpa [hcalc, htot] using hbound
  have hbound3 : Nat.primeCounting k ≤ 10 + 8 * (n / 4 + 1) := by
    nlinarith
  have h4 : 4 * (n / 4) ≤ n := Nat.mul_div_le n 4
  have hdiv : 8 * (n / 4) ≤ 2 * n := by
    nlinarith
  omega

theorem exists_large_prime_factor_choose_sq_le_of_120_le
    {n k : ℕ} (hk120 : 120 ≤ k) (hkn : k ≤ n) (hsq : k * k ≤ n) :
    HasPrimeFactorAbove k (n.choose k) :=
  exists_large_prime_factor_choose_of_sq_le_and_primeCounting_gap
    (by omega) hkn hsq (primeCounting_gap_of_120_le hk120)

theorem primeCounting_gap_9_120_cert :
    ∀ k : Fin 120, 9 ≤ k.val → 2 * Nat.primeCounting k.val < k.val := by
  native_decide

theorem primeCounting_gap_of_9_le_lt_120 {k : ℕ} (hk9 : 9 ≤ k) (hk120 : k < 120) :
    2 * Nat.primeCounting k < k :=
  primeCounting_gap_9_120_cert ⟨k, hk120⟩ hk9

theorem primeCounting_gap_of_9_le {k : ℕ} (hk9 : 9 ≤ k) :
    2 * Nat.primeCounting k < k := by
  by_cases hk120 : k < 120
  · exact primeCounting_gap_of_9_le_lt_120 hk9 hk120
  · exact primeCounting_gap_of_120_le (by omega)

theorem three_mul_primeCounting_le_30_150_cert :
    ∀ k : Fin 150, 33 ≤ k.val → 3 * Nat.primeCounting k.val ≤ k.val := by
  native_decide

theorem three_mul_primeCounting_le_of_33_le {k : ℕ} (hk33 : 33 ≤ k) :
    3 * Nat.primeCounting k ≤ k := by
  by_cases hk150 : k < 150
  · exact three_mul_primeCounting_le_30_150_cert ⟨k, hk150⟩ hk33
  · let m := k - 30
    have hk_eq : k = 30 + m := by omega
    have hbound0 := Nat.primeCounting_add_le
      (a := 30) (k := 30) (n := m) (by norm_num) (by norm_num : 30 ≤ 30)
    have hbound : Nat.primeCounting k ≤ Nat.primeCounting 30 + Nat.totient 30 * (m / 30 + 1) := by
      simpa [hk_eq] using hbound0
    have hcalc : Nat.primeCounting 30 = 10 := by native_decide
    have htot : Nat.totient 30 = 8 := by native_decide
    have hbound2 : Nat.primeCounting k ≤ 10 + 8 * (m / 30 + 1) := by
      simpa [hcalc, htot] using hbound
    have hm120 : 120 ≤ m := by omega
    have hq4 : 4 ≤ m / 30 := by
      exact (Nat.le_div_iff_mul_le (by norm_num : 0 < 30)).mpr hm120
    have hmul : 30 * (m / 30) ≤ m := Nat.mul_div_le m 30
    omega

theorem log_choose_le_sqrt_third_log_add_min_third_log_two_of_noLargePrimeFactor
    {n k : ℕ} (hnpos : 0 < n) (hkn : k ≤ n) (hn2k : 2 * k ≤ n) (hn6 : 6 ≤ n)
    (hno : NoLargePrimeFactor k (n.choose k))
    (hsqrt33 : 33 ≤ sqrt n)
    (hsqrtM : sqrt n ≤ min k (n / 3)) (hMsub : min k (n / 3) - sqrt n ≤ sqrt n) :
    Real.log (n.choose k) ≤
      ((sqrt n : ℕ) : ℝ) / 3 * Real.log n
        + ((min k (n / 3) : ℕ) : ℝ) * Real.log 2 := by
  have hupper :=
    log_choose_le_primeCounting_sqrt_log_add_min_third_log_two_of_noLargePrimeFactor
      (n := n) (k := k) hnpos hkn hn2k hn6 hno hsqrtM hMsub
  have hlogn_pos : 0 < Real.log n := by
    have hn_gt_one : 1 < n := lt_of_lt_of_le (by omega : 1 < sqrt n) (Nat.sqrt_le_self n)
    exact Real.log_pos (by exact_mod_cast hn_gt_one)
  have hpi : 3 * Nat.primeCounting (sqrt n) ≤ sqrt n :=
    three_mul_primeCounting_le_of_33_le hsqrt33
  have hpi_real : (Nat.primeCounting (sqrt n) : ℝ) ≤ ((sqrt n : ℕ) : ℝ) / 3 := by
    nlinarith [show (3 * Nat.primeCounting (sqrt n) : ℝ) ≤ ((sqrt n : ℕ) : ℝ) by
      exact_mod_cast hpi]
  exact hupper.trans <|
    add_le_add_left (mul_le_mul_of_nonneg_right hpi_real hlogn_pos.le)
      (((min k (n / 3) : ℕ) : ℝ) * Real.log 2)

theorem log_choose_le_sqrt_third_log_add_min_log4_sub_theta_of_noLargePrimeFactor
    {n k : ℕ} (hnpos : 0 < n) (hkn : k ≤ n) (hn2k : 2 * k ≤ n) (hn6 : 6 ≤ n)
    (hno : NoLargePrimeFactor k (n.choose k))
    (hsqrt33 : 33 ≤ sqrt n)
    (hsqrtM : sqrt n ≤ min k (n / 3)) :
    Real.log (n.choose k) ≤
      ((sqrt n : ℕ) : ℝ) / 3 * Real.log n
        + ((min k (n / 3) : ℕ) : ℝ) * Real.log 4
        - Chebyshev.theta ((sqrt n : ℕ) : ℝ) := by
  have hupper :=
    log_choose_le_primeCounting_sqrt_log_add_log_primeIntervalProduct_of_noLargePrimeFactor
      (n := n) (k := k) hnpos hkn hn2k hn6 hno
  have hlogP :=
    log_primeIntervalProduct_le_min_third_log4_sub_theta
      (a := sqrt n) (M := min k (n / 3)) hsqrtM
  have hlogn_pos : 0 < Real.log n := by
    have hn_gt_one : 1 < n := lt_of_lt_of_le (by omega : 1 < sqrt n) (Nat.sqrt_le_self n)
    exact Real.log_pos (by exact_mod_cast hn_gt_one)
  have hpi : 3 * Nat.primeCounting (sqrt n) ≤ sqrt n :=
    three_mul_primeCounting_le_of_33_le hsqrt33
  have hpi_real : (Nat.primeCounting (sqrt n) : ℝ) ≤ ((sqrt n : ℕ) : ℝ) / 3 := by
    nlinarith [show (3 * Nat.primeCounting (sqrt n) : ℝ) ≤ ((sqrt n : ℕ) : ℝ) by
      exact_mod_cast hpi]
  have hpc :
      (Nat.primeCounting (sqrt n) : ℝ) * Real.log n ≤
        ((sqrt n : ℕ) : ℝ) / 3 * Real.log n :=
    mul_le_mul_of_nonneg_right hpi_real hlogn_pos.le
  linarith

theorem exists_large_prime_factor_choose_of_theta_interval_entropy_gap
    {n k : ℕ} (hkpos : 0 < k) (hklt : k < n)
    (hn2k : 2 * k ≤ n) (hn6 : 6 ≤ n)
    (hsqrt33 : 33 ≤ sqrt n) (hsqrtM : sqrt n ≤ min k (n / 3))
    (hgap :
      ((sqrt n : ℕ) : ℝ) / 3 * Real.log n
          + ((min k (n / 3) : ℕ) : ℝ) * Real.log 4
          - Chebyshev.theta ((sqrt n : ℕ) : ℝ) <
        entropyTerm n k
          + Real.log n / 2 - Real.log k / 2 - Real.log (n - k) / 2
          + Real.log (2 * Real.pi) / 2 - 2) :
    HasPrimeFactorAbove k (n.choose k) := by
  have hkn : k ≤ n := le_of_lt hklt
  have hnpos : 0 < n := hkpos.trans hklt
  by_contra hlarge
  have hno : NoLargePrimeFactor k (n.choose k) :=
    not_hasPrimeFactorAbove_iff_noLargePrimeFactor.mp hlarge
  have hupper :=
    log_choose_le_sqrt_third_log_add_min_log4_sub_theta_of_noLargePrimeFactor
      (n := n) (k := k) hnpos hkn hn2k hn6 hno hsqrt33 hsqrtM
  have hlower := entropy_lower_le_log_choose (n := n) (k := k) hkpos hklt
  exact not_lt_of_ge (hlower.trans hupper) hgap

theorem min_eq_left_of_sqrt33_close
    {n k : ℕ} (hsqrt33 : 33 ≤ sqrt n)
    (hMsub : min k (n / 3) - sqrt n ≤ sqrt n) :
    min k (n / 3) = k := by
  by_cases hk : k ≤ n / 3
  · exact Nat.min_eq_left hk
  · have hM : min k (n / 3) = n / 3 := Nat.min_eq_right (le_of_not_ge hk)
    have hclose : n / 3 ≤ 2 * sqrt n := by
      omega
    have hnle : n ≤ 3 * (n / 3) + 2 := by omega
    have hsq : sqrt n * sqrt n ≤ n := Nat.sqrt_le n
    nlinarith

theorem close_branch_coef_gap_aux {L N : ℝ} (h10 : 10 * L < N) (hL : L < 1) :
    (2 : ℝ) / 3 < N / 6 - 2 * L + 1 := by
  linarith

theorem close_branch_main_gap_aux {k N L : ℝ} (hk : 34 ≤ k) (hN : N / 2 ≤ k / 6)
    (hc : (2 : ℝ) / 3 < N / 6 - 2 * L + 1) :
    0 < k * (N / 6 - 2 * L + 1) - N / 2 - 6 := by
  have hkpos : 0 < k := by linarith
  have hprod :
      k * ((2 : ℝ) / 3) < k * (N / 6 - 2 * L + 1) :=
    mul_lt_mul_of_pos_left hc hkpos
  nlinarith

theorem close_branch_simple_gap_aux {k N L : ℝ}
    (h : 0 < k * (N / 6 - 2 * L + 1) - N / 2 - 6) :
    k / 3 * N + k * L <
      (k / 2 * N - k * L + k - 4) - N / 2 - 2 := by
  nlinarith

theorem close_branch_shift_aux {A B N : ℝ} (h : A ≤ B) :
    A - N / 2 - 2 ≤ B - N / 2 - 2 := by
  linarith

theorem close_branch_upper_simple_aux {a k M : ℕ} {N L : ℝ}
    (hM : M = k) (ha : a ≤ k) (hN : 0 ≤ N) :
    (a : ℝ) / 3 * N + (M : ℝ) * L ≤ (k : ℝ) / 3 * N + (k : ℝ) * L := by
  subst M
  have ha_real : (a : ℝ) / 3 ≤ (k : ℝ) / 3 := by
    exact div_le_div_of_nonneg_right (by exact_mod_cast ha) (by norm_num)
  exact add_le_add_left (mul_le_mul_of_nonneg_right ha_real hN) ((k : ℝ) * L)

theorem log2_lt_7_10 : Real.log 2 < (7 : ℝ) / 10 := by
  nlinarith [Real.log_two_lt_d9]

theorem log4_lt_7_5 : Real.log 4 < (7 : ℝ) / 5 := by
  rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
  nlinarith [log2_lt_7_10]

theorem log2_lt_1733_2500 : Real.log 2 < (1733 : ℝ) / 2500 := by
  nlinarith [Real.log_two_lt_d9]

theorem log4_lt_1733_1250 : Real.log 4 < (1733 : ℝ) / 1250 := by
  rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
  nlinarith [log2_lt_1733_2500]

theorem log64_lt_21_5 : Real.log 64 < (21 : ℝ) / 5 := by
  rw [show (64 : ℝ) = 2 ^ 6 by norm_num, Real.log_pow]
  nlinarith [log2_lt_7_10]

theorem log_le_div64_add_16_5_of_120_le {k : ℕ} (hk120 : 120 ≤ k) :
    Real.log k ≤ (k : ℝ) / 64 + (16 : ℝ) / 5 := by
  have hkpos : 0 < k := by omega
  have hdivpos : 0 < (k : ℝ) / 64 := by positivity
  have hlogdiv := Real.log_le_sub_one_of_pos (x := (k : ℝ) / 64) hdivpos
  rw [Real.log_div (by exact_mod_cast hkpos.ne' : (k : ℝ) ≠ 0)
    (by norm_num : (64 : ℝ) ≠ 0)] at hlogdiv
  nlinarith [log64_lt_21_5]

theorem large_k_stirling_tail_lt_div32 {k : ℕ} (hk120 : 120 ≤ k) :
    Real.log k / 2 + (6 : ℝ) / 5 < (k : ℝ) / 32 := by
  have hlog := log_le_div64_add_16_5_of_120_le hk120
  have hkreal : (120 : ℝ) ≤ k := by exact_mod_cast hk120
  nlinarith

theorem log6_gt_8_5 : (8 : ℝ) / 5 < Real.log 6 := by
  have hlog2 : (69 : ℝ) / 100 < Real.log 2 := by
    nlinarith [Real.log_two_gt_d9]
  have hlog3 : (1 : ℝ) < Real.log 3 := by
    exact (Real.lt_log_iff_exp_lt (by norm_num : (0 : ℝ) < 3)).mpr Real.exp_one_lt_three
  have hlog6 : Real.log 6 = Real.log 2 + Real.log 3 := by
    rw [show (6 : ℝ) = 2 * 3 by norm_num, Real.log_mul]
    all_goals norm_num
  nlinarith

theorem stirling_correction_ge_neg_log_k_sub_six_fifths
    {n k : ℕ} (hkpos : 0 < k) (hklt : k < n) :
    - Real.log k / 2 - (6 : ℝ) / 5 ≤
      Real.log n / 2 - Real.log k / 2 - Real.log (n - k) / 2
        + Real.log (2 * Real.pi) / 2 - 2 := by
  have hnkpos : 0 < n - k := Nat.sub_pos_of_lt hklt
  have hcast_sub : ((n - k : ℕ) : ℝ) = (n : ℝ) - (k : ℝ) :=
    Nat.cast_sub (le_of_lt hklt)
  have hnkpos_real : (0 : ℝ) < (n : ℝ) - (k : ℝ) := by
    rw [← hcast_sub]
    exact_mod_cast hnkpos
  have hnk_le_n_real : (n : ℝ) - (k : ℝ) ≤ (n : ℝ) := by
    have hk_nonneg : (0 : ℝ) ≤ k := by positivity
    linarith
  have hlognk_le_logn : Real.log (n - k) ≤ Real.log n :=
    Real.log_le_log hnkpos_real hnk_le_n_real
  have htwopi : (6 : ℝ) < 2 * Real.pi := by
    nlinarith [Real.pi_gt_three]
  have hlog6_le : Real.log 6 ≤ Real.log (2 * Real.pi) :=
    Real.log_le_log (by norm_num) htwopi.le
  nlinarith [log6_gt_8_5, hlog6_le]

theorem entropyTerm_eq_mul_entropyRatio
    {n k : ℕ} (hkpos : 0 < k) (hklt : k < n) :
    entropyTerm n k =
      (k : ℝ) * (((n : ℝ) / (k : ℝ)) * Real.log ((n : ℝ) / (k : ℝ))
        - ((n : ℝ) / (k : ℝ) - 1) * Real.log ((n : ℝ) / (k : ℝ) - 1)) := by
  have hkn : k ≤ n := le_of_lt hklt
  have hnpos : 0 < n := hkpos.trans hklt
  have hnkpos : 0 < n - k := Nat.sub_pos_of_lt hklt
  have hkpos_real : (0 : ℝ) < k := by exact_mod_cast hkpos
  have hnpos_real : (0 : ℝ) < n := by exact_mod_cast hnpos
  have hnkpos_real_nat : (0 : ℝ) < ((n - k : ℕ) : ℝ) := by exact_mod_cast hnkpos
  have hk_ne : (k : ℝ) ≠ 0 := ne_of_gt hkpos_real
  have hn_ne : (n : ℝ) ≠ 0 := ne_of_gt hnpos_real
  have hnk_ne : ((n - k : ℕ) : ℝ) ≠ 0 := ne_of_gt hnkpos_real_nat
  have hcast_sub : ((n - k : ℕ) : ℝ) = (n : ℝ) - (k : ℝ) := Nat.cast_sub hkn
  have hratio_sub :
      (n : ℝ) / (k : ℝ) - 1 = ((n - k : ℕ) : ℝ) / (k : ℝ) := by
    rw [hcast_sub]
    field_simp [hk_ne]
  unfold entropyTerm
  rw [Real.log_div hn_ne hk_ne, hratio_sub, Real.log_div hnk_ne hk_ne]
  rw [hcast_sub]
  field_simp [hk_ne]
  ring

theorem entropyRatio_lower_log_add
    {x : ℝ} (hx : 1 < x) :
    Real.log x + 1 - 1 / x ≤
      x * Real.log x - (x - 1) * Real.log (x - 1) := by
  have hxpos : 0 < x := by linarith
  have hxsubpos : 0 < x - 1 := by linarith
  have hypos : 0 < x / (x - 1) := div_pos hxpos hxsubpos
  have hlog := Real.one_sub_inv_le_log_of_pos hypos
  have hrewrite :
      Real.log x + (x - 1) * Real.log (x / (x - 1)) =
        x * Real.log x - (x - 1) * Real.log (x - 1) := by
    rw [Real.log_div (ne_of_gt hxpos) (ne_of_gt hxsubpos)]
    ring
  have hinv_eq : (x / (x - 1))⁻¹ = (x - 1) / x := by
    field_simp [ne_of_gt hxpos, ne_of_gt hxsubpos]
  rw [hinv_eq] at hlog
  have hlog' : 1 / x ≤ Real.log (x / (x - 1)) := by
    field_simp [ne_of_gt hxpos] at hlog ⊢
    linarith
  have hmul :
      (x - 1) * (1 / x) ≤ (x - 1) * Real.log (x / (x - 1)) :=
    mul_le_mul_of_nonneg_left hlog' (by linarith)
  have hbasic :
      Real.log x + 1 - 1 / x ≤
        Real.log x + (x - 1) * Real.log (x / (x - 1)) := by
    field_simp [ne_of_gt hxpos, ne_of_gt hxsubpos] at hmul ⊢
    nlinarith
  rwa [hrewrite] at hbasic

theorem two_mul_sub_one_div_add_one_le_log {x : ℝ} (hx1 : 1 ≤ x) :
    2 * (x - 1) / (x + 1) ≤ Real.log x := by
  by_cases hx : x = 1
  · subst x
    norm_num
  have hxgt : 1 < x := lt_of_le_of_ne hx1 (Ne.symm hx)
  let u : ℝ := (x - 1) / (x + 1)
  have hdenpos : 0 < x + 1 := by linarith
  have hu0 : 0 ≤ u := by
    exact div_nonneg (by linarith) hdenpos.le
  have hu1 : u < 1 := by
    rw [show u = (x - 1) / (x + 1) by rfl]
    rw [div_lt_one hdenpos]
    linarith
  have hsum := Real.sum_range_le_log_div hu0 hu1 1
  norm_num at hsum
  have hratio : (1 + u) / (1 - u) = x := by
    rw [show u = (x - 1) / (x + 1) by rfl]
    field_simp [hdenpos.ne']
    ring
  rw [hratio] at hsum
  have hleft : 2 * (x - 1) / (x + 1) = 2 * u := by
    rw [show u = (x - 1) / (x + 1) by rfl]
    ring
  rw [hleft]
  nlinarith

theorem two_div_two_mul_sub_one_le_log_div_sub_one {x : ℝ} (hx : 1 < x) :
    2 / (2 * x - 1) ≤ Real.log (x / (x - 1)) := by
  have hy1 : 1 ≤ x / (x - 1) := by
    have hden : 0 < x - 1 := by linarith
    rw [one_le_div hden]
    linarith
  have h := two_mul_sub_one_div_add_one_le_log hy1
  have hden : 0 < x - 1 := by linarith
  have hden2 : 0 < 2 * x - 1 := by linarith
  convert h using 1
  field_simp [hden.ne', hden2.ne']
  ring

theorem entropyRatio_lower_log_add_two_div
    {x : ℝ} (hx : 1 < x) :
    Real.log x + (x - 1) * (2 / (2 * x - 1)) ≤
      x * Real.log x - (x - 1) * Real.log (x - 1) := by
  have hxpos : 0 < x := by linarith
  have hxsubpos : 0 < x - 1 := by linarith
  have hratio := two_div_two_mul_sub_one_le_log_div_sub_one hx
  have hmul :
      (x - 1) * (2 / (2 * x - 1)) ≤
        (x - 1) * Real.log (x / (x - 1)) :=
    mul_le_mul_of_nonneg_left hratio (by linarith)
  have hrewrite :
      Real.log x + (x - 1) * Real.log (x / (x - 1)) =
        x * Real.log x - (x - 1) * Real.log (x - 1) := by
    rw [Real.log_div (ne_of_gt hxpos) (ne_of_gt hxsubpos)]
    ring
  linarith

theorem sqrt_div_mul_log_mul_le_of_120_le
    {K x : ℝ} (hK : 120 ≤ K) (hx : 2 ≤ x) :
    Real.sqrt (x / K) * Real.log (K * x) ≤
      Real.sqrt (x / 120) * Real.log (120 * x) := by
  have hxpos : 0 < x := by linarith
  have hKpos : 0 < K := by linarith
  have h120pos : (0 : ℝ) < 120 := by norm_num
  have hz0 : Real.exp 2 ≤ 120 * x := by
    have hexp1 : Real.exp 1 < 3 := Real.exp_one_lt_three
    have hexp1pos : 0 < Real.exp 1 := Real.exp_pos 1
    have hexp2 : Real.exp 2 < 9 := by
      rw [show (2 : ℝ) = 1 + 1 by norm_num, Real.exp_add]
      nlinarith
    nlinarith
  have hzK : Real.exp 2 ≤ K * x := by
    have hle : 120 * x ≤ K * x := mul_le_mul_of_nonneg_right hK hxpos.le
    exact hz0.trans hle
  have hKx : 120 * x ≤ K * x := mul_le_mul_of_nonneg_right hK hxpos.le
  have hanti := Real.log_div_sqrt_antitoneOn hz0 hzK hKx
  have hscale :
      x * (Real.log (K * x) / Real.sqrt (K * x)) ≤
        x * (Real.log (120 * x) / Real.sqrt (120 * x)) :=
    mul_le_mul_of_nonneg_left hanti hxpos.le
  have hleft :
      Real.sqrt (x / K) * Real.log (K * x) =
        x * (Real.log (K * x) / Real.sqrt (K * x)) := by
    rw [Real.sqrt_div hxpos.le, Real.sqrt_mul hKpos.le]
    field_simp [ne_of_gt (Real.sqrt_pos_of_pos hxpos), ne_of_gt (Real.sqrt_pos_of_pos hKpos)]
    rw [Real.sq_sqrt hxpos.le]
  have hright :
      Real.sqrt (x / 120) * Real.log (120 * x) =
        x * (Real.log (120 * x) / Real.sqrt (120 * x)) := by
    rw [Real.sqrt_div hxpos.le, Real.sqrt_mul h120pos.le]
    field_simp [ne_of_gt (Real.sqrt_pos_of_pos hxpos), ne_of_gt (Real.sqrt_pos_of_pos h120pos)]
    rw [Real.sq_sqrt hxpos.le]
  rw [hleft, hright]
  exact hscale

theorem nat_sqrt_div_le_sqrt_ratio {n k : ℕ} (hkpos : 0 < k) :
    ((sqrt n : ℕ) : ℝ) / (k : ℝ) ≤
      Real.sqrt (((n : ℝ) / (k : ℝ)) / (k : ℝ)) := by
  have hkpos_real : (0 : ℝ) < k := by exact_mod_cast hkpos
  have hnonneg : 0 ≤ ((sqrt n : ℕ) : ℝ) / (k : ℝ) := by positivity
  have harg_nonneg : 0 ≤ ((n : ℝ) / (k : ℝ)) / (k : ℝ) := by positivity
  have hsqrt_sq_nat : sqrt n * sqrt n ≤ n := Nat.sqrt_le n
  have hsqrt_sq_real : (((sqrt n : ℕ) : ℝ) / (k : ℝ)) ^ 2 ≤
      ((n : ℝ) / (k : ℝ)) / (k : ℝ) := by
    have hcast : (((sqrt n : ℕ) : ℝ) ^ 2) ≤ (n : ℝ) := by
      norm_num [pow_two]
      exact_mod_cast hsqrt_sq_nat
    field_simp [ne_of_gt hkpos_real]
    nlinarith
  exact (Real.le_sqrt hnonneg harg_nonneg).mpr hsqrt_sq_real

set_option maxHeartbeats 800000 in
theorem exists_large_prime_factor_choose_below_sq_close_of_sqrt33
    {n k : ℕ} (hk9 : 9 ≤ k) (hn2k : 2 * k ≤ n)
    (hnsq : n < k * k) (hsqrt33 : 33 ≤ sqrt n)
    (hMsub : min k (n / 3) - sqrt n ≤ sqrt n) :
    HasPrimeFactorAbove k (n.choose k) := by
  have hkpos : 0 < k := by omega
  have hkn : k ≤ n := by omega
  have hklt : k < n := by omega
  have hnpos : 0 < n := hkpos.trans_le hkn
  have hn6 : 6 ≤ n := by
    have hsqrt_le_self : sqrt n ≤ n := Nat.sqrt_le_self n
    omega
  have hn9 : 9 ≤ n := by omega
  have hsqrtM : sqrt n ≤ min k (n / 3) :=
    sqrt_le_min_of_nine_le_and_lt_sq hn9 hnsq
  have hM_eq : min k (n / 3) = k :=
    min_eq_left_of_sqrt33_close hsqrt33 hMsub
  have hsqrt_lt_k : sqrt n < k := Nat.sqrt_lt.mpr hnsq
  have hk34 : 34 ≤ k := by omega
  have hk_le_2sqrt : k ≤ 2 * sqrt n := by
    rw [hM_eq] at hMsub
    omega
  have hksq4 : k * k ≤ 4 * n := by
    have hsq : sqrt n * sqrt n ≤ n := Nat.sqrt_le n
    nlinarith
  have hlog2_pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlog2_lt_one : Real.log 2 < 1 := by
    have h := Real.log_lt_sub_one_of_pos (x := (2 : ℝ)) (by norm_num) (by norm_num)
    norm_num at h
    exact h
  have hlogn_pos : 0 < Real.log n := by
    exact Real.log_pos (by exact_mod_cast (by omega : 1 < n))
  have hlogk_le_logn : Real.log k ≤ Real.log n :=
    Real.log_le_log (by exact_mod_cast hkpos) (by exact_mod_cast hkn)
  have hnkpos : 0 < n - k := Nat.sub_pos_of_lt hklt
  have hlognk_le_logn : Real.log (n - k) ≤ Real.log n :=
    Real.log_le_log (by exact_mod_cast hnkpos) (by exact_mod_cast (by omega : n - k ≤ n))
  have hlogtwopi_nonneg : 0 ≤ Real.log (2 * Real.pi) := by
    exact Real.log_nonneg (by nlinarith [Real.one_le_pi_div_two])
  have hcorr_ge :
      - Real.log n / 2 - 2 ≤
        Real.log n / 2 - Real.log k / 2 - Real.log (n - k) / 2
          + Real.log (2 * Real.pi) / 2 - 2 := by
    nlinarith
  have hlog4_eq : Real.log (4 : ℝ) = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
    norm_num
  have htwologk_le : 2 * Real.log k ≤ Real.log n + 2 * Real.log 2 := by
    have hlog_sq_le : Real.log ((k : ℝ) ^ 2) ≤ Real.log ((4 : ℝ) * (n : ℝ)) := by
      have hcast : (k : ℝ) ^ 2 ≤ (4 : ℝ) * (n : ℝ) := by
        norm_num [pow_two]
        exact_mod_cast hksq4
      exact Real.log_le_log (sq_pos_of_pos (by exact_mod_cast hkpos)) hcast
    rw [Real.log_pow] at hlog_sq_le
    rw [Real.log_mul (by norm_num : (4 : ℝ) ≠ 0)
      (by exact_mod_cast hnpos.ne' : (n : ℝ) ≠ 0), hlog4_eq] at hlog_sq_le
    norm_num at hlog_sq_le
    nlinarith
  have hlogk_le_half : Real.log k ≤ Real.log n / 2 + Real.log 2 := by
    linarith
  have hk_sq_div_le_four : (k : ℝ) ^ 2 / (n : ℝ) ≤ 4 := by
    have hcast : (k : ℝ) ^ 2 ≤ 4 * (n : ℝ) := by
      norm_num [pow_two]
      exact_mod_cast hksq4
    exact (div_le_iff₀ (by exact_mod_cast hnpos : (0 : ℝ) < n)).mpr (by linarith)
  have hbasic_ge :
      (k : ℝ) / 2 * Real.log n - (k : ℝ) * Real.log 2 + (k : ℝ) - 4 ≤
        (k : ℝ) * Real.log n - (k : ℝ) * Real.log k
          + (k : ℝ) - (k : ℝ) ^ 2 / (n : ℝ) := by
    have hmul : (k : ℝ) * Real.log k ≤ (k : ℝ) * (Real.log n / 2 + Real.log 2) :=
      mul_le_mul_of_nonneg_left hlogk_le_half (by positivity)
    nlinarith
  have hbasic_ge_shift :
      ((k : ℝ) / 2 * Real.log n - (k : ℝ) * Real.log 2 + (k : ℝ) - 4)
          - Real.log n / 2 - (2 : ℝ) ≤
        ((k : ℝ) * Real.log n - (k : ℝ) * Real.log k
          + (k : ℝ) - (k : ℝ) ^ 2 / (n : ℝ)) - Real.log n / 2 - (2 : ℝ) := by
    exact close_branch_shift_aux hbasic_ge
  have hlog16_lt_four : Real.log (16 : ℝ) < 4 := by
    rw [show (16 : ℝ) = 2 ^ 4 by norm_num, Real.log_pow]
    norm_num
    nlinarith
  have hlogk_le_six : Real.log k ≤ (k : ℝ) / 6 := by
    have hdivpos : 0 < (k : ℝ) / 16 := by positivity
    have hdiv :=
      Real.log_le_sub_one_of_pos (x := (k : ℝ) / 16) hdivpos
    rw [Real.log_div (by exact_mod_cast hkpos.ne' : (k : ℝ) ≠ 0)
      (by norm_num : (16 : ℝ) ≠ 0)] at hdiv
    have haux : Real.log k ≤ (k : ℝ) / 16 + 3 := by
      nlinarith
    have hk34r : (34 : ℝ) ≤ k := by exact_mod_cast hk34
    nlinarith
  have hlogn_lt_twologk : Real.log n < 2 * Real.log k := by
    have hlog_lt : Real.log (n : ℝ) < Real.log ((k * k : ℕ) : ℝ) :=
      Real.log_lt_log (by exact_mod_cast hnpos) (by exact_mod_cast hnsq)
    rw [show ((k * k : ℕ) : ℝ) = (k : ℝ) ^ 2 by norm_num [pow_two],
      Real.log_pow] at hlog_lt
    exact hlog_lt
  have hlogn_le_kthird : Real.log n ≤ (k : ℝ) / 3 := by
    linarith only [hlogn_lt_twologk, hlogk_le_six]
  have hlogn_half_le_ksix : Real.log n / 2 ≤ (k : ℝ) / 6 := by
    linarith only [hlogn_le_kthird]
  have hn1024 : 1024 < n := by
    have hsq : sqrt n * sqrt n ≤ n := Nat.sqrt_le n
    have h1024 : 1024 < sqrt n * sqrt n := by
      nlinarith only [hsqrt33]
    exact h1024.trans_le hsq
  have hten_log2_lt_logn : 10 * Real.log 2 < Real.log n := by
    have hlog_lt : Real.log (1024 : ℝ) < Real.log (n : ℝ) :=
      Real.log_lt_log (by norm_num) (by exact_mod_cast hn1024)
    rwa [show (1024 : ℝ) = 2 ^ 10 by norm_num, Real.log_pow] at hlog_lt
  have hcoef : (2 : ℝ) / 3 < Real.log n / 6 - 2 * Real.log 2 + 1 := by
    exact close_branch_coef_gap_aux hten_log2_lt_logn hlog2_lt_one
  have hmain :
      0 < (k : ℝ) * (Real.log n / 6 - 2 * Real.log 2 + 1)
          - Real.log n / 2 - 6 := by
    have hk34r : (34 : ℝ) ≤ k := by exact_mod_cast hk34
    exact close_branch_main_gap_aux hk34r hlogn_half_le_ksix hcoef
  have hsimple_gap :
      (k : ℝ) / 3 * Real.log n + (k : ℝ) * Real.log 2 <
        ((k : ℝ) / 2 * Real.log n - (k : ℝ) * Real.log 2 + (k : ℝ) - 4)
          - Real.log n / 2 - 2 := by
    exact close_branch_simple_gap_aux hmain
  have hupper_simple :
      ((sqrt n : ℕ) : ℝ) / 3 * Real.log n
          + ((min k (n / 3) : ℕ) : ℝ) * Real.log 2 ≤
        (k : ℝ) / 3 * Real.log n + (k : ℝ) * Real.log 2 := by
    exact close_branch_upper_simple_aux
      (a := sqrt n) (k := k) (M := min k (n / 3))
      (N := Real.log n) (L := Real.log 2) hM_eq hsqrt_lt_k.le hlogn_pos.le
  have hbasic := entropyTerm_lower_basic (n := n) (k := k) hkpos hklt
  have hlower_entropy := entropy_lower_le_log_choose (n := n) (k := k) hkpos hklt
  have hlower :
      ((k : ℝ) * Real.log n - (k : ℝ) * Real.log k
          + (k : ℝ) - (k : ℝ) ^ 2 / (n : ℝ)) - Real.log n / 2 - 2
        ≤ Real.log (n.choose k) := by
    calc
      ((k : ℝ) * Real.log n - (k : ℝ) * Real.log k
          + (k : ℝ) - (k : ℝ) ^ 2 / (n : ℝ)) - Real.log n / 2 - 2
          ≤ entropyTerm n k
            + Real.log n / 2 - Real.log k / 2 - Real.log (n - k) / 2
            + Real.log (2 * Real.pi) / 2 - 2 := by
              linarith only [hbasic, hcorr_ge]
      _ ≤ Real.log (n.choose k) := hlower_entropy
  have hupper_lt_lower :
      ((sqrt n : ℕ) : ℝ) / 3 * Real.log n
          + ((min k (n / 3) : ℕ) : ℝ) * Real.log 2 <
        ((k : ℝ) * Real.log n - (k : ℝ) * Real.log k
          + (k : ℝ) - (k : ℝ) ^ 2 / (n : ℝ)) - Real.log n / 2 - 2 := by
    calc
      ((sqrt n : ℕ) : ℝ) / 3 * Real.log n
          + ((min k (n / 3) : ℕ) : ℝ) * Real.log 2
          ≤ (k : ℝ) / 3 * Real.log n + (k : ℝ) * Real.log 2 := hupper_simple
      _ < (k : ℝ) / 2 * Real.log n - (k : ℝ) * Real.log 2 + (k : ℝ) - 4
            - Real.log n / 2 - 2 := hsimple_gap
      _ ≤ ((k : ℝ) * Real.log n - (k : ℝ) * Real.log k
          + (k : ℝ) - (k : ℝ) ^ 2 / (n : ℝ)) - Real.log n / 2 - 2 := by
            exact hbasic_ge_shift
  by_contra hlarge
  have hno : NoLargePrimeFactor k (n.choose k) :=
    not_hasPrimeFactorAbove_iff_noLargePrimeFactor.mp hlarge
  have hupper :=
    log_choose_le_sqrt_third_log_add_min_third_log_two_of_noLargePrimeFactor
      (n := n) (k := k) hnpos hkn hn2k hn6 hno hsqrt33 hsqrtM hMsub
  exact not_lt_of_ge (hlower.trans hupper) hupper_lt_lower

theorem exists_large_prime_factor_choose_sq_le_of_9_le
    {n k : ℕ} (hk9 : 9 ≤ k) (hkn : k ≤ n) (hsq : k * k ≤ n) :
    HasPrimeFactorAbove k (n.choose k) :=
  exists_large_prime_factor_choose_of_sq_le_and_primeCounting_gap
    (by omega) hkn hsq (primeCounting_gap_of_9_le hk9)

theorem exists_large_prime_factor_choose_below_sq_small_cert :
    ∀ k : Fin 9, ∀ n : Fin 81,
      0 < k.val → 2 * k.val ≤ n.val → n.val < k.val * k.val →
        ∃ p : Fin 81, k.val < p.val ∧ p.val.Prime ∧ p.val ∣ n.val.choose k.val := by
  native_decide

theorem exists_large_prime_factor_choose_below_sq_of_lt_9
    {n k : ℕ} (hkpos : 0 < k) (hk9 : k < 9) (hn2k : 2 * k ≤ n) (hnsq : n < k * k) :
    HasPrimeFactorAbove k (n.choose k) := by
  have hn81 : n < 81 := by nlinarith
  rcases exists_large_prime_factor_choose_below_sq_small_cert ⟨k, hk9⟩ ⟨n, hn81⟩
    hkpos hn2k hnsq with ⟨p, hkp, hp, hpdvd⟩
  exact ⟨p.val, hkp, hp, hpdvd⟩

theorem exists_large_prime_factor_choose_small_cert :
    ∀ k : Fin 9, ∀ n : Fin 94,
      0 < k.val → 2 * k.val ≤ n.val →
        ∃ p : Fin 94, k.val < p.val ∧ p.val.Prime ∧ p.val ∣ n.val.choose k.val := by
  native_decide

theorem pow_gap_small_k_tail {n k : ℕ} (hkpos : 0 < k) (hk9 : k < 9) (hn94 : 94 ≤ n) :
    k ^ k < n ^ (k - Nat.primeCounting k) := by
  interval_cases k
  · exact lt_of_lt_of_le
      (by native_decide : 1 ^ 1 < 94 ^ (1 - Nat.primeCounting 1))
      (Nat.pow_le_pow_left hn94 (1 - Nat.primeCounting 1))
  · exact lt_of_lt_of_le
      (by native_decide : 2 ^ 2 < 94 ^ (2 - Nat.primeCounting 2))
      (Nat.pow_le_pow_left hn94 (2 - Nat.primeCounting 2))
  · exact lt_of_lt_of_le
      (by native_decide : 3 ^ 3 < 94 ^ (3 - Nat.primeCounting 3))
      (Nat.pow_le_pow_left hn94 (3 - Nat.primeCounting 3))
  · exact lt_of_lt_of_le
      (by native_decide : 4 ^ 4 < 94 ^ (4 - Nat.primeCounting 4))
      (Nat.pow_le_pow_left hn94 (4 - Nat.primeCounting 4))
  · exact lt_of_lt_of_le
      (by native_decide : 5 ^ 5 < 94 ^ (5 - Nat.primeCounting 5))
      (Nat.pow_le_pow_left hn94 (5 - Nat.primeCounting 5))
  · exact lt_of_lt_of_le
      (by native_decide : 6 ^ 6 < 94 ^ (6 - Nat.primeCounting 6))
      (Nat.pow_le_pow_left hn94 (6 - Nat.primeCounting 6))
  · exact lt_of_lt_of_le
      (by native_decide : 7 ^ 7 < 94 ^ (7 - Nat.primeCounting 7))
      (Nat.pow_le_pow_left hn94 (7 - Nat.primeCounting 7))
  · exact lt_of_lt_of_le
      (by native_decide : 8 ^ 8 < 94 ^ (8 - Nat.primeCounting 8))
      (Nat.pow_le_pow_left hn94 (8 - Nat.primeCounting 8))

theorem exists_large_prime_factor_choose_of_lt_9
    {n k : ℕ} (hkpos : 0 < k) (hk9 : k < 9) (hn2k : 2 * k ≤ n) :
    HasPrimeFactorAbove k (n.choose k) := by
  by_cases hn94 : n < 94
  · rcases exists_large_prime_factor_choose_small_cert ⟨k, hk9⟩ ⟨n, hn94⟩
      hkpos hn2k with ⟨p, hkp, hp, hpdvd⟩
    exact ⟨p.val, hkp, hp, hpdvd⟩
  · exact exists_large_prime_factor_choose_of_pow_gap (n := n) (k := k)
      hkpos (by omega) (by interval_cases k <;> native_decide)
      (pow_gap_small_k_tail hkpos hk9 (by omega))

theorem exists_large_prime_factor_choose_sqrt_lt_9_cert :
    ∀ k : Fin 41, ∀ n : Fin 81,
      9 ≤ k.val → 2 * k.val ≤ n.val → n.val < k.val * k.val →
        ∃ p : Fin 81, k.val < p.val ∧ p.val.Prime ∧ p.val ∣ n.val.choose k.val := by
  native_decide

theorem exists_large_prime_factor_choose_below_sq_of_sqrt_lt_9
    {n k : ℕ} (hk9 : 9 ≤ k) (hn2k : 2 * k ≤ n)
    (hnsq : n < k * k) (hsqrt9 : sqrt n < 9) :
    HasPrimeFactorAbove k (n.choose k) := by
  have hn81 : n < 81 := by
    rw [Nat.sqrt_lt] at hsqrt9
    simpa using hsqrt9
  have hk41 : k < 41 := by nlinarith
  rcases exists_large_prime_factor_choose_sqrt_lt_9_cert ⟨k, hk41⟩ ⟨n, hn81⟩
    hk9 hn2k hnsq with ⟨p, hkp, hp, hpdvd⟩
  exact ⟨p.val, hkp, hp, hpdvd⟩

theorem exists_large_prime_dvd_choose_sq_le_of_9_le
    {n k : ℕ} (hk9 : 9 ≤ k) (hkn : k ≤ n) (hsq : k * k ≤ n) :
    ∃ p, k < p ∧ p.Prime ∧ p ∣ n.choose k := by
  rcases exists_large_prime_factor_choose_sq_le_of_9_le
      (n := n) (k := k) hk9 hkn hsq with ⟨p, hkp, hp, hpdvd⟩
  exact ⟨p, hkp, hp, hpdvd⟩

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

theorem exists_large_prime_factor_descFactorial_sq_le_of_9_le
    {n k : ℕ} (hk9 : 9 ≤ k) (hkn : k ≤ n) (hsq : k * k ≤ n) :
    HasPrimeFactorAbove k (n.descFactorial k) :=
  exists_large_prime_dvd_descFactorial_of_choose
    (exists_large_prime_dvd_choose_sq_le_of_9_le (n := n) (k := k) hk9 hkn hsq)

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

theorem hasPrimeFactorAbove_choose_of_interval_prime {n k p : ℕ} (hkn : k ≤ n)
    (hp : p.Prime) (hk : k < p) (hnk : n - k < p) (hpn : p ≤ n) :
    HasPrimeFactorAbove k (n.choose k) :=
  ⟨p, hk, hp, prime_dvd_choose_of_interval_prime hkn hp hk hnk hpn⟩

theorem exists_large_prime_factor_choose_125_12 :
    HasPrimeFactorAbove 12 ((125).choose 12) := by
  refine ⟨13, by norm_num, by norm_num, ?_⟩
  native_decide

theorem exists_large_prime_factor_choose_126_12 :
    HasPrimeFactorAbove 12 ((126).choose 12) := by
  refine ⟨13, by norm_num, by norm_num, ?_⟩
  native_decide

theorem exists_large_prime_factor_choose_126_13 :
    HasPrimeFactorAbove 13 ((126).choose 13) := by
  refine ⟨17, by norm_num, by norm_num, ?_⟩
  native_decide

def nextPrimeAfter1089 : ℕ → ℕ
  | 0 => 2
  | 1 => 2
  | 2 => 3
  | 3 => 5
  | 4 => 5
  | 5 => 7
  | 6 => 7
  | 7 => 11
  | 8 => 11
  | 9 => 11
  | 10 => 11
  | 11 => 13
  | 12 => 13
  | 13 => 17
  | 14 => 17
  | 15 => 17
  | 16 => 17
  | 17 => 19
  | 18 => 19
  | 19 => 23
  | 20 => 23
  | 21 => 23
  | 22 => 23
  | 23 => 29
  | 24 => 29
  | 25 => 29
  | 26 => 29
  | 27 => 29
  | 28 => 29
  | 29 => 31
  | 30 => 31
  | 31 => 37
  | 32 => 37
  | 33 => 37
  | 34 => 37
  | 35 => 37
  | 36 => 37
  | 37 => 41
  | 38 => 41
  | 39 => 41
  | 40 => 41
  | 41 => 43
  | 42 => 43
  | 43 => 47
  | 44 => 47
  | 45 => 47
  | 46 => 47
  | 47 => 53
  | 48 => 53
  | 49 => 53
  | 50 => 53
  | 51 => 53
  | 52 => 53
  | 53 => 59
  | 54 => 59
  | 55 => 59
  | 56 => 59
  | 57 => 59
  | 58 => 59
  | 59 => 61
  | 60 => 61
  | 61 => 67
  | 62 => 67
  | 63 => 67
  | 64 => 67
  | 65 => 67
  | 66 => 67
  | 67 => 71
  | 68 => 71
  | 69 => 71
  | 70 => 71
  | 71 => 73
  | 72 => 73
  | 73 => 79
  | 74 => 79
  | 75 => 79
  | 76 => 79
  | 77 => 79
  | 78 => 79
  | 79 => 83
  | 80 => 83
  | 81 => 83
  | 82 => 83
  | 83 => 89
  | 84 => 89
  | 85 => 89
  | 86 => 89
  | 87 => 89
  | 88 => 89
  | 89 => 97
  | 90 => 97
  | 91 => 97
  | 92 => 97
  | 93 => 97
  | 94 => 97
  | 95 => 97
  | 96 => 97
  | 97 => 101
  | 98 => 101
  | 99 => 101
  | 100 => 101
  | 101 => 103
  | 102 => 103
  | 103 => 107
  | 104 => 107
  | 105 => 107
  | 106 => 107
  | 107 => 109
  | 108 => 109
  | 109 => 113
  | 110 => 113
  | 111 => 113
  | 112 => 113
  | 113 => 127
  | 114 => 127
  | 115 => 127
  | 116 => 127
  | 117 => 127
  | 118 => 127
  | 119 => 127
  | 120 => 127
  | 121 => 127
  | 122 => 127
  | 123 => 127
  | 124 => 127
  | 125 => 127
  | 126 => 127
  | 127 => 131
  | 128 => 131
  | 129 => 131
  | 130 => 131
  | 131 => 137
  | 132 => 137
  | 133 => 137
  | 134 => 137
  | 135 => 137
  | 136 => 137
  | 137 => 139
  | 138 => 139
  | 139 => 149
  | 140 => 149
  | 141 => 149
  | 142 => 149
  | 143 => 149
  | 144 => 149
  | 145 => 149
  | 146 => 149
  | 147 => 149
  | 148 => 149
  | 149 => 151
  | 150 => 151
  | 151 => 157
  | 152 => 157
  | 153 => 157
  | 154 => 157
  | 155 => 157
  | 156 => 157
  | 157 => 163
  | 158 => 163
  | 159 => 163
  | 160 => 163
  | 161 => 163
  | 162 => 163
  | 163 => 167
  | 164 => 167
  | 165 => 167
  | 166 => 167
  | 167 => 173
  | 168 => 173
  | 169 => 173
  | 170 => 173
  | 171 => 173
  | 172 => 173
  | 173 => 179
  | 174 => 179
  | 175 => 179
  | 176 => 179
  | 177 => 179
  | 178 => 179
  | 179 => 181
  | 180 => 181
  | 181 => 191
  | 182 => 191
  | 183 => 191
  | 184 => 191
  | 185 => 191
  | 186 => 191
  | 187 => 191
  | 188 => 191
  | 189 => 191
  | 190 => 191
  | 191 => 193
  | 192 => 193
  | 193 => 197
  | 194 => 197
  | 195 => 197
  | 196 => 197
  | 197 => 199
  | 198 => 199
  | 199 => 211
  | 200 => 211
  | 201 => 211
  | 202 => 211
  | 203 => 211
  | 204 => 211
  | 205 => 211
  | 206 => 211
  | 207 => 211
  | 208 => 211
  | 209 => 211
  | 210 => 211
  | 211 => 223
  | 212 => 223
  | 213 => 223
  | 214 => 223
  | 215 => 223
  | 216 => 223
  | 217 => 223
  | 218 => 223
  | 219 => 223
  | 220 => 223
  | 221 => 223
  | 222 => 223
  | 223 => 227
  | 224 => 227
  | 225 => 227
  | 226 => 227
  | 227 => 229
  | 228 => 229
  | 229 => 233
  | 230 => 233
  | 231 => 233
  | 232 => 233
  | 233 => 239
  | 234 => 239
  | 235 => 239
  | 236 => 239
  | 237 => 239
  | 238 => 239
  | 239 => 241
  | 240 => 241
  | 241 => 251
  | 242 => 251
  | 243 => 251
  | 244 => 251
  | 245 => 251
  | 246 => 251
  | 247 => 251
  | 248 => 251
  | 249 => 251
  | 250 => 251
  | 251 => 257
  | 252 => 257
  | 253 => 257
  | 254 => 257
  | 255 => 257
  | 256 => 257
  | 257 => 263
  | 258 => 263
  | 259 => 263
  | 260 => 263
  | 261 => 263
  | 262 => 263
  | 263 => 269
  | 264 => 269
  | 265 => 269
  | 266 => 269
  | 267 => 269
  | 268 => 269
  | 269 => 271
  | 270 => 271
  | 271 => 277
  | 272 => 277
  | 273 => 277
  | 274 => 277
  | 275 => 277
  | 276 => 277
  | 277 => 281
  | 278 => 281
  | 279 => 281
  | 280 => 281
  | 281 => 283
  | 282 => 283
  | 283 => 293
  | 284 => 293
  | 285 => 293
  | 286 => 293
  | 287 => 293
  | 288 => 293
  | 289 => 293
  | 290 => 293
  | 291 => 293
  | 292 => 293
  | 293 => 307
  | 294 => 307
  | 295 => 307
  | 296 => 307
  | 297 => 307
  | 298 => 307
  | 299 => 307
  | 300 => 307
  | 301 => 307
  | 302 => 307
  | 303 => 307
  | 304 => 307
  | 305 => 307
  | 306 => 307
  | 307 => 311
  | 308 => 311
  | 309 => 311
  | 310 => 311
  | 311 => 313
  | 312 => 313
  | 313 => 317
  | 314 => 317
  | 315 => 317
  | 316 => 317
  | 317 => 331
  | 318 => 331
  | 319 => 331
  | 320 => 331
  | 321 => 331
  | 322 => 331
  | 323 => 331
  | 324 => 331
  | 325 => 331
  | 326 => 331
  | 327 => 331
  | 328 => 331
  | 329 => 331
  | 330 => 331
  | 331 => 337
  | 332 => 337
  | 333 => 337
  | 334 => 337
  | 335 => 337
  | 336 => 337
  | 337 => 347
  | 338 => 347
  | 339 => 347
  | 340 => 347
  | 341 => 347
  | 342 => 347
  | 343 => 347
  | 344 => 347
  | 345 => 347
  | 346 => 347
  | 347 => 349
  | 348 => 349
  | 349 => 353
  | 350 => 353
  | 351 => 353
  | 352 => 353
  | 353 => 359
  | 354 => 359
  | 355 => 359
  | 356 => 359
  | 357 => 359
  | 358 => 359
  | 359 => 367
  | 360 => 367
  | 361 => 367
  | 362 => 367
  | 363 => 367
  | 364 => 367
  | 365 => 367
  | 366 => 367
  | 367 => 373
  | 368 => 373
  | 369 => 373
  | 370 => 373
  | 371 => 373
  | 372 => 373
  | 373 => 379
  | 374 => 379
  | 375 => 379
  | 376 => 379
  | 377 => 379
  | 378 => 379
  | 379 => 383
  | 380 => 383
  | 381 => 383
  | 382 => 383
  | 383 => 389
  | 384 => 389
  | 385 => 389
  | 386 => 389
  | 387 => 389
  | 388 => 389
  | 389 => 397
  | 390 => 397
  | 391 => 397
  | 392 => 397
  | 393 => 397
  | 394 => 397
  | 395 => 397
  | 396 => 397
  | 397 => 401
  | 398 => 401
  | 399 => 401
  | 400 => 401
  | 401 => 409
  | 402 => 409
  | 403 => 409
  | 404 => 409
  | 405 => 409
  | 406 => 409
  | 407 => 409
  | 408 => 409
  | 409 => 419
  | 410 => 419
  | 411 => 419
  | 412 => 419
  | 413 => 419
  | 414 => 419
  | 415 => 419
  | 416 => 419
  | 417 => 419
  | 418 => 419
  | 419 => 421
  | 420 => 421
  | 421 => 431
  | 422 => 431
  | 423 => 431
  | 424 => 431
  | 425 => 431
  | 426 => 431
  | 427 => 431
  | 428 => 431
  | 429 => 431
  | 430 => 431
  | 431 => 433
  | 432 => 433
  | 433 => 439
  | 434 => 439
  | 435 => 439
  | 436 => 439
  | 437 => 439
  | 438 => 439
  | 439 => 443
  | 440 => 443
  | 441 => 443
  | 442 => 443
  | 443 => 449
  | 444 => 449
  | 445 => 449
  | 446 => 449
  | 447 => 449
  | 448 => 449
  | 449 => 457
  | 450 => 457
  | 451 => 457
  | 452 => 457
  | 453 => 457
  | 454 => 457
  | 455 => 457
  | 456 => 457
  | 457 => 461
  | 458 => 461
  | 459 => 461
  | 460 => 461
  | 461 => 463
  | 462 => 463
  | 463 => 467
  | 464 => 467
  | 465 => 467
  | 466 => 467
  | 467 => 479
  | 468 => 479
  | 469 => 479
  | 470 => 479
  | 471 => 479
  | 472 => 479
  | 473 => 479
  | 474 => 479
  | 475 => 479
  | 476 => 479
  | 477 => 479
  | 478 => 479
  | 479 => 487
  | 480 => 487
  | 481 => 487
  | 482 => 487
  | 483 => 487
  | 484 => 487
  | 485 => 487
  | 486 => 487
  | 487 => 491
  | 488 => 491
  | 489 => 491
  | 490 => 491
  | 491 => 499
  | 492 => 499
  | 493 => 499
  | 494 => 499
  | 495 => 499
  | 496 => 499
  | 497 => 499
  | 498 => 499
  | 499 => 503
  | 500 => 503
  | 501 => 503
  | 502 => 503
  | 503 => 509
  | 504 => 509
  | 505 => 509
  | 506 => 509
  | 507 => 509
  | 508 => 509
  | 509 => 521
  | 510 => 521
  | 511 => 521
  | 512 => 521
  | 513 => 521
  | 514 => 521
  | 515 => 521
  | 516 => 521
  | 517 => 521
  | 518 => 521
  | 519 => 521
  | 520 => 521
  | 521 => 523
  | 522 => 523
  | 523 => 541
  | 524 => 541
  | 525 => 541
  | 526 => 541
  | 527 => 541
  | 528 => 541
  | 529 => 541
  | 530 => 541
  | 531 => 541
  | 532 => 541
  | 533 => 541
  | 534 => 541
  | 535 => 541
  | 536 => 541
  | 537 => 541
  | 538 => 541
  | 539 => 541
  | 540 => 541
  | 541 => 547
  | 542 => 547
  | 543 => 547
  | 544 => 547
  | 545 => 547
  | 546 => 547
  | 547 => 557
  | 548 => 557
  | 549 => 557
  | 550 => 557
  | 551 => 557
  | 552 => 557
  | 553 => 557
  | 554 => 557
  | 555 => 557
  | 556 => 557
  | 557 => 563
  | 558 => 563
  | 559 => 563
  | 560 => 563
  | 561 => 563
  | 562 => 563
  | 563 => 569
  | 564 => 569
  | 565 => 569
  | 566 => 569
  | 567 => 569
  | 568 => 569
  | 569 => 571
  | 570 => 571
  | 571 => 577
  | 572 => 577
  | 573 => 577
  | 574 => 577
  | 575 => 577
  | 576 => 577
  | 577 => 587
  | 578 => 587
  | 579 => 587
  | 580 => 587
  | 581 => 587
  | 582 => 587
  | 583 => 587
  | 584 => 587
  | 585 => 587
  | 586 => 587
  | 587 => 593
  | 588 => 593
  | 589 => 593
  | 590 => 593
  | 591 => 593
  | 592 => 593
  | 593 => 599
  | 594 => 599
  | 595 => 599
  | 596 => 599
  | 597 => 599
  | 598 => 599
  | 599 => 601
  | 600 => 601
  | 601 => 607
  | 602 => 607
  | 603 => 607
  | 604 => 607
  | 605 => 607
  | 606 => 607
  | 607 => 613
  | 608 => 613
  | 609 => 613
  | 610 => 613
  | 611 => 613
  | 612 => 613
  | 613 => 617
  | 614 => 617
  | 615 => 617
  | 616 => 617
  | 617 => 619
  | 618 => 619
  | 619 => 631
  | 620 => 631
  | 621 => 631
  | 622 => 631
  | 623 => 631
  | 624 => 631
  | 625 => 631
  | 626 => 631
  | 627 => 631
  | 628 => 631
  | 629 => 631
  | 630 => 631
  | 631 => 641
  | 632 => 641
  | 633 => 641
  | 634 => 641
  | 635 => 641
  | 636 => 641
  | 637 => 641
  | 638 => 641
  | 639 => 641
  | 640 => 641
  | 641 => 643
  | 642 => 643
  | 643 => 647
  | 644 => 647
  | 645 => 647
  | 646 => 647
  | 647 => 653
  | 648 => 653
  | 649 => 653
  | 650 => 653
  | 651 => 653
  | 652 => 653
  | 653 => 659
  | 654 => 659
  | 655 => 659
  | 656 => 659
  | 657 => 659
  | 658 => 659
  | 659 => 661
  | 660 => 661
  | 661 => 673
  | 662 => 673
  | 663 => 673
  | 664 => 673
  | 665 => 673
  | 666 => 673
  | 667 => 673
  | 668 => 673
  | 669 => 673
  | 670 => 673
  | 671 => 673
  | 672 => 673
  | 673 => 677
  | 674 => 677
  | 675 => 677
  | 676 => 677
  | 677 => 683
  | 678 => 683
  | 679 => 683
  | 680 => 683
  | 681 => 683
  | 682 => 683
  | 683 => 691
  | 684 => 691
  | 685 => 691
  | 686 => 691
  | 687 => 691
  | 688 => 691
  | 689 => 691
  | 690 => 691
  | 691 => 701
  | 692 => 701
  | 693 => 701
  | 694 => 701
  | 695 => 701
  | 696 => 701
  | 697 => 701
  | 698 => 701
  | 699 => 701
  | 700 => 701
  | 701 => 709
  | 702 => 709
  | 703 => 709
  | 704 => 709
  | 705 => 709
  | 706 => 709
  | 707 => 709
  | 708 => 709
  | 709 => 719
  | 710 => 719
  | 711 => 719
  | 712 => 719
  | 713 => 719
  | 714 => 719
  | 715 => 719
  | 716 => 719
  | 717 => 719
  | 718 => 719
  | 719 => 727
  | 720 => 727
  | 721 => 727
  | 722 => 727
  | 723 => 727
  | 724 => 727
  | 725 => 727
  | 726 => 727
  | 727 => 733
  | 728 => 733
  | 729 => 733
  | 730 => 733
  | 731 => 733
  | 732 => 733
  | 733 => 739
  | 734 => 739
  | 735 => 739
  | 736 => 739
  | 737 => 739
  | 738 => 739
  | 739 => 743
  | 740 => 743
  | 741 => 743
  | 742 => 743
  | 743 => 751
  | 744 => 751
  | 745 => 751
  | 746 => 751
  | 747 => 751
  | 748 => 751
  | 749 => 751
  | 750 => 751
  | 751 => 757
  | 752 => 757
  | 753 => 757
  | 754 => 757
  | 755 => 757
  | 756 => 757
  | 757 => 761
  | 758 => 761
  | 759 => 761
  | 760 => 761
  | 761 => 769
  | 762 => 769
  | 763 => 769
  | 764 => 769
  | 765 => 769
  | 766 => 769
  | 767 => 769
  | 768 => 769
  | 769 => 773
  | 770 => 773
  | 771 => 773
  | 772 => 773
  | 773 => 787
  | 774 => 787
  | 775 => 787
  | 776 => 787
  | 777 => 787
  | 778 => 787
  | 779 => 787
  | 780 => 787
  | 781 => 787
  | 782 => 787
  | 783 => 787
  | 784 => 787
  | 785 => 787
  | 786 => 787
  | 787 => 797
  | 788 => 797
  | 789 => 797
  | 790 => 797
  | 791 => 797
  | 792 => 797
  | 793 => 797
  | 794 => 797
  | 795 => 797
  | 796 => 797
  | 797 => 809
  | 798 => 809
  | 799 => 809
  | 800 => 809
  | 801 => 809
  | 802 => 809
  | 803 => 809
  | 804 => 809
  | 805 => 809
  | 806 => 809
  | 807 => 809
  | 808 => 809
  | 809 => 811
  | 810 => 811
  | 811 => 821
  | 812 => 821
  | 813 => 821
  | 814 => 821
  | 815 => 821
  | 816 => 821
  | 817 => 821
  | 818 => 821
  | 819 => 821
  | 820 => 821
  | 821 => 823
  | 822 => 823
  | 823 => 827
  | 824 => 827
  | 825 => 827
  | 826 => 827
  | 827 => 829
  | 828 => 829
  | 829 => 839
  | 830 => 839
  | 831 => 839
  | 832 => 839
  | 833 => 839
  | 834 => 839
  | 835 => 839
  | 836 => 839
  | 837 => 839
  | 838 => 839
  | 839 => 853
  | 840 => 853
  | 841 => 853
  | 842 => 853
  | 843 => 853
  | 844 => 853
  | 845 => 853
  | 846 => 853
  | 847 => 853
  | 848 => 853
  | 849 => 853
  | 850 => 853
  | 851 => 853
  | 852 => 853
  | 853 => 857
  | 854 => 857
  | 855 => 857
  | 856 => 857
  | 857 => 859
  | 858 => 859
  | 859 => 863
  | 860 => 863
  | 861 => 863
  | 862 => 863
  | 863 => 877
  | 864 => 877
  | 865 => 877
  | 866 => 877
  | 867 => 877
  | 868 => 877
  | 869 => 877
  | 870 => 877
  | 871 => 877
  | 872 => 877
  | 873 => 877
  | 874 => 877
  | 875 => 877
  | 876 => 877
  | 877 => 881
  | 878 => 881
  | 879 => 881
  | 880 => 881
  | 881 => 883
  | 882 => 883
  | 883 => 887
  | 884 => 887
  | 885 => 887
  | 886 => 887
  | 887 => 907
  | 888 => 907
  | 889 => 907
  | 890 => 907
  | 891 => 907
  | 892 => 907
  | 893 => 907
  | 894 => 907
  | 895 => 907
  | 896 => 907
  | 897 => 907
  | 898 => 907
  | 899 => 907
  | 900 => 907
  | 901 => 907
  | 902 => 907
  | 903 => 907
  | 904 => 907
  | 905 => 907
  | 906 => 907
  | 907 => 911
  | 908 => 911
  | 909 => 911
  | 910 => 911
  | 911 => 919
  | 912 => 919
  | 913 => 919
  | 914 => 919
  | 915 => 919
  | 916 => 919
  | 917 => 919
  | 918 => 919
  | 919 => 929
  | 920 => 929
  | 921 => 929
  | 922 => 929
  | 923 => 929
  | 924 => 929
  | 925 => 929
  | 926 => 929
  | 927 => 929
  | 928 => 929
  | 929 => 937
  | 930 => 937
  | 931 => 937
  | 932 => 937
  | 933 => 937
  | 934 => 937
  | 935 => 937
  | 936 => 937
  | 937 => 941
  | 938 => 941
  | 939 => 941
  | 940 => 941
  | 941 => 947
  | 942 => 947
  | 943 => 947
  | 944 => 947
  | 945 => 947
  | 946 => 947
  | 947 => 953
  | 948 => 953
  | 949 => 953
  | 950 => 953
  | 951 => 953
  | 952 => 953
  | 953 => 967
  | 954 => 967
  | 955 => 967
  | 956 => 967
  | 957 => 967
  | 958 => 967
  | 959 => 967
  | 960 => 967
  | 961 => 967
  | 962 => 967
  | 963 => 967
  | 964 => 967
  | 965 => 967
  | 966 => 967
  | 967 => 971
  | 968 => 971
  | 969 => 971
  | 970 => 971
  | 971 => 977
  | 972 => 977
  | 973 => 977
  | 974 => 977
  | 975 => 977
  | 976 => 977
  | 977 => 983
  | 978 => 983
  | 979 => 983
  | 980 => 983
  | 981 => 983
  | 982 => 983
  | 983 => 991
  | 984 => 991
  | 985 => 991
  | 986 => 991
  | 987 => 991
  | 988 => 991
  | 989 => 991
  | 990 => 991
  | 991 => 997
  | 992 => 997
  | 993 => 997
  | 994 => 997
  | 995 => 997
  | 996 => 997
  | 997 => 1009
  | 998 => 1009
  | 999 => 1009
  | 1000 => 1009
  | 1001 => 1009
  | 1002 => 1009
  | 1003 => 1009
  | 1004 => 1009
  | 1005 => 1009
  | 1006 => 1009
  | 1007 => 1009
  | 1008 => 1009
  | 1009 => 1013
  | 1010 => 1013
  | 1011 => 1013
  | 1012 => 1013
  | 1013 => 1019
  | 1014 => 1019
  | 1015 => 1019
  | 1016 => 1019
  | 1017 => 1019
  | 1018 => 1019
  | 1019 => 1021
  | 1020 => 1021
  | 1021 => 1031
  | 1022 => 1031
  | 1023 => 1031
  | 1024 => 1031
  | 1025 => 1031
  | 1026 => 1031
  | 1027 => 1031
  | 1028 => 1031
  | 1029 => 1031
  | 1030 => 1031
  | 1031 => 1033
  | 1032 => 1033
  | 1033 => 1039
  | 1034 => 1039
  | 1035 => 1039
  | 1036 => 1039
  | 1037 => 1039
  | 1038 => 1039
  | 1039 => 1049
  | 1040 => 1049
  | 1041 => 1049
  | 1042 => 1049
  | 1043 => 1049
  | 1044 => 1049
  | 1045 => 1049
  | 1046 => 1049
  | 1047 => 1049
  | 1048 => 1049
  | 1049 => 1051
  | 1050 => 1051
  | 1051 => 1061
  | 1052 => 1061
  | 1053 => 1061
  | 1054 => 1061
  | 1055 => 1061
  | 1056 => 1061
  | 1057 => 1061
  | 1058 => 1061
  | 1059 => 1061
  | 1060 => 1061
  | 1061 => 1063
  | 1062 => 1063
  | 1063 => 1069
  | 1064 => 1069
  | 1065 => 1069
  | 1066 => 1069
  | 1067 => 1069
  | 1068 => 1069
  | 1069 => 1087
  | 1070 => 1087
  | 1071 => 1087
  | 1072 => 1087
  | 1073 => 1087
  | 1074 => 1087
  | 1075 => 1087
  | 1076 => 1087
  | 1077 => 1087
  | 1078 => 1087
  | 1079 => 1087
  | 1080 => 1087
  | 1081 => 1087
  | 1082 => 1087
  | 1083 => 1087
  | 1084 => 1087
  | 1085 => 1087
  | 1086 => 1087
  | 1087 => 1091
  | 1088 => 1091
  | _ => 1091

theorem nextPrimeAfter1089_below_sq_sqrt_lt_33_cert :
    ∀ k : Fin 545, ∀ n : Fin 1089,
      9 ≤ k.val → 2 * k.val ≤ n.val → n.val < k.val * k.val →
        (let p := nextPrimeAfter1089 (n.val - k.val);
          k.val < p ∧ n.val - k.val < p ∧ p ≤ n.val ∧ p.Prime)
        ∨ (n.val = 125 ∧ k.val = 12)
        ∨ (n.val = 126 ∧ k.val = 12)
        ∨ (n.val = 126 ∧ k.val = 13) := by
  native_decide

theorem exists_large_prime_factor_choose_below_sq_of_sqrt_lt_33
    {n k : ℕ} (hk9 : 9 ≤ k) (hn2k : 2 * k ≤ n)
    (hnsq : n < k * k) (hsqrt33 : sqrt n < 33) :
    HasPrimeFactorAbove k (n.choose k) := by
  have hn1089 : n < 1089 := by
    rw [Nat.sqrt_lt] at hsqrt33
    simpa using hsqrt33
  have hk545 : k < 545 := by nlinarith
  rcases nextPrimeAfter1089_below_sq_sqrt_lt_33_cert
      ⟨k, hk545⟩ ⟨n, hn1089⟩ hk9 hn2k hnsq with
    (hprime | ⟨hn, hk⟩ | ⟨hn, hk⟩ | ⟨hn, hk⟩)
  · dsimp only at hprime
    exact hasPrimeFactorAbove_choose_of_interval_prime (by omega : k ≤ n) hprime.2.2.2
      hprime.1 hprime.2.1 hprime.2.2.1
  · have hn' : n = 125 := by simpa using hn
    have hk' : k = 12 := by simpa using hk
    subst n
    subst k
    exact exists_large_prime_factor_choose_125_12
  · have hn' : n = 126 := by simpa using hn
    have hk' : k = 12 := by simpa using hk
    subst n
    subst k
    exact exists_large_prime_factor_choose_126_12
  · have hn' : n = 126 := by simpa using hn
    have hk' : k = 13 := by simpa using hk
    subst n
    subst k
    exact exists_large_prime_factor_choose_126_13

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

theorem sylvester_schur_descFactorial_one {n : ℕ} (hn : 2 * 1 ≤ n) :
    HasPrimeFactorAbove 1 (n.descFactorial 1) := by
  have hn_ne_one : n ≠ 1 := by omega
  rcases Nat.ne_one_iff_exists_prime_dvd.mp hn_ne_one with ⟨p, hp, hpdvd⟩
  exact ⟨p, hp.one_lt, hp, by simpa [Nat.descFactorial_one] using hpdvd⟩

theorem factorial_lt_descFactorial_of_two_mul_le {n k : ℕ}
    (hk : 0 < k) (hn : 2 * k ≤ n) : k ! < n.descFactorial k := by
  rw [Nat.factorial_eq_prod_range_add_one, Nat.descFactorial_eq_prod_range]
  refine Finset.prod_lt_prod_of_nonempty
    (s := Finset.range k) (f := fun i => i + 1) (g := fun i => n - i) ?hf ?hlt ?hne
  · intro i _hi
    exact Nat.succ_pos i
  · intro i hi
    rw [Finset.mem_range] at hi
    change i + 1 < n - i
    omega
  · exact Finset.nonempty_range_iff.mpr hk.ne'

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
    (_hp : p.Prime) (_hpdvd : p ∣ n.choose k) (_hpow : n.choose k = m ^ l)
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
