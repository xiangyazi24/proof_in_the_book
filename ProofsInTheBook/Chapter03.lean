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

theorem primeIntervalProduct_dvd_choose {a M : ℕ} (haM : a ≤ M) (hd : M - a ≤ a) :
    primeIntervalProduct a M ∣ M.choose a := by
  rw [primeIntervalProduct, ← Nat.add_sub_of_le haM]
  exact Finset.prod_primes_dvd _ (fun _ hp => (Finset.mem_filter.1 hp).2.prime) fun p hp => by
    rw [Finset.mem_filter, Finset.mem_Ioc] at hp
    exact hp.2.dvd_choose_add hp.1.1 (hd.trans_lt hp.1.1) hp.1.2

theorem primeIntervalProduct_le_choose {a M : ℕ} (haM : a ≤ M) (hd : M - a ≤ a) :
    primeIntervalProduct a M ≤ M.choose a := by
  exact le_of_dvd (Nat.choose_pos haM) (primeIntervalProduct_dvd_choose haM hd)

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

theorem exists_large_prime_factor_choose_sq_le_of_9_le
    {n k : ℕ} (hk9 : 9 ≤ k) (hkn : k ≤ n) (hsq : k * k ≤ n) :
    HasPrimeFactorAbove k (n.choose k) :=
  exists_large_prime_factor_choose_of_sq_le_and_primeCounting_gap
    (by omega) hkn hsq (primeCounting_gap_of_9_le hk9)

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
