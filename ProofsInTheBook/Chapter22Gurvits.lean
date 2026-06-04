import Mathlib
import ProofsInTheBook.Chapter22

/-!
# Chapter 22 (van der Waerden permanent bound) — Gurvits capacity, algebraic core

The Gurvits capacity proof reduces `perm(A) ≥ n!/nⁿ` (for doubly stochastic `A`) to a chain of
capacity inequalities with reduction constant `G(k) = ((k-1)/k)^{k-1}`. The product of these
constants telescopes to exactly `n!/nⁿ` — that is the algebraic heart proved here. Blueprint:
`HANDOFF/CH22_GURVITS_CAPACITY.md`.
-/

namespace ProofsInTheBook.Chapter22Gurvits

open scoped BigOperators
open ProofsInTheBook.Chapter22

noncomputable section

/-- Gurvits capacity-reduction constant `G(k) = ((k-1)/k)^{k-1}`, with `G(0)=G(1)=1`. -/
noncomputable def G (k : ℕ) : ℝ := ((k - 1 : ℝ) / (k : ℝ)) ^ (k - 1)

@[simp] lemma G_one : G 1 = 1 := by simp [G]

@[simp] lemma G_zero : G 0 = 1 := by simp [G]

/-- For `m ≥ 1`, `G(m+1) = (m/(m+1))^m`. -/
lemma G_succ (m : ℕ) : G (m + 1) = ((m : ℝ) / (m + 1 : ℝ)) ^ m := by
  simp only [G, Nat.add_sub_cancel]
  norm_num

/-- **The Gurvits product telescopes to `n!/nⁿ`.**
`∏_{m=2}^{n} G(m) = n! / nⁿ`. -/
theorem gurvits_product_telescopes (n : ℕ) (hn : 1 ≤ n) :
    ∏ m ∈ Finset.Icc 2 n, G m = (n.factorial : ℝ) / (n : ℝ) ^ n := by
  induction n with
  | zero => omega
  | succ n ih =>
      rcases Nat.lt_or_ge n 1 with hn1 | hn1
      · -- n = 0, so n+1 = 1: empty product, RHS = 1!/1 = 1
        interval_cases n
        simp
      · -- n ≥ 1: peel off the top factor G(n+1)
        rw [Finset.prod_Icc_succ_top (by omega : 2 ≤ n + 1), ih hn1, G_succ]
        have hnpos : (0 : ℝ) < n := by exact_mod_cast hn1
        have hn1pos : (0 : ℝ) < (n : ℝ) + 1 := by positivity
        rw [div_pow]
        rw [Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
        field_simp
        ring

/-!
### The AM-GM product bound (key inequality of the univariate Gurvits step)

For nonnegative `λ` and `t`, `∏ᵢ (1 + λᵢ t) ≤ (1 + (Σλ) t / k)^k`. This is AM-GM applied to the
`k` factors `1 + λᵢ t`, and it is the inequality that, evaluated at the optimal `t`, yields the
Gurvits capacity-reduction constant `G(k) = ((k-1)/k)^{k-1}`.
-/

/-- AM-GM: `∏ᵢ (1 + λᵢ t) ≤ (1 + (Σλ) t / k)^k` for nonnegative `λ`, `t`. -/
lemma prod_one_add_mul_le {k : ℕ} (hk : 1 ≤ k) (lam : Fin k → ℝ)
    (hlam : ∀ i, 0 ≤ lam i) (t : ℝ) (ht : 0 ≤ t) :
    ∏ i, (1 + lam i * t) ≤ (1 + (∑ i, lam i) * t / k) ^ k := by
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  set y : Fin k → ℝ := fun i => 1 + lam i * t with hy_def
  have hy : ∀ i ∈ (Finset.univ : Finset (Fin k)), 0 ≤ y i := by
    intro i _; have : 0 ≤ lam i * t := mul_nonneg (hlam i) ht; simp only [hy_def]; linarith
  have hw : ∀ i ∈ (Finset.univ : Finset (Fin k)), 0 ≤ ((k : ℝ)⁻¹) := by
    intro i _; positivity
  have hw' : ∑ _i : Fin k, ((k : ℝ)⁻¹) = 1 := by
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    field_simp
  have hgeom := Real.geom_mean_le_arith_mean_weighted Finset.univ (fun _ => (k : ℝ)⁻¹) y hw hw' hy
  -- ∏ y_i ^ (1/k) ≤ ∑ (1/k) y_i = avg
  set avg : ℝ := 1 + (∑ i, lam i) * t / k with havg_def
  have hsum : ∑ i, ((k : ℝ)⁻¹) * y i = avg := by
    rw [← Finset.mul_sum]
    have hsy : ∑ i, y i = (k : ℝ) + (∑ i, lam i) * t := by
      simp only [hy_def]
      rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
        nsmul_eq_mul, mul_one, ← Finset.sum_mul]
    rw [hsy, havg_def]
    field_simp
  rw [hsum] at hgeom
  -- ∏ y_i ^ (1/k) = (∏ y_i) ^ (1/k)
  have hprod_rpow : ∏ i, (y i) ^ ((k : ℝ)⁻¹) = (∏ i, y i) ^ ((k : ℝ)⁻¹) :=
    Real.finsetProd_rpow Finset.univ y hy _
  rw [hprod_rpow] at hgeom
  have hprodpos : 0 ≤ ∏ i, y i := Finset.prod_nonneg hy
  -- raise both sides to the (k:ℝ) power, then simplify the LHS exponent (1/k)*k = 1
  have hpow := Real.rpow_le_rpow (Real.rpow_nonneg hprodpos _) hgeom (le_of_lt hkR)
  rw [← Real.rpow_mul hprodpos] at hpow
  have hkne : (k : ℝ) ≠ 0 := ne_of_gt hkR
  rw [inv_mul_cancel₀ hkne, Real.rpow_one, Real.rpow_natCast] at hpow
  simpa [hy_def, havg_def] using hpow

/-- Power cancellation: `G(k) · (k/(k-1))^k = k/(k-1)` for `k ≥ 2`. -/
lemma G_mul_ratio_pow {k : ℕ} (hk : 2 ≤ k) :
    G k * ((k : ℝ) / ((k : ℝ) - 1)) ^ k = (k : ℝ) / ((k : ℝ) - 1) := by
  obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
  have hm1 : 1 ≤ m := by omega
  have hmpos : (0 : ℝ) < m := by exact_mod_cast hm1
  rw [G_succ]
  have hcast : ((m + 1 : ℕ) : ℝ) = (m : ℝ) + 1 := by push_cast; ring
  rw [hcast]
  have hkey : ((m : ℝ) / ((m : ℝ) + 1)) * (((m : ℝ) + 1) / (m : ℝ)) = 1 := by
    field_simp
  have hsimp : ((m : ℝ) + 1) / ((m : ℝ) + 1 - 1) = ((m : ℝ) + 1) / (m : ℝ) := by ring_nf
  rw [hsimp, pow_succ, ← mul_assoc, ← mul_pow, hkey, one_pow, one_mul]

/-- **Univariate Gurvits lemma (factored form).** If `C·t ≤ c·∏ᵢ(1+λᵢt)` for all `t>0`, with
`c, λᵢ ≥ 0` and `Σλ > 0` and `k ≥ 2`, then `G(k)·C ≤ c·Σλ`. (`c·Σλ` is the coefficient of `t`
in `c·∏(1+λᵢt)`.) This is the analytic crux of the Gurvits capacity reduction step. -/
lemma univariate_gurvits_factored {k : ℕ} (hk : 2 ≤ k) (c C : ℝ) (lam : Fin k → ℝ)
    (hc : 0 ≤ c) (hlam : ∀ i, 0 ≤ lam i) (hS : 0 < ∑ i, lam i)
    (hbound : ∀ t : ℝ, 0 < t → C * t ≤ c * ∏ i, (1 + lam i * t)) :
    G k * C ≤ c * ∑ i, lam i := by
  set S : ℝ := ∑ i, lam i with hSdef
  have hkR : (2 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  have hk1 : (0 : ℝ) < (k : ℝ) - 1 := by linarith
  have hkpos : (0 : ℝ) < (k : ℝ) := by linarith
  set t0 : ℝ := (k : ℝ) / (S * ((k : ℝ) - 1)) with ht0def
  have ht0 : 0 < t0 := by rw [ht0def]; positivity
  have h3 : 1 + S * t0 / k = (k : ℝ) / ((k : ℝ) - 1) := by
    rw [ht0def]; field_simp; ring
  have h1 := hbound t0 ht0
  have h2 := prod_one_add_mul_le (by omega : 1 ≤ k) lam hlam t0 (le_of_lt ht0)
  have h4 : C * t0 ≤ c * ((k : ℝ) / ((k : ℝ) - 1)) ^ k := by
    calc C * t0 ≤ c * ∏ i, (1 + lam i * t0) := h1
      _ ≤ c * (1 + S * t0 / k) ^ k := by
          apply mul_le_mul_of_nonneg_left _ hc; rw [hSdef]; exact h2
      _ = c * ((k : ℝ) / ((k : ℝ) - 1)) ^ k := by rw [h3]
  -- multiply by G k ≥ 0, use the cancellation, and that c*k/(k-1) = c*S*t0
  have hGnn : 0 ≤ G k := by
    rw [G]; positivity
  have h5 : G k * (C * t0) ≤ G k * (c * ((k : ℝ) / ((k : ℝ) - 1)) ^ k) :=
    mul_le_mul_of_nonneg_left h4 hGnn
  rw [show G k * (c * ((k : ℝ) / ((k : ℝ) - 1)) ^ k)
        = c * (G k * ((k : ℝ) / ((k : ℝ) - 1)) ^ k) by ring, G_mul_ratio_pow hk] at h5
  -- h5 : G k * (C * t0) ≤ c * (k/(k-1)); and c*(k/(k-1)) = (c*S)*t0
  have h6 : c * ((k : ℝ) / ((k : ℝ) - 1)) = (c * S) * t0 := by
    rw [ht0def]; field_simp
  rw [h6, ← mul_assoc] at h5
  -- h5 : G k * C * t0 ≤ c * S * t0; cancel t0 > 0
  exact le_of_mul_le_mul_right h5 ht0

/-!
### Algebraic interface to the Chapter 22 capacity core

The analytic Gurvits step should produce the lower bound with the telescoping
product of the constants `G(2), ..., G(n)`.  The theorem below is the purely
algebraic last mile: once that iterated capacity estimate is available for the
row-linear polynomial, the exact `n! / n^n` squarefree-coefficient core follows.
-/

/-- The remaining iterated Gurvits capacity estimate, stated with the product
constant before telescoping. -/
structure GurvitsIteratedCapacityCertificate (n : ℕ) where
  squarefree_bound :
    ∀ A : Matrix (Fin n) (Fin n) ℝ,
      (∀ i j, 0 ≤ A i j) →
      RowLinearCapacityAtLeastOne A →
      (∏ m ∈ Finset.Icc 2 n, G m) ≤ rowLinearSquarefreeCoefficient A

/-- The iterated Gurvits product bound discharges the literal squarefree
coefficient core, by the telescoping identity above. -/
theorem squarefreeCoefficientCore_of_iteratedCapacityCertificate (n : ℕ)
    (cert : GurvitsIteratedCapacityCertificate n) :
    GurvitsSquarefreeCoefficientFromCapacityCore n := by
  refine ⟨?_⟩
  intro A hA hcap
  by_cases hn0 : n = 0
  · subst n
    simpa using cert.squarefree_bound A hA hcap
  · have hn : 1 ≤ n := Nat.succ_le_of_lt (Nat.pos_of_ne_zero hn0)
    simpa [gurvits_product_telescopes n hn] using cert.squarefree_bound A hA hcap

/-- Low dimensions are already discharged in `Chapter22`; this re-exports that
fact from the Gurvits file. -/
theorem squarefreeCoefficientCore_of_le_two (n : ℕ) (hn : n ≤ 2) :
    GurvitsSquarefreeCoefficientFromCapacityCore n :=
  Chapter22.squarefreeCoefficientCore_of_le_two n hn

theorem vanDerWaerdenAnalyticCore_of_iteratedCapacityCertificate (n : ℕ)
    (cert : GurvitsIteratedCapacityCertificate n) :
    VanDerWaerdenAnalyticCore n :=
  Chapter22.vanDerWaerdenAnalyticCore_of_squarefreeCoefficientCore
    (squarefreeCoefficientCore_of_iteratedCapacityCertificate n cert)

theorem chapter22_from_iteratedCapacityCertificate
    (cert : ∀ m : ℕ, 3 ≤ m → GurvitsIteratedCapacityCertificate m)
    (n : ℕ) (A : Matrix (Fin n) (Fin n) ℝ)
    (hA : A ∈ doublyStochastic ℝ (Fin n)) :
    (n.factorial : ℝ) / (n : ℝ) ^ n ≤ A.permanent := by
  exact Chapter22.chapter22
    (fun m hm => squarefreeCoefficientCore_of_iteratedCapacityCertificate m (cert m hm))
    n A hA

end

end ProofsInTheBook.Chapter22Gurvits
