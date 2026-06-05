import Mathlib
import ProofsInTheBook.Chapter22
import ProofsInTheBook.Chapter22Stable

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

/-- `G k ≥ 0`. -/
lemma G_nonneg (k : ℕ) : 0 ≤ G k := by
  rcases Nat.lt_or_ge k 2 with hk | hk
  · interval_cases k <;> simp
  · rw [G]
    apply pow_nonneg
    apply div_nonneg _ (by positivity)
    have : (2 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
    linarith

/-!
### Capacity lower-bound bookkeeping for the reduction chain

The analytic-free stable-polynomial step is most convenient to state as a
lower-bound invariant rather than as an actual infimum.  `CapLB p c` means that
`c` is a certified lower bound for the Gurvits capacity of `p`.
-/

def NonnegativeCoefficients {m : ℕ} (p : MvPolynomial (Fin m) ℝ) : Prop :=
  ∀ a : Fin m →₀ ℕ, 0 ≤ MvPolynomial.coeff a p

def PositiveVector {m : ℕ} (x : Fin m → ℝ) : Prop :=
  ∀ i, 0 < x i

def CapLB {m : ℕ} (p : MvPolynomial (Fin m) ℝ) (c : ℝ) : Prop :=
  ∀ x : Fin m → ℝ, PositiveVector x → c * ∏ i, x i ≤ MvPolynomial.eval x p

def AllDegreeCoefficientsPositive {m : ℕ} (d : ℕ) (p : MvPolynomial (Fin m) ℝ) :
    Prop :=
  ∀ a : Fin m →₀ ℕ, a.degree = d → 0 < MvPolynomial.coeff a p

lemma nonnegativeCoefficients_C {m : ℕ} {c : ℝ} (hc : 0 ≤ c) :
    NonnegativeCoefficients (MvPolynomial.C c : MvPolynomial (Fin m) ℝ) := by
  classical
  intro a
  rw [MvPolynomial.coeff_C]
  split_ifs <;> positivity

lemma nonnegativeCoefficients_X {m : ℕ} (i : Fin m) :
    NonnegativeCoefficients (MvPolynomial.X i : MvPolynomial (Fin m) ℝ) := by
  classical
  intro a
  rw [MvPolynomial.coeff_X']
  split_ifs <;> positivity

lemma NonnegativeCoefficients.add {m : ℕ} {p q : MvPolynomial (Fin m) ℝ}
    (hp : NonnegativeCoefficients p) (hq : NonnegativeCoefficients q) :
    NonnegativeCoefficients (p + q) := by
  intro a
  rw [MvPolynomial.coeff_add]
  exact add_nonneg (hp a) (hq a)

lemma NonnegativeCoefficients.mul {m : ℕ} {p q : MvPolynomial (Fin m) ℝ}
    (hp : NonnegativeCoefficients p) (hq : NonnegativeCoefficients q) :
    NonnegativeCoefficients (p * q) := by
  classical
  intro a
  rw [MvPolynomial.coeff_mul]
  exact Finset.sum_nonneg fun b _ =>
    mul_nonneg (hp b.1) (hq b.2)

lemma nonnegativeCoefficients_sum {m : ℕ} {ι : Type*} (s : Finset ι)
    (f : ι → MvPolynomial (Fin m) ℝ)
    (hf : ∀ i ∈ s, NonnegativeCoefficients (f i)) :
    NonnegativeCoefficients (∑ i ∈ s, f i) := by
  classical
  induction s using Finset.induction with
  | empty =>
      intro a
      simp
  | insert i s his ih =>
      simp_rw [Finset.sum_insert his]
      exact (hf i (Finset.mem_insert_self i s)).add
        (ih fun j hj => hf j (Finset.mem_insert_of_mem hj))

lemma nonnegativeCoefficients_prod {m : ℕ} {ι : Type*} (s : Finset ι)
    (f : ι → MvPolynomial (Fin m) ℝ)
    (hf : ∀ i ∈ s, NonnegativeCoefficients (f i)) :
    NonnegativeCoefficients (∏ i ∈ s, f i) := by
  classical
  induction s using Finset.induction with
  | empty =>
      exact nonnegativeCoefficients_C (by positivity : (0 : ℝ) ≤ 1)
  | insert i s his ih =>
      simp_rw [Finset.prod_insert his]
      exact (hf i (Finset.mem_insert_self i s)).mul
        (ih fun j hj => hf j (Finset.mem_insert_of_mem hj))

lemma rowLinearMvPolynomial_nonnegativeCoefficients {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℝ) (hA : ∀ i j, 0 ≤ A i j) :
    NonnegativeCoefficients (rowLinearMvPolynomial A) := by
  classical
  rw [rowLinearMvPolynomial]
  apply nonnegativeCoefficients_prod
  intro i _
  apply nonnegativeCoefficients_sum
  intro j _
  exact (nonnegativeCoefficients_C (hA i j)).mul (nonnegativeCoefficients_X j)

lemma rowLinearMvPolynomial_isHomogeneous {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℝ) :
    (rowLinearMvPolynomial A).IsHomogeneous n := by
  classical
  rw [rowLinearMvPolynomial]
  convert MvPolynomial.IsHomogeneous.prod (Finset.univ : Finset (Fin n))
    (fun i => ∑ j, MvPolynomial.C (A i j) * (MvPolynomial.X j : MvPolynomial (Fin n) ℝ))
    (fun _ => 1) ?_ using 1
  · simp
  · intro i _hi
    apply MvPolynomial.IsHomogeneous.sum
    intro j _hj
    exact MvPolynomial.isHomogeneous_C_mul_X (A i j) j

lemma eval_nonneg_of_nonnegativeCoefficients {m : ℕ} {p : MvPolynomial (Fin m) ℝ}
    (hp : NonnegativeCoefficients p) {x : Fin m → ℝ} (hx : ∀ i, 0 ≤ x i) :
    0 ≤ MvPolynomial.eval x p := by
  rw [MvPolynomial.eval_eq]
  apply Finset.sum_nonneg
  intro a ha
  exact mul_nonneg (hp a) (Finset.prod_nonneg fun i _ => pow_nonneg (hx i) _)

lemma eval_pos_of_nonnegativeCoefficients {m : ℕ} {p : MvPolynomial (Fin m) ℝ}
    (hp : NonnegativeCoefficients p) (hp_ne : p ≠ 0)
    {x : Fin m → ℝ} (hx : ∀ i, 0 < x i) :
    0 < MvPolynomial.eval x p := by
  rw [MvPolynomial.eval_eq]
  apply Finset.sum_pos'
  · intro a ha
    exact mul_nonneg (hp a) (Finset.prod_nonneg fun i _ => pow_nonneg (le_of_lt (hx i)) _)
  · obtain ⟨a, ha⟩ := MvPolynomial.support_nonempty.mpr hp_ne
    refine ⟨a, ha, ?_⟩
    have hcoeff_ne : MvPolynomial.coeff a p ≠ 0 := MvPolynomial.mem_support_iff.mp ha
    have hcoeff_pos : 0 < MvPolynomial.coeff a p :=
      lt_of_le_of_ne (hp a) (Ne.symm hcoeff_ne)
    exact mul_pos hcoeff_pos (Finset.prod_pos fun i _ => pow_pos (hx i) _)

lemma coeff_mul_C_mul_X_of_pos {m : ℕ}
    (p : MvPolynomial (Fin m) ℝ) (a : Fin m →₀ ℕ) (j : Fin m) (c : ℝ)
    (ha : a j ≠ 0) :
    MvPolynomial.coeff a (p * (MvPolynomial.C c * MvPolynomial.X j)) =
      MvPolynomial.coeff (a - Finsupp.single j 1) p * c := by
  have hsum : a - Finsupp.single j 1 + Finsupp.single j 1 = a :=
    Finsupp.sub_add_single_one_cancel ha
  rw [← hsum]
  rw [show p * (MvPolynomial.C c * MvPolynomial.X j) =
      MvPolynomial.C c * (p * MvPolynomial.X j) by ring]
  rw [MvPolynomial.coeff_C_mul, MvPolynomial.coeff_mul_X]
  have hsub : (a - Finsupp.single j 1 + Finsupp.single j 1) - Finsupp.single j 1 =
      a - Finsupp.single j 1 := by
    rw [hsum]
  rw [hsub]
  ring

lemma degree_sub_single_of_pos {m d : ℕ}
    (a : Fin m →₀ ℕ) (j : Fin m) (hdeg : a.degree = d + 1) (ha : a j ≠ 0) :
    (a - Finsupp.single j 1).degree = d := by
  have hsum : a - Finsupp.single j 1 + Finsupp.single j 1 = a :=
    Finsupp.sub_add_single_one_cancel ha
  have hdeg_sum := congrArg Finsupp.degree hsum
  simp [hdeg] at hdeg_sum
  omega

lemma exists_pos_apply_of_degree_pos {m : ℕ} (a : Fin m →₀ ℕ) (hdeg : 0 < a.degree) :
    ∃ j : Fin m, 0 < a j := by
  by_contra h
  push Not at h
  have hazero : a = 0 := by
    ext j
    exact Nat.eq_zero_of_le_zero (h j)
  rw [hazero] at hdeg
  simp at hdeg

lemma allDegreeCoefficientsPositive_one {m : ℕ} :
    AllDegreeCoefficientsPositive 0 (1 : MvPolynomial (Fin m) ℝ) := by
  intro a hdeg
  have ha0 : a = 0 := (Finsupp.degree_eq_zero_iff a).mp hdeg
  subst a
  simp

lemma allDegreeCoefficientsPositive_mul_positive_linear {m d : ℕ}
    {p : MvPolynomial (Fin m) ℝ} (hpnonneg : NonnegativeCoefficients p)
    (hp : AllDegreeCoefficientsPositive d p) (C : Fin m → ℝ) (hC : ∀ j, 0 < C j) :
    AllDegreeCoefficientsPositive (d + 1)
      (p * ∑ j, MvPolynomial.C (C j) * (MvPolynomial.X j : MvPolynomial (Fin m) ℝ)) := by
  intro a hdeg
  have hdegpos : 0 < a.degree := by rw [hdeg]; omega
  obtain ⟨j0, hj0pos⟩ := exists_pos_apply_of_degree_pos a hdegpos
  rw [Finset.mul_sum, MvPolynomial.coeff_sum]
  apply Finset.sum_pos'
  · intro j _hj
    exact (hpnonneg.mul ((nonnegativeCoefficients_C (le_of_lt (hC j))).mul
      (nonnegativeCoefficients_X j))) a
  · refine ⟨j0, Finset.mem_univ j0, ?_⟩
    rw [coeff_mul_C_mul_X_of_pos p a j0 (C j0) (ne_of_gt hj0pos)]
    exact mul_pos (hp _ (degree_sub_single_of_pos a j0 hdeg (ne_of_gt hj0pos))) (hC j0)

lemma product_positive_linear_allDegreeCoefficientsPositive {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℝ) (hApos : ∀ i j, 0 < A i j) (s : Finset (Fin n)) :
    AllDegreeCoefficientsPositive s.card
      (∏ i ∈ s, ∑ j, MvPolynomial.C (A i j) *
        (MvPolynomial.X j : MvPolynomial (Fin n) ℝ)) := by
  classical
  induction s using Finset.induction with
  | empty =>
      simpa using (allDegreeCoefficientsPositive_one (m := n))
  | insert i s his ih =>
      rw [Finset.card_insert_of_notMem his]
      simp_rw [Finset.prod_insert his]
      rw [mul_comm]
      exact allDegreeCoefficientsPositive_mul_positive_linear
        (nonnegativeCoefficients_prod s
          (fun i => ∑ j, MvPolynomial.C (A i j) *
            (MvPolynomial.X j : MvPolynomial (Fin n) ℝ))
          (by
            intro i _hi
            apply nonnegativeCoefficients_sum
            intro j _hj
            exact (nonnegativeCoefficients_C (le_of_lt (hApos i j))).mul
              (nonnegativeCoefficients_X j)))
        ih (A i) (hApos i)

lemma rowLinearMvPolynomial_allDegreeCoefficientsPositive {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℝ) (hApos : ∀ i j, 0 < A i j) :
    AllDegreeCoefficientsPositive n (rowLinearMvPolynomial A) := by
  classical
  rw [rowLinearMvPolynomial]
  simpa using
    product_positive_linear_allDegreeCoefficientsPositive A hApos (Finset.univ : Finset (Fin n))

def firstReduction {m : ℕ} (p : MvPolynomial (Fin (m + 1)) ℝ) :
    MvPolynomial (Fin m) ℝ :=
  Polynomial.coeff (MvPolynomial.finSuccEquiv ℝ m p) 1

lemma coeff_firstReduction {m : ℕ} (p : MvPolynomial (Fin (m + 1)) ℝ)
    (a : Fin m →₀ ℕ) :
    MvPolynomial.coeff a (firstReduction p) =
      MvPolynomial.coeff (Finsupp.cons 1 a) p := by
  simpa [firstReduction] using MvPolynomial.finSuccEquiv_coeff_coeff a p 1

lemma firstReduction_nonnegativeCoefficients {m : ℕ}
    {p : MvPolynomial (Fin (m + 1)) ℝ}
    (hp : NonnegativeCoefficients p) :
    NonnegativeCoefficients (firstReduction p) := by
  intro a
  rw [coeff_firstReduction]
  exact hp _

lemma firstReduction_isHomogeneous {m : ℕ}
    {p : MvPolynomial (Fin (m + 1)) ℝ}
    (hp : p.IsHomogeneous (m + 1)) :
    (firstReduction p).IsHomogeneous m := by
  simpa [firstReduction] using
    hp.finSuccEquiv_coeff_isHomogeneous 1 m (by omega)

lemma degree_cons {m : ℕ} (k : ℕ) (a : Fin m →₀ ℕ) :
    (Finsupp.cons k a).degree = k + a.degree := by
  rw [Finsupp.degree_eq_sum, Fin.sum_univ_succ, Finsupp.degree_eq_sum]
  simp [Finsupp.cons_zero, Finsupp.cons_succ]

lemma allDegreeCoefficientsPositive_firstReduction {m : ℕ}
    {p : MvPolynomial (Fin (m + 1)) ℝ}
    (hp : AllDegreeCoefficientsPositive (m + 1) p) :
    AllDegreeCoefficientsPositive m (firstReduction p) := by
  intro a hdeg
  rw [coeff_firstReduction]
  have hcons : (Finsupp.cons 1 a).degree = m + 1 := by
    rw [degree_cons, hdeg]
    omega
  exact hp (Finsupp.cons 1 a) hcons

lemma coeff_finSuccEquiv_nonnegativeCoefficients {m : ℕ}
    {p : MvPolynomial (Fin (m + 1)) ℝ}
    (hp : NonnegativeCoefficients p) (i : ℕ) :
    NonnegativeCoefficients (Polynomial.coeff (MvPolynomial.finSuccEquiv ℝ m p) i) := by
  intro a
  rw [MvPolynomial.finSuccEquiv_coeff_coeff]
  exact hp _

def iteratedFirstReductionCoefficient : (m : ℕ) → MvPolynomial (Fin m) ℝ → ℝ
  | 0, p => MvPolynomial.coeff (squarefreeExponent 0) p
  | m + 1, p => iteratedFirstReductionCoefficient m (firstReduction p)

lemma squarefreeExponent_succ (m : ℕ) :
    Finsupp.cons 1 (squarefreeExponent m) = squarefreeExponent (m + 1) := by
  ext i
  refine Fin.cases ?_ ?_ i
  · simp [squarefreeExponent]
  · intro j
    simp [squarefreeExponent]

lemma finsupp_fin_one_eq_squarefree_of_degree_one (a : Fin 1 →₀ ℕ) (hdeg : a.degree = 1) :
    a = squarefreeExponent 1 := by
  apply Finsupp.ext
  intro j
  fin_cases j
  have h : a 0 = 1 := by
    simpa [Finsupp.degree_eq_sum, Fin.sum_univ_one] using hdeg
  simp [squarefreeExponent, h]

lemma eval_one_eq_squarefreeCoeff_of_homogeneous_one
    {p : MvPolynomial (Fin 1) ℝ} (hhom : p.IsHomogeneous 1) :
    MvPolynomial.eval (fun _ : Fin 1 => (1 : ℝ)) p =
      MvPolynomial.coeff (squarefreeExponent 1) p := by
  rw [MvPolynomial.eval_eq]
  rw [Finset.sum_eq_single (squarefreeExponent 1)]
  · simp
  · intro a _ha hne
    have hcoeff0 : MvPolynomial.coeff a p = 0 := by
      by_cases hdeg : a.degree = 1
      · exact False.elim (hne (finsupp_fin_one_eq_squarefree_of_degree_one a hdeg))
      · exact hhom.coeff_eq_zero hdeg
    rw [hcoeff0, zero_mul]
  · intro hnot
    rw [MvPolynomial.mem_support_iff] at hnot
    have hc0 : MvPolynomial.coeff (squarefreeExponent 1) p = 0 := not_not.mp hnot
    rw [hc0, zero_mul]

lemma iteratedFirstReductionCoefficient_eq_squarefreeCoefficient :
    ∀ (m : ℕ) (p : MvPolynomial (Fin m) ℝ),
      iteratedFirstReductionCoefficient m p =
        MvPolynomial.coeff (squarefreeExponent m) p
  | 0, p => rfl
  | m + 1, p => by
      rw [iteratedFirstReductionCoefficient,
        iteratedFirstReductionCoefficient_eq_squarefreeCoefficient m (firstReduction p),
        coeff_firstReduction, squarefreeExponent_succ]

def sectionPolynomial {m : ℕ} (p : MvPolynomial (Fin (m + 1)) ℝ)
    (x : Fin m → ℝ) : Polynomial ℝ :=
  Polynomial.map (MvPolynomial.eval x) (MvPolynomial.finSuccEquiv ℝ m p)

def complexSectionPolynomial {m : ℕ} (p : MvPolynomial (Fin (m + 1)) ℝ)
    (z : Fin m → ℂ) : Polynomial ℂ :=
  Polynomial.map (MvPolynomial.eval z)
    (MvPolynomial.finSuccEquiv ℂ m (p.map (algebraMap ℝ ℂ)))

def complexLineSection {m : ℕ} (q : MvPolynomial (Fin m) ℂ)
    (a b : Fin m → ℂ) : Polynomial ℂ :=
  MvPolynomial.eval₂ Polynomial.C
    (fun j => Polynomial.C (a j) + Polynomial.C (b j) * Polynomial.X) q

lemma coeff_prod_of_natDegree_le_sum {ι R : Type*} [CommSemiring R]
    [DecidableEq ι] (s : Finset ι) (f : ι → Polynomial R) (d : ι → ℕ)
    (h : ∀ i ∈ s, (f i).natDegree ≤ d i) :
    (∏ i ∈ s, f i).coeff (∑ i ∈ s, d i) =
      ∏ i ∈ s, (f i).coeff (d i) := by
  classical
  induction s using Finset.induction with
  | empty =>
      simp
  | insert i s his ih =>
      have hprod : (∏ j ∈ s, f j).natDegree ≤ ∑ j ∈ s, d j := by
        exact (Polynomial.natDegree_prod_le (s := s) (f := f)).trans
          (Finset.sum_le_sum fun j hj => h j (Finset.mem_insert_of_mem hj))
      rw [Finset.prod_insert his, Finset.sum_insert his, Finset.prod_insert his]
      rw [Polynomial.coeff_mul_add_eq_of_natDegree_le
        (h i (Finset.mem_insert_self i s)) hprod]
      rw [ih (fun j hj => h j (Finset.mem_insert_of_mem hj))]

lemma coeff_linear_pow_top {R : Type*} [CommSemiring R] (a b : R) (n : ℕ) :
    ((Polynomial.C a + Polynomial.C b * Polynomial.X : Polynomial R) ^ n).coeff n = b ^ n := by
  have hlin : (Polynomial.C a + Polynomial.C b * Polynomial.X : Polynomial R).natDegree ≤ 1 := by
    simpa only [add_comm] using (Polynomial.natDegree_linear_le (a := b) (b := a))
  have h := Polynomial.coeff_pow_of_natDegree_le
    (p := (Polynomial.C a + Polynomial.C b * Polynomial.X : Polynomial R)) (m := n) (n := 1) hlin
  have hcoeff : (Polynomial.C a + Polynomial.C b * Polynomial.X : Polynomial R).coeff 1 = b := by
    simp
  rw [Nat.mul_one, hcoeff] at h
  exact h

lemma coeff_complexLineSection_monomial_degree {m : ℕ}
    (u : Fin m →₀ ℕ) (c : ℂ) (a b : Fin m → ℂ) :
    (complexLineSection (MvPolynomial.monomial u c) a b).coeff u.degree =
      c * ∏ i ∈ u.support, b i ^ u i := by
  classical
  rw [complexLineSection, MvPolynomial.eval₂_monomial, Polynomial.coeff_C_mul]
  have hprod :
      (∏ x ∈ u.support,
          (Polynomial.C (a x) + Polynomial.C (b x) * Polynomial.X : Polynomial ℂ) ^ u x).coeff
        (∑ x ∈ u.support, u x) =
        ∏ x ∈ u.support,
          (((Polynomial.C (a x) + Polynomial.C (b x) * Polynomial.X : Polynomial ℂ) ^ u x).coeff (u x)) :=
    coeff_prod_of_natDegree_le_sum u.support
      (fun x => (Polynomial.C (a x) + Polynomial.C (b x) * Polynomial.X : Polynomial ℂ) ^ u x)
      (fun x => u x)
      (by
        intro x _hx
        have hlin :
            (Polynomial.C (a x) + Polynomial.C (b x) * Polynomial.X : Polynomial ℂ).natDegree ≤ 1 := by
          simpa only [add_comm] using
            (Polynomial.natDegree_linear_le (a := b x) (b := a x))
        simpa only [Nat.mul_one] using Polynomial.natDegree_pow_le_of_le (u x) hlin)
  rw [Finsupp.prod]
  change c *
      (∏ x ∈ u.support,
        (Polynomial.C (a x) + Polynomial.C (b x) * Polynomial.X : Polynomial ℂ) ^ u x).coeff
        (∑ x ∈ u.support, u x) =
    c * ∏ i ∈ u.support, b i ^ u i
  rw [hprod]
  congr 1
  apply Finset.prod_congr rfl
  intro x _hx
  exact coeff_linear_pow_top (a x) (b x) (u x)

lemma complexLineSection_coeff_of_isHomogeneous {m d : ℕ}
    {q : MvPolynomial (Fin m) ℂ} (hq : q.IsHomogeneous d)
    (a b : Fin m → ℂ) :
    (complexLineSection q a b).coeff d = MvPolynomial.eval b q := by
  classical
  conv_lhs =>
    rw [q.as_sum]
  rw [complexLineSection, MvPolynomial.eval₂_sum, Polynomial.finsetSum_coeff]
  rw [MvPolynomial.eval_eq]
  apply Finset.sum_congr rfl
  intro u hu
  have hdeg : u.degree = d := by
    rw [← hq (MvPolynomial.mem_support_iff.mp hu)]
    rw [Finsupp.degree, Finsupp.weight_apply, Finsupp.sum]
    change (∑ i ∈ u.support, u i) =
      ∑ a ∈ u.support, u a • ((1 : Fin m → ℕ) a)
    simp
  rw [← hdeg]
  change
    (complexLineSection (MvPolynomial.monomial u (MvPolynomial.coeff u q)) a b).coeff u.degree =
      MvPolynomial.coeff u q * ∏ i ∈ u.support, b i ^ u i
  rw [coeff_complexLineSection_monomial_degree]

lemma complexLineSection_monomial_natDegree_le_degree {m : ℕ}
    (u : Fin m →₀ ℕ) (c : ℂ) (a b : Fin m → ℂ) :
    (complexLineSection (MvPolynomial.monomial u c) a b).natDegree ≤ u.degree := by
  classical
  rw [complexLineSection, MvPolynomial.eval₂_monomial]
  refine (Polynomial.natDegree_C_mul_le c _).trans ?_
  have hprod :
      (∏ x ∈ u.support,
          ((Polynomial.C (a x) + Polynomial.C (b x) * Polynomial.X : Polynomial ℂ) ^ u x)).natDegree
        ≤ ∑ x ∈ u.support, u x := by
    exact (Polynomial.natDegree_prod_le
      (s := u.support)
      (f := fun x => (Polynomial.C (a x) + Polynomial.C (b x) * Polynomial.X : Polynomial ℂ) ^ u x)).trans
      (Finset.sum_le_sum fun x _hx => by
        have hlin :
            (Polynomial.C (a x) + Polynomial.C (b x) * Polynomial.X : Polynomial ℂ).natDegree ≤ 1 := by
          simpa only [add_comm] using
            (Polynomial.natDegree_linear_le (a := b x) (b := a x))
        simpa only [Nat.mul_one] using Polynomial.natDegree_pow_le_of_le (u x) hlin)
  rw [Finsupp.degree]
  exact hprod

lemma complexLineSection_natDegree_le_of_isHomogeneous {m d : ℕ}
    {q : MvPolynomial (Fin m) ℂ} (hq : q.IsHomogeneous d)
    (a b : Fin m → ℂ) :
    (complexLineSection q a b).natDegree ≤ d := by
  classical
  rw [Polynomial.natDegree_le_iff_coeff_eq_zero]
  intro N hN
  conv_lhs =>
    rw [q.as_sum]
  rw [complexLineSection, MvPolynomial.eval₂_sum, Polynomial.finsetSum_coeff]
  apply Finset.sum_eq_zero
  intro u hu
  have hdeg : u.degree = d := by
    rw [← hq (MvPolynomial.mem_support_iff.mp hu)]
    rw [Finsupp.degree, Finsupp.weight_apply, Finsupp.sum]
    change (∑ i ∈ u.support, u i) =
      ∑ a ∈ u.support, u a • ((1 : Fin m → ℕ) a)
    simp
  change
    (complexLineSection (MvPolynomial.monomial u (MvPolynomial.coeff u q)) a b).coeff N = 0
  exact Polynomial.coeff_eq_zero_of_natDegree_lt
    (lt_of_le_of_lt (complexLineSection_monomial_natDegree_le_degree u (MvPolynomial.coeff u q) a b)
      (by omega))

lemma complexLineSection_natDegree_le_totalDegree {m : ℕ}
    (q : MvPolynomial (Fin m) ℂ) (a b : Fin m → ℂ) :
    (complexLineSection q a b).natDegree ≤ q.totalDegree := by
  classical
  rw [Polynomial.natDegree_le_iff_coeff_eq_zero]
  intro N hN
  conv_lhs =>
    rw [q.as_sum]
  rw [complexLineSection, MvPolynomial.eval₂_sum, Polynomial.finsetSum_coeff]
  apply Finset.sum_eq_zero
  intro u hu
  change
    (complexLineSection (MvPolynomial.monomial u (MvPolynomial.coeff u q)) a b).coeff N = 0
  exact Polynomial.coeff_eq_zero_of_natDegree_lt
    (lt_of_le_of_lt (complexLineSection_monomial_natDegree_le_degree u (MvPolynomial.coeff u q) a b)
      (lt_of_le_of_lt (MvPolynomial.le_totalDegree hu) hN))

lemma complexLineSection_natDegree_eq_of_isHomogeneous_eval_ne_zero {m d : ℕ}
    {q : MvPolynomial (Fin m) ℂ} (hq : q.IsHomogeneous d)
    (a b : Fin m → ℂ) (hbq : MvPolynomial.eval b q ≠ 0) :
    (complexLineSection q a b).natDegree = d := by
  apply Polynomial.natDegree_eq_of_le_of_coeff_ne_zero
    (complexLineSection_natDegree_le_of_isHomogeneous hq a b)
  rw [complexLineSection_coeff_of_isHomogeneous hq a b]
  exact hbq

lemma complexLineSection_firstReduction_natDegree {m : ℕ}
    {p : MvPolynomial (Fin (m + 1)) ℝ}
    (hpcoeff : NonnegativeCoefficients p)
    (hhom : p.IsHomogeneous (m + 1))
    (hp_ne : firstReduction p ≠ 0)
    (a b : Fin m → ℝ) (hb : ∀ j, 0 < b j) :
    (complexLineSection ((firstReduction p).map (algebraMap ℝ ℂ))
      (fun j => (a j : ℂ)) (fun j => (b j : ℂ))).natDegree = m := by
  have hhomC : ((firstReduction p).map (algebraMap ℝ ℂ)).IsHomogeneous m := by
    simpa using (firstReduction_isHomogeneous hhom).map (algebraMap ℝ ℂ)
  have hpos : 0 < MvPolynomial.eval b (firstReduction p) :=
    eval_pos_of_nonnegativeCoefficients (firstReduction_nonnegativeCoefficients hpcoeff) hp_ne hb
  have hmap_eval :
      MvPolynomial.eval (fun j => (b j : ℂ))
        ((firstReduction p).map (algebraMap ℝ ℂ)) =
        (MvPolynomial.eval b (firstReduction p) : ℂ) := by
    simpa [Function.comp_def] using
      (MvPolynomial.map_eval (q := algebraMap ℝ ℂ) (g := b) (p := firstReduction p)).symm
  apply complexLineSection_natDegree_eq_of_isHomogeneous_eval_ne_zero hhomC
  rw [hmap_eval]
  exact Complex.ofReal_ne_zero.mpr (ne_of_gt hpos)

def distinguishedDerivativeAt {m : ℕ} (p : MvPolynomial (Fin (m + 1)) ℝ)
    (c : ℂ) : MvPolynomial (Fin m) ℂ :=
  Polynomial.eval (MvPolynomial.C c)
    (Polynomial.derivative (MvPolynomial.finSuccEquiv ℂ m (p.map (algebraMap ℝ ℂ))))

lemma distinguishedDerivativeAt_zero {m : ℕ}
    (p : MvPolynomial (Fin (m + 1)) ℝ) :
    distinguishedDerivativeAt p 0 = (firstReduction p).map (algebraMap ℝ ℂ) := by
  ext a
  simp only [distinguishedDerivativeAt, firstReduction, MvPolynomial.C_0]
  rw [Polynomial.eval, Polynomial.eval₂_at_zero]
  rw [Polynomial.coeff_derivative]
  simp
  rw [MvPolynomial.finSuccEquiv_coeff_coeff, MvPolynomial.coeff_map, MvPolynomial.coeff_map,
    MvPolynomial.finSuccEquiv_coeff_coeff]

lemma complexLineSection_coeff_eval_C_eq_sum {m : ℕ}
    (P : Polynomial (MvPolynomial (Fin m) ℂ)) (a b : Fin m → ℂ) (k : ℕ) (c : ℂ) :
    (complexLineSection (Polynomial.eval (MvPolynomial.C c) P) a b).coeff k =
      ∑ i ∈ Finset.range (P.natDegree + 1),
        c ^ i * (complexLineSection (P.coeff i) a b).coeff k := by
  rw [Polynomial.eval_eq_sum_range]
  rw [complexLineSection, MvPolynomial.eval₂_sum, Polynomial.finsetSum_coeff]
  apply Finset.sum_congr rfl
  intro i _hi
  rw [MvPolynomial.eval₂_mul]
  have hCpow :
      MvPolynomial.eval₂ Polynomial.C
        (fun j => Polynomial.C (a j) + Polynomial.C (b j) * Polynomial.X)
        (MvPolynomial.C c ^ i : MvPolynomial (Fin m) ℂ) = Polynomial.C (c ^ i) := by
    simp
  rw [hCpow, mul_comm, Polynomial.coeff_C_mul]
  rfl

lemma continuous_complexLineSection_coeff_eval_C {m : ℕ}
    (P : Polynomial (MvPolynomial (Fin m) ℂ)) (a b : Fin m → ℂ) (k : ℕ) :
    Continuous fun c : ℂ =>
      (complexLineSection (Polynomial.eval (MvPolynomial.C c) P) a b).coeff k := by
  rw [show (fun c : ℂ =>
        (complexLineSection (Polynomial.eval (MvPolynomial.C c) P) a b).coeff k) =
      fun c : ℂ => ∑ i ∈ Finset.range (P.natDegree + 1),
        c ^ i * (complexLineSection (P.coeff i) a b).coeff k by
    funext c
    exact complexLineSection_coeff_eval_C_eq_sum P a b k c]
  exact continuous_finsetSum _ (fun i _ => (continuous_id.pow i).mul continuous_const)

lemma derivative_finSuccEquiv_coeff_totalDegree_le {m : ℕ}
    {p : MvPolynomial (Fin (m + 1)) ℝ}
    (hhom : p.IsHomogeneous (m + 1)) (i : ℕ) :
    (Polynomial.coeff
      (Polynomial.derivative (MvPolynomial.finSuccEquiv ℂ m (p.map (algebraMap ℝ ℂ)))) i).totalDegree ≤ m := by
  let Q := MvPolynomial.finSuccEquiv ℂ m (p.map (algebraMap ℝ ℂ))
  change (Polynomial.coeff (Polynomial.derivative Q) i).totalDegree ≤ m
  rw [Polynomial.coeff_derivative]
  refine (MvPolynomial.totalDegree_mul _ _).trans ?_
  have hconst : ((↑i + 1 : MvPolynomial (Fin m) ℂ).totalDegree) = 0 := by
    rw [← Nat.cast_one, ← Nat.cast_add]
    rw [← MvPolynomial.C_eq_coe_nat (R := ℂ) (σ := Fin m) (i + 1)]
    rw [MvPolynomial.totalDegree_C]
  rw [hconst]
  change (Polynomial.coeff Q (i + 1)).totalDegree + 0 ≤ m
  by_cases hq : Polynomial.coeff Q (i + 1) = 0
  · rw [hq, MvPolynomial.totalDegree_zero]
    exact Nat.zero_le m
  · have hle := MvPolynomial.totalDegree_coeff_finSuccEquiv_add_le
      (p.map (algebraMap ℝ ℂ)) (i + 1) hq
    change (Polynomial.coeff Q (i + 1)).totalDegree + (i + 1) ≤
      (p.map (algebraMap ℝ ℂ)).totalDegree at hle
    have hhomC : (p.map (algebraMap ℝ ℂ)).IsHomogeneous (m + 1) := by
      simpa using hhom.map (algebraMap ℝ ℂ)
    have htot : (p.map (algebraMap ℝ ℂ)).totalDegree ≤ m + 1 := hhomC.totalDegree_le
    omega

lemma distinguishedDerivativeAt_totalDegree_le {m : ℕ}
    {p : MvPolynomial (Fin (m + 1)) ℝ}
    (hhom : p.IsHomogeneous (m + 1)) (c : ℂ) :
    (distinguishedDerivativeAt p c).totalDegree ≤ m := by
  rw [distinguishedDerivativeAt, Polynomial.eval_eq_sum_range]
  apply MvPolynomial.totalDegree_finsetSum_le
  intro i _hi
  refine (MvPolynomial.totalDegree_mul _ _).trans ?_
  have hCpow_le : (MvPolynomial.C c ^ i : MvPolynomial (Fin m) ℂ).totalDegree ≤ 0 := by
    simpa [MvPolynomial.totalDegree_C] using
      (MvPolynomial.totalDegree_pow (MvPolynomial.C c : MvPolynomial (Fin m) ℂ) i)
  have hCpow : (MvPolynomial.C c ^ i : MvPolynomial (Fin m) ℂ).totalDegree = 0 :=
    le_antisymm hCpow_le (Nat.zero_le _)
  rw [hCpow]
  simpa using derivative_finSuccEquiv_coeff_totalDegree_le hhom i

lemma sectionPolynomial_eval {m : ℕ} (p : MvPolynomial (Fin (m + 1)) ℝ)
    (x : Fin m → ℝ) (t : ℝ) :
    Polynomial.eval t (sectionPolynomial p x) =
      MvPolynomial.eval (Fin.cons t x) p := by
  simpa [sectionPolynomial] using
    (MvPolynomial.eval_eq_eval_mv_eval' (s := x) (y := t) (f := p)).symm

lemma complexSectionPolynomial_eval {m : ℕ} (p : MvPolynomial (Fin (m + 1)) ℝ)
    (z : Fin m → ℂ) (t : ℂ) :
    Polynomial.eval t (complexSectionPolynomial p z) =
      MvPolynomial.eval (Fin.cons t z) (p.map (algebraMap ℝ ℂ)) := by
  simpa [complexSectionPolynomial] using
    (MvPolynomial.eval_eq_eval_mv_eval' (s := z) (y := t)
      (f := p.map (algebraMap ℝ ℂ))).symm

lemma complexLineSection_eval {m : ℕ} (q : MvPolynomial (Fin m) ℂ)
    (a b : Fin m → ℂ) (t : ℂ) :
    Polynomial.eval t (complexLineSection q a b) =
      MvPolynomial.eval (fun j => a j + b j * t) q := by
  induction q using MvPolynomial.induction_on' with
  | monomial u c =>
      rw [complexLineSection, MvPolynomial.eval₂_monomial, MvPolynomial.eval_monomial,
        Polynomial.eval_mul, Polynomial.eval_C]
      congr 1
      rw [Finsupp.prod, Polynomial.eval_prod, Finsupp.prod]
      apply Finset.prod_congr rfl
      intro i _hi
      rw [Polynomial.eval_pow, Polynomial.eval_add, Polynomial.eval_mul,
        Polynomial.eval_C, Polynomial.eval_X, Polynomial.eval_C]
  | add p q hp hq =>
      rw [complexLineSection, MvPolynomial.eval₂_add, Polynomial.eval_add,
        MvPolynomial.eval_add]
      change Polynomial.eval t (complexLineSection p a b) +
          Polynomial.eval t (complexLineSection q a b) =
        (MvPolynomial.eval (fun j => a j + b j * t) p) +
          (MvPolynomial.eval (fun j => a j + b j * t) q)
      rw [hp, hq]

lemma distinguishedDerivativeAt_eval {m : ℕ}
    (p : MvPolynomial (Fin (m + 1)) ℝ) (z : Fin m → ℂ) (c : ℂ) :
    MvPolynomial.eval z (distinguishedDerivativeAt p c) =
      Polynomial.eval c (Polynomial.derivative (complexSectionPolynomial p z)) := by
  let P := Polynomial.derivative (MvPolynomial.finSuccEquiv ℂ m (p.map (algebraMap ℝ ℂ)))
  have h :
      Polynomial.eval₂ (MvPolynomial.eval z) c P =
        MvPolynomial.eval z (Polynomial.eval (MvPolynomial.C c) P) := by
    simpa using
      (Polynomial.eval₂_hom (p := P) (f := MvPolynomial.eval z) (x := MvPolynomial.C c))
  simp [distinguishedDerivativeAt, complexSectionPolynomial, Polynomial.derivative_map,
    Polynomial.eval_map, P, h.symm]

lemma complexSectionPolynomial_no_uhp_root {m : ℕ}
    {p : MvPolynomial (Fin (m + 1)) ℝ}
    (hp : ProofsInTheBook.Chapter22Stable.RealStable p)
    {z : Fin m → ℂ} (hz : ∀ i, 0 < (z i).im) :
    ∀ w : ℂ, 0 < w.im → Polynomial.eval w (complexSectionPolynomial p z) ≠ 0 := by
  intro w hw
  rw [complexSectionPolynomial_eval]
  exact hp (Fin.cons w z) (by
    intro i
    refine Fin.cases ?_ ?_ i
    · exact hw
    · intro j
      exact hz j)

lemma distinguishedDerivativeLine_eval_ne_zero_of_section_derivative_ne_zero {m : ℕ}
    {p : MvPolynomial (Fin (m + 1)) ℝ}
    (hp : ProofsInTheBook.Chapter22Stable.RealStable p)
    {c : ℂ} (hc : 0 < c.im) (a b : Fin m → ℝ) (hb : ∀ j, 0 < b j) :
    ∀ t : ℂ, 0 < t.im →
      Polynomial.derivative
          (complexSectionPolynomial p (fun j => (a j : ℂ) + (b j : ℂ) * t)) ≠ 0 →
      Polynomial.eval t
          (complexLineSection (distinguishedDerivativeAt p c)
            (fun j => (a j : ℂ)) (fun j => (b j : ℂ))) ≠ 0 := by
  intro t ht hder_ne hzero
  let z : Fin m → ℂ := fun j => (a j : ℂ) + (b j : ℂ) * t
  have hz : ∀ j, 0 < (z j).im := by
    intro j
    dsimp [z]
    simp [Complex.mul_im]
    exact mul_pos (hb j) ht
  have hsection_no_roots :
      ∀ w : ℂ, 0 < w.im → Polynomial.eval w (complexSectionPolynomial p z) ≠ 0 :=
    complexSectionPolynomial_no_uhp_root hp hz
  have hsection_roots :
      ∀ w ∈ (complexSectionPolynomial p z).roots, w.im ≤ 0 := by
    intro w hw
    by_contra hnot
    have hwpos : 0 < w.im := lt_of_not_ge hnot
    have hroot := (Polynomial.mem_roots'.mp hw).2
    exact hsection_no_roots w hwpos (by simpa [Polynomial.IsRoot] using hroot)
  have hder_roots :
      ∀ w ∈ (Polynomial.derivative (complexSectionPolynomial p z)).roots, w.im ≤ 0 :=
    ProofsInTheBook.Chapter22Stable.derivative_roots_im_nonpos
      (complexSectionPolynomial p z) hsection_roots
  have hczero :
      Polynomial.eval c (Polynomial.derivative (complexSectionPolynomial p z)) = 0 := by
    have hline :=
      complexLineSection_eval (distinguishedDerivativeAt p c)
        (fun j => (a j : ℂ)) (fun j => (b j : ℂ)) t
    rw [hline] at hzero
    have hdist := distinguishedDerivativeAt_eval p z c
    simpa [z] using hdist.symm.trans hzero
  have hcmem : c ∈ (Polynomial.derivative (complexSectionPolynomial p z)).roots :=
    Polynomial.mem_roots'.mpr ⟨hder_ne, by simpa [Polynomial.IsRoot] using hczero⟩
  have := hder_roots c hcmem
  linarith

lemma sectionPolynomial_coeff_one {m : ℕ} (p : MvPolynomial (Fin (m + 1)) ℝ)
    (x : Fin m → ℝ) :
    Polynomial.coeff (sectionPolynomial p x) 1 =
      MvPolynomial.eval x (firstReduction p) := by
  simp [sectionPolynomial, firstReduction]

lemma sectionPolynomial_coeff_nonneg {m : ℕ} {p : MvPolynomial (Fin (m + 1)) ℝ}
    (hp : NonnegativeCoefficients p) {x : Fin m → ℝ} (hx : ∀ i, 0 ≤ x i) (k : ℕ) :
    0 ≤ Polynomial.coeff (sectionPolynomial p x) k := by
  rw [sectionPolynomial, Polynomial.coeff_map]
  exact eval_nonneg_of_nonnegativeCoefficients
    (coeff_finSuccEquiv_nonnegativeCoefficients hp k) hx

lemma sectionPolynomial_coeff_pos_of_coeff_ne_zero {m : ℕ}
    {p : MvPolynomial (Fin (m + 1)) ℝ}
    (hp : NonnegativeCoefficients p) {x : Fin m → ℝ} (hx : ∀ i, 0 < x i)
    {k : ℕ} (hk : Polynomial.coeff (MvPolynomial.finSuccEquiv ℝ m p) k ≠ 0) :
    0 < Polynomial.coeff (sectionPolynomial p x) k := by
  rw [sectionPolynomial, Polynomial.coeff_map]
  exact eval_pos_of_nonnegativeCoefficients
    (coeff_finSuccEquiv_nonnegativeCoefficients hp k) hk hx

lemma coeff_zero_prod_one_add_mul_X {ι : Type*} [DecidableEq ι] (s : Finset ι)
    (lam : ι → ℝ) :
    (∏ i ∈ s, (1 + Polynomial.C (lam i) * Polynomial.X : Polynomial ℝ)).coeff 0 = 1 := by
  classical
  induction s using Finset.induction with
  | empty =>
      simp
  | insert i s his ih =>
      rw [Finset.prod_insert his]
      rw [Polynomial.mul_coeff_zero, ih]
      simp

lemma coeff_one_prod_one_add_mul_X {ι : Type*} [DecidableEq ι] (s : Finset ι)
    (lam : ι → ℝ) :
    (∏ i ∈ s, (1 + Polynomial.C (lam i) * Polynomial.X : Polynomial ℝ)).coeff 1 =
      ∑ i ∈ s, lam i := by
  classical
  induction s using Finset.induction with
  | empty =>
      simpa using (Polynomial.coeff_one (R := ℝ) (n := 1))
  | insert i s his ih =>
      rw [Finset.prod_insert his, Finset.sum_insert his]
      rw [Polynomial.mul_coeff_one, ih, coeff_zero_prod_one_add_mul_X s lam]
      have hcoeff_one : (1 : Polynomial ℝ).coeff 1 = 0 := by
        simpa using (Polynomial.coeff_one (R := ℝ) (n := 1))
      simp [hcoeff_one]
      ring

lemma coeff_one_C_mul_prod_one_add_mul_X {ι : Type*} [DecidableEq ι] (s : Finset ι)
    (c : ℝ) (lam : ι → ℝ) :
    (Polynomial.C c * ∏ i ∈ s,
        (1 + Polynomial.C (lam i) * Polynomial.X : Polynomial ℝ)).coeff 1 =
      c * ∑ i ∈ s, lam i := by
  rw [Polynomial.coeff_C_mul, coeff_one_prod_one_add_mul_X]

lemma root_neg_of_nonnegative_coefficients_of_coeff_zero_pos {q : Polynomial ℝ}
    (hcoeff : ∀ n : ℕ, 0 ≤ q.coeff n) (h0 : 0 < q.coeff 0)
    {r : ℝ} (hr : r ∈ q.roots) :
    r < 0 := by
  have hroot : q.IsRoot r := (Polynomial.mem_roots'.mp hr).2
  by_contra hnot
  have hr_nonneg : 0 ≤ r := le_of_not_gt hnot
  have hsum_pos :
      0 < ∑ i ∈ Finset.range (q.natDegree + 1), q.coeff i * r ^ i := by
    apply Finset.sum_pos'
    · intro i _hi
      exact mul_nonneg (hcoeff i) (pow_nonneg hr_nonneg i)
    · refine ⟨0, ?_, ?_⟩
      · simp
      · simpa using h0
  have heval : q.eval r = ∑ i ∈ Finset.range (q.natDegree + 1), q.coeff i * r ^ i :=
    Polynomial.eval_eq_sum_range r
  have hzero : q.eval r = 0 := by
    simpa [Polynomial.IsRoot] using hroot
  linarith

lemma roots_enum_toList {α : Type*} (s : Multiset α) {d : ℕ} (hcard : s.card = d) :
    Multiset.map (fun i : Fin d =>
      s.toList.get (Fin.cast (((Multiset.length_toList s).trans hcard).symm) i))
      Finset.univ.val = s := by
  rw [Fin.univ_val_map]
  have hlen : s.toList.length = d := by rw [Multiset.length_toList, hcard]
  change (List.ofFn (fun i : Fin d => s.toList.get (Fin.cast hlen.symm i)) :
    Multiset α) = s
  have hlist :
      List.ofFn (fun i : Fin d => s.toList.get (Fin.cast hlen.symm i)) = s.toList := by
    exact (List.ofFn_congr hlen (s.toList.get)).symm.trans (List.ofFn_get s.toList)
  exact (congrArg (fun l : List α => (l : Multiset α)) hlist).trans (Multiset.coe_toList s)

lemma roots_enum_toList_mem {α : Type*} (s : Multiset α) {d : ℕ} (hcard : s.card = d)
    (i : Fin d) :
    s.toList.get (Fin.cast (((Multiset.length_toList s).trans hcard).symm) i) ∈ s := by
  have hmem : s.toList.get (Fin.cast (((Multiset.length_toList s).trans hcard).symm) i) ∈
      s.toList := List.get_mem _ _
  rwa [Multiset.mem_toList] at hmem

structure FactoredSectionData (k : ℕ) (q : Polynomial ℝ) where
  c : ℝ
  lam : Fin k → ℝ
  c_nonneg : 0 ≤ c
  lam_nonneg : ∀ i, 0 ≤ lam i
  sum_lam_pos : 0 < ∑ i, lam i
  eval_eq : ∀ t : ℝ, Polynomial.eval t q = c * ∏ i, (1 + lam i * t)
  coeff_one_eq : Polynomial.coeff q 1 = c * ∑ i, lam i

noncomputable def rootsAsFin (q : Polynomial ℝ) (hcard : q.roots.card = q.natDegree)
    (i : Fin q.natDegree) : ℝ :=
  q.roots.toList.get
    (Fin.cast (((Multiset.length_toList q.roots).trans hcard).symm) i)

lemma rootsAsFin_mem (q : Polynomial ℝ) (hcard : q.roots.card = q.natDegree)
    (i : Fin q.natDegree) :
    rootsAsFin q hcard i ∈ q.roots := by
  simpa [rootsAsFin] using roots_enum_toList_mem q.roots hcard i

lemma rootsAsFin_enum (q : Polynomial ℝ) (hcard : q.roots.card = q.natDegree) :
    Finset.univ.val.map (rootsAsFin q hcard) = q.roots := by
  simpa [rootsAsFin] using roots_enum_toList q.roots hcard

lemma polynomialCoeff_finSuccEquiv_ne_zero_of_allDegree {m k : ℕ}
    {p : MvPolynomial (Fin (m + 1)) ℝ}
    (hp : AllDegreeCoefficientsPositive (m + 1) p)
    (a : Fin m →₀ ℕ) (hdeg : k + a.degree = m + 1) :
    Polynomial.coeff (MvPolynomial.finSuccEquiv ℝ m p) k ≠ 0 := by
  intro hzero
  have hcoeff_pos :
      0 < MvPolynomial.coeff a (Polynomial.coeff (MvPolynomial.finSuccEquiv ℝ m p) k) := by
    rw [MvPolynomial.finSuccEquiv_coeff_coeff]
    exact hp (Finsupp.cons k a) (by rw [degree_cons, hdeg])
  rw [hzero] at hcoeff_pos
  simp at hcoeff_pos

lemma sectionPolynomial_coeff_pos_of_allDegree {m k : ℕ}
    {p : MvPolynomial (Fin (m + 1)) ℝ}
    (hpcoeff : NonnegativeCoefficients p)
    (hp : AllDegreeCoefficientsPositive (m + 1) p)
    {x : Fin m → ℝ} (hx : PositiveVector x)
    (a : Fin m →₀ ℕ) (hdeg : k + a.degree = m + 1) :
    0 < (sectionPolynomial p x).coeff k := by
  rw [sectionPolynomial, Polynomial.coeff_map]
  exact eval_pos_of_nonnegativeCoefficients
    (coeff_finSuccEquiv_nonnegativeCoefficients hpcoeff k)
    (polynomialCoeff_finSuccEquiv_ne_zero_of_allDegree hp a hdeg) hx

lemma sectionPolynomial_const_coeff_pos_of_allDegree {m : ℕ}
    (hm : 1 ≤ m) {p : MvPolynomial (Fin (m + 1)) ℝ}
    (hpcoeff : NonnegativeCoefficients p)
    (hp : AllDegreeCoefficientsPositive (m + 1) p)
    {x : Fin m → ℝ} (hx : PositiveVector x) :
    0 < (sectionPolynomial p x).coeff 0 := by
  let j0 : Fin m := ⟨0, by omega⟩
  let a : Fin m →₀ ℕ := Finsupp.single j0 (m + 1)
  exact sectionPolynomial_coeff_pos_of_allDegree hpcoeff hp hx a (by simp [a])

lemma sectionPolynomial_top_coeff_pos_of_allDegree {m : ℕ}
    {p : MvPolynomial (Fin (m + 1)) ℝ}
    (hpcoeff : NonnegativeCoefficients p)
    (hp : AllDegreeCoefficientsPositive (m + 1) p)
    {x : Fin m → ℝ} (hx : PositiveVector x) :
    0 < (sectionPolynomial p x).coeff (m + 1) := by
  exact sectionPolynomial_coeff_pos_of_allDegree hpcoeff hp hx 0 (by simp)

lemma sectionPolynomial_natDegree_eq_of_allDegree {m : ℕ}
    {p : MvPolynomial (Fin (m + 1)) ℝ}
    (hpcoeff : NonnegativeCoefficients p)
    (hp : AllDegreeCoefficientsPositive (m + 1) p)
    (hhom : p.IsHomogeneous (m + 1))
    {x : Fin m → ℝ} (hx : PositiveVector x) :
    (sectionPolynomial p x).natDegree = m + 1 := by
  apply Polynomial.natDegree_eq_of_le_of_coeff_ne_zero
  · refine Polynomial.natDegree_map_le.trans ?_
    rw [MvPolynomial.natDegree_finSuccEquiv]
    exact (MvPolynomial.degreeOf_le_totalDegree p 0).trans hhom.totalDegree_le
  · exact ne_of_gt (sectionPolynomial_top_coeff_pos_of_allDegree hpcoeff hp hx)

lemma isHomogeneous_zero_eq_C_coeff_zero_complex {m : ℕ} {p : MvPolynomial (Fin m) ℂ}
    (hp : p.IsHomogeneous 0) :
    p = MvPolynomial.C (MvPolynomial.coeff 0 p) := by
  ext a
  by_cases ha : a = 0
  · subst a
    simp
  · have hdeg_ne : a.degree ≠ 0 := by
      intro hdeg
      exact ha ((Finsupp.degree_eq_zero_iff a).mp hdeg)
    have h0a : ¬ (0 : Fin m →₀ ℕ) = a := fun h => ha h.symm
    rw [hp.coeff_eq_zero hdeg_ne]
    simp [h0a]

lemma complexSectionPolynomial_top_coeff_ne_zero_of_allDegree {m : ℕ}
    {p : MvPolynomial (Fin (m + 1)) ℝ}
    (hp : AllDegreeCoefficientsPositive (m + 1) p)
    (hhom : p.IsHomogeneous (m + 1))
    (z : Fin m → ℂ) :
    (complexSectionPolynomial p z).coeff (m + 1) ≠ 0 := by
  let topPoly : MvPolynomial (Fin m) ℂ :=
    Polynomial.coeff (MvPolynomial.finSuccEquiv ℂ m (p.map (algebraMap ℝ ℂ))) (m + 1)
  have hhomC : (p.map (algebraMap ℝ ℂ)).IsHomogeneous (m + 1) := by
    simpa using hhom.map (algebraMap ℝ ℂ)
  have htopHom : topPoly.IsHomogeneous 0 := by
    dsimp [topPoly]
    simpa using hhomC.finSuccEquiv_coeff_isHomogeneous (m + 1) 0 (by omega)
  have htop0_ne : MvPolynomial.coeff 0 topPoly ≠ 0 := by
    dsimp [topPoly]
    rw [MvPolynomial.finSuccEquiv_coeff_coeff, MvPolynomial.coeff_map]
    exact Complex.ofReal_ne_zero.mpr
      (ne_of_gt (hp (Finsupp.cons (m + 1) 0) (by simp [degree_cons])))
  rw [complexSectionPolynomial, Polynomial.coeff_map]
  change MvPolynomial.eval z topPoly ≠ 0
  rw [isHomogeneous_zero_eq_C_coeff_zero_complex htopHom]
  simpa using htop0_ne

lemma complexSectionPolynomial_natDegree_eq_of_allDegree {m : ℕ}
    {p : MvPolynomial (Fin (m + 1)) ℝ}
    (hp : AllDegreeCoefficientsPositive (m + 1) p)
    (hhom : p.IsHomogeneous (m + 1))
    (z : Fin m → ℂ) :
    (complexSectionPolynomial p z).natDegree = m + 1 := by
  apply Polynomial.natDegree_eq_of_le_of_coeff_ne_zero
  · refine Polynomial.natDegree_map_le.trans ?_
    rw [MvPolynomial.natDegree_finSuccEquiv]
    have hhomC : (p.map (algebraMap ℝ ℂ)).IsHomogeneous (m + 1) := by
      simpa using hhom.map (algebraMap ℝ ℂ)
    exact (MvPolynomial.degreeOf_le_totalDegree (p.map (algebraMap ℝ ℂ)) 0).trans
      hhomC.totalDegree_le
  · exact complexSectionPolynomial_top_coeff_ne_zero_of_allDegree hp hhom z

lemma coeff_finSuccEquiv_map_complex {m : ℕ}
    (p : MvPolynomial (Fin (m + 1)) ℝ) (k : ℕ) :
    Polynomial.coeff (MvPolynomial.finSuccEquiv ℂ m (p.map (algebraMap ℝ ℂ))) k =
      (Polynomial.coeff (MvPolynomial.finSuccEquiv ℝ m p) k).map (algebraMap ℝ ℂ) := by
  ext a
  rw [MvPolynomial.finSuccEquiv_coeff_coeff]
  rw [MvPolynomial.coeff_map, MvPolynomial.coeff_map]
  rw [MvPolynomial.finSuccEquiv_coeff_coeff]

lemma complexSectionPolynomial_ofReal {m : ℕ}
    (p : MvPolynomial (Fin (m + 1)) ℝ) (x : Fin m → ℝ) :
    complexSectionPolynomial p (fun j => (x j : ℂ)) =
      (sectionPolynomial p x).map (algebraMap ℝ ℂ) := by
  ext k
  simp [complexSectionPolynomial, sectionPolynomial, Polynomial.coeff_map,
    coeff_finSuccEquiv_map_complex]
  rw [MvPolynomial.eval₂_eq_eval_map]
  exact (MvPolynomial.map_eval (q := algebraMap ℝ ℂ) (g := x)
    (p := ((MvPolynomial.finSuccEquiv ℝ m) p).coeff k)).symm

lemma complexSectionPolynomial_coeff_tendsto {m : ℕ}
    (p : MvPolynomial (Fin (m + 1)) ℝ) {zN : ℕ → Fin m → ℂ} {z : Fin m → ℂ}
    (hz : Filter.Tendsto zN Filter.atTop (nhds z)) (k : ℕ) :
    Filter.Tendsto (fun N : ℕ => (complexSectionPolynomial p (zN N)).coeff k)
      Filter.atTop (nhds ((complexSectionPolynomial p z).coeff k)) := by
  simp [complexSectionPolynomial, Polynomial.coeff_map]
  exact ((MvPolynomial.continuous_eval
    (Polynomial.coeff (MvPolynomial.finSuccEquiv ℂ m (p.map (algebraMap ℝ ℂ))) k)).tendsto z).comp hz

lemma tendsto_upper_perturb {m : ℕ} (x : Fin m → ℝ) :
    Filter.Tendsto
      (fun N : ℕ => fun j : Fin m => (x j : ℂ) + (((N + 1 : ℕ) : ℝ)⁻¹ : ℂ) * Complex.I)
      Filter.atTop (nhds (fun j : Fin m => (x j : ℂ))) := by
  rw [tendsto_pi_nhds]
  intro j
  have hepsR : Filter.Tendsto (fun N : ℕ => (((N + 1 : ℕ) : ℝ)⁻¹ : ℝ))
      Filter.atTop (nhds 0) := by
    simpa using (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  have hepsC : Filter.Tendsto (fun N : ℕ => ((((N + 1 : ℕ) : ℝ)⁻¹ : ℝ) : ℂ))
      Filter.atTop (nhds 0) :=
    Complex.continuous_ofReal.continuousAt.tendsto.comp hepsR
  simpa using (tendsto_const_nhds.add (hepsC.mul tendsto_const_nhds))

lemma upper_perturb_im_pos {m : ℕ} (x : Fin m → ℝ) (N : ℕ) (j : Fin m) :
    0 < ((x j : ℂ) + (((N + 1 : ℕ) : ℝ)⁻¹ : ℂ) * Complex.I).im := by
  simp only [Complex.add_im, Complex.ofReal_im, zero_add, Complex.mul_I_im]
  rw [Complex.inv_re]
  have hpos : 0 < (((N + 1 : ℕ) : ℝ)) := by positivity
  have hnorm : 0 < Complex.normSq ((((N + 1 : ℕ) : ℝ) : ℂ)) := by
    exact Complex.normSq_pos.mpr (by exact_mod_cast ne_of_gt hpos)
  exact div_pos hpos hnorm

lemma sectionPolynomial_realRooted_of_realStable_allDegree {m : ℕ}
    {p : MvPolynomial (Fin (m + 1)) ℝ}
    (hstable : ProofsInTheBook.Chapter22Stable.RealStable p)
    (hp : AllDegreeCoefficientsPositive (m + 1) p)
    (hhom : p.IsHomogeneous (m + 1))
    (x : Fin m → ℝ) :
    ProofsInTheBook.Chapter22Stable.RealRooted (sectionPolynomial p x) := by
  let zN : ℕ → Fin m → ℂ := fun N j =>
    (x j : ℂ) + (((N + 1 : ℕ) : ℝ)⁻¹ : ℂ) * Complex.I
  let z0 : Fin m → ℂ := fun j => (x j : ℂ)
  let qN : ℕ → Polynomial ℂ := fun N => complexSectionPolynomial p (zN N)
  let q0 : Polynomial ℂ := complexSectionPolynomial p z0
  have hzN : Filter.Tendsto zN Filter.atTop (nhds z0) := by
    simpa [zN, z0] using tendsto_upper_perturb x
  have hdegN : ∀ N, (qN N).natDegree = m + 1 := by
    intro N
    exact complexSectionPolynomial_natDegree_eq_of_allDegree hp hhom (zN N)
  have hdeg0 : q0.natDegree = m + 1 :=
    complexSectionPolynomial_natDegree_eq_of_allDegree hp hhom z0
  have hq0_ne : q0 ≠ 0 := by
    intro hzero
    have := hdeg0
    rw [hzero, Polynomial.natDegree_zero] at this
    omega
  have hcoeff : ∀ k, Filter.Tendsto (fun N : ℕ => (qN N).coeff k) Filter.atTop
      (nhds (q0.coeff k)) := by
    intro k
    exact complexSectionPolynomial_coeff_tendsto p hzN k
  have hrootsN : ∀ N, ∀ w ∈ (qN N).roots, w.im ≤ 0 := by
    intro N w hw
    by_contra hnot
    have hwpos : 0 < w.im := lt_of_not_ge hnot
    have hroot := (Polynomial.mem_roots'.mp hw).2
    exact complexSectionPolynomial_no_uhp_root hstable
      (fun j => upper_perturb_im_pos x N j) w hwpos
      (by simpa [qN, zN, Polynomial.IsRoot] using hroot)
  have hroots0 : ∀ w ∈ q0.roots, w.im ≤ 0 :=
    ProofsInTheBook.Chapter22Stable.roots_im_nonpos_of_tendsto (m + 1) qN q0
      hdegN hdeg0 hq0_ne hcoeff hrootsN
  apply ProofsInTheBook.Chapter22Stable.realRooted_of_forall_uhp_ne_zero
  intro w hw hzero
  have hzero_eval : Polynomial.eval w q0 = 0 := by
    dsimp [q0, z0]
    rw [complexSectionPolynomial_ofReal]
    simpa [Polynomial.aeval_def, Polynomial.eval_map] using hzero
  have hmem : w ∈ q0.roots :=
    Polynomial.mem_roots'.mpr ⟨hq0_ne, by simpa [Polynomial.IsRoot] using hzero_eval⟩
  have := hroots0 w hmem
  linarith

lemma tendsto_I_inv_nat :
    Filter.Tendsto (fun N : ℕ => ((((N + 1 : ℕ) : ℝ)⁻¹ : ℂ) * Complex.I))
      Filter.atTop (nhds 0) := by
  have hepsR : Filter.Tendsto (fun N : ℕ => (((N + 1 : ℕ) : ℝ)⁻¹ : ℝ))
      Filter.atTop (nhds 0) := by
    simpa using (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  have hepsC : Filter.Tendsto (fun N : ℕ => ((((N + 1 : ℕ) : ℝ)⁻¹ : ℝ) : ℂ))
      Filter.atTop (nhds 0) :=
    Complex.continuous_ofReal.continuousAt.tendsto.comp hepsR
  simpa using hepsC.mul tendsto_const_nhds

lemma I_inv_nat_im_pos (N : ℕ) :
    0 < ((((N + 1 : ℕ) : ℝ)⁻¹ : ℂ) * Complex.I).im := by
  simp only [Complex.mul_I_im]
  rw [Complex.inv_re]
  have hpos : 0 < (((N + 1 : ℕ) : ℝ)) := by positivity
  have hnorm : 0 < Complex.normSq ((((N + 1 : ℕ) : ℝ) : ℂ)) := by
    exact Complex.normSq_pos.mpr (by exact_mod_cast ne_of_gt hpos)
  exact div_pos hpos hnorm

lemma firstReduction_ne_zero_of_allDegree {m : ℕ} (hm : 1 ≤ m)
    {p : MvPolynomial (Fin (m + 1)) ℝ}
    (hp : AllDegreeCoefficientsPositive (m + 1) p) :
    firstReduction p ≠ 0 := by
  let j0 : Fin m := ⟨0, by omega⟩
  let a : Fin m →₀ ℕ := Finsupp.single j0 m
  have hpos : 0 < MvPolynomial.coeff a (firstReduction p) :=
    allDegreeCoefficientsPositive_firstReduction hp a (by simp [a])
  intro hzero
  rw [hzero] at hpos
  simp at hpos

lemma complexSectionPolynomial_derivative_ne_zero_of_allDegree {m : ℕ}
    {p : MvPolynomial (Fin (m + 1)) ℝ}
    (hp : AllDegreeCoefficientsPositive (m + 1) p)
    (hhom : p.IsHomogeneous (m + 1)) (z : Fin m → ℂ) :
    Polynomial.derivative (complexSectionPolynomial p z) ≠ 0 := by
  intro hder
  have hnat0 := Polynomial.natDegree_eq_zero_of_derivative_eq_zero hder
  have hnat := complexSectionPolynomial_natDegree_eq_of_allDegree hp hhom z
  rw [hnat] at hnat0
  omega

lemma firstReduction_realStable_of_allDegree {m : ℕ} (hm : 1 ≤ m)
    {p : MvPolynomial (Fin (m + 1)) ℝ}
    (hpcoeff : NonnegativeCoefficients p)
    (hp : AllDegreeCoefficientsPositive (m + 1) p)
    (hhom : p.IsHomogeneous (m + 1))
    (hstable : ProofsInTheBook.Chapter22Stable.RealStable p) :
    ProofsInTheBook.Chapter22Stable.RealStable (firstReduction p) := by
  intro z hz hzero
  let ar : Fin m → ℝ := fun j => (z j).re
  let br : Fin m → ℝ := fun j => (z j).im
  let a : Fin m → ℂ := fun j => (ar j : ℂ)
  let b : Fin m → ℂ := fun j => (br j : ℂ)
  let cN : ℕ → ℂ := fun N => ((((N + 1 : ℕ) : ℝ)⁻¹ : ℂ) * Complex.I)
  let qN : ℕ → Polynomial ℂ := fun N =>
    complexLineSection (distinguishedDerivativeAt p (cN N)) a b
  let q0 : Polynomial ℂ :=
    complexLineSection ((firstReduction p).map (algebraMap ℝ ℂ)) a b
  have hbpos : ∀ j, 0 < br j := by
    intro j
    exact hz j
  have hfr_ne : firstReduction p ≠ 0 := firstReduction_ne_zero_of_allDegree hm hp
  have hdeg0 : q0.natDegree = m := by
    dsimp [q0, a, b]
    exact complexLineSection_firstReduction_natDegree hpcoeff hhom hfr_ne ar br hbpos
  have hq0_ne : q0 ≠ 0 := by
    intro hq
    have := hdeg0
    rw [hq, Polynomial.natDegree_zero] at this
    omega
  have hq0_coeff_m_ne : q0.coeff m ≠ 0 := by
    have hlead := Polynomial.leadingCoeff_ne_zero.mpr hq0_ne
    simpa [Polynomial.leadingCoeff, hdeg0] using hlead
  have hcoeff : ∀ k, Filter.Tendsto (fun N : ℕ => (qN N).coeff k) Filter.atTop
      (nhds (q0.coeff k)) := by
    intro k
    let P : Polynomial (MvPolynomial (Fin m) ℂ) :=
      Polynomial.derivative (MvPolynomial.finSuccEquiv ℂ m (p.map (algebraMap ℝ ℂ)))
    have ht := (continuous_complexLineSection_coeff_eval_C P a b k).tendsto 0
    have ht' := ht.comp tendsto_I_inv_nat
    have hlimit :
        complexLineSection (Polynomial.eval (MvPolynomial.C 0) P) a b = q0 := by
      dsimp [P, q0]
      simpa [distinguishedDerivativeAt] using
        congrArg (fun q => complexLineSection q a b) (distinguishedDerivativeAt_zero p)
    rw [hlimit] at ht'
    simpa [Function.comp_def, qN, cN, P, distinguishedDerivativeAt] using ht'
  have hdegN_eventually : ∀ᶠ N in Filter.atTop, (qN N).natDegree = m := by
    have hnorm_tend := (hcoeff m).norm
    have hnorm_pos : 0 < ‖q0.coeff m‖ := norm_pos_iff.mpr hq0_coeff_m_ne
    have hev : ∀ᶠ N in Filter.atTop, 0 < ‖(qN N).coeff m‖ :=
      hnorm_tend.eventually (lt_mem_nhds hnorm_pos)
    filter_upwards [hev] with N hNnorm
    have hcoeff_ne : (qN N).coeff m ≠ 0 := norm_pos_iff.mp hNnorm
    have hle : (qN N).natDegree ≤ m := by
      dsimp [qN]
      exact (complexLineSection_natDegree_le_totalDegree (distinguishedDerivativeAt p (cN N)) a b).trans
        (distinguishedDerivativeAt_totalDegree_le hhom (cN N))
    exact Polynomial.natDegree_eq_of_le_of_coeff_ne_zero hle hcoeff_ne
  have hrootsN : ∀ᶠ N in Filter.atTop, ∀ w ∈ (qN N).roots, w.im ≤ 0 := by
    apply Filter.Eventually.of_forall
    intro N w hw
    by_contra hnot
    have hwpos : 0 < w.im := lt_of_not_ge hnot
    have hroot := (Polynomial.mem_roots'.mp hw).2
    have hne_der : Polynomial.derivative
        (complexSectionPolynomial p (fun j => (ar j : ℂ) + (br j : ℂ) * w)) ≠ 0 :=
      complexSectionPolynomial_derivative_ne_zero_of_allDegree hp hhom _
    have hne := distinguishedDerivativeLine_eval_ne_zero_of_section_derivative_ne_zero hstable
      (I_inv_nat_im_pos N) ar br hbpos w hwpos hne_der
    exact hne (by simpa [qN, cN, a, b, Polynomial.IsRoot] using hroot)
  have hroots0 : ∀ w ∈ q0.roots, w.im ≤ 0 :=
    ProofsInTheBook.Chapter22Stable.roots_im_nonpos_of_tendsto_eventually m qN q0
      hdegN_eventually hdeg0 hq0_ne hcoeff hrootsN
  have hz_repr : (fun j : Fin m => (ar j : ℂ) + (br j : ℂ) * Complex.I) = z := by
    funext j
    apply Complex.ext <;> simp [ar, br]
  have hIroot_eval : Polynomial.eval Complex.I q0 = 0 := by
    dsimp [q0, a, b]
    rw [complexLineSection_eval, hz_repr]
    simpa using hzero
  have hImem : Complex.I ∈ q0.roots :=
    Polynomial.mem_roots'.mpr ⟨hq0_ne, by simpa [Polynomial.IsRoot] using hIroot_eval⟩
  have hI_im_nonpos := hroots0 Complex.I hImem
  norm_num at hI_im_nonpos

noncomputable def factoredSectionData_natDegree_of_realRooted_nonnegative {q : Polynomial ℝ}
    (hcoeff : ∀ n : ℕ, 0 ≤ q.coeff n) (h0 : 0 < q.coeff 0)
    (hrooted : ProofsInTheBook.Chapter22Stable.RealRooted q)
    (hdeg_pos : 0 < q.natDegree) :
    FactoredSectionData q.natDegree q := by
  classical
  have hq_ne : q ≠ 0 := by
    intro hq
    rw [hq] at h0
    simp at h0
  have hsplits : q.Splits := by
    rw [Polynomial.splits_iff_card_roots]
    exact hrooted
  have hcard : q.roots.card = q.natDegree := hrooted
  let r : Fin q.natDegree → ℝ := rootsAsFin q hcard
  let lam : Fin q.natDegree → ℝ := fun i => - (r i)⁻¹
  have hr_mem : ∀ i, r i ∈ q.roots := by
    intro i
    exact rootsAsFin_mem q hcard i
  have hr_neg : ∀ i, r i < 0 := by
    intro i
    exact root_neg_of_nonnegative_coefficients_of_coeff_zero_pos hcoeff h0 (hr_mem i)
  have hr_ne : ∀ i, r i ≠ 0 := fun i => (hr_neg i).ne
  have hlam_pos : ∀ i, 0 < lam i := by
    intro i
    dsimp [lam]
    have hinv : (r i)⁻¹ < 0 := by
      simpa using (inv_lt_zero.mpr (hr_neg i))
    linarith
  have hroots_enum : Finset.univ.val.map r = q.roots := by
    simpa [r] using rootsAsFin_enum q hcard
  have heval_roots : ∀ t : ℝ, q.eval t = q.leadingCoeff * ∏ i, (t - r i) := by
    intro t
    have h := hsplits.eval_eq_prod_roots t
    rw [← hroots_enum] at h
    simpa [Finset.prod, Multiset.map_map, Function.comp_def] using h
  have hconst : q.coeff 0 = q.leadingCoeff * ∏ i, (-r i) := by
    have h0eval := heval_roots 0
    rw [Polynomial.coeff_zero_eq_eval_zero]
    simpa using h0eval
  have heval_factored : ∀ t : ℝ,
      q.eval t = q.coeff 0 * ∏ i, (1 + lam i * t) := by
    intro t
    have hfactor_each : ∀ i : Fin q.natDegree,
        t - r i = (-r i) * (1 + lam i * t) := by
      intro i
      dsimp [lam]
      field_simp [hr_ne i]
      ring
    have hprod :
        (∏ i, (t - r i)) = (∏ i, (-r i)) * ∏ i, (1 + lam i * t) := by
      simp_rw [hfactor_each]
      rw [Finset.prod_mul_distrib]
    rw [heval_roots t, hprod, hconst]
    ring
  refine
    ⟨q.coeff 0, lam, le_of_lt h0, (fun i => le_of_lt (hlam_pos i)), ?_, ?_, ?_⟩
  · haveI : Nonempty (Fin q.natDegree) := ⟨⟨0, hdeg_pos⟩⟩
    exact Finset.sum_pos (fun i _ => hlam_pos i) Finset.univ_nonempty
  · exact heval_factored
  · have hpoly :
        q = Polynomial.C (q.coeff 0) *
          ∏ i, (1 + Polynomial.C (lam i) * Polynomial.X : Polynomial ℝ) := by
      apply Polynomial.funext
      intro t
      calc
        q.eval t = q.coeff 0 * ∏ i, (1 + lam i * t) := heval_factored t
        _ = Polynomial.eval t
            (Polynomial.C (q.coeff 0) *
              ∏ i, (1 + Polynomial.C (lam i) * Polynomial.X : Polynomial ℝ)) := by
              have hprod_eval :
                  Polynomial.eval t
                    (∏ i, (1 + Polynomial.C (lam i) * Polynomial.X : Polynomial ℝ)) =
                    ∏ i, (1 + lam i * t) := by
                rw [Polynomial.eval_prod]
                simp
              rw [Polynomial.eval_mul, Polynomial.eval_C, hprod_eval]
    calc
      q.coeff 1 =
          (Polynomial.C (q.coeff 0) *
            ∏ i, (1 + Polynomial.C (lam i) * Polynomial.X : Polynomial ℝ)).coeff 1 :=
        congrArg (fun p : Polynomial ℝ => p.coeff 1) hpoly
      _ = q.coeff 0 * ∑ i, lam i :=
        coeff_one_C_mul_prod_one_add_mul_X
          (Finset.univ : Finset (Fin q.natDegree)) (q.coeff 0) lam

def PositiveFactoredSections {m : ℕ} (p : MvPolynomial (Fin (m + 1)) ℝ) : Type :=
  ∀ x : Fin m → ℝ, PositiveVector x →
    FactoredSectionData (m + 1) (sectionPolynomial p x)

noncomputable def positiveFactoredSections_of_realRooted_sections {m : ℕ}
    {p : MvPolynomial (Fin (m + 1)) ℝ}
    (hpcoeff : NonnegativeCoefficients p)
    (hrooted :
      ∀ x : Fin m → ℝ, PositiveVector x →
        ProofsInTheBook.Chapter22Stable.RealRooted (sectionPolynomial p x))
    (hconst :
      ∀ x : Fin m → ℝ, PositiveVector x →
        0 < (sectionPolynomial p x).coeff 0)
    (hdegree :
      ∀ x : Fin m → ℝ, PositiveVector x →
        (sectionPolynomial p x).natDegree = m + 1) :
    PositiveFactoredSections p := by
  intro x hx
  have hcoeff : ∀ n : ℕ, 0 ≤ (sectionPolynomial p x).coeff n := by
    intro n
    exact sectionPolynomial_coeff_nonneg hpcoeff (fun i => le_of_lt (hx i)) n
  have hdeg_pos : 0 < (sectionPolynomial p x).natDegree := by
    rw [hdegree x hx]
    omega
  simpa [hdegree x hx] using
    factoredSectionData_natDegree_of_realRooted_nonnegative
      (q := sectionPolynomial p x) hcoeff (hconst x hx) (hrooted x hx) hdeg_pos

noncomputable def positiveFactoredSections_of_realStable_allDegree {m : ℕ}
    (hm : 1 ≤ m) {p : MvPolynomial (Fin (m + 1)) ℝ}
    (hpcoeff : NonnegativeCoefficients p)
    (hp : AllDegreeCoefficientsPositive (m + 1) p)
    (hhom : p.IsHomogeneous (m + 1))
    (hstable : ProofsInTheBook.Chapter22Stable.RealStable p) :
    PositiveFactoredSections p :=
  positiveFactoredSections_of_realRooted_sections hpcoeff
    (fun x _hx => sectionPolynomial_realRooted_of_realStable_allDegree hstable hp hhom x)
    (fun _x hx => sectionPolynomial_const_coeff_pos_of_allDegree hm hpcoeff hp hx)
    (fun _x hx => sectionPolynomial_natDegree_eq_of_allDegree hpcoeff hp hhom hx)

lemma firstReduction_capLB_of_factoredSections {m : ℕ}
    {p : MvPolynomial (Fin (m + 1)) ℝ} {C : ℝ}
    (hm : 1 ≤ m)
    (hsections : PositiveFactoredSections p)
    (hcap : CapLB p C) :
    CapLB (firstReduction p) (G (m + 1) * C) := by
  intro x hx
  obtain ⟨c, lam, hc, hlam, hS, heval, hcoeff⟩ := hsections x hx
  have hbound :
      ∀ t : ℝ, 0 < t →
        (C * ∏ i, x i) * t ≤ c * ∏ i, (1 + lam i * t) := by
    intro t ht
    have hpos : PositiveVector (Fin.cons t x) := by
      intro i
      refine Fin.cases ?_ ?_ i
      · exact ht
      · intro j
        exact hx j
    have h := hcap (Fin.cons t x) hpos
    rw [← sectionPolynomial_eval p x t, heval t] at h
    simpa [Fin.prod_univ_succ, mul_assoc, mul_comm, mul_left_comm] using h
  have hstep :
      G (m + 1) * (C * ∏ i, x i) ≤ c * ∑ i, lam i :=
    univariate_gurvits_factored (k := m + 1) (by omega) c
      (C * ∏ i, x i) lam hc hlam hS hbound
  calc
    (G (m + 1) * C) * ∏ i, x i =
        G (m + 1) * (C * ∏ i, x i) := by ring
    _ ≤ c * ∑ i, lam i := hstep
    _ = Polynomial.coeff (sectionPolynomial p x) 1 := hcoeff.symm
    _ = MvPolynomial.eval x (firstReduction p) := sectionPolynomial_coeff_one p x

lemma rowLinear_capLB_one_of_capacity {n : ℕ}
    {A : Matrix (Fin n) (Fin n) ℝ}
    (hcap : RowLinearCapacityAtLeastOne A) :
    CapLB (rowLinearMvPolynomial A) 1 := by
  intro x hx
  simpa [CapLB, PositiveVector, eval_rowLinearMvPolynomial, one_mul] using
    hcap.le_rowLinearProduct x hx

lemma row_sum_pos_of_nonnegative_of_capacity {n : ℕ}
    {A : Matrix (Fin n) (Fin n) ℝ}
    (hA : ∀ i j, 0 ≤ A i j)
    (hcap : RowLinearCapacityAtLeastOne A) (i : Fin n) :
    0 < ∑ j, A i j := by
  have hx : PositiveVector (fun _ : Fin n => (1 : ℝ)) := by
    intro j
    positivity
  have h := hcap.le_rowLinearProduct (fun _ : Fin n => (1 : ℝ)) hx
  have hprod_ge_one : 1 ≤ ∏ i, ∑ j, A i j := by
    simpa [rowLinearProduct] using h
  have hprod_pos : 0 < ∏ i, ∑ j, A i j := by linarith
  have hrow_nonneg : 0 ≤ ∑ j, A i j :=
    Finset.sum_nonneg fun j _ => hA i j
  by_contra hnot
  have hrow_le_zero : ∑ j, A i j ≤ 0 := le_of_not_gt hnot
  have hrow_zero : ∑ j, A i j = 0 := le_antisymm hrow_le_zero hrow_nonneg
  have hprod_zero : (∏ i, ∑ j, A i j) = 0 :=
    Finset.prod_eq_zero (Finset.mem_univ i) hrow_zero
  linarith

lemma rowLinearMvPolynomial_realStable_of_capacity {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℝ)
    (hA : ∀ i j, 0 ≤ A i j)
    (hcap : RowLinearCapacityAtLeastOne A) :
    ProofsInTheBook.Chapter22Stable.RealStable (rowLinearMvPolynomial A) :=
  ProofsInTheBook.Chapter22Stable.rowLinearMvPolynomial_realStable A hA
    (row_sum_pos_of_nonnegative_of_capacity hA hcap)

theorem stable_allDegree_capacity_bound :
    ∀ (m : ℕ) (p : MvPolynomial (Fin m) ℝ) (C : ℝ), 1 ≤ m →
      NonnegativeCoefficients p →
      AllDegreeCoefficientsPositive m p →
      p.IsHomogeneous m →
      ProofsInTheBook.Chapter22Stable.RealStable p →
      CapLB p C →
      (∏ i ∈ Finset.Icc 2 m, G i) * C ≤
        MvPolynomial.coeff (squarefreeExponent m) p
  | 0, _p, _C, hm, _hpcoeff, _hpall, _hhom, _hstable, _hcap => by omega
  | 1, p, C, _hm, _hpcoeff, _hpall, hhom, _hstable, hcap => by
      have hx : PositiveVector (fun _ : Fin 1 => (1 : ℝ)) := by
        intro i
        fin_cases i
        positivity
      have h := hcap (fun _ : Fin 1 => (1 : ℝ)) hx
      simpa [eval_one_eq_squarefreeCoeff_of_homogeneous_one hhom] using h
  | m + 2, p, C, _hm, hpcoeff, hpall, hhom, hstable, hcap => by
      let p' : MvPolynomial (Fin (m + 1)) ℝ := firstReduction p
      have hm1 : 1 ≤ m + 1 := by omega
      have hsections : PositiveFactoredSections p :=
        positiveFactoredSections_of_realStable_allDegree hm1 hpcoeff hpall hhom hstable
      have hcap' : CapLB p' (G (m + 2) * C) := by
        exact firstReduction_capLB_of_factoredSections hm1 hsections hcap
      have hpcoeff' : NonnegativeCoefficients p' :=
        firstReduction_nonnegativeCoefficients hpcoeff
      have hpall' : AllDegreeCoefficientsPositive (m + 1) p' :=
        allDegreeCoefficientsPositive_firstReduction hpall
      have hhom' : p'.IsHomogeneous (m + 1) :=
        firstReduction_isHomogeneous hhom
      have hstable' : ProofsInTheBook.Chapter22Stable.RealStable p' :=
        firstReduction_realStable_of_allDegree hm1 hpcoeff hpall hhom hstable
      have ih := stable_allDegree_capacity_bound (m + 1) p' (G (m + 2) * C)
        hm1 hpcoeff' hpall' hhom' hstable' hcap'
      have hcoeff_eq :
          MvPolynomial.coeff (squarefreeExponent (m + 1)) p' =
            MvPolynomial.coeff (squarefreeExponent (m + 2)) p := by
        dsimp [p']
        rw [coeff_firstReduction, squarefreeExponent_succ]
      rw [← hcoeff_eq]
      calc
        (∏ i ∈ Finset.Icc 2 (m + 2), G i) * C =
            (∏ i ∈ Finset.Icc 2 (m + 1), G i) * (G (m + 2) * C) := by
              rw [Finset.prod_Icc_succ_top (by omega : 2 ≤ m + 2)]
              ring
        _ ≤ MvPolynomial.coeff (squarefreeExponent (m + 1)) p' := ih

structure GurvitsCapacityReductionData (n : ℕ)
    (A : Matrix (Fin n) (Fin n) ℝ) where
  cap : ℕ → ℝ
  top_capacity : 1 ≤ cap n
  step_capacity :
    ∀ m, 2 ≤ m → m ≤ n → G m * cap m ≤ cap (m - 1)
  bottom_capacity : cap 1 ≤ rowLinearSquarefreeCoefficient A

/-- **The capacity iteration.** Given a capacity sequence `cap` with the per-step Gurvits
bound `G(m)·cap(m) ≤ cap(m-1)` for `2 ≤ m ≤ n`, the product of the constants times `cap(n)`
bounds `cap(1)`: `(∏_{m=2}^n G(m))·cap(n) ≤ cap(1)`. (Combined with the telescoping identity
and `cap(n) ≥ 1`, this gives the `n!/nⁿ` bound.) -/
lemma capacity_chain (cap : ℕ → ℝ) :
    ∀ n, 1 ≤ n → (∀ m, 2 ≤ m → m ≤ n → G m * cap m ≤ cap (m - 1)) →
      (∏ m ∈ Finset.Icc 2 n, G m) * cap n ≤ cap 1 := by
  intro n
  induction n with
  | zero => intro h; omega
  | succ n ih =>
      intro _hn hstep
      rcases Nat.lt_or_ge n 1 with hn0 | hn1
      · -- n = 0, so succ n = 1: empty product
        interval_cases n
        simp
      · -- n ≥ 1
        have hstep' : ∀ m, 2 ≤ m → m ≤ n → G m * cap m ≤ cap (m - 1) :=
          fun m hm2 hmn => hstep m hm2 (by omega)
        have hIH := ih hn1 hstep'
        have hprodnn : 0 ≤ ∏ m ∈ Finset.Icc 2 n, G m :=
          Finset.prod_nonneg (fun m _ => G_nonneg m)
        rw [Finset.prod_Icc_succ_top (by omega : 2 ≤ n + 1)]
        calc (∏ m ∈ Finset.Icc 2 n, G m) * G (n + 1) * cap (n + 1)
            = (∏ m ∈ Finset.Icc 2 n, G m) * (G (n + 1) * cap (n + 1)) := by ring
          _ ≤ (∏ m ∈ Finset.Icc 2 n, G m) * cap n := by
              apply mul_le_mul_of_nonneg_left _ hprodnn
              have := hstep (n + 1) (by omega) (by omega)
              simpa using this
          _ ≤ cap 1 := hIH

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

theorem iteratedCapacityCertificate_of_capacityReductionData (n : ℕ) (hn : 1 ≤ n)
    (hdata :
      ∀ A : Matrix (Fin n) (Fin n) ℝ,
        (∀ i j, 0 ≤ A i j) →
        RowLinearCapacityAtLeastOne A →
        GurvitsCapacityReductionData n A) :
    GurvitsIteratedCapacityCertificate n := by
  refine ⟨?_⟩
  intro A hA hcap
  let data := hdata A hA hcap
  have hchain :
      (∏ m ∈ Finset.Icc 2 n, G m) * data.cap n ≤ data.cap 1 :=
    capacity_chain data.cap n hn data.step_capacity
  have hprod_nonneg : 0 ≤ ∏ m ∈ Finset.Icc 2 n, G m :=
    Finset.prod_nonneg fun m _ => G_nonneg m
  have hprod_le :
      (∏ m ∈ Finset.Icc 2 n, G m) ≤
        (∏ m ∈ Finset.Icc 2 n, G m) * data.cap n := by
    calc
      (∏ m ∈ Finset.Icc 2 n, G m) =
          (∏ m ∈ Finset.Icc 2 n, G m) * 1 := by ring
      _ ≤ (∏ m ∈ Finset.Icc 2 n, G m) * data.cap n :=
          mul_le_mul_of_nonneg_left data.top_capacity hprod_nonneg
  exact hprod_le.trans (hchain.trans data.bottom_capacity)

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

theorem chapter22_from_capacityReductionData
    (hdata :
      ∀ m : ℕ, 3 ≤ m →
        ∀ A : Matrix (Fin m) (Fin m) ℝ,
          (∀ i j, 0 ≤ A i j) →
          RowLinearCapacityAtLeastOne A →
          GurvitsCapacityReductionData m A)
    (n : ℕ) (A : Matrix (Fin n) (Fin n) ℝ)
    (hA : A ∈ doublyStochastic ℝ (Fin n)) :
    (n.factorial : ℝ) / (n : ℝ) ^ n ≤ A.permanent := by
  exact chapter22_from_iteratedCapacityCertificate
    (fun m hm =>
      iteratedCapacityCertificate_of_capacityReductionData m (by omega) (hdata m hm))
    n A hA

theorem chapter22_positive (n : ℕ) (A : Matrix (Fin n) (Fin n) ℝ)
    (hpos : ∀ i j, 0 < A i j)
    (hA : A ∈ doublyStochastic ℝ (Fin n)) :
    (n.factorial : ℝ) / (n : ℝ) ^ n ≤ A.permanent := by
  by_cases hn0 : n = 0
  · subst n
    simpa using Chapter22.van_der_Waerden_permanent_fin_zero A hA
  · have hn : 1 ≤ n := Nat.succ_le_of_lt (Nat.pos_of_ne_zero hn0)
    have hnonneg : ∀ i j, 0 ≤ A i j := fun i j => le_of_lt (hpos i j)
    have hcap : RowLinearCapacityAtLeastOne A :=
      rowLinearCapacityAtLeastOne_of_doublyStochastic A hA
    have hbound :
        (∏ i ∈ Finset.Icc 2 n, G i) ≤ rowLinearSquarefreeCoefficient A := by
      have h := stable_allDegree_capacity_bound n (rowLinearMvPolynomial A) 1 hn
        (rowLinearMvPolynomial_nonnegativeCoefficients A hnonneg)
        (rowLinearMvPolynomial_allDegreeCoefficientsPositive A hpos)
        (rowLinearMvPolynomial_isHomogeneous A)
        (rowLinearMvPolynomial_realStable_of_capacity A hnonneg hcap)
        (rowLinear_capLB_one_of_capacity hcap)
      simpa [rowLinearSquarefreeCoefficient] using h
    rw [rowLinearSquarefreeCoefficient_eq_permanent A] at hbound
    simpa [gurvits_product_telescopes n hn] using hbound

lemma permanent_tendsto_of_entrywise {n : ℕ}
    {B : ℕ → Matrix (Fin n) (Fin n) ℝ} {A : Matrix (Fin n) (Fin n) ℝ}
    (hentry : ∀ i j, Filter.Tendsto (fun N : ℕ => B N i j) Filter.atTop
      (nhds (A i j))) :
    Filter.Tendsto (fun N : ℕ => (B N).permanent) Filter.atTop (nhds A.permanent) := by
  classical
  unfold Matrix.permanent
  exact tendsto_finsetSum Finset.univ fun σ _ =>
    tendsto_finsetProd Finset.univ fun i _ => hentry (σ i) i

theorem chapter22_unconditional (n : ℕ) (A : Matrix (Fin n) (Fin n) ℝ)
    (hA : A ∈ doublyStochastic ℝ (Fin n)) :
    (n.factorial : ℝ) / (n : ℝ) ^ n ≤ A.permanent := by
  by_cases hn0 : n = 0
  · subst n
    simpa using Chapter22.van_der_Waerden_permanent_fin_zero A hA
  · have hn : 1 ≤ n := Nat.succ_le_of_lt (Nat.pos_of_ne_zero hn0)
    let θ : ℕ → ℝ := fun N => (((N + 1 : ℕ) : ℝ)⁻¹)
    let Aθ : ℕ → Matrix (Fin n) (Fin n) ℝ :=
      fun N => (1 - θ N) • A + θ N • flatDoublyStochasticMatrix n
    have hθ_pos : ∀ N, 0 < θ N := by
      intro N
      dsimp [θ]
      positivity
    have hθ_le_one : ∀ N, θ N ≤ 1 := by
      intro N
      have hden : (1 : ℝ) ≤ ((N + 1 : ℕ) : ℝ) := by
        exact_mod_cast Nat.succ_le_succ (Nat.zero_le N)
      simpa [θ] using inv_le_one_of_one_le₀ hden
    have hflat : flatDoublyStochasticMatrix n ∈ doublyStochastic ℝ (Fin n) :=
      flatDoublyStochasticMatrix_mem_doublyStochastic n
    have hAθ_ds : ∀ N, Aθ N ∈ doublyStochastic ℝ (Fin n) := by
      intro N
      have hleft : 0 ≤ 1 - θ N := sub_nonneg.mpr (hθ_le_one N)
      have hright : 0 ≤ θ N := le_of_lt (hθ_pos N)
      have hsum : (1 - θ N) + θ N = 1 := by ring
      simpa [Aθ] using
        (convex_doublyStochastic (R := ℝ) (n := Fin n)) hA hflat hleft hright hsum
    have hAθ_pos : ∀ N i j, 0 < Aθ N i j := by
      intro N i j
      have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
      have hflat_pos : 0 < flatDoublyStochasticMatrix n i j := by
        simpa [flatDoublyStochasticMatrix] using inv_pos.mpr hnR
      have hAij : 0 ≤ A i j := nonneg_of_mem_doublyStochastic hA
      have hleft : 0 ≤ (1 - θ N) * A i j :=
        mul_nonneg (sub_nonneg.mpr (hθ_le_one N)) hAij
      have hright : 0 < θ N * flatDoublyStochasticMatrix n i j :=
        mul_pos (hθ_pos N) hflat_pos
      simpa [Aθ, Matrix.add_apply, Matrix.smul_apply] using add_pos_of_nonneg_of_pos hleft hright
    have hθ_tend : Filter.Tendsto θ Filter.atTop (nhds 0) := by
      simpa [θ] using (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
    have hentry : ∀ i j, Filter.Tendsto (fun N : ℕ => Aθ N i j) Filter.atTop
        (nhds (A i j)) := by
      intro i j
      have hleft :
          Filter.Tendsto (fun N : ℕ => (1 - θ N) * A i j) Filter.atTop
            (nhds ((1 - 0) * A i j)) :=
        (tendsto_const_nhds.sub hθ_tend).mul tendsto_const_nhds
      have hright :
          Filter.Tendsto
            (fun N : ℕ => θ N * flatDoublyStochasticMatrix n i j) Filter.atTop
            (nhds (0 * flatDoublyStochasticMatrix n i j)) :=
        hθ_tend.mul tendsto_const_nhds
      simpa [Aθ, Matrix.add_apply, Matrix.smul_apply] using hleft.add hright
    have hperm_tend :
        Filter.Tendsto (fun N : ℕ => (Aθ N).permanent) Filter.atTop
          (nhds A.permanent) :=
      permanent_tendsto_of_entrywise hentry
    have hineq : ∀ N, (n.factorial : ℝ) / (n : ℝ) ^ n ≤ (Aθ N).permanent := by
      intro N
      exact chapter22_positive n (Aθ N) (hAθ_pos N) (hAθ_ds N)
    exact ge_of_tendsto hperm_tend (Filter.Eventually.of_forall hineq)

end

end ProofsInTheBook.Chapter22Gurvits
