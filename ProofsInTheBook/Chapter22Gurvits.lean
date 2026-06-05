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

structure FactoredSectionData (k : ℕ) (q : Polynomial ℝ) where
  c : ℝ
  lam : Fin k → ℝ
  c_nonneg : 0 ≤ c
  lam_nonneg : ∀ i, 0 ≤ lam i
  sum_lam_pos : 0 < ∑ i, lam i
  eval_eq : ∀ t : ℝ, Polynomial.eval t q = c * ∏ i, (1 + lam i * t)
  coeff_one_eq : Polynomial.coeff q 1 = c * ∑ i, lam i

def PositiveFactoredSections {m : ℕ} (p : MvPolynomial (Fin (m + 1)) ℝ) : Type :=
  ∀ x : Fin m → ℝ, PositiveVector x →
    FactoredSectionData (m + 1) (sectionPolynomial p x)

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

end

end ProofsInTheBook.Chapter22Gurvits
