import Mathlib

/-!
# Chapter 21: A theorem of Pólya on polynomials

From "Proofs from THE BOOK":

**Pólya's theorem**: If f(x) is a polynomial with integer values at
all integers, then f can be written as a linear combination of
binomial coefficients C(x,0), C(x,1), C(x,2), ....

The book proves this via finite differences: Δⁿf(0) = ∑(-1)^k C(n,k)f(n-k).
-/

namespace ProofsInTheBook.Chapter21

noncomputable section

open Finset Function Polynomial

/-!
### The finite-difference step

Pólya's theorem is proved by repeatedly applying the forward difference
operator.  The binomial-coefficient basis is adapted to this operator because
`Δ C(x, k + 1) = C(x, k)`, which is just Pascal's identity in polynomial form.
-/

def forwardDifference (f : ℤ → ℤ) : ℤ → ℤ :=
  fun x => f (x + 1) - f x

theorem binomial_forwardDifference (x : ℤ) (k : ℕ) :
    forwardDifference (fun y : ℤ => Ring.choose y (k + 1)) x = Ring.choose x k := by
  unfold forwardDifference
  change Ring.choose (x + 1) (k + 1) - Ring.choose x (k + 1) = Ring.choose x k
  rw [Ring.choose_succ_succ]
  abel

theorem binomial_forwardDifference_zero (x : ℤ) :
    forwardDifference (fun _ : ℤ => (1 : ℤ)) x = 0 := by
  simp [forwardDifference]

theorem chapter21_difference_step (x : ℤ) (k : ℕ) :
    forwardDifference (fun y : ℤ => Ring.choose y (k + 1)) x = Ring.choose x k :=
  binomial_forwardDifference x k

/-!
### Pólya's integer-valued polynomial theorem

We formalize the book theorem for polynomials over `ℚ`: if such a polynomial
takes integer values at every integer, then it is a finite `ℤ`-linear
combination of the binomial polynomials `x ↦ Ring.choose x k`.
-/

/-- The binomial polynomial `x choose k`, represented in `ℚ[X]`. -/
def binomialPolynomial (k : ℕ) : ℚ[X] :=
  (k.factorial : ℚ)⁻¹ • descPochhammer ℚ k

lemma descPochhammer_smeval_rat_eq_eval (x : ℚ) (k : ℕ) :
    (descPochhammer ℤ k).smeval x = (descPochhammer ℚ k).eval x := by
  rw [← Polynomial.eval₂_smulOneHom_eq_smeval ℤ (descPochhammer ℤ k) x]
  rw [Polynomial.eval₂_eq_eval_map, descPochhammer_map]

lemma eval_binomialPolynomial (x : ℚ) (k : ℕ) :
    (binomialPolynomial k).eval x = Ring.choose x k := by
  have h := Ring.descPochhammer_eq_factorial_smul_choose (r := x) (n := k)
  rw [descPochhammer_smeval_rat_eq_eval] at h
  rw [nsmul_eq_mul] at h
  rw [binomialPolynomial, eval_smul, h]
  rw [smul_eq_mul]
  field_simp [Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero k)]

lemma eval_binomialPolynomial_zero (k : ℕ) :
    (binomialPolynomial k).eval 0 = if k = 0 then 1 else 0 := by
  rw [eval_binomialPolynomial]
  exact Ring.choose_zero_ite ℚ k

/-- Forward difference on polynomials, `P(x+1)-P(x)`. -/
def polynomialForwardDifference (P : ℚ[X]) : ℚ[X] :=
  P.comp (Polynomial.X + 1) - P

/-- Linear-map packaging of polynomial forward difference. -/
def polynomialForwardDifferenceₗ : ℚ[X] →ₗ[ℚ] ℚ[X] where
  toFun := polynomialForwardDifference
  map_add' P Q := by
    simp [polynomialForwardDifference, add_comp]
    abel
  map_smul' a P := by
    simp [polynomialForwardDifference, Polynomial.smul_comp, smul_sub]

lemma eval_polynomialForwardDifference (P : ℚ[X]) (x : ℚ) :
    (polynomialForwardDifference P).eval x = fwdDiff (1 : ℚ) P.eval x := by
  simp [polynomialForwardDifference, fwdDiff]

lemma polynomialForwardDifference_binomial (k : ℕ) :
    polynomialForwardDifference (binomialPolynomial (k + 1)) = binomialPolynomial k := by
  apply Polynomial.eq_of_infinite_eval_eq
  apply (Set.infinite_range_of_injective Rat.natCast_injective).mono
  rintro x ⟨m, rfl⟩
  simp only [Set.mem_setOf_eq]
  rw [eval_polynomialForwardDifference]
  simp only [fwdDiff]
  rw [eval_binomialPolynomial ((m : ℚ) + 1) (k + 1)]
  rw [eval_binomialPolynomial (m : ℚ) (k + 1)]
  rw [eval_binomialPolynomial (m : ℚ) k]
  rw [Ring.choose_succ_succ]
  abel

lemma polynomialForwardDifference_binomial_zero :
    polynomialForwardDifference (binomialPolynomial 0) = 0 := by
  simp [polynomialForwardDifference, binomialPolynomial]

lemma fwdDiff_polynomialForwardDifference_coeff (P : ℚ[X]) (k : ℕ) :
    ((fwdDiff (1 : ℚ))^[k] (polynomialForwardDifference P).eval) 0 =
      ((fwdDiff (1 : ℚ))^[k + 1] P.eval) 0 := by
  have hD : (polynomialForwardDifference P).eval = fwdDiff (1 : ℚ) P.eval := by
    funext x
    exact eval_polynomialForwardDifference P x
  rw [hD]
  rw [Function.iterate_succ_apply]

/-- The Newton expansion with rational forward-difference coefficients. -/
def newtonPolynomial (P : ℚ[X]) (n : ℕ) : ℚ[X] :=
  ∑ k ∈ range n, (((fwdDiff (1 : ℚ))^[k] P.eval) 0) • binomialPolynomial k

lemma polynomialForwardDifference_newtonPolynomial_succ (P : ℚ[X]) (n : ℕ) :
    polynomialForwardDifference (newtonPolynomial P (n + 1)) =
      newtonPolynomial (polynomialForwardDifference P) n := by
  rw [newtonPolynomial]
  change polynomialForwardDifferenceₗ
      (∑ k ∈ range (n + 1),
        (((fwdDiff (1 : ℚ))^[k] P.eval) 0) • binomialPolynomial k) = _
  rw [map_sum]
  simp only [map_smul, polynomialForwardDifferenceₗ]
  rw [sum_range_succ']
  simp [polynomialForwardDifference_binomial_zero, polynomialForwardDifference_binomial,
    newtonPolynomial, fwdDiff_polynomialForwardDifference_coeff]

lemma eval_newtonPolynomial_zero_succ (P : ℚ[X]) (n : ℕ) :
    (newtonPolynomial P (n + 1)).eval 0 = P.eval 0 := by
  rw [newtonPolynomial, eval_finsetSum, sum_range_succ']
  simp [eval_smul, eval_binomialPolynomial_zero]

lemma polynomial_eq_zero_of_forwardDifference_eq_zero_of_eval_zero
    (P : ℚ[X]) (hΔ : polynomialForwardDifference P = 0) (h0 : P.eval 0 = 0) : P = 0 := by
  apply Polynomial.eq_of_infinite_eval_eq
  apply (Set.infinite_range_of_injective Rat.natCast_injective).mono
  rintro x ⟨m, rfl⟩
  simp only [Set.mem_setOf_eq, eval_zero]
  induction m with
  | zero => simpa using h0
  | succ m ih =>
      have hstep := congr_arg (fun Q : ℚ[X] => Q.eval (m : ℚ)) hΔ
      have hstep' : P.eval ((m : ℚ) + 1) - P.eval (m : ℚ) = 0 := by
        simpa [polynomialForwardDifference] using hstep
      have hnext : P.eval ((m.succ : ℕ) : ℚ) = P.eval (m : ℚ) := by
        rw [Nat.cast_succ]
        linarith
      rw [hnext, ih]

theorem newtonPolynomial_eq_of_fwdDiff_iter_eq_zero :
    ∀ (n : ℕ) (P : ℚ[X]),
      ((fwdDiff (1 : ℚ))^[n] P.eval = 0) → P = newtonPolynomial P n
  | 0, P, hnil => by
      rw [newtonPolynomial, sum_range_zero]
      apply Polynomial.eq_of_infinite_eval_eq
      apply (Set.infinite_range_of_injective Rat.natCast_injective).mono
      rintro x ⟨m, rfl⟩
      simp only [Set.mem_setOf_eq, eval_zero]
      exact congr_fun hnil (m : ℚ)
  | n + 1, P, hnil => by
      have hDnil : ((fwdDiff (1 : ℚ))^[n] (polynomialForwardDifference P).eval = 0) := by
        have hD : (polynomialForwardDifference P).eval = fwdDiff (1 : ℚ) P.eval := by
          funext x
          exact eval_polynomialForwardDifference P x
        rw [hD]
        simpa [Function.iterate_succ_apply] using hnil
      have hDexp :=
        newtonPolynomial_eq_of_fwdDiff_iter_eq_zero n (polynomialForwardDifference P) hDnil
      have hΔ : polynomialForwardDifference (P - newtonPolynomial P (n + 1)) = 0 := by
        change polynomialForwardDifferenceₗ (P - newtonPolynomial P (n + 1)) = 0
        rw [map_sub]
        change polynomialForwardDifference P -
          polynomialForwardDifference (newtonPolynomial P (n + 1)) = 0
        rw [polynomialForwardDifference_newtonPolynomial_succ]
        nth_rw 1 [hDexp]
        rw [sub_self]
      have h0 : (P - newtonPolynomial P (n + 1)).eval 0 = 0 := by
        rw [eval_sub, eval_newtonPolynomial_zero_succ]
        ring
      have hzero := polynomial_eq_zero_of_forwardDifference_eq_zero_of_eval_zero
        (P - newtonPolynomial P (n + 1)) hΔ h0
      exact sub_eq_zero.mp hzero

/-- A rational polynomial is integer-valued if it maps every integer to an integer. -/
def IsIntegerValuedPolynomial (P : ℚ[X]) : Prop :=
  ∀ z : ℤ, ∃ m : ℤ, P.eval (z : ℚ) = (m : ℚ)

def integerValue (P : ℚ[X]) (hP : IsIntegerValuedPolynomial P) (z : ℤ) : ℤ :=
  Classical.choose (hP z)

lemma integerValue_spec (P : ℚ[X]) (hP : IsIntegerValuedPolynomial P) (z : ℤ) :
    P.eval (z : ℚ) = (integerValue P hP z : ℚ) :=
  Classical.choose_spec (hP z)

/-- The integer coefficient `Δ^k P(0)`, computed from integer values of `P`. -/
def polyaCoeff (P : ℚ[X]) (hP : IsIntegerValuedPolynomial P) (k : ℕ) : ℤ :=
  ∑ i ∈ range (k + 1),
    ((-1 : ℤ) ^ (k - i) * (k.choose i : ℤ)) * integerValue P hP (i : ℤ)

lemma polyaCoeff_cast_eq_fwdDiff (P : ℚ[X]) (hP : IsIntegerValuedPolynomial P) (k : ℕ) :
    (polyaCoeff P hP k : ℚ) = ((fwdDiff (1 : ℚ))^[k] P.eval) 0 := by
  rw [fwdDiff_iter_eq_sum_shift]
  rw [polyaCoeff]
  rw [Int.cast_sum]
  apply Finset.sum_congr rfl
  intro i _hi
  rw [Int.cast_mul]
  simp only [zero_add, nsmul_eq_mul, mul_one]
  have hv : P.eval (i : ℚ) = (integerValue P hP (i : ℤ) : ℚ) := by
    simpa using integerValue_spec P hP (i : ℤ)
  rw [← hv]
  simp [zsmul_eq_mul]

/--
Pólya's theorem: every rational polynomial that is integer-valued on all
integers is a finite `ℤ`-linear combination of the binomial polynomials.
The coefficient of `binomialPolynomial k` is the iterated forward difference
`Δ^k P(0)`.
-/
theorem chapter21 (P : ℚ[X]) (hP : IsIntegerValuedPolynomial P) :
    ∃ c : ℕ → ℤ,
      (∀ k : ℕ, (c k : ℚ) = ((fwdDiff (1 : ℚ))^[k] P.eval) 0) ∧
        P = ∑ k ∈ range (P.natDegree + 1), (c k : ℚ) • binomialPolynomial k := by
  let c : ℕ → ℤ := polyaCoeff P hP
  refine ⟨c, ?_, ?_⟩
  · intro k
    exact polyaCoeff_cast_eq_fwdDiff P hP k
  · have hnil : ((fwdDiff (1 : ℚ))^[P.natDegree + 1] P.eval = 0) :=
      Polynomial.fwdDiff_iter_eq_zero_of_degree_lt (P := P) (n := P.natDegree + 1)
        (Nat.lt_succ_self P.natDegree)
    nth_rw 1 [newtonPolynomial_eq_of_fwdDiff_iter_eq_zero (P.natDegree + 1) P hnil]
    rw [newtonPolynomial]
    apply Finset.sum_congr rfl
    intro k _hk
    rw [← polyaCoeff_cast_eq_fwdDiff P hP k]

end

end ProofsInTheBook.Chapter21
