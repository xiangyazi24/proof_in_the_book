import Mathlib
import ProofsInTheBook.PermanentConvexity

/-!
# Chapter 22: Van der Waerden's permanent conjecture

From "Proofs from THE BOOK":

**Van der Waerden's conjecture** (now theorem, proved by Falikman and
Egorychev): The permanent of a doubly stochastic n×n matrix is minimized
by the matrix with all entries 1/n, giving perm ≥ n!/nⁿ.

The book presents the proof using the theory of mixed discriminants.

Formalization status: this file now states the genuine theorem over Mathlib's
`doublyStochastic` predicate.  The proved local part is the equality-case
computation for the flat matrix, the `n ≤ 2` unconditional lower bounds, the
`n = 0,1,2` instances of the coefficient-from-capacity analytic core, and the
weighted-AM-GM capacity lower bound for row-linear products of doubly
stochastic matrices.  It identifies the squarefree coefficient of the
row-linear `MvPolynomial` with the row-linear mixed coefficient and hence with
the permanent, and packages the checkerboard boundary-convexity step for
opposite exchange endpoints.  The remaining arbitrary-dimension lower bound is
exposed as a point-17 honest frontier: it is conditional on the missing
Falikman-Egorychev/Gurvits coefficient-from-capacity inequality for `n ≥ 3`,
now stated on the actual squarefree coefficient of the row-linear polynomial
rather than replaced by the flat-matrix special case.  The equality-only-if-flat
strengthening belongs to the same unformalized analytic equality-case layer.

The exact intended unconditional Lean endpoint is:

```
theorem van_der_waerden_permanent_conjecture (n : ℕ)
    (A : Matrix (Fin n) (Fin n) ℝ)
    (hA : A ∈ doublyStochastic ℝ (Fin n)) :
    (n.factorial : ℝ) / (n : ℝ) ^ n ≤ A.permanent
```
-/

namespace ProofsInTheBook.Chapter22

open Matrix
open ProofsInTheBook.PermanentConvexity

noncomputable section

/-!
### The equality case and the honest analytic frontier

The van der Waerden theorem says every doubly stochastic matrix has permanent
at least `n! / n^n`, with equality at the flat matrix.
-/

def flatDoublyStochasticMatrix (n : ℕ) : Matrix (Fin n) (Fin n) ℝ :=
  fun _ _ => (n : ℝ)⁻¹

theorem flatDoublyStochasticMatrix_mem_doublyStochastic (n : ℕ) :
    flatDoublyStochasticMatrix n ∈ doublyStochastic ℝ (Fin n) := by
  classical
  rw [mem_doublyStochastic_iff_sum]
  refine ⟨?_, ?_, ?_⟩
  · intro i j
    exact inv_nonneg.mpr (Nat.cast_nonneg n)
  · intro i
    have hn : (n : ℝ) ≠ 0 := by
      exact_mod_cast (Nat.lt_of_le_of_lt (Nat.zero_le i.val) i.isLt).ne'
    simp [flatDoublyStochasticMatrix, Finset.sum_const, Fintype.card_fin, hn]
  · intro j
    have hn : (n : ℝ) ≠ 0 := by
      exact_mod_cast (Nat.lt_of_le_of_lt (Nat.zero_le j.val) j.isLt).ne'
    simp [flatDoublyStochasticMatrix, Finset.sum_const, Fintype.card_fin, hn]

theorem permanent_flatDoublyStochasticMatrix (n : ℕ) :
    (flatDoublyStochasticMatrix n).permanent = (n.factorial : ℝ) / (n : ℝ) ^ n := by
  calc
    (flatDoublyStochasticMatrix n).permanent =
        (n.factorial : ℝ) * ((n : ℝ)⁻¹) ^ n := by
      simp [flatDoublyStochasticMatrix, Matrix.permanent, Finset.prod_const, Fintype.card_perm]
    _ = (n.factorial : ℝ) / (n : ℝ) ^ n := by
      rw [inv_pow, div_eq_mul_inv]

theorem flatDoublyStochasticMatrix_attains_van_der_Waerden_bound (n : ℕ) :
    flatDoublyStochasticMatrix n ∈ doublyStochastic ℝ (Fin n) ∧
      (flatDoublyStochasticMatrix n).permanent =
        (n.factorial : ℝ) / (n : ℝ) ^ n :=
  ⟨flatDoublyStochasticMatrix_mem_doublyStochastic n,
    permanent_flatDoublyStochasticMatrix n⟩

/-- Row-linear product `∏ᵢ ∑ⱼ Aᵢⱼ xⱼ`, the polynomial used in Gurvits's
stable-polynomial proof of Van der Waerden's conjecture. -/
def rowLinearProduct {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (x : Fin n → ℝ) : ℝ :=
  ∏ i, ∑ j, A i j * x j

/-- The same row-linear product as a multivariate polynomial. -/
def rowLinearMvPolynomial {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) :
    MvPolynomial (Fin n) ℝ :=
  ∏ i, ∑ j, MvPolynomial.C (A i j) * MvPolynomial.X j

theorem eval_rowLinearMvPolynomial {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (x : Fin n → ℝ) :
    MvPolynomial.eval x (rowLinearMvPolynomial A) = rowLinearProduct A x := by
  simp [rowLinearMvPolynomial, rowLinearProduct]

/-- The exponent vector of the squarefree monomial `∏ⱼ xⱼ`. -/
def squarefreeExponent (n : ℕ) : Fin n →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm (fun _ => 1)

/-- The squarefree coefficient of `∏ᵢ ∑ⱼ Aᵢⱼ xⱼ`. -/
def rowLinearSquarefreeCoefficient {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) : ℝ :=
  MvPolynomial.coeff (squarefreeExponent n) (rowLinearMvPolynomial A)

/--
The mixed coefficient of the row-linear product, written as the sum over
choosing one column in each row and requiring that every column is chosen once.
This is the coefficient of the squarefree monomial `∏ⱼ xⱼ` in the expanded
row-linear product.
-/
def rowLinearMixedCoefficient {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) : ℝ :=
  ∑ σ : Equiv.Perm (Fin n), ∏ i, A i (σ i)

private def permInvEquiv (α : Type*) : Equiv.Perm α ≃ Equiv.Perm α where
  toFun σ := σ.symm
  invFun σ := σ.symm
  left_inv σ := by ext x; simp
  right_inv σ := by ext x; simp

/-- The mixed coefficient of the row-linear product is the permanent. -/
theorem rowLinearMixedCoefficient_eq_permanent {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℝ) :
    rowLinearMixedCoefficient A = A.permanent := by
  classical
  unfold rowLinearMixedCoefficient Matrix.permanent
  refine (Fintype.sum_equiv (permInvEquiv (Fin n))
    (fun σ : Equiv.Perm (Fin n) => ∏ i, A i (σ i))
    (fun σ : Equiv.Perm (Fin n) => ∏ i, A (σ i) i) ?_).trans ?_
  · intro σ
    simp
    exact Fintype.prod_equiv σ
      (fun i => A i (σ i))
      (fun i => A (σ.symm i) i)
      (by intro i; simp)
  · rfl

private theorem sum_single_one_eq_squarefreeExponent_iff_bijective {n : ℕ}
    (f : Fin n → Fin n) :
    (∑ i, Finsupp.single (f i) 1) = squarefreeExponent n ↔ Function.Bijective f := by
  constructor
  · intro h
    have hcard : ∀ j : Fin n, (Finset.univ.filter (fun i => f i = j)).card = 1 := by
      intro j
      have hj : (∑ i, Finsupp.single (f i) 1) j = 1 := by
        rw [h]
        simp [squarefreeExponent]
      have hsum : (∑ i, (if f i = j then (1 : ℕ) else 0)) = 1 := by
        simpa [Finsupp.single_apply, eq_comm] using hj
      rw [Finset.card_eq_sum_ones]
      simpa [Finset.sum_filter] using hsum
    refine ⟨?_, ?_⟩
    · intro i k hik
      have hi : i ∈ Finset.univ.filter (fun x => f x = f i) := by simp
      have hk : k ∈ Finset.univ.filter (fun x => f x = f i) := by simp [hik]
      rcases Finset.card_eq_one.mp (hcard (f i)) with ⟨a, ha⟩
      have hi_eq : i = a := by simpa [ha] using hi
      have hk_eq : k = a := by simpa [ha] using hk
      exact hi_eq.trans hk_eq.symm
    · intro j
      rcases Finset.card_eq_one.mp (hcard j) with ⟨i, hi⟩
      refine ⟨i, ?_⟩
      have : i ∈ Finset.univ.filter (fun x => f x = j) := by simp [hi]
      simpa using this
  · intro hbij
    ext j
    have hsum : (∑ i, (if f i = j then (1 : ℕ) else 0)) = 1 := by
      rcases hbij.2 j with ⟨i, hi⟩
      rw [Finset.sum_eq_single i]
      · simp [hi]
      · intro k _hk hki
        have hfk : f k ≠ j := by
          intro hkj
          exact hki (hbij.1 (hkj.trans hi.symm))
        simp [hfk]
      · intro hi_not
        exact (hi_not (Finset.mem_univ i)).elim
    have hleft : (∑ i, Finsupp.single (f i) 1) j =
        ∑ i, (if f i = j then (1 : ℕ) else 0) := by
      simp [Finsupp.single_apply, eq_comm]
    rw [hleft, hsum]
    simp [squarefreeExponent]

private theorem rowLinearTerm_eq_monomial {n : Type*} [DecidableEq n] [Fintype n]
    (a : n → ℝ) (f : n → n) :
    (∏ i, MvPolynomial.C (a i) * MvPolynomial.X (f i) : MvPolynomial n ℝ) =
      MvPolynomial.monomial (∑ i, Finsupp.single (f i) 1) (∏ i, a i) := by
  classical
  simp_rw [show ∀ i, MvPolynomial.C (a i) * MvPolynomial.X (f i) =
      (MvPolynomial.monomial (Finsupp.single (f i) 1) (a i) : MvPolynomial n ℝ) by
    intro i
    rw [MvPolynomial.X, MvPolynomial.C_mul_monomial]
    simp]
  induction (Finset.univ : Finset n) using Finset.induction with
  | empty =>
      simp
  | insert i s his ih =>
      simp [Finset.prod_insert, Finset.sum_insert, his, ih, MvPolynomial.monomial_mul]

private theorem rowLinearMvPolynomial_expand {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℝ) :
    rowLinearMvPolynomial A =
      ∑ f : Fin n → Fin n, ∏ i, MvPolynomial.C (A i (f i)) * MvPolynomial.X (f i) := by
  classical
  unfold rowLinearMvPolynomial
  rw [Fintype.prod_sum]

theorem rowLinearSquarefreeCoefficient_eq_function_sum {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℝ) :
    rowLinearSquarefreeCoefficient A =
      ∑ f : Fin n → Fin n, if Function.Bijective f then ∏ i, A i (f i) else 0 := by
  classical
  unfold rowLinearSquarefreeCoefficient
  rw [rowLinearMvPolynomial_expand A]
  simp_rw [rowLinearTerm_eq_monomial]
  rw [MvPolynomial.coeff_sum]
  refine Finset.sum_congr rfl ?_
  intro f _hf
  have hcoeff : MvPolynomial.coeff (squarefreeExponent n)
      (MvPolynomial.monomial (∑ i, Finsupp.single (f i) 1) (∏ i, A i (f i)) :
        MvPolynomial (Fin n) ℝ) =
      if (∑ i, Finsupp.single (f i) 1) = squarefreeExponent n then
        ∏ i, A i (f i) else 0 := by
    rw [MvPolynomial.coeff_monomial]
  rw [hcoeff]
  by_cases hbij : Function.Bijective f
  · have hexp : (∑ i, Finsupp.single (f i) 1) = squarefreeExponent n :=
      (sum_single_one_eq_squarefreeExponent_iff_bijective f).2 hbij
    rw [if_pos hexp, if_pos hbij]
  · have hexp : (∑ i, Finsupp.single (f i) 1) ≠ squarefreeExponent n := by
      intro h
      exact hbij ((sum_single_one_eq_squarefreeExponent_iff_bijective f).1 h)
    rw [if_neg hexp, if_neg hbij]

private def bijectiveFunctionEquivPerm (n : ℕ) :
    {f : Fin n → Fin n // Function.Bijective f} ≃ Equiv.Perm (Fin n) where
  toFun f := Equiv.ofBijective f.1 f.2
  invFun σ := ⟨σ, σ.bijective⟩
  left_inv f := by
    apply Subtype.ext
    funext i
    exact Equiv.ofBijective_apply f.1 f.2 i
  right_inv σ := by
    ext i
    rfl

private theorem function_sum_bijective_eq_rowLinearMixedCoefficient {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℝ) :
    (∑ f : Fin n → Fin n, if Function.Bijective f then ∏ i, A i (f i) else 0) =
      rowLinearMixedCoefficient A := by
  classical
  rw [← Finset.sum_filter]
  rw [Finset.sum_subtype
    (s := Finset.univ.filter (fun f : Fin n → Fin n => Function.Bijective f))]
  · unfold rowLinearMixedCoefficient
    exact Fintype.sum_equiv (bijectiveFunctionEquivPerm n)
      (fun f : {f : Fin n → Fin n // Function.Bijective f} => ∏ i, A i (f.1 i))
      (fun σ : Equiv.Perm (Fin n) => ∏ i, A i (σ i))
      (by intro f; rfl)
  · intro f
    simp

/-- The squarefree `MvPolynomial` coefficient is the row-linear mixed coefficient. -/
theorem rowLinearSquarefreeCoefficient_eq_mixedCoefficient {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℝ) :
    rowLinearSquarefreeCoefficient A = rowLinearMixedCoefficient A := by
  rw [rowLinearSquarefreeCoefficient_eq_function_sum,
    function_sum_bijective_eq_rowLinearMixedCoefficient]

/-- The squarefree `MvPolynomial` coefficient of the row-linear product is the permanent. -/
theorem rowLinearSquarefreeCoefficient_eq_permanent {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℝ) :
    rowLinearSquarefreeCoefficient A = A.permanent := by
  rw [rowLinearSquarefreeCoefficient_eq_mixedCoefficient, rowLinearMixedCoefficient_eq_permanent]

/--
The capacity lower bound needed for the row-linear product:
`∏ⱼ xⱼ ≤ ∏ᵢ ∑ⱼ Aᵢⱼ xⱼ` on the positive orthant.  For a doubly stochastic
matrix this follows from weighted AM-GM plus the column-sum equations.
-/
structure RowLinearCapacityAtLeastOne {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) where
  le_rowLinearProduct :
    ∀ x : Fin n → ℝ, (∀ j, 0 < x j) → ∏ j, x j ≤ rowLinearProduct A x

/--
The weighted-AM-GM/capacity step in Gurvits's proof, specialized to the
row-linear product associated to a doubly stochastic matrix.
-/
theorem rowLinearCapacityAtLeastOne_of_doublyStochastic {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℝ)
    (hA : A ∈ doublyStochastic ℝ (Fin n)) :
    RowLinearCapacityAtLeastOne A := by
  classical
  refine ⟨?_⟩
  intro x hx
  have hfactor :
      ∀ i : Fin n, (∏ j, x j ^ A i j) ≤ ∑ j, A i j * x j := by
    intro i
    simpa using Real.geom_mean_le_arith_mean_weighted (s := Finset.univ)
      (w := fun j => A i j) (z := x)
      (fun j _ => nonneg_of_mem_doublyStochastic hA)
      (by simpa using sum_row_of_mem_doublyStochastic hA i)
      (fun j _ => le_of_lt (hx j))
  have hprod :
      (∏ i, ∏ j, x j ^ A i j) ≤ rowLinearProduct A x := by
    unfold rowLinearProduct
    exact Finset.prod_le_prod
      (fun _i _hi => Finset.prod_nonneg fun j _hj => Real.rpow_nonneg (le_of_lt (hx j)) _)
      (fun i _hi => hfactor i)
  calc
    (∏ j, x j) = ∏ j, x j ^ (1 : ℝ) := by
      simp [Real.rpow_one]
    _ = ∏ j, x j ^ (∑ i, A i j) := by
      simp [sum_col_of_mem_doublyStochastic hA]
    _ = ∏ j, ∏ i, x j ^ A i j := by
      refine Finset.prod_congr rfl ?_
      intro j _hj
      rw [Real.rpow_sum_of_pos (hx j)]
    _ = ∏ i, ∏ j, x j ^ A i j := by
      rw [Finset.prod_comm]
    _ ≤ rowLinearProduct A x := hprod

/--
Gurvits's coefficient-from-capacity step, expressed on the actual mixed
coefficient of the row-linear polynomial.  This is the analytic theorem still
needed in arbitrary dimension: capacity at least one implies the squarefree
mixed coefficient is at least `n! / n^n`.
-/
structure GurvitsCoefficientFromCapacityCore (n : ℕ) where
  mixed_coefficient_bound :
    ∀ A : Matrix (Fin n) (Fin n) ℝ,
      (∀ i j, 0 ≤ A i j) →
      RowLinearCapacityAtLeastOne A →
      (n.factorial : ℝ) / (n : ℝ) ^ n ≤ rowLinearMixedCoefficient A

/--
The same Gurvits coefficient-from-capacity frontier, stated literally on the
squarefree coefficient of the row-linear `MvPolynomial`.
-/
structure GurvitsSquarefreeCoefficientFromCapacityCore (n : ℕ) where
  squarefree_coefficient_bound :
    ∀ A : Matrix (Fin n) (Fin n) ℝ,
      (∀ i j, 0 ≤ A i j) →
      RowLinearCapacityAtLeastOne A →
      (n.factorial : ℝ) / (n : ℝ) ^ n ≤ rowLinearSquarefreeCoefficient A

theorem gurvitsCoefficientFromCapacityCore_of_squarefreeCoefficientCore
    {n : ℕ} (core : GurvitsSquarefreeCoefficientFromCapacityCore n) :
    GurvitsCoefficientFromCapacityCore n := by
  refine ⟨?_⟩
  intro A hA hcap
  simpa [rowLinearSquarefreeCoefficient_eq_mixedCoefficient A] using
    core.squarefree_coefficient_bound A hA hcap

theorem squarefreeCoefficientCore_of_gurvitsCoefficientFromCapacityCore
    {n : ℕ} (core : GurvitsCoefficientFromCapacityCore n) :
    GurvitsSquarefreeCoefficientFromCapacityCore n := by
  refine ⟨?_⟩
  intro A hA hcap
  simpa [rowLinearSquarefreeCoefficient_eq_mixedCoefficient A] using
    core.mixed_coefficient_bound A hA hcap

/--
The remaining analytic core behind the full theorem.

* `coefficient_bound` is the deep Falikman-Egorychev/Gurvits
  coefficient-from-capacity inequality specialized to row-linear products:
  the squarefree coefficient, equivalently the mixed coefficient/permanent, is
  at least `n! / n^n`.

This is deliberately not a proof of Van der Waerden hidden in a harmless name:
the capacity hypothesis is now proved above from double stochasticity, and
this structure isolates the still-unformalized coefficient inequality needed
to pass from capacity to the permanent lower bound.

Mathlib gap as of this formalization: there is no available real-stable
polynomial capacity theorem, mixed-discriminant Alexandrov-Fenchel inequality,
or specialized Gurvits coefficient bound for `rowLinearProduct`.  Apart from
the elementary dimensions proved below, the exact missing lemma is the
`coefficient_bound` field below.
-/
structure VanDerWaerdenAnalyticCore (n : ℕ) where
  coefficient_bound :
    ∀ A : Matrix (Fin n) (Fin n) ℝ,
      (∀ i j, 0 ≤ A i j) →
      RowLinearCapacityAtLeastOne A →
      (n.factorial : ℝ) / (n : ℝ) ^ n ≤ A.permanent

/--
The Gurvits mixed-coefficient theorem implies the permanent-form analytic
core, because the row-linear mixed coefficient is exactly the permanent.
-/
theorem vanDerWaerdenAnalyticCore_of_gurvitsCoefficientFromCapacityCore
    {n : ℕ} (core : GurvitsCoefficientFromCapacityCore n) :
    VanDerWaerdenAnalyticCore n := by
  refine ⟨?_⟩
  intro A hA hcap
  simpa [rowLinearMixedCoefficient_eq_permanent A] using
    core.mixed_coefficient_bound A hA hcap

theorem vanDerWaerdenAnalyticCore_of_squarefreeCoefficientCore
    {n : ℕ} (core : GurvitsSquarefreeCoefficientFromCapacityCore n) :
    VanDerWaerdenAnalyticCore n :=
  vanDerWaerdenAnalyticCore_of_gurvitsCoefficientFromCapacityCore
    (gurvitsCoefficientFromCapacityCore_of_squarefreeCoefficientCore core)

theorem gurvitsCoefficientFromCapacityCore_of_vanDerWaerdenAnalyticCore
    {n : ℕ} (core : VanDerWaerdenAnalyticCore n) :
    GurvitsCoefficientFromCapacityCore n := by
  refine ⟨?_⟩
  intro A hA hcap
  simpa [rowLinearMixedCoefficient_eq_permanent A] using
    core.coefficient_bound A hA hcap

theorem permanent_nonneg_of_entrywise_nonneg {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℝ) (hA : ∀ i j, 0 ≤ A i j) :
    0 ≤ A.permanent := by
  classical
  unfold Matrix.permanent
  exact Finset.sum_nonneg fun σ _ =>
    Finset.prod_nonneg fun i _ => hA (σ i) i

/-!
### Elementary low-dimensional cases

The full theorem is deep, but dimensions `0`, `1`, and `2` are elementary.
These results discharge the analytic-core assumption in the small cases instead
of hiding them behind the frontier theorem.
-/

theorem van_der_Waerden_permanent_fin_zero
    (A : Matrix (Fin 0) (Fin 0) ℝ)
    (_hA : A ∈ doublyStochastic ℝ (Fin 0)) :
    ((0 : ℕ).factorial : ℝ) / (0 : ℝ) ^ 0 ≤ A.permanent := by
  simp [Matrix.permanent]

theorem van_der_Waerden_permanent_fin_one
    (A : Matrix (Fin 1) (Fin 1) ℝ)
    (hA : A ∈ doublyStochastic ℝ (Fin 1)) :
    ((1 : ℕ).factorial : ℝ) / (1 : ℝ) ^ 1 ≤ A.permanent := by
  have h00 : A 0 0 = 1 := by
    simpa using sum_row_of_mem_doublyStochastic hA 0
  simp [h00]

private def permFinTwoEquiv : Equiv.Perm (Fin 2) ≃ Fin 2 where
  toFun σ := σ 0
  invFun k := if k = 0 then 1 else Equiv.swap (0 : Fin 2) 1
  left_inv σ := by
    by_cases h : σ 0 = 0
    · have hσ1 : σ 1 = 1 := by
        have hne : σ 1 ≠ 0 := by
          intro h1
          have : (1 : Fin 2) = 0 := σ.injective (by rw [h1, h])
          norm_num at this
        have hneval : (σ 1).val ≠ 0 := by
          intro hv
          exact hne (Fin.ext hv)
        have hlt : (σ 1).val < 2 := (σ 1).isLt
        apply Fin.ext
        omega
      ext i
      fin_cases i <;> simp [h, hσ1]
    · have hσ0 : σ 0 = 1 := by
        have hneval : (σ 0).val ≠ 0 := by
          intro hv
          exact h (Fin.ext hv)
        have hlt : (σ 0).val < 2 := (σ 0).isLt
        apply Fin.ext
        omega
      have hσ1 : σ 1 = 0 := by
        have hne : σ 1 ≠ 1 := by
          intro h1
          have : (1 : Fin 2) = 0 := σ.injective (by rw [h1, hσ0])
          norm_num at this
        have hneval : (σ 1).val ≠ 1 := by
          intro hv
          exact hne (Fin.ext hv)
        have hlt : (σ 1).val < 2 := (σ 1).isLt
        apply Fin.ext
        omega
      ext i
      fin_cases i <;> simp [hσ0, hσ1]
  right_inv k := by
    fin_cases k <;> simp

private theorem permanent_fin_two (A : Matrix (Fin 2) (Fin 2) ℝ) :
    A.permanent = A 0 0 * A 1 1 + A 1 0 * A 0 1 := by
  rw [Matrix.permanent]
  trans ∑ k : Fin 2, ∏ i, A ((permFinTwoEquiv.symm k) i) i
  · exact Fintype.sum_equiv permFinTwoEquiv (fun σ => ∏ i, A (σ i) i)
      (fun k => ∏ i, A ((permFinTwoEquiv.symm k) i) i) (by
        intro σ
        simp)
  · simp [permFinTwoEquiv, Fin.sum_univ_two, Fin.prod_univ_two]

theorem van_der_Waerden_permanent_fin_two
    (A : Matrix (Fin 2) (Fin 2) ℝ)
    (hA : A ∈ doublyStochastic ℝ (Fin 2)) :
    ((2 : ℕ).factorial : ℝ) / (2 : ℝ) ^ 2 ≤ A.permanent := by
  have hperm := permanent_fin_two A
  have hrow1 : A 1 0 + A 1 1 = 1 := by
    simpa [Fin.sum_univ_two] using sum_row_of_mem_doublyStochastic hA 1
  have hcol0 : A 0 0 + A 1 0 = 1 := by
    simpa [Fin.sum_univ_two] using sum_col_of_mem_doublyStochastic hA 0
  have h01_eq_10 : A 0 1 = A 1 0 := by
    have hrow0 : A 0 0 + A 0 1 = 1 := by
      simpa [Fin.sum_univ_two] using sum_row_of_mem_doublyStochastic hA 0
    nlinarith
  have h11_eq_00 : A 1 1 = A 0 0 := by
    nlinarith
  rw [hperm, h01_eq_10, h11_eq_00]
  norm_num
  nlinarith [sq_nonneg (A 0 0 - A 1 0)]

/-- The coefficient-from-capacity analytic core is elementary in dimension `0`. -/
theorem vanDerWaerdenAnalyticCore_fin_zero : VanDerWaerdenAnalyticCore 0 := by
  refine ⟨?_⟩
  intro A _hA _hcap
  simp [Matrix.permanent]

/-- The coefficient-from-capacity analytic core is elementary in dimension `1`. -/
theorem vanDerWaerdenAnalyticCore_fin_one : VanDerWaerdenAnalyticCore 1 := by
  refine ⟨?_⟩
  intro A _hA hcap
  have hx : ∀ j : Fin 1, 0 < (fun _ : Fin 1 => (1 : ℝ)) j := by
    simp
  have h := hcap.le_rowLinearProduct (fun _ : Fin 1 => (1 : ℝ)) hx
  simpa [rowLinearProduct, Matrix.permanent] using h

/-- The coefficient-from-capacity analytic core is elementary in dimension `2`.

Writing the row-linear product as
`ac x₀² + (ad + bc) x₀x₁ + bd x₁²`, capacity gives nonnegativity of
`ac t² + (ad + bc - 1)t + bd` on the positive ray.  Together with
nonnegativity of the entries, this extends to all real `t` after the easy
case `ad + bc ≥ 1`; the quadratic-discriminant bound then gives
`ad + bc ≥ 1 / 2`, which is exactly the permanent lower bound for `2 × 2`
matrices.
-/
theorem vanDerWaerdenAnalyticCore_fin_two : VanDerWaerdenAnalyticCore 2 := by
  refine ⟨?_⟩
  intro A hA hcap
  have hhalf : (1 : ℝ) / 2 ≤ A 0 0 * A 1 1 + A 1 0 * A 0 1 := by
    let p : ℝ := A 0 0 * A 1 1 + A 1 0 * A 0 1
    by_cases hp : 1 ≤ p
    · linarith
    · have hp_le_one : p ≤ 1 := le_of_not_ge hp
      have hnonneg_quad : ∀ t : ℝ, 0 ≤ (A 0 0 * A 1 0) * (t * t) +
          (A 0 0 * A 1 1 + A 0 1 * A 1 0 - 1) * t + A 0 1 * A 1 1 := by
        intro t
        rcases lt_trichotomy t 0 with htneg | rfl | htpos
        · have hac : 0 ≤ A 0 0 * A 1 0 := mul_nonneg (hA 0 0) (hA 1 0)
          have hbd : 0 ≤ A 0 1 * A 1 1 := mul_nonneg (hA 0 1) (hA 1 1)
          have hmid : 0 ≤
              (A 0 0 * A 1 1 + A 0 1 * A 1 0 - 1) * t := by
            have hcoef : A 0 0 * A 1 1 + A 0 1 * A 1 0 - 1 ≤ 0 := by
              dsimp [p] at hp_le_one
              nlinarith
            exact mul_nonneg_of_nonpos_of_nonpos hcoef htneg.le
          have hquad : 0 ≤ (A 0 0 * A 1 0) * (t * t) :=
            mul_nonneg hac (mul_self_nonneg t)
          nlinarith
        · simpa using mul_nonneg (hA 0 1) (hA 1 1)
        · have hx : ∀ j : Fin 2,
              0 < (fun i : Fin 2 => if i = 0 then t else 1) j := by
            intro j
            fin_cases j <;> simp [htpos]
          have h := hcap.le_rowLinearProduct
            (fun i : Fin 2 => if i = 0 then t else 1) hx
          simp [rowLinearProduct, Fin.sum_univ_two, Fin.prod_univ_two] at h
          nlinarith
      have hdisc := discrim_le_zero (a := A 0 0 * A 1 0)
        (b := A 0 0 * A 1 1 + A 0 1 * A 1 0 - 1)
        (c := A 0 1 * A 1 1) hnonneg_quad
      have hq_le : 4 * ((A 0 0 * A 1 0) * (A 0 1 * A 1 1)) ≤ p ^ 2 := by
        dsimp [p]
        nlinarith [sq_nonneg (A 0 0 * A 1 1 - A 1 0 * A 0 1)]
      have hdisc' : (p - 1) ^ 2 ≤
          4 * ((A 0 0 * A 1 0) * (A 0 1 * A 1 1)) := by
        rw [discrim] at hdisc
        dsimp [p]
        nlinarith
      have hp_sq : (p - 1) ^ 2 ≤ p ^ 2 := le_trans hdisc' hq_le
      nlinarith
  rw [permanent_fin_two A]
  norm_num
  exact hhalf

/-- The analytic-core assumption is completely discharged in dimensions `0`, `1`, and `2`. -/
theorem vanDerWaerdenAnalyticCore_of_le_two (n : ℕ) (hn : n ≤ 2) :
    VanDerWaerdenAnalyticCore n := by
  interval_cases n
  · exact vanDerWaerdenAnalyticCore_fin_zero
  · exact vanDerWaerdenAnalyticCore_fin_one
  · exact vanDerWaerdenAnalyticCore_fin_two

theorem gurvitsCoefficientFromCapacityCore_of_le_two (n : ℕ) (hn : n ≤ 2) :
    GurvitsCoefficientFromCapacityCore n :=
  gurvitsCoefficientFromCapacityCore_of_vanDerWaerdenAnalyticCore
    (vanDerWaerdenAnalyticCore_of_le_two n hn)

theorem squarefreeCoefficientCore_of_le_two (n : ℕ) (hn : n ≤ 2) :
    GurvitsSquarefreeCoefficientFromCapacityCore n :=
  squarefreeCoefficientCore_of_gurvitsCoefficientFromCapacityCore
    (gurvitsCoefficientFromCapacityCore_of_le_two n hn)

theorem van_der_Waerden_permanent_conjecture_of_le_two (n : ℕ) (hn : n ≤ 2)
    (A : Matrix (Fin n) (Fin n) ℝ)
    (hA : A ∈ doublyStochastic ℝ (Fin n)) :
    (n.factorial : ℝ) / (n : ℝ) ^ n ≤ A.permanent := by
  interval_cases n
  · simpa using van_der_Waerden_permanent_fin_zero A hA
  · simpa using van_der_Waerden_permanent_fin_one A hA
  · simpa using van_der_Waerden_permanent_fin_two A hA

/-- Chapter 22 with no analytic-core assumption in the elementary low dimensions. -/
theorem chapter22_of_le_two (n : ℕ) (hn : n ≤ 2)
    (A : Matrix (Fin n) (Fin n) ℝ)
    (hA : A ∈ doublyStochastic ℝ (Fin n)) :
    (n.factorial : ℝ) / (n : ℝ) ^ n ≤ A.permanent :=
  van_der_Waerden_permanent_conjecture_of_le_two n hn A hA

/-! ### Boundary-convexity interface from checkerboard exchanges -/

/--
The Chapter 22 specialization of the checkerboard boundary-convexity package:
from any positive-width opposite checkerboard direction, both maximal
endpoints remain doubly stochastic, each endpoint lies on the boundary, and
the permanent at the original matrix is bounded by the corresponding convex
combination of the two endpoint permanents.

This is not yet the Van der Waerden lower bound by itself: a convexity upper
bound is the input needed for the minimizer/equality-case analysis or for the
stronger AF/Gurvits coefficient inequality.
-/
theorem checkerboardEndpointPair_boundaryConvexity {n : ℕ}
    {A : Matrix (Fin n) (Fin n) ℝ} {r s c d : Fin n}
    (hrs : r ≠ s) (hcd : c ≠ d) (hA : A ∈ doublyStochastic ℝ (Fin n))
    (hpos : 0 < checkerboardExchangeAmount A r s c d +
      checkerboardExchangeAmount A r s d c) :
    checkerboardExchangeEndpoint A r s c d ∈ doublyStochastic ℝ (Fin n) ∧
      checkerboardExchangeEndpoint A r s d c ∈ doublyStochastic ℝ (Fin n) ∧
      (checkerboardExchangeEndpoint A r s c d r d = 0 ∨
        checkerboardExchangeEndpoint A r s c d s c = 0) ∧
      (checkerboardExchangeEndpoint A r s d c r c = 0 ∨
        checkerboardExchangeEndpoint A r s d c s d = 0) ∧
      A.permanent ≤
        (1 - checkerboardExchangeAmount A r s d c /
            (checkerboardExchangeAmount A r s c d +
              checkerboardExchangeAmount A r s d c)) *
          (checkerboardExchangeEndpoint A r s d c).permanent +
        (checkerboardExchangeAmount A r s d c /
            (checkerboardExchangeAmount A r s c d +
              checkerboardExchangeAmount A r s d c)) *
          (checkerboardExchangeEndpoint A r s c d).permanent := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact checkerboardExchangeEndpoint_mem_doublyStochastic hrs hcd hA
  · exact checkerboardExchangeEndpoint_mem_doublyStochastic hrs hcd.symm hA
  · exact checkerboardExchangeEndpoint_boundary_zero
      (M := A) (r := r) (s := s) (c := c) (d := d) hrs hcd
  · exact checkerboardExchangeEndpoint_boundary_zero
      (M := A) (r := r) (s := s) (c := d) (d := c) hrs hcd.symm
  · exact checkerboardExchangeEndpoint_backward_line_permanent_le
      (M := A) (r := r) (s := s) (c := c) (d := d) hrs hcd hA hpos

/-- The genuine Van der Waerden permanent lower-bound statement, conditional
on the named analytic core above.  Point-17 status: ③, conditional on an
unproved but precisely identified analytic theorem, not a flat-matrix
fragment. -/
theorem van_der_Waerden_permanent_conjecture_from_analyticCore (n : ℕ)
    (core : VanDerWaerdenAnalyticCore n)
    (A : Matrix (Fin n) (Fin n) ℝ)
    (hA : A ∈ doublyStochastic ℝ (Fin n)) :
    (n.factorial : ℝ) / (n : ℝ) ^ n ≤ A.permanent := by
  exact core.coefficient_bound A
    (fun i j => nonneg_of_mem_doublyStochastic hA)
    (rowLinearCapacityAtLeastOne_of_doublyStochastic A hA)

/--
The same conditional endpoint, but stated with the genuine Gurvits
mixed-coefficient theorem as the assumption.
-/
theorem van_der_Waerden_permanent_conjecture_from_gurvitsCoefficientCore
    (n : ℕ) (core : GurvitsCoefficientFromCapacityCore n)
    (A : Matrix (Fin n) (Fin n) ℝ)
    (hA : A ∈ doublyStochastic ℝ (Fin n)) :
    (n.factorial : ℝ) / (n : ℝ) ^ n ≤ A.permanent := by
  exact van_der_Waerden_permanent_conjecture_from_analyticCore n
    (vanDerWaerdenAnalyticCore_of_gurvitsCoefficientFromCapacityCore core) A hA

/--
The same conditional endpoint from the literal squarefree-coefficient version
of the Gurvits/AF theorem.
-/
theorem van_der_Waerden_permanent_conjecture_from_squarefreeCoefficientCore
    (n : ℕ) (core : GurvitsSquarefreeCoefficientFromCapacityCore n)
    (A : Matrix (Fin n) (Fin n) ℝ)
    (hA : A ∈ doublyStochastic ℝ (Fin n)) :
    (n.factorial : ℝ) / (n : ℝ) ^ n ≤ A.permanent := by
  exact van_der_Waerden_permanent_conjecture_from_analyticCore n
    (vanDerWaerdenAnalyticCore_of_squarefreeCoefficientCore core) A hA

/--
The genuine Van der Waerden permanent lower-bound statement, with the analytic
core assumption needed only in dimensions `n ≥ 3`; dimensions `0`, `1`, and
`2` are discharged above.
-/
theorem van_der_Waerden_permanent_conjecture_from_large_dim_analyticCore
    (core : ∀ m : ℕ, 3 ≤ m → VanDerWaerdenAnalyticCore m)
    (n : ℕ) (A : Matrix (Fin n) (Fin n) ℝ)
    (hA : A ∈ doublyStochastic ℝ (Fin n)) :
    (n.factorial : ℝ) / (n : ℝ) ^ n ≤ A.permanent := by
  by_cases hn : n ≤ 2
  · exact van_der_Waerden_permanent_conjecture_of_le_two n hn A hA
  · have h3 : 3 ≤ n := by omega
    exact van_der_Waerden_permanent_conjecture_from_analyticCore n (core n h3) A hA

theorem van_der_Waerden_permanent_conjecture_from_large_dim_gurvitsCore
    (core : ∀ m : ℕ, 3 ≤ m → GurvitsCoefficientFromCapacityCore m)
    (n : ℕ) (A : Matrix (Fin n) (Fin n) ℝ)
    (hA : A ∈ doublyStochastic ℝ (Fin n)) :
    (n.factorial : ℝ) / (n : ℝ) ^ n ≤ A.permanent := by
  exact van_der_Waerden_permanent_conjecture_from_large_dim_analyticCore
    (fun m hm => vanDerWaerdenAnalyticCore_of_gurvitsCoefficientFromCapacityCore
      (core m hm)) n A hA

theorem van_der_Waerden_permanent_conjecture_from_large_dim_squarefreeCoefficientCore
    (core : ∀ m : ℕ, 3 ≤ m → GurvitsSquarefreeCoefficientFromCapacityCore m)
    (n : ℕ) (A : Matrix (Fin n) (Fin n) ℝ)
    (hA : A ∈ doublyStochastic ℝ (Fin n)) :
    (n.factorial : ℝ) / (n : ℝ) ^ n ≤ A.permanent := by
  exact van_der_Waerden_permanent_conjecture_from_large_dim_analyticCore
    (fun m hm => vanDerWaerdenAnalyticCore_of_squarefreeCoefficientCore
      (core m hm)) n A hA

theorem chapter22
    (core : ∀ m : ℕ, 3 ≤ m → VanDerWaerdenAnalyticCore m)
    (n : ℕ)
    (A : Matrix (Fin n) (Fin n) ℝ)
    (hA : A ∈ doublyStochastic ℝ (Fin n)) :
    (n.factorial : ℝ) / (n : ℝ) ^ n ≤ A.permanent :=
  van_der_Waerden_permanent_conjecture_from_large_dim_analyticCore core n A hA

end

end ProofsInTheBook.Chapter22
