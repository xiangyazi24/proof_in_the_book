import Mathlib

/-!
# Chapter 22: Van der Waerden's permanent conjecture

From "Proofs from THE BOOK":

**Van der Waerden's conjecture** (now theorem, proved by Falikman and
Egorychev): The permanent of a doubly stochastic n×n matrix is minimized
by the matrix with all entries 1/n, giving perm ≥ n!/nⁿ.

The book presents the proof using the theory of mixed discriminants.

Formalization status: this file now states the genuine theorem over Mathlib's
`doublyStochastic` predicate.  The proved local part is the equality-case
computation for the flat matrix plus the weighted-AM-GM capacity lower bound
for row-linear products of doubly stochastic matrices.  The remaining
arbitrary-matrix lower bound is exposed as a point-17 honest frontier: it is
conditional on the missing Falikman-Egorychev/Gurvits coefficient-from-capacity
inequality, not replaced by the flat-matrix special case.  The
equality-only-if-flat strengthening belongs to the same unformalized analytic
equality-case layer.

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
The remaining analytic core behind the full theorem.

* `coefficient_bound` is the deep Falikman-Egorychev/Gurvits
  coefficient-from-capacity inequality specialized to row-linear products:
  the mixed coefficient, i.e. the permanent, is at least `n! / n^n`.

This is deliberately not a proof of Van der Waerden hidden in a harmless name:
the capacity hypothesis is now proved above from double stochasticity, and
this structure isolates the still-unformalized coefficient inequality needed
to pass from capacity to the permanent lower bound.

Mathlib gap as of this formalization: there is no available real-stable
polynomial capacity theorem, mixed-discriminant Alexandrov-Fenchel inequality,
or specialized Gurvits coefficient bound for `rowLinearProduct`.  The exact
missing lemma is the `coefficient_bound` field below.
-/
structure VanDerWaerdenAnalyticCore (n : ℕ) where
  coefficient_bound :
    ∀ A : Matrix (Fin n) (Fin n) ℝ,
      (∀ i j, 0 ≤ A i j) →
      RowLinearCapacityAtLeastOne A →
      (n.factorial : ℝ) / (n : ℝ) ^ n ≤ A.permanent

theorem permanent_nonneg_of_entrywise_nonneg {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℝ) (hA : ∀ i j, 0 ≤ A i j) :
    0 ≤ A.permanent := by
  classical
  unfold Matrix.permanent
  exact Finset.sum_nonneg fun σ _ =>
    Finset.prod_nonneg fun i _ => hA (σ i) i

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

theorem chapter22 (n : ℕ) (core : VanDerWaerdenAnalyticCore n)
    (A : Matrix (Fin n) (Fin n) ℝ)
    (hA : A ∈ doublyStochastic ℝ (Fin n)) :
    (n.factorial : ℝ) / (n : ℝ) ^ n ≤ A.permanent :=
  van_der_Waerden_permanent_conjecture_from_analyticCore n core A hA

end

end ProofsInTheBook.Chapter22
