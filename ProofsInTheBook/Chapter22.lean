import Mathlib

/-!
# Chapter 22: Van der Waerden's permanent conjecture

From "Proofs from THE BOOK":

**Van der Waerden's conjecture** (now theorem, proved by Falikman and
Egorychev): The permanent of a doubly stochastic n×n matrix is minimized
by the matrix with all entries 1/n, giving perm ≥ n!/nⁿ.

The book presents the proof using the theory of mixed discriminants.
-/

namespace ProofsInTheBook.Chapter22

open Matrix

noncomputable section

/-!
### The equality case matrix

The van der Waerden theorem says every doubly stochastic matrix has permanent
at least `n! / n^n`, with equality at the flat matrix.  This file records the
exact permanent computation for that flat matrix.
-/

def flatDoublyStochasticMatrix (n : ℕ) : Matrix (Fin n) (Fin n) ℝ :=
  fun _ _ => (n : ℝ)⁻¹

theorem permanent_flatDoublyStochasticMatrix (n : ℕ) :
    (flatDoublyStochasticMatrix n).permanent = (n.factorial : ℝ) / (n : ℝ) ^ n := by
  calc
    (flatDoublyStochasticMatrix n).permanent =
        (n.factorial : ℝ) * ((n : ℝ)⁻¹) ^ n := by
      simp [flatDoublyStochasticMatrix, Matrix.permanent, Finset.prod_const, Fintype.card_perm]
    _ = (n.factorial : ℝ) / (n : ℝ) ^ n := by
      rw [inv_pow, div_eq_mul_inv]

theorem chapter22 (n : ℕ) :
    (flatDoublyStochasticMatrix n).permanent = (n.factorial : ℝ) / (n : ℝ) ^ n :=
  permanent_flatDoublyStochasticMatrix n

end

end ProofsInTheBook.Chapter22
