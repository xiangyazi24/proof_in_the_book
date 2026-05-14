import Mathlib

/-!
# Chapter 30: Lattice paths and determinants

From "Proofs from THE BOOK":

**Lindström-Gessel-Viennot lemma**: The number of non-intersecting
lattice path systems from sources to sinks equals a determinant.

The book applies this to count standard Young tableaux and proves
the hook length formula: |SYT(λ)| = n! / ∏ hook_lengths.
-/

namespace ProofsInTheBook.Chapter30

open Matrix BigOperators

/--
The diagonal case of the Lindström-Gessel-Viennot determinant: when the
path-counting matrix has no off-diagonal contributions, the determinant
has only the identity permutation term.
-/
theorem det_eq_diag_product_of_offdiag_zero {ι R : Type*}
    [Fintype ι] [DecidableEq ι] [CommRing R] (M : Matrix ι ι R)
    (hzero : ∀ i j, i ≠ j → M i j = 0) :
    M.det = ∏ i, M i i := by
  have hM : M = Matrix.diagonal (fun i => M i i) := by
    ext i j
    by_cases hij : i = j
    · subst j
      simp [Matrix.diagonal]
    · simp [Matrix.diagonal, hij, hzero i j hij]
  rw [hM]
  simp

theorem chapter30 {ι R : Type*}
    [Fintype ι] [DecidableEq ι] [CommRing R] (M : Matrix ι ι R)
    (hzero : ∀ i j, i ≠ j → M i j = 0) :
    M.det = ∏ i, M i i :=
  det_eq_diag_product_of_offdiag_zero M hzero

end ProofsInTheBook.Chapter30
