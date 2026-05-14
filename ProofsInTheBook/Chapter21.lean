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

theorem chapter21 (x : ℤ) (k : ℕ) :
    forwardDifference (fun y : ℤ => Ring.choose y (k + 1)) x = Ring.choose x k :=
  binomial_forwardDifference x k

end

end ProofsInTheBook.Chapter21
