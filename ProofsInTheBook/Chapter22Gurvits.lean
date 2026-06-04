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
