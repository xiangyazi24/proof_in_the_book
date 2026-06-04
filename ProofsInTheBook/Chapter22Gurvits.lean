import Mathlib

/-!
# Chapter 22 (van der Waerden permanent bound) — Gurvits capacity, algebraic core

The Gurvits capacity proof reduces `perm(A) ≥ n!/nⁿ` (for doubly stochastic `A`) to a chain of
capacity inequalities with reduction constant `G(k) = ((k-1)/k)^{k-1}`. The product of these
constants telescopes to exactly `n!/nⁿ` — that is the algebraic heart proved here. Blueprint:
`HANDOFF/CH22_GURVITS_CAPACITY.md`.
-/

namespace ProofsInTheBook.Chapter22Gurvits

open scoped BigOperators

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
