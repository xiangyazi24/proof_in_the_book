import Mathlib

/-!
# Chapter 19: The fundamental theorem of algebra

From "Proofs from THE BOOK":

**FTA**: Every non-constant polynomial with complex coefficients has a root.

The book presents a proof using the minimum modulus principle:
Consider |p(z)| for a polynomial p of degree n ≥ 1. Since |p(z)| → ∞
as |z| → ∞, the minimum of |p(z)| is attained at some z₀. If |p(z₀)| > 0,
write p(z₀ + w) = p(z₀) + cₘwᵐ + higher terms (m ≥ 1). Choosing w
to make cₘwᵐ point opposite to p(z₀) reduces |p(z₀ + w)| < |p(z₀)|,
contradicting minimality.
-/

namespace ProofsInTheBook.Chapter19

open Polynomial

/-- Translate a polynomial to local coordinates around `z₀`: `w ↦ p(w + z₀)`. -/
noncomputable def shiftedPolynomial (p : ℂ[X]) (z₀ : ℂ) : ℂ[X] :=
  p.comp (Polynomial.X + Polynomial.C z₀)

theorem shiftedPolynomial_eval (p : ℂ[X]) (z₀ w : ℂ) :
    (shiftedPolynomial p z₀).eval w = p.eval (w + z₀) := by
  simp [shiftedPolynomial]

theorem shiftedPolynomial_eval_zero (p : ℂ[X]) (z₀ : ℂ) :
    (shiftedPolynomial p z₀).eval 0 = p.eval z₀ := by
  simpa using shiftedPolynomial_eval p z₀ 0

theorem shiftedPolynomial_coeff_zero (p : ℂ[X]) (z₀ : ℂ) :
    (shiftedPolynomial p z₀).coeff 0 = p.eval z₀ := by
  rw [Polynomial.coeff_zero_eq_eval_zero, shiftedPolynomial_eval_zero]

/--
Root transfer after translating to local coordinates. This is the algebraic
step used in the minimum-modulus proof after expanding around the minimizing
point.
-/
theorem isRoot_of_shiftedPolynomial_isRoot {p : ℂ[X]} {z₀ w : ℂ}
    (h : IsRoot (shiftedPolynomial p z₀) w) : IsRoot p (w + z₀) := by
  simpa [Polynomial.IsRoot, shiftedPolynomial_eval] using h

/--
The explicit linear case behind the minimum-modulus proof of the fundamental
theorem of algebra: a nonzero first-order term can be cancelled by moving in
the direction `-b / c`.
-/
theorem linear_polynomial_has_root (b c : ℂ) (hc : c ≠ 0) :
    IsRoot (Polynomial.C c * Polynomial.X + Polynomial.C b) (-b / c) := by
  simp [Polynomial.IsRoot]
  field_simp [hc]
  ring

theorem monic_linear_has_root (a : ℂ) : IsRoot (Polynomial.X - Polynomial.C a) a := by
  simp [Polynomial.IsRoot]

theorem chapter19 (b c : ℂ) (hc : c ≠ 0) :
    IsRoot (Polynomial.C c * Polynomial.X + Polynomial.C b) (-b / c) :=
  linear_polynomial_has_root b c hc

end ProofsInTheBook.Chapter19
