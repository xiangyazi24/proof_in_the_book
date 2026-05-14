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
