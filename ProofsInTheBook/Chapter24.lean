import Mathlib

/-!
# Chapter 24: Cotangent and the Herglotz trick

From "Proofs from THE BOOK":

**Herglotz trick**: The partial fraction expansion
π·cot(πx) = 1/x + ∑_{n=1}^∞ (1/(x+n) + 1/(x-n))
is proved by showing both sides satisfy the same functional equation
f(x) + f(1-x) = ... and f(x+1) = f(x), with matching initial conditions.

Applications include the Basel problem (Chapter 8) and evaluation of
the Riemann zeta function at even integers.
-/

namespace ProofsInTheBook.Chapter24

/-- The elementary `π`-periodicity of the real cotangent. -/
theorem cot_add_pi (x : ℝ) : Real.cot (x + Real.pi) = Real.cot x := by
  rw [Real.cot_eq_cos_div_sin, Real.cot_eq_cos_div_sin, Real.cos_add_pi, Real.sin_add_pi]
  ring

/-- Cotangent is odd; this is one of the symmetries used in Herglotz's trick. -/
theorem cot_neg (x : ℝ) : Real.cot (-x) = -Real.cot x := by
  rw [Real.cot_eq_cos_div_sin, Real.cot_eq_cos_div_sin, Real.cos_neg, Real.sin_neg]
  ring

/-- The `x ↦ x + 1` functional equation for `cot(πx)`. -/
theorem cot_pi_add_one (x : ℝ) : Real.cot (Real.pi * (x + 1)) = Real.cot (Real.pi * x) := by
  have harg : Real.pi * (x + 1) = Real.pi * x + Real.pi := by ring
  rw [harg, cot_add_pi]

/-- The `x ↦ 1 - x` symmetry for `cot(πx)`. -/
theorem cot_pi_one_sub (x : ℝ) : Real.cot (Real.pi * (1 - x)) = -Real.cot (Real.pi * x) := by
  have harg : Real.pi * (1 - x) = -(Real.pi * x) + Real.pi := by ring
  rw [harg, cot_add_pi, cot_neg]

/--
The rational-function side of the `x ↦ 1 - x` Herglotz functional equation
for the two singular terms.
-/
theorem reciprocal_add_one_sub (x : ℝ) (hx : x ≠ 0) (hx1 : x ≠ 1) :
    1 / x + 1 / (1 - x) = 1 / (x * (1 - x)) := by
  field_simp [hx, sub_ne_zero.mpr hx1]
  ring_nf

theorem chapter24 (x : ℝ) :
    Real.pi * Real.cot (Real.pi * x) + Real.pi * Real.cot (Real.pi * (1 - x)) = 0 := by
  rw [cot_pi_one_sub]
  ring

end ProofsInTheBook.Chapter24
