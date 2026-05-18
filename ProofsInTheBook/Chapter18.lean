import Mathlib

/-!
# Chapter 18: In praise of inequalities

From "Proofs from THE BOOK":

**AM-GM inequality**: For non-negative reals, (a+b)/2 ≥ √(ab).

*Book proof (2-variable case).* From (√a - √b)² ≥ 0 we get
a - 2√(ab) + b ≥ 0, hence (a+b)/2 ≥ √(ab).

**Cauchy-Schwarz**: (∑aᵢbᵢ)² ≤ (∑aᵢ²)(∑bᵢ²), proved via the
discriminant of the quadratic ∑(aᵢx + bᵢ)² ≥ 0.
-/

namespace ProofsInTheBook.Chapter18

/-!
### AM-GM: the (a-b)² ≥ 0 trick

The simplest nontrivial inequality: for all reals a, b,
  a² + b² ≥ 2ab
follows from (a-b)² ≥ 0. This is the heart of AM-GM.
-/

theorem chapter18_sq_abs_le (a b : ℝ) : 2 * a * b ≤ a ^ 2 + b ^ 2 := by
  nlinarith [sq_nonneg (a - b)]

theorem chapter18_am_gm_sq (a b : ℝ) (_ha : 0 ≤ a) (_hb : 0 ≤ b) :
    a * b ≤ ((a + b) / 2) ^ 2 := by
  nlinarith [sq_nonneg (a - b)]

theorem chapter18 (a b : ℝ) : 2 * a * b ≤ a ^ 2 + b ^ 2 :=
  chapter18_sq_abs_le a b

end ProofsInTheBook.Chapter18
