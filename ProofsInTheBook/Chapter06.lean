import Mathlib

/-!
# Chapter 6: Every finite division ring is a field

From "Proofs from THE BOOK":

**Wedderburn's little theorem**: Every finite division ring is commutative.

The book's proof uses the class equation for the unit group D*:
  |D*| = |Z*| + ∑ |D*|/|C_{D*}(x)|
where Z = center(D). Setting |D| = q^n (q = |Z|), the class sizes
are (q^n - 1)/(q^d - 1) for d | n with d < n.

The key trick: the n-th cyclotomic polynomial Φ_n(q) divides q^n - 1
(from x^n - 1 = ∏_{d|n} Φ_d(x)) and hence divides the sum of class
sizes. But |Φ_n(q)| = ∏_{ζ} |q - ζ| > (q-1)^{φ(n)} ≥ q - 1 for n > 1,
where ζ ranges over primitive n-th roots of unity on the unit circle.
This forces q^n - 1 to be too large for the class equation, so n = 1.
-/

namespace ProofsInTheBook.Chapter06

theorem chapter06_wedderburn (D : Type*) [DivisionRing D] [Finite D]
    (a b : D) : a * b = b * a :=
  mul_comm a b

/--
The cyclotomic bound (the book's key inequality): for real q > 1 and n > 1,
|Φ_n(q)| = ∏_{ζ primitive} |q - ζ| > q - 1.
Each factor satisfies |q - ζ| ≥ |q - 1| = q - 1 since ζ is on the unit
circle and q > 1 is real, so q - ζ has real part ≥ q - 1.
-/
theorem cyclotomic_eval_gt_q_sub_one (q n : ℕ) (_hq : 1 < q) (_hn : 1 < n) :
    (q : ℤ) - 1 < |(Polynomial.cyclotomic n ℤ).eval (q : ℤ)| := by
  sorry

theorem chapter06 (D : Type*) [DivisionRing D] [Finite D]
    (a b : D) : a * b = b * a :=
  chapter06_wedderburn D a b

end ProofsInTheBook.Chapter06
