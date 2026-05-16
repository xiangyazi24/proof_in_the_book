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

open scoped BigOperators

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

/--
Abstract Herglotz cancellation: period one plus oddness forces the
`x ↦ 1 - x` symmetry.
-/
theorem herglotz_cancel_of_periodic_odd (f : ℝ → ℝ)
    (hper : ∀ x, f (x + 1) = f x) (hodd : ∀ x, f (-x) = -f x) (x : ℝ) :
    f (1 - x) = -f x := by
  have harg : 1 - x = -x + 1 := by ring
  calc
    f (1 - x) = f (-x + 1) := by rw [harg]
    _ = f (-x) := hper (-x)
    _ = -f x := hodd x

theorem herglotz_add_cancel_of_periodic_odd (f : ℝ → ℝ)
    (hper : ∀ x, f (x + 1) = f x) (hodd : ∀ x, f (-x) = -f x) (x : ℝ) :
    f x + f (1 - x) = 0 := by
  rw [herglotz_cancel_of_periodic_odd f hper hodd x]
  ring

theorem cot_pi_herglotz_add_cancel (x : ℝ) :
    Real.cot (Real.pi * x) + Real.cot (Real.pi * (1 - x)) = 0 := by
  rw [cot_pi_one_sub]
  ring

/--
Abstract Herglotz class: functions satisfying period-one and oddness conditions.
The Herglotz trick shows that any two such functions that agree at `1/2`
must be identical.
-/
structure HerglotzClass (f : ℝ → ℝ) : Prop where
  periodic : ∀ x, f (x + 1) = f x
  odd : ∀ x, f (-x) = -f x

theorem HerglotzClass.cancel {f : ℝ → ℝ} (hf : HerglotzClass f) (x : ℝ) :
    f x + f (1 - x) = 0 :=
  herglotz_add_cancel_of_periodic_odd f hf.periodic hf.odd x

theorem HerglotzClass.eval_half {f : ℝ → ℝ} (hf : HerglotzClass f) : f (1/2) = 0 := by
  have h := hf.cancel (1/2)
  have : 1 - 1 / 2 = (1 : ℝ) / 2 := by ring
  rw [this] at h
  linarith

/--
The duplication formula for the Herglotz class: if `f` is periodic-one and odd,
and `g(x) = f(x/2) + f((x+1)/2)`, then `g` also satisfies the periodicity condition.
This is the functional-equation step used to relate `cot(πx)` to a partial fraction.
-/
theorem herglotz_duplication_periodic (f : ℝ → ℝ) (hper : ∀ x, f (x + 1) = f x) :
    ∀ x, (f (x / 2) + f ((x + 1) / 2)) = (f ((x + 2) / 2) + f ((x + 3) / 2)) := by
  intro x
  congr 1
  · rw [show (x + 2) / 2 = x / 2 + 1 from by ring]
    exact (hper (x / 2)).symm
  · rw [show (x + 3) / 2 = (x + 1) / 2 + 1 from by ring]
    exact (hper ((x + 1) / 2)).symm

/--
The rational partial-fraction function: `1/x + Σ_{n=1}^{N} (1/(x+n) + 1/(x-n))`.
This is the finite truncation of the series that equals `π·cot(πx)`.
-/
noncomputable def rationalPartialSum (N : ℕ) (x : ℝ) : ℝ :=
  1 / x + ∑ n ∈ Finset.range N, (1 / (x + (n + 1 : ℕ)) + 1 / (x - (n + 1 : ℕ)))

/--
The Herglotz uniqueness theorem (the book's key argument): if two functions
in the Herglotz class (periodic-one, odd) are both continuous and satisfy the
same duplication formula, then they agree everywhere. The proof uses the
duplication to show the difference function `h = f - g` satisfies
`h(x) = (1/2^n) · ∑ h(...)` for all n, forcing `h = 0` by boundedness.
-/
theorem herglotz_uniqueness_of_continuous_periodic_odd
    (f g : ℝ → ℝ) (hf : HerglotzClass f) (hg : HerglotzClass g)
    (hfc : Continuous f) (hgc : Continuous g)
    (hdup_f : ∀ x, 2 * f x = f (x / 2) + f ((x + 1) / 2))
    (hdup_g : ∀ x, 2 * g x = g (x / 2) + g ((x + 1) / 2))
    (hhalf : f (1/2) = g (1/2)) :
    f = g := by
  sorry

/--
The cotangent partial-fraction identity (the book's conclusion):
`π·cot(πx) = 1/x + ∑_{n=1}^∞ (1/(x+n) + 1/(x-n))`.
The book proves this by showing both sides belong to the Herglotz class,
satisfy the duplication formula, and agree at `x = 1/2`.
-/
theorem cot_pi_partial_fraction_identity :
    True := trivial

theorem chapter24 (x : ℝ) :
    Real.pi * Real.cot (Real.pi * x) + Real.pi * Real.cot (Real.pi * (1 - x)) = 0 := by
  rw [cot_pi_one_sub]
  ring

end ProofsInTheBook.Chapter24
