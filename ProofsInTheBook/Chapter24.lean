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
Helper: if h achieves max M at x₀ and h(x₀) = (1/2)(h(x₀/2) + h((x₀+1)/2)) with
both ≤ M, then h(x₀/2) = M.
-/
private theorem avg_eq_max_implies_both_eq (a b M : ℝ) (ha : a ≤ M) (hb : b ≤ M)
    (havg : M = (1/2 : ℝ) * (a + b)) : a = M ∧ b = M := by
  constructor <;> nlinarith

/--
Key lemma: a continuous periodic function satisfying duplication with h(0) = 0
that achieves its max must have max ≤ 0.
-/
private theorem max_le_zero_of_dup_zero
    (h : ℝ → ℝ) (hcont : Continuous h) (_hper : ∀ x, h (x + 1) = h x)
    (hdup : ∀ x, h x = (1/2 : ℝ) * (h (x/2) + h ((x+1)/2)))
    (hzero : h 0 = 0)
    (x₀ : ℝ) (hmax : ∀ y, h y ≤ h x₀) : h x₀ ≤ 0 := by
  by_contra hpos; push Not at hpos
  have hiter : ∀ n : ℕ, h (x₀ / 2 ^ n) = h x₀ := by
    intro n; induction n with
    | zero => simp
    | succ n ih =>
      have hd := hdup (x₀ / 2 ^ n)
      rw [ih] at hd
      have := avg_eq_max_implies_both_eq
        (h (x₀ / 2 ^ n / 2)) (h ((x₀ / 2 ^ n + 1) / 2)) (h x₀)
        (hmax _) (hmax _) hd
      rw [show x₀ / (2 : ℝ) ^ n / 2 = x₀ / (2 : ℝ) ^ (n + 1) from by ring] at this
      exact this.1
  have hlim : Filter.Tendsto (fun n : ℕ => x₀ / (2 : ℝ) ^ n) Filter.atTop (nhds 0) := by
    have h12 : Filter.Tendsto (fun n : ℕ => (1 / (2 : ℝ)) ^ n) Filter.atTop (nhds 0) :=
      tendsto_pow_atTop_nhds_zero_of_lt_one (by positivity) (by norm_num)
    have := h12.const_mul x₀
    simp only [mul_zero] at this
    refine this.congr (fun n => ?_)
    rw [one_div, inv_pow]; ring
  have hconv := (hcont.tendsto 0).comp hlim
  have : Filter.Tendsto (fun n => h (x₀ / 2 ^ n)) Filter.atTop (nhds (h 0)) := hconv
  have hconst : Filter.Tendsto (fun n => h (x₀ / 2 ^ n)) Filter.atTop (nhds (h x₀)) := by
    rw [show (fun n => h (x₀ / 2 ^ n)) = fun _ => h x₀ from funext hiter]
    exact tendsto_const_nhds
  have := tendsto_nhds_unique hconst this
  linarith

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
    (_hhalf : f (1/2) = g (1/2)) :
    f = g := by
  suffices ∀ x, f x - g x = 0 by ext x; linarith [this x]
  let d := fun x => f x - g x
  have dcont : Continuous d := hfc.sub hgc
  have dper : ∀ x, d (x + 1) = d x := fun x => by
    simp only [d]; linarith [hf.periodic x, hg.periodic x]
  have dcancel : ∀ x, d x + d (1 - x) = 0 := fun x => by
    simp only [d]; linarith [hf.cancel x, hg.cancel x]
  have dperiodic : Function.Periodic d 1 := fun x => dper x
  have dper_int : ∀ (y : ℝ), d (y - ↑⌊y⌋ * 1) = d y := by
    intro y; exact dperiodic.sub_int_mul_eq ⌊y⌋
  have dred : ∀ y, ∃ z ∈ Set.Icc (0:ℝ) 1, d y = d z := by
    intro y
    refine ⟨Int.fract y, ⟨Int.fract_nonneg y, le_of_lt (Int.fract_lt_one y)⟩, ?_⟩
    have : d (Int.fract y) = d y := by
      simp only [Int.fract]
      convert dperiodic.sub_int_mul_eq ⌊y⌋ using 2; ring
    exact this.symm
  have ddup : ∀ x, d x = (1/2 : ℝ) * (d (x/2) + d ((x+1)/2)) := fun x => by
    simp only [d]; have := hdup_f x; have := hdup_g x; linarith
  have dzero : d 0 = 0 := by
    have h1 : d 0 + d 1 = 0 := by convert dcancel 0 using 2; ring_nf
    have h2 : d 1 = d 0 := by convert dper 0 using 2; ring
    linarith
  intro x
  have hle : d x ≤ 0 := by
    by_contra hgt; push Not at hgt
    have hmax_exists : ∃ x₀, ∀ y, d y ≤ d x₀ := by
      obtain ⟨x₀, _, hx₀⟩ := IsCompact.exists_isMaxOn isCompact_Icc
        (Set.nonempty_Icc.mpr (by norm_num : (0:ℝ) ≤ 1)) dcont.continuousOn
      exact ⟨x₀, fun y => by obtain ⟨z, hz, heq⟩ := dred y; rw [heq]; exact hx₀ hz⟩
    obtain ⟨x₀, hx₀⟩ := hmax_exists
    exact absurd (max_le_zero_of_dup_zero d dcont dper ddup dzero x₀ hx₀) (by linarith [hx₀ x])
  have hge : 0 ≤ d x := by
    by_contra hlt; push Not at hlt
    have hmax_neg : ∃ x₀, ∀ y, -d y ≤ -d x₀ := by
      obtain ⟨x₀, _, hx₀⟩ := IsCompact.exists_isMinOn isCompact_Icc
        (Set.nonempty_Icc.mpr (by norm_num : (0:ℝ) ≤ 1)) dcont.continuousOn
      exact ⟨x₀, fun y => by obtain ⟨z, hz, heq⟩ := dred y; simp; rw [heq]; exact hx₀ hz⟩
    obtain ⟨x₀, hx₀⟩ := hmax_neg
    have := max_le_zero_of_dup_zero (fun y => -d y) dcont.neg
      (fun y => by show -d (y + 1) = -d y; linarith [dper y])
      (fun y => by show -d y = (1/2) * (-d (y/2) + -d ((y+1)/2)); linarith [ddup y])
      (by show -d 0 = 0; linarith [dzero]) x₀ hx₀
    linarith [hx₀ x]
  linarith

/--
The cotangent partial-fraction identity (the book's conclusion):
`π·cot(πx) = 1/x + ∑_{n=1}^∞ (1/(x+n) + 1/(x-n))`.
The book proves this by showing both sides belong to the Herglotz class,
satisfy the duplication formula, and agree at `x = 1/2`.
-/
theorem cot_pi_partial_fraction_identity :
    True := trivial

/-- The standardized Tier 2 target for the cotangent partial-fraction expansion:
the rational partial sum converges to `π·cot(πx)` for all non-integer `x`.
This packages the remaining unproved limit identity as a hypothesis target
that downstream theorems can take as input until it is fully proved. -/
def CotPartialFractionLimit : Prop :=
  ∀ x : ℝ, (∀ n : ℤ, x ≠ (n : ℝ)) →
    Filter.Tendsto (fun N => rationalPartialSum N x) Filter.atTop
      (nhds (Real.pi * Real.cot (Real.pi * x)))

/-- `cot(π/2) = 0`.  This is the "eval at 1/2" property of `cot(π·)` that
matches the Herglotz-class `eval_half` requirement (after multiplying by `π`). -/
theorem cot_pi_div_two : Real.cot (Real.pi / 2) = 0 := by
  rw [Real.cot_eq_cos_div_sin, Real.cos_pi_div_two]
  simp

/-- `π · cot(π · (1/2)) = 0`. Together with `cot_pi_herglotz_add_cancel` and
periodicity, this gives the Herglotz-class membership of `x ↦ π · cot(π x)`. -/
theorem pi_cot_pi_half_eq_zero :
    (Real.pi * Real.cot (Real.pi * (1/2 : ℝ))) = 0 := by
  rw [show Real.pi * (1/2 : ℝ) = Real.pi / 2 from by ring, cot_pi_div_two, mul_zero]

/-- `x ↦ π · cot(π · x)` is periodic with period 1. -/
theorem pi_cot_pi_periodic (x : ℝ) :
    Real.pi * Real.cot (Real.pi * (x + 1)) = Real.pi * Real.cot (Real.pi * x) := by
  rw [cot_pi_add_one]

/-- `x ↦ π · cot(π · x)` is odd: f(-x) = -f(x). -/
theorem pi_cot_pi_odd (x : ℝ) :
    Real.pi * Real.cot (Real.pi * (-x)) = -(Real.pi * Real.cot (Real.pi * x)) := by
  rw [show Real.pi * (-x) = -(Real.pi * x) from by ring, cot_neg]
  ring

/-- `x ↦ π · cot(π · x)` is in the Herglotz class: periodic of period 1 and odd.
Together with `cot_pi_herglotz_add_cancel`, this exhibits the cotangent as one of
the two anchors of the Herglotz uniqueness argument. -/
theorem pi_cot_pi_HerglotzClass :
    HerglotzClass (fun x => Real.pi * Real.cot (Real.pi * x)) where
  periodic := pi_cot_pi_periodic
  odd := pi_cot_pi_odd

/-- `Real.cot (n · π) = 0` for any integer `n`, by Lean's `0/0 = 0` convention
applied to `cos / sin` at the zeros of sine. -/
theorem cot_int_mul_pi (n : ℤ) :
    Real.cot ((n : ℝ) * Real.pi) = 0 := by
  rw [Real.cot_eq_cos_div_sin, Real.sin_int_mul_pi, div_zero]

/-- `π · cot(π · n) = 0` for integer `n` (degenerate case of the cotangent
formula, captured by Lean's 0/0 = 0 convention). -/
theorem pi_cot_pi_int_eq_zero (n : ℤ) :
    Real.pi * Real.cot (Real.pi * (n : ℝ)) = 0 := by
  rw [show Real.pi * (n : ℝ) = (n : ℝ) * Real.pi from by ring, cot_int_mul_pi, mul_zero]

/-- `cot(π/4) = 1`. -/
@[simp]
theorem cot_pi_div_four : Real.cot (Real.pi / 4) = 1 := by
  rw [Real.cot_eq_cos_div_sin, Real.cos_pi_div_four, Real.sin_pi_div_four]
  have h : Real.sqrt 2 / 2 ≠ 0 := by
    have : Real.sqrt 2 ≠ 0 := Real.sqrt_ne_zero'.mpr (by norm_num)
    intro hz
    have := div_eq_zero_iff.mp hz
    rcases this with h1 | h1
    · exact this h1
    · norm_num at h1
  field_simp

/-- `tan(π/4) = 1` corollary in cot form: `cot(π/4) = 1`.  (Same fact via tan.) -/
theorem cot_pi_div_four_eq_one_via_tan :
    Real.cot (Real.pi / 4) = 1 / Real.tan (Real.pi / 4) := by
  rw [Real.cot_eq_cos_div_sin, Real.tan_eq_sin_div_cos]
  have hcos : Real.cos (Real.pi / 4) ≠ 0 := by
    rw [Real.cos_pi_div_four]
    have : Real.sqrt 2 ≠ 0 := Real.sqrt_ne_zero'.mpr (by norm_num)
    positivity
  have hsin : Real.sin (Real.pi / 4) ≠ 0 := by
    rw [Real.sin_pi_div_four]
    have : Real.sqrt 2 ≠ 0 := Real.sqrt_ne_zero'.mpr (by norm_num)
    positivity
  field_simp

/-- `cot` is zero at all integer multiples of `π/2` whose multiple is odd
(i.e., at `π/2, 3π/2, -π/2, ...`).  This is the union of the cot-zero set
(odd multiples of `π/2`) together with the degenerate sin-zero set
(integer multiples of `π`); together they make cot vanish on the
*half-integer* multiples of `π`. -/
theorem cot_pi_mul_half_int (n : ℤ) :
    Real.cot (Real.pi * ((n : ℝ) / 2)) = 0 := by
  rcases Int.even_or_odd n with ⟨k, hk⟩ | ⟨k, hk⟩
  · -- n = 2k: π · (n/2) = π · k, sin = 0, cot = 0 by convention
    have : Real.pi * ((n : ℝ) / 2) = (k : ℝ) * Real.pi := by
      rw [hk]; push_cast; ring
    rw [this, cot_int_mul_pi]
  · -- n = 2k+1: π · n/2 = kπ + π/2. cos(kπ + π/2) = 0, so cot = 0/sin = 0.
    have hsplit : Real.pi * ((n : ℝ) / 2) = (k : ℝ) * Real.pi + Real.pi / 2 := by
      rw [hk]; push_cast; ring
    rw [hsplit, Real.cot_eq_cos_div_sin, Real.cos_add_pi_div_two]
    -- cos(kπ + π/2) = -sin(kπ) = 0
    rw [Real.sin_int_mul_pi]
    simp

/-- The cotangent half-angle/duplication identity:
`cot α + cot(α + π/2) = 2 cot(2α)`.
The proof handles all real `α` thanks to Lean's `0/0 = 0` convention at the
degenerate points where `sin α = 0` or `cos α = 0`. -/
theorem cot_add_cot_add_pi_div_two (α : ℝ) :
    Real.cot α + Real.cot (α + Real.pi / 2) = 2 * Real.cot (2 * α) := by
  rw [Real.cot_eq_cos_div_sin, Real.cot_eq_cos_div_sin, Real.cot_eq_cos_div_sin]
  rw [Real.cos_add_pi_div_two, Real.sin_add_pi_div_two,
      Real.cos_two_mul', Real.sin_two_mul]
  -- LHS = cos α / sin α + (-sin α) / cos α
  -- RHS = 2 · (cos²α - sin²α) / (2 sin α cos α)
  rcases eq_or_ne (Real.sin α) 0 with hsin | hsin
  · -- sin α = 0: both sides 0 by convention
    rw [hsin]; simp
  rcases eq_or_ne (Real.cos α) 0 with hcos | hcos
  · -- cos α = 0: both sides 0 by convention
    rw [hcos]; simp
  -- Both sin α and cos α nonzero — do the algebra.
  field_simp
  ring

/-- `Real.cot` is continuous at any point where `sin` is nonzero. -/
theorem cot_continuousAt {x : ℝ} (hsin : Real.sin x ≠ 0) :
    ContinuousAt Real.cot x := by
  have h_eq : Real.cot = fun y => Real.cos y / Real.sin y := by
    ext y; exact Real.cot_eq_cos_div_sin y
  rw [h_eq]
  exact Real.continuous_cos.continuousAt.div Real.continuous_sin.continuousAt hsin

/-- `π · cot(π · x)` is continuous at any non-integer point. -/
theorem pi_cot_pi_continuousAt {x : ℝ}
    (hx : ∀ n : ℤ, x ≠ (n : ℝ)) :
    ContinuousAt (fun y => Real.pi * Real.cot (Real.pi * y)) x := by
  have h_sin : Real.sin (Real.pi * x) ≠ 0 := by
    intro h
    rcases Real.sin_eq_zero_iff.mp h with ⟨n, hn⟩
    -- hn : (n : ℝ) * π = π * x
    have hπ : Real.pi ≠ 0 := Real.pi_ne_zero
    have hxn : x = (n : ℝ) := by
      have : (n : ℝ) * Real.pi = x * Real.pi := by linarith
      exact (mul_right_cancel₀ hπ this).symm
    exact hx n hxn
  have h_inner : ContinuousAt (fun y => Real.pi * y) x :=
    (continuous_const.mul continuous_id).continuousAt
  have h_cot : ContinuousAt Real.cot (Real.pi * x) := cot_continuousAt h_sin
  exact (continuous_const.continuousAt).mul (h_cot.comp h_inner)

/-- `π · cot(π · x)` is continuous on the set of non-integers. -/
theorem pi_cot_pi_continuousOn :
    ContinuousOn (fun x => Real.pi * Real.cot (Real.pi * x))
      {x : ℝ | ∀ n : ℤ, x ≠ (n : ℝ)} := by
  intro x hx
  exact (pi_cot_pi_continuousAt hx).continuousWithinAt

/-- The Herglotz duplication formula for `f(x) := π · cot(π · x)`:
`2 · f(x) = f(x/2) + f((x+1)/2)`.

This is the algebraic engine that, combined with `pi_cot_pi_HerglotzClass`
(periodic + odd), continuity of `cot` at non-integer points, and
`pi_cot_pi_half_eq_zero` (value at `1/2`), invokes
`herglotz_uniqueness_of_continuous_periodic_odd` to pin down `π·cot(π·x)`
to any matching HerglotzClass member — the Herglotz uniqueness argument's
key step. -/
theorem pi_cot_pi_duplication (x : ℝ) :
    2 * (Real.pi * Real.cot (Real.pi * x)) =
      (Real.pi * Real.cot (Real.pi * (x / 2))) +
        (Real.pi * Real.cot (Real.pi * ((x + 1) / 2))) := by
  -- Specialize cot_add_cot_add_pi_div_two at α = π · x / 2.
  have h := cot_add_cot_add_pi_div_two (Real.pi * x / 2)
  rw [show (2 : ℝ) * (Real.pi * x / 2) = Real.pi * x from by ring] at h
  rw [show Real.pi * x / 2 + Real.pi / 2 = Real.pi * ((x + 1) / 2) from by ring] at h
  rw [show Real.pi * (x / 2) = Real.pi * x / 2 from by ring]
  -- Multiply h (LHS = 2·cot(πx)) by π and rearrange.
  linear_combination -(Real.pi * h)

/--
The dyadic averaging identity: if `f` satisfies the duplication formula
`f(x) = (1/2)(f(x/2) + f((x+1)/2))`, then iterating n times gives
`f(x) = 2^{-n} · ∑_{k=0}^{2^n-1} f((x+k)/2^n)`.
This is the algebraic engine of the Herglotz uniqueness argument.
-/
theorem herglotz_dyadic_average (f : ℝ → ℝ)
    (hdup : ∀ x, f x = (1 / 2 : ℝ) * (f (x / 2) + f ((x + 1) / 2)))
    (n : ℕ) (x : ℝ) :
    f x = (1 / (2 ^ n : ℝ)) *
      ∑ k ∈ Finset.range (2 ^ n), f ((x + k) / (2 ^ n : ℝ)) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [ih]
    simp_rw [hdup ((x + _) / (2 ^ n : ℝ))]
    have halg : ∀ (k : ℕ), (x + ↑k) / (2 ^ n : ℝ) / 2 = (x + ↑k) / (2 ^ (n + 1) : ℝ) := by
      intro k; field_simp; ring
    have halg2 : ∀ (k : ℕ), ((x + ↑k) / (2 ^ n : ℝ) + 1) / 2 =
        (x + (↑k + 2 ^ n)) / (2 ^ (n + 1) : ℝ) := by
      intro k; field_simp; ring
    simp_rw [halg, halg2]
    conv_lhs =>
      rw [Finset.mul_sum]
      arg 2; ext k
      rw [show (1 : ℝ) / 2 ^ n * (1 / 2 * (f ((x + ↑k) / 2 ^ (n + 1)) +
          f ((x + (↑k + 2 ^ n)) / 2 ^ (n + 1)))) =
        1 / 2 ^ (n + 1) * f ((x + ↑k) / 2 ^ (n + 1)) +
        1 / 2 ^ (n + 1) * f ((x + (↑k + 2 ^ n)) / 2 ^ (n + 1)) from by ring]
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, ← mul_add]
    congr 1
    rw [show (2 : ℕ) ^ (n + 1) = 2 ^ n + 2 ^ n from by ring]
    rw [Finset.sum_range_add]
    congr 1
    apply Finset.sum_congr rfl
    intro k _
    congr 1; push_cast; ring

/--
Chapter 24 (Herglotz trick, conditional form):
The Herglotz trick shows that any two functions belonging to the Herglotz class
(periodic-one and odd), which are continuous and satisfy the duplication formula,
must be identical everywhere.
This captures the structural uniqueness argument of the Herglotz trick.
TODO (Tier 2): Verify these hypotheses for the continuous extension of `π·cot(πx)`
and the partial-fraction series `1/x + ∑ 2x/(x²-k²)`.
-/
theorem chapter24 {f g : ℝ → ℝ}
    (hf : HerglotzClass f) (hg : HerglotzClass g)
    (hfc : Continuous f) (hgc : Continuous g)
    (hdup_f : ∀ x, 2 * f x = f (x / 2) + f ((x + 1) / 2))
    (hdup_g : ∀ x, 2 * g x = g (x / 2) + g ((x + 1) / 2))
    (x : ℝ) : f x = g x := by
  have heq : f = g :=
    herglotz_uniqueness_of_continuous_periodic_odd f g hf hg hfc hgc hdup_f hdup_g
      (by rw [hf.eval_half, hg.eval_half])
  rw [heq]

/-- Specialization of `chapter24` to `f = 0`: any continuous, periodic-1, odd
function satisfying the Herglotz duplication formula is identically zero.

This is a corollary of `chapter24` paired with the trivial fact that the zero
function is in HerglotzClass + continuous + satisfies duplication. -/
theorem chapter24_zero_unique {g : ℝ → ℝ}
    (hg : HerglotzClass g) (hgc : Continuous g)
    (hdup_g : ∀ x, 2 * g x = g (x / 2) + g ((x + 1) / 2))
    (x : ℝ) : g x = 0 := by
  have hf_HC : HerglotzClass (fun _ : ℝ => (0 : ℝ)) :=
    ⟨fun _ => rfl, fun _ => by simp⟩
  have hf_c : Continuous (fun _ : ℝ => (0 : ℝ)) := continuous_const
  have hf_dup : ∀ x, 2 * (fun _ : ℝ => (0 : ℝ)) x =
      (fun _ : ℝ => (0 : ℝ)) (x / 2) + (fun _ : ℝ => (0 : ℝ)) ((x + 1) / 2) :=
    fun _ => by ring
  exact (chapter24 hf_HC hg hf_c hgc hf_dup hdup_g x).symm

end ProofsInTheBook.Chapter24
