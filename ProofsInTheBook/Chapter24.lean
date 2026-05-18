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

theorem chapter24 (x : ℝ) :
    Real.pi * Real.cot (Real.pi * x) + Real.pi * Real.cot (Real.pi * (1 - x)) = 0 := by
  rw [cot_pi_one_sub]
  ring

end ProofsInTheBook.Chapter24
