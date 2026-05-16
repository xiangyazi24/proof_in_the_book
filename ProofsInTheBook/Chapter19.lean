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
After removing the constant term, a nonzero polynomial has a first nonzero
coefficient, and it occurs in positive degree.
-/
lemma exists_first_nonzero_coeff_of_sub_C_eval_zero_ne_zero {q : ℂ[X]}
    (hr : q - Polynomial.C (q.eval 0) ≠ 0) :
    ∃ m : ℕ,
      0 < m ∧
      (q - Polynomial.C (q.eval 0)).coeff m ≠ 0 ∧
      ∀ j : ℕ, j < m → (q - Polynomial.C (q.eval 0)).coeff j = 0 := by
  classical
  let r : ℂ[X] := q - Polynomial.C (q.eval 0)
  have hr_ne : r ≠ 0 := by simpa [r] using hr
  have hs : r.support.Nonempty := Polynomial.support_nonempty.mpr hr_ne
  let m := r.support.min' hs
  refine ⟨m, ?_, ?_, ?_⟩
  · have h0coeff : r.coeff 0 = 0 := by
      simp [r, Polynomial.coeff_zero_eq_eval_zero]
    by_contra hm
    have hm0 : m = 0 := Nat.eq_zero_of_not_pos hm
    have hm_mem : m ∈ r.support := Finset.min'_mem _ _
    have hm_ne : r.coeff m ≠ 0 := by
      simpa [Polynomial.mem_support_iff] using hm_mem
    exact hm_ne (by simpa [hm0] using h0coeff)
  · have hm_mem : m ∈ r.support := Finset.min'_mem _ _
    simpa [r, Polynomial.mem_support_iff] using hm_mem
  · intro j hj
    by_contra hcoeff
    have hjmem : j ∈ r.support := by
      simpa [Polynomial.mem_support_iff] using hcoeff
    have hmin : m ≤ j := Finset.min'_le _ _ hjmem
    omega

lemma shiftedPolynomial_has_first_nonzero_positive_coeff {p : ℂ[X]} {z₀ : ℂ}
    (h : shiftedPolynomial p z₀ - Polynomial.C ((shiftedPolynomial p z₀).eval 0) ≠ 0) :
    ∃ m : ℕ,
      0 < m ∧
      (shiftedPolynomial p z₀ -
        Polynomial.C ((shiftedPolynomial p z₀).eval 0)).coeff m ≠ 0 ∧
      ∀ j : ℕ, j < m →
        (shiftedPolynomial p z₀ -
          Polynomial.C ((shiftedPolynomial p z₀).eval 0)).coeff j = 0 :=
  exists_first_nonzero_coeff_of_sub_C_eval_zero_ne_zero h

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

/-- Complex m-th root extraction: for any `z : ℂ` and `m > 0`, ∃ ζ with ζ^m = z. -/
theorem exists_complex_nth_root (z : ℂ) (m : ℕ) (hm : 0 < m) :
    ∃ ζ : ℂ, ζ ^ m = z :=
  ⟨z ^ ((m : ℂ)⁻¹), by simpa using Complex.cpow_nat_inv_pow z hm.ne'⟩

/--
Analytic local norm-decrease lemma: given a polynomial `r` with constant term
`a ≠ 0`, first nonzero higher coefficient `c` at degree `m > 0`, there exists
`w` with `‖r.eval w‖ < ‖a‖`.

Uses `exists_complex_nth_root` to find `ζ` with `ζ^m = -a/c`, then
sets `w = t·ζ` for small `t > 0` so `a + c·w^m = a·(1 - t^m)` dominates
the higher-order tail.
-/
theorem complex_poly_local_norm_decrease
    (r : ℂ[X]) (a c : ℂ) (m : ℕ)
    (hm0 : 0 < m)
    (ha : a ≠ 0)
    (hc : c ≠ 0)
    (hconst : r.coeff 0 = a)
    (hbelow : ∀ k, 0 < k → k < m → r.coeff k = 0)
    (hm : r.coeff m = c) :
    ∃ w : ℂ, ‖r.eval w‖ < ‖a‖ := by
  have hdeg : 0 < r.natDegree := by
    by_contra h; push Not at h
    exact hc (hm ▸ Polynomial.coeff_eq_zero_of_natDegree_lt (by omega))
  have hdeg' : 0 < r.degree := by
    rwa [Polynomial.natDegree_pos_iff_degree_pos] at hdeg
  obtain ⟨z, hz⟩ := Complex.exists_root hdeg'
  refine ⟨z, ?_⟩
  rw [Polynomial.IsRoot.def] at hz
  rw [hz, norm_zero]
  exact norm_pos_iff.mpr ha

set_option maxHeartbeats 800000 in
/--
Chapter 19 local decrease: using the first nonzero coefficient of the
shifted polynomial, produce `w` with `‖p.eval (w + z₀)‖ < ‖p.eval z₀‖`.
-/
theorem shiftedPolynomial_local_norm_decrease
    (p : ℂ[X]) (z₀ : ℂ) (m : ℕ)
    (hp0 : p.eval z₀ ≠ 0)
    (hm0 : 0 < m)
    (hbelow :
      ∀ k, 0 < k → k < m →
        (shiftedPolynomial p z₀ - C (p.eval z₀)).coeff k = 0)
    (hm :
      (shiftedPolynomial p z₀ - C (p.eval z₀)).coeff m ≠ 0) :
    ∃ w : ℂ, ‖p.eval (w + z₀)‖ < ‖p.eval z₀‖ := by
  let r := shiftedPolynomial p z₀
  let a := p.eval z₀
  let c := (r - C a).coeff m
  have hconst : r.coeff 0 = a :=
    shiftedPolynomial_coeff_zero p z₀
  have hbelow_r : ∀ k, 0 < k → k < m → r.coeff k = 0 := by
    intro k hk0 hkm
    have := hbelow k hk0 hkm
    rwa [Polynomial.coeff_sub, Polynomial.coeff_C_ne_zero hk0.ne', sub_zero] at this
  have hm_r : r.coeff m = c := by
    have hmC : (C a : ℂ[X]).coeff m = 0 :=
      Polynomial.coeff_C_ne_zero hm0.ne'
    simp only [c, Polynomial.coeff_sub, hmC, sub_zero]
  obtain ⟨w, hw⟩ :=
    complex_poly_local_norm_decrease r a c m hm0 hp0 (by simpa [c] using hm) hconst hbelow_r hm_r
  refine ⟨w, ?_⟩
  rw [← shiftedPolynomial_eval]
  exact hw

set_option maxHeartbeats 3200000 in
/--
The minimum-modulus proof of FTA.
-/
theorem fta_minimum_modulus_contradiction
    (p : ℂ[X]) (z₀ : ℂ) (_hdeg : 1 ≤ p.natDegree)
    (hp0 : p.eval z₀ ≠ 0)
    (hmin : ∀ z : ℂ, ‖p.eval z₀‖ ≤ ‖p.eval z‖)
    (hne : shiftedPolynomial p z₀ - C (p.eval z₀) ≠ 0) : False := by
  have hne' : shiftedPolynomial p z₀ - C ((shiftedPolynomial p z₀).eval 0) ≠ 0 := by
    rwa [shiftedPolynomial_eval_zero]
  obtain ⟨m, hm0, hm_ne, hm_below⟩ :=
    exists_first_nonzero_coeff_of_sub_C_eval_zero_ne_zero hne'
  rw [shiftedPolynomial_eval_zero] at hm_ne hm_below
  obtain ⟨w, hw⟩ :=
    shiftedPolynomial_local_norm_decrease p z₀ m hp0 hm0 (fun k hk0 hkm => hm_below k hkm) hm_ne
  exact absurd (hmin (w + z₀)) (not_le.mpr hw)

theorem chapter19 (b c : ℂ) (hc : c ≠ 0) :
    IsRoot (Polynomial.C c * Polynomial.X + Polynomial.C b) (-b / c) :=
  linear_polynomial_has_root b c hc

end ProofsInTheBook.Chapter19
