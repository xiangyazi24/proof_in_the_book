import Mathlib

/-!
# Real-stable polynomials (toward Chapter 22, Gurvits capacity)

A real multivariate polynomial is **real-stable** if it has no zero with all variables in the
open upper half-plane. This is the polynomial class underlying Gurvits's capacity proof. Here we
build the definition and the closure properties that are elementary (product closure, stability of
nonnegative linear forms — hence of the row-linear product `∏ rows`). The hard remaining closure
(`∂/∂xₘ` preserves real-stability — the Lieb–Sokal lemma) is isolated as `DerivPreservesStable`.
-/

namespace ProofsInTheBook.Chapter22Stable

open MvPolynomial

/-- A real multivariate polynomial is real-stable if it is nonzero whenever every variable lies
in the open upper half-plane. -/
def RealStable {m : ℕ} (p : MvPolynomial (Fin m) ℝ) : Prop :=
  ∀ z : Fin m → ℂ, (∀ i, 0 < (z i).im) →
    MvPolynomial.eval z (p.map (algebraMap ℝ ℂ)) ≠ 0

/-- The product of real-stable polynomials is real-stable. -/
lemma RealStable.mul {m : ℕ} {p q : MvPolynomial (Fin m) ℝ}
    (hp : RealStable p) (hq : RealStable q) : RealStable (p * q) := by
  intro z hz
  rw [map_mul, map_mul]
  exact mul_ne_zero (hp z hz) (hq z hz)

/-- A nonempty finite product of real-stable polynomials is real-stable. -/
lemma RealStable.prod {m : ℕ} {ι : Type*} (s : Finset ι)
    {f : ι → MvPolynomial (Fin m) ℝ} (hf : ∀ i ∈ s, RealStable (f i)) :
    RealStable (∏ i ∈ s, f i) := by
  intro z hz
  rw [map_prod, map_prod]
  exact Finset.prod_ne_zero_iff.mpr (fun i hi => hf i hi z hz)

/-- A nonnegative linear form `∑ⱼ Cⱼ Xⱼ` with positive total weight is real-stable: its value at
any upper-half-plane point has strictly positive imaginary part. -/
lemma linearForm_stable {m : ℕ} (C : Fin m → ℝ) (hC : ∀ j, 0 ≤ C j)
    (hpos : 0 < ∑ j, C j) :
    RealStable (∑ j, MvPolynomial.C (C j) * (X j : MvPolynomial (Fin m) ℝ)) := by
  intro z hz
  have hval : MvPolynomial.eval z
      ((∑ j, MvPolynomial.C (C j) * (X j : MvPolynomial (Fin m) ℝ)).map (algebraMap ℝ ℂ))
      = ∑ j, (C j : ℂ) * z j := by
    rw [map_sum, map_sum]
    apply Finset.sum_congr rfl
    intro j _
    rw [map_mul, map_mul, MvPolynomial.map_C, MvPolynomial.map_X, eval_C, eval_X]
    simp
  rw [hval]
  have him : (∑ j, (C j : ℂ) * z j).im = ∑ j, C j * (z j).im := by
    rw [Complex.im_sum]
    apply Finset.sum_congr rfl
    intro j _
    simp [Complex.mul_im]
  have hExists : ∃ j, 0 < C j := by
    by_contra h
    push_neg at h
    have : ∑ j, C j ≤ 0 := Finset.sum_nonpos (fun j _ => h j)
    linarith
  obtain ⟨j0, hj0⟩ := hExists
  have hpos' : 0 < (∑ j, (C j : ℂ) * z j).im := by
    rw [him]
    apply Finset.sum_pos'
    · intro j _; exact mul_nonneg (hC j) (le_of_lt (hz j))
    · exact ⟨j0, Finset.mem_univ j0, mul_pos hj0 (hz j0)⟩
  intro hz0
  rw [hz0] at hpos'
  simp at hpos'

/-
The remaining hard stability closure for the Gurvits reduction is the Lieb–Sokal lemma:
`∂/∂xₘ` (followed by setting `xₘ = 0`) preserves real-stability. That is the genuine analytic
input still to be formalized; it is NOT stated as a degenerate placeholder here.
-/

end ProofsInTheBook.Chapter22Stable
