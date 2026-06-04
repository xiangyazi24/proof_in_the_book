import Mathlib
import ProofsInTheBook.Chapter22

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

/-- **The row-linear product is real-stable** (the base of the Gurvits capacity iteration): for a
nonnegative matrix with strictly positive row sums (e.g. doubly stochastic), `∏ᵢ ∑ⱼ Aᵢⱼ Xⱼ` is
real-stable. -/
lemma rowLinearMvPolynomial_realStable {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (hA : ∀ i j, 0 ≤ A i j) (hrow : ∀ i, 0 < ∑ j, A i j) :
    RealStable (ProofsInTheBook.Chapter22.rowLinearMvPolynomial A) := by
  rw [ProofsInTheBook.Chapter22.rowLinearMvPolynomial]
  apply RealStable.prod
  intro i _
  exact linearForm_stable (A i) (fun j => hA i j) (hrow i)

/-!
### Univariate real-rootedness and its derivative closure (the univariate Lieb–Sokal heart)

A univariate real polynomial is real-rooted iff it splits over ℝ — equivalently its root multiset
(with multiplicity) has cardinality equal to its degree. The derivative of a real-rooted polynomial
is again real-rooted (Rolle's theorem / interlacing). This is the one-variable case of the stability
closure; the full multivariate Lieb–Sokal lemma (`∂/∂xₘ` preserves real-stability) lifts it via the
Hurwitz theorem and remains the genuine remaining analytic input for the Gurvits reduction.
-/

open Polynomial in
/-- A univariate real polynomial is real-rooted: all roots real (splits over ℝ), i.e. the root
multiset cardinality equals the degree. -/
def RealRooted (p : ℝ[X]) : Prop := Multiset.card p.roots = p.natDegree

open Polynomial in
/-- **A real polynomial with no root in the open upper half-plane is real-rooted**
(conjugate-pairing: a non-real root would have a conjugate in the upper half-plane). This is the
bridge from univariate real-stability to real-rootedness, used in the Lieb–Sokal lifting. -/
lemma realRooted_of_forall_uhp_ne_zero (q : ℝ[X])
    (h : ∀ w : ℂ, 0 < w.im → Polynomial.aeval w q ≠ 0) : RealRooted q := by
  rcases eq_or_ne q 0 with rfl | hq0
  · simp [RealRooted]
  rw [RealRooted, ← Polynomial.splits_iff_card_roots]
  apply Polynomial.Splits.of_splits_map_of_injective (i := algebraMap ℝ ℂ)
    (algebraMap ℝ ℂ).injective (IsAlgClosed.splits _)
  intro a ha
  have haroot : Polynomial.aeval a q = 0 := by
    have h2 := (Polynomial.mem_roots'.mp ha).2
    rwa [Polynomial.IsRoot, Polynomial.eval_map, ← Polynomial.aeval_def] at h2
  have him : a.im = 0 := by
    by_contra hne
    rcases lt_or_gt_of_ne hne with hneg | hpos
    · have hconj : Polynomial.aeval ((starRingEnd ℂ) a) q = 0 := by
        rw [Polynomial.aeval_conj, haroot, map_zero]
      have hconjim : 0 < ((starRingEnd ℂ) a).im := by
        rw [Complex.conj_im]; linarith
      exact h _ hconjim hconj
    · exact h a hpos haroot
  refine ⟨a.re, ?_⟩
  apply Complex.ext
  · simp
  · simp [him]

open Polynomial in
/-- **The derivative of a real-rooted polynomial is real-rooted** (Rolle interlacing). -/
lemma RealRooted.derivative {p : ℝ[X]} (hp : RealRooted p) :
    RealRooted (Polynomial.derivative p) := by
  unfold RealRooted at hp ⊢
  have h1 : Multiset.card p.roots ≤ Multiset.card (Polynomial.derivative p).roots + 1 :=
    Polynomial.card_roots_le_derivative p
  have h2 : Multiset.card (Polynomial.derivative p).roots ≤ (Polynomial.derivative p).natDegree :=
    Polynomial.card_roots' _
  have h3 : (Polynomial.derivative p).natDegree ≤ p.natDegree - 1 :=
    Polynomial.natDegree_derivative_le p
  omega

end ProofsInTheBook.Chapter22Stable
