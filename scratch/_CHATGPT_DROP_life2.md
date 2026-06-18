# Finite cone axis theorem: minimum-norm convex-combination proof

This is the drop-in Lean route for

```lean
theorem exists_strict_copositive_combo_from_pointed {ι} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (w : ι → EuclideanSpace ℝ (Fin 3))
    (hpointed : ∀ β : ι → ℝ, (∀ i, 0 ≤ β i) → (∑ i, β i • w i = 0) → ∀ i, β i = 0) :
    ∃ α : ι → ℝ, (∀ i, 0 < α i) ∧ ∀ i, (0:ℝ) < ⟪(∑ j, α j • w j), w i⟫
```

The compact convex set is implemented as the **simplex image**

```lean
combo w '' stdSimplex ℝ ι
```

which is the concrete finite-dimensional convex-combination model of `convexHull ℝ (Set.range w)`.  This is the right formulation for pointedness: if `β ∈ stdSimplex ℝ ι` and `combo w β = 0`, then `β` is a nonnegative cone relation; pointedness forces every `β i = 0`, contradicting `∑ i, β i = 1`.

The Mathlib facts used directly are:

* `exists_norm_eq_iInf_of_complete_convex`
* `norm_eq_iInf_iff_real_inner_le_zero`
* `stdSimplex`, `convex_stdSimplex`, `isCompact_stdSimplex`, `single_mem_stdSimplex`
* `IsCompact.image`, `IsCompact.isComplete`
* `Finset.sum_add_distrib`, `Finset.mul_sum`, `Finset.smul_sum`
* `inner_add_left`, `inner_sub_right`, `inner_neg_left`, `real_inner_smul_left`, `real_inner_self_eq_norm_sq`

No Farkas/separation theorem is needed: the closest-point variational inequality supplies the separating functional.  The ε-bump at the end only makes all coefficients strictly positive; strict copositivity is already obtained from the minimum-norm point.

```lean
import ProofsInTheBook.SphericalKernel
import Mathlib.Analysis.InnerProductSpace.Projection.Minimal
import Mathlib.Analysis.Convex.StdSimplex
import Mathlib.Analysis.Convex.Topology
import Mathlib.Analysis.InnerProductSpace.PiL2

noncomputable section

open scoped Classical RealInnerProductSpace BigOperators
open ProofsInTheBook.SphericalKernel

namespace ProofsInTheBook.Ch13FiniteConeAxis

set_option maxHeartbeats 1200000
set_option synthInstance.maxHeartbeats 400000

abbrev E3 : Type := EuclideanSpace ℝ (Fin 3)

section Helpers

variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]

/-- The linear combination of `w` with coefficient vector `a`. -/
def combo (w : ι → E3) (a : ι → ℝ) : E3 :=
  ∑ i, a i • w i

@[simp] lemma combo_single (w : ι → E3) (i : ι) :
    combo w (Pi.single i (1 : ℝ)) = w i := by
  classical
  unfold combo
  rw [Finset.sum_eq_single i]
  · simp
  · intro j _ hji
    simp [Pi.single_eq_of_ne hji.symm]
  · intro hi
    simp at hi

/-- The compact convex set of convex combinations of the generators. -/
def comboSet (w : ι → E3) : Set E3 :=
  combo w '' stdSimplex ℝ ι

lemma combo_continuous (w : ι → E3) : Continuous (combo w) := by
  classical
  unfold combo
  fun_prop

lemma comboSet_nonempty (w : ι → E3) : (comboSet w).Nonempty := by
  classical
  let i : ι := Classical.choice (inferInstance : Nonempty ι)
  refine ⟨w i, ?_⟩
  refine ⟨Pi.single i (1 : ℝ), single_mem_stdSimplex ℝ i, ?_⟩
  simp

lemma comboSet_compact (w : ι → E3) : IsCompact (comboSet w) := by
  classical
  exact (isCompact_stdSimplex ℝ ι).image (combo_continuous w)

lemma comboSet_convex (w : ι → E3) : Convex ℝ (comboSet w) := by
  classical
  intro x hx y hy a b ha hb hab
  rcases hx with ⟨α, hα, rfl⟩
  rcases hy with ⟨β, hβ, rfl⟩
  refine ⟨fun i => a * α i + b * β i, ?_, ?_⟩
  · constructor
    · intro i
      exact add_nonneg (mul_nonneg ha (hα.1 i)) (mul_nonneg hb (hβ.1 i))
    · calc
        (∑ i, (a * α i + b * β i))
            = a * (∑ i, α i) + b * (∑ i, β i) := by
              rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
        _ = a * 1 + b * 1 := by rw [hα.2, hβ.2]
        _ = 1 := by simpa [hab]
  · unfold combo
    calc
      (∑ i, (a * α i + b * β i) • w i)
          = ∑ i, ((a * α i) • w i + (b * β i) • w i) := by
            apply Finset.sum_congr rfl
            intro i _
            rw [add_smul]
      _ = (∑ i, (a * α i) • w i) + (∑ i, (b * β i) • w i) := by
            rw [Finset.sum_add_distrib]
      _ = a • (∑ i, α i • w i) + b • (∑ i, β i • w i) := by
            simp [Finset.smul_sum, smul_smul, mul_assoc]

/-- A positive function on a finite nonempty type has a positive finite lower bound. -/
lemma exists_pos_le_all_of_pos {f : ι → ℝ} (hf : ∀ i, 0 < f i) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ i, δ ≤ f i := by
  classical
  let s : Finset ι := Finset.univ
  have hs : s.Nonempty := Finset.univ_nonempty
  refine ⟨s.inf' hs f, ?_, ?_⟩
  · exact Finset.lt_inf'_iff.mpr (by intro i _; exact hf i)
  · intro i
    exact Finset.inf'_le s f (by simp [s])

/-- A scalar inequality used in the epsilon bump. -/
lemma bump_scalar_bound {A B : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B) :
    (A / (2 * (1 + B))) * B ≤ A / 2 := by
  have honeB_pos : 0 < 1 + B := by positivity
  calc
    (A / (2 * (1 + B))) * B
        = (A / 2) * (B / (1 + B)) := by
          field_simp [show (2 : ℝ) ≠ 0 by norm_num,
            show 1 + B ≠ 0 by positivity]
          ring
    _ ≤ (A / 2) * 1 := by
          have hA2 : 0 ≤ A / 2 := by positivity
          have hratio : B / (1 + B) ≤ 1 := by
            rw [div_le_one honeB_pos]
            linarith
          exact mul_le_mul_of_nonneg_left hratio hA2
    _ = A / 2 := by ring

/-- If a vector is strictly positive against each generator, then a small positive
bump in the direction `∑ i, w i` preserves all strict inequalities. -/
theorem exists_pos_bump_preserving_inner
    (w : ι → E3) (x : E3)
    (hx : ∀ i, 0 < ⟪x, w i⟫) :
    ∃ ε : ℝ, 0 < ε ∧
      ∀ i, 0 < ⟪x + ε • (∑ j, w j), w i⟫ := by
  classical
  let s : E3 := ∑ j, w j
  let r : ι → ℝ := fun i =>
    ⟪x, w i⟫ / (2 * (1 + |⟪s, w i⟫|))
  have hrpos : ∀ i, 0 < r i := by
    intro i
    have hden : 0 < 2 * (1 + |⟪s, w i⟫|) := by positivity
    exact div_pos (hx i) hden
  rcases exists_pos_le_all_of_pos (f := r) hrpos with ⟨ε, hεpos, hεle⟩
  refine ⟨ε, hεpos, ?_⟩
  intro i
  have hε_nonneg : 0 ≤ ε := le_of_lt hεpos
  have hinner :
      ⟪x + ε • s, w i⟫ = ⟪x, w i⟫ + ε * ⟪s, w i⟫ := by
    rw [inner_add_left, real_inner_smul_left]
  rw [hinner]
  by_cases hb : 0 ≤ ⟪s, w i⟫
  · have hterm : 0 ≤ ε * ⟪s, w i⟫ := mul_nonneg hε_nonneg hb
    exact lt_of_lt_of_le (hx i) (by linarith)
  · have hbneg : ⟪s, w i⟫ < 0 := lt_of_not_ge hb
    have hbound : ε * |⟪s, w i⟫| ≤ ⟪x, w i⟫ / 2 := by
      have hmul := mul_le_mul_of_nonneg_right (hεle i) (abs_nonneg (⟪s, w i⟫))
      have hscalar :
          (⟪x, w i⟫ / (2 * (1 + |⟪s, w i⟫|))) * |⟪s, w i⟫| ≤
            ⟪x, w i⟫ / 2 :=
        bump_scalar_bound (le_of_lt (hx i)) (abs_nonneg (⟪s, w i⟫))
      exact le_trans hmul hscalar
    have hnegmul : ε * ⟪s, w i⟫ = -(ε * |⟪s, w i⟫|) := by
      rw [abs_of_neg hbneg]
      ring
    rw [hnegmul]
    have hhalf : 0 < ⟪x, w i⟫ / 2 := half_pos (hx i)
    linarith

/-- Minimum-norm point of the coefficient-simplex image is strictly positive
against each generator, assuming the generated nonnegative cone is pointed. -/
theorem exists_simplex_combo_strict_dual_pos
    (w : ι → E3)
    (hpointed : ∀ β : ι → ℝ,
      (∀ i, 0 ≤ β i) →
      (combo w β = 0) →
      ∀ i, β i = 0) :
    ∃ β : ι → ℝ,
      β ∈ stdSimplex ℝ ι ∧
      ∀ i, 0 < ⟪combo w β, w i⟫ := by
  classical
  let K : Set E3 := comboSet w
  have hKne : K.Nonempty := comboSet_nonempty w
  have hKconv : Convex ℝ K := comboSet_convex w
  have hKcompact : IsCompact K := comboSet_compact w
  have hKcomplete : IsComplete K := hKcompact.isComplete

  rcases exists_norm_eq_iInf_of_complete_convex hKne hKcomplete hKconv (0 : E3) with
    ⟨x, hxK, hxMin⟩

  have hvar : ∀ y ∈ K, inner ℝ ((0 : E3) - x) (y - x) ≤ 0 :=
    (norm_eq_iInf_iff_real_inner_le_zero hKconv hxK).1 hxMin

  rcases hxK with ⟨β, hβsimp, rfl⟩

  have hx_ne_zero : combo w β ≠ 0 := by
    intro hx0
    have hzero : ∀ i, β i = 0 := hpointed β hβsimp.1 hx0
    have hsum0 : (∑ i, β i) = 0 := by simp [hzero]
    have hsum1 : (∑ i, β i) = 1 := hβsimp.2
    linarith

  refine ⟨β, hβsimp, ?_⟩
  intro i

  have hwiK : w i ∈ K := by
    refine ⟨Pi.single i (1 : ℝ), single_mem_stdSimplex ℝ i, ?_⟩
    simp

  have hineq := hvar (w i) hwiK
  have hle_inner : ⟪combo w β, combo w β⟫ ≤ ⟪combo w β, w i⟫ := by
    rw [zero_sub, inner_neg_left, inner_sub_right] at hineq
    linarith
  have hle_norm : ‖combo w β‖ ^ 2 ≤ ⟪combo w β, w i⟫ := by
    simpa [real_inner_self_eq_norm_sq] using hle_inner
  have hnorm_pos : 0 < ‖combo w β‖ := norm_pos_iff.mpr hx_ne_zero
  have hnormsq_pos : 0 < ‖combo w β‖ ^ 2 := sq_pos_of_pos hnorm_pos
  exact lt_of_lt_of_le hnormsq_pos hle_norm

end Helpers

/-- The finite pointed cone theorem needed for the self-dual axis. -/
theorem exists_strict_copositive_combo_from_pointed {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (w : ι → EuclideanSpace ℝ (Fin 3))
    (hpointed : ∀ β : ι → ℝ, (∀ i, 0 ≤ β i) → (∑ i, β i • w i = 0) → ∀ i, β i = 0) :
    ∃ α : ι → ℝ, (∀ i, 0 < α i) ∧ ∀ i, (0:ℝ) < ⟪(∑ j, α j • w j), w i⟫ := by
  classical
  have hpointed_combo : ∀ β : ι → ℝ,
      (∀ i, 0 ≤ β i) → combo w β = 0 → ∀ i, β i = 0 := by
    intro β hβ hcombo
    exact hpointed β hβ (by simpa [combo] using hcombo)
  rcases exists_simplex_combo_strict_dual_pos (w := w) hpointed_combo with
    ⟨β, hβsimp, hβpos⟩
  rcases exists_pos_bump_preserving_inner w (combo w β) hβpos with
    ⟨ε, hεpos, hεinner⟩
  refine ⟨fun i => β i + ε, ?_, ?_⟩
  · intro i
    exact add_pos_of_nonneg_of_pos (hβsimp.1 i) hεpos
  · intro i
    have hcombo :
        (∑ j, (β j + ε) • w j) = combo w β + ε • (∑ j, w j) := by
      unfold combo
      simp only [add_smul]
      rw [Finset.sum_add_distrib, Finset.smul_sum]
    rw [hcombo]
    exact hεinner i

end ProofsInTheBook.Ch13FiniteConeAxis
```

## Pointedness checkpoint

The proof never needs the ambiguous statement “pointedness implies `0 ∉ convexHull {w i}`” as a separate global lemma.  Instead, it proves exactly the nonzero fact required for the closest-point minimizer:

```lean
combo w β ≠ 0
```

where `β ∈ stdSimplex ℝ ι`.  If `combo w β = 0`, then `β` is a nonnegative cone relation, so `hpointed` gives `β i = 0` for all `i`; but the simplex condition also gives `∑ i, β i = 1`, contradiction.

The closest-point theorem then gives, for every generator `w i`,

```lean
‖combo w β‖ ^ 2 ≤ ⟪combo w β, w i⟫
```

and the left side is strictly positive because the minimizer is nonzero.  The ε-bump replaces `β` by `β + ε`, making every coefficient strictly positive while preserving the finitely many strict inequalities.