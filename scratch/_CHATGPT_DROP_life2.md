# Finite cone axis theorem: closest-point route and compile boundary

This note responds to the request for a complete Lean proof of

```lean
theorem exists_strict_copositive_combo_from_pointed
    {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (w : ι → EuclideanSpace ℝ (Fin 3))
    (hpointed : ∀ β : ι → ℝ,
      (∀ i, 0 ≤ β i) →
      (∑ i, β i • w i = 0) →
      ∀ i, β i = 0) :
    ∃ α : ι → ℝ,
      (∀ i, 0 < α i) ∧
      ∀ i, (0 : ℝ) < ⟪(∑ j, α j • w j), w i⟫
```

I cannot honestly claim a no-`sorry`, compiling Lean proof here: the session has no Lean executable or checked checkout, and this theorem is API-sensitive.  The closest-point route is mathematically correct and the needed Mathlib lemmas exist, but turning it into a compiling file requires checking exact simp normal forms for `stdSimplex`, `convexHull`, `ContinuousLinearMap`, and `iInf` minimizer statements.  I am therefore recording the exact Mathlib names, the proof obligations, and the Lean target structure rather than fabricating an untested proof.

## 1. Exact Mathlib APIs to use

The closest-point/minimizer APIs are in:

```lean
import Mathlib.Analysis.InnerProductSpace.Projection.Minimal
```

The documented theorem names are:

```lean
exists_norm_eq_iInf_of_complete_convex
norm_eq_iInf_iff_real_inner_le_zero
```

Their relevant shapes are:

```lean
exists_norm_eq_iInf_of_complete_convex
  {K : Set F} (ne : K.Nonempty) (h₁ : IsComplete K) (h₂ : Convex ℝ K) (u : F) :
  ∃ v ∈ K, ‖u - v‖ = ⨅ (w : K), ‖u - (w : F)‖

norm_eq_iInf_iff_real_inner_le_zero
  {K : Set F} (h : Convex ℝ K) {u v : F} (hv : v ∈ K) :
  ‖u - v‖ = ⨅ (w : K), ‖u - (w : F)‖ ↔
    ∀ w ∈ K, inner ℝ (u - v) (w - v) ≤ 0
```

The finite simplex APIs are in:

```lean
import Mathlib.Analysis.Convex.StdSimplex
import Mathlib.Analysis.Convex.Topology
```

The documented names are:

```lean
stdSimplex
convex_stdSimplex
isClosed_stdSimplex
isCompact_stdSimplex
stdSimplex.zero_le
stdSimplex.sum_eq_one
single_mem_stdSimplex
Set.Finite.convexHull_eq_image
Set.Finite.isCompact_convexHull
Set.Finite.isClosed_convexHull
```

For the theorem below, the cleanest route is to avoid extracting from `convexHull` and instead define the compact convex set directly as the image of the standard simplex under the coefficient-combination map.

## 2. Core definitions

```lean
import ProofsInTheBook.SphericalKernel
import Mathlib.Analysis.InnerProductSpace.Projection.Minimal
import Mathlib.Analysis.Convex.StdSimplex
import Mathlib.Analysis.Convex.Topology
import Mathlib.Analysis.Convex.Cone.Dual

noncomputable section
open scoped Classical RealInnerProductSpace BigOperators
open ProofsInTheBook.SphericalKernel

namespace ProofsInTheBook.Ch13FiniteConeAxis

abbrev E3 : Type := EuclideanSpace ℝ (Fin 3)

variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]

/-- The linear combination of `w` with coefficient vector `a`. -/
def combo (w : ι → E3) (a : ι → ℝ) : E3 :=
  ∑ i, a i • w i

/-- The coefficient-combination map as a linear map.  If a local proof has trouble
with `map_add'`/`map_smul'`, define this first as `combo` and use `linear_combination`
for the few algebraic identities instead. -/
noncomputable def comboLinear (w : ι → E3) : (ι → ℝ) →ₗ[ℝ] E3 where
  toFun := combo w
  map_add' := by
    intro a b
    unfold combo
    simp only [Pi.add_apply, add_smul]
    rw [Finset.sum_add_distrib]
  map_smul' := by
    intro c a
    unfold combo
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro i _
    simp [smul_smul, mul_comm, mul_left_comm, mul_assoc]

/-- The compact convex hull image of the coefficient simplex. -/
def comboSet (w : ι → E3) : Set E3 :=
  (comboLinear w) '' stdSimplex ℝ ι

end ProofsInTheBook.Ch13FiniteConeAxis
```

## 3. Closest-point lemma to prove locally

The key local theorem should be this.  It is the exact replacement for Stiemke/Gordan.

```lean
namespace ProofsInTheBook.Ch13FiniteConeAxis

/-- Minimum-norm point of the convex hull of the generators is strictly positive
against every generator, assuming the generated cone is pointed. -/
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
  -- Let `K = comboSet w`.
  let K : Set E3 := comboSet w

  -- Nonempty: choose any simplex vertex.
  have hKne : K.Nonempty := by
    classical
    obtain ⟨i0⟩ := (inferInstance : Nonempty ι)
    refine ⟨combo w (Pi.single i0 1), ?_⟩
    refine ⟨Pi.single i0 1, single_mem_stdSimplex ℝ i0, ?_⟩
    rfl

  -- Convex: image of the convex standard simplex under a linear map.
  have hKconv : Convex ℝ K := by
    -- Expected proof:
    --   exact (convex_stdSimplex ℝ ι).image (comboLinear w)
    -- Depending on the pinned Mathlib, the theorem may be named `Convex.image`.
    exact (convex_stdSimplex ℝ ι).image (comboLinear w)

  -- Compact image of compact simplex, hence complete.
  have hKcompact : IsCompact K := by
    -- Expected proof:
    --   exact (isCompact_stdSimplex ℝ ι).image (comboLinear w).continuous
    exact (isCompact_stdSimplex ℝ ι).image (comboLinear w).continuous

  have hKcomplete : IsComplete K := by
    -- In current Mathlib this is usually available as `hKcompact.isComplete`.
    exact hKcompact.isComplete

  -- Pick the closest point to `0` in `K`.
  rcases exists_norm_eq_iInf_of_complete_convex hKne hKcomplete hKconv (0 : E3) with
    ⟨x, hxK, hxMin⟩

  -- Variational inequality for the closest point.
  have hvar : ∀ y ∈ K, inner ℝ ((0 : E3) - x) (y - x) ≤ 0 :=
    (norm_eq_iInf_iff_real_inner_le_zero hKconv hxK).1 hxMin

  -- Extract simplex coefficients for `x`.
  rcases hxK with ⟨β, hβsimp, rfl⟩

  -- `x ≠ 0`, otherwise pointedness contradicts `∑ β_i = 1`.
  have hx_ne_zero : combo w β ≠ 0 := by
    intro hx0
    have hzero : ∀ i, β i = 0 := hpointed β (fun i => (stdSimplex.zero_le ⟨β, hβsimp⟩ i)) hx0
    have hsum0 : (∑ i, β i) = 0 := by
      simp [hzero]
    have hsum1 : (∑ i, β i) = 1 := stdSimplex.sum_eq_one ⟨β, hβsimp⟩
    linarith

  refine ⟨β, hβsimp, ?_⟩
  intro i

  -- The generator `w i` belongs to `K`, using the `i`-th simplex vertex.
  have hwiK : w i ∈ K := by
    refine ⟨Pi.single i 1, single_mem_stdSimplex ℝ i, ?_⟩
    -- `combo w (Pi.single i 1) = w i`.
    unfold combo comboLinear
    simp

  have hineq := hvar (w i) hwiK
  -- hineq : inner ℝ (0 - combo w β) (w i - combo w β) ≤ 0
  have hle : ‖combo w β‖ ^ 2 ≤ ⟪combo w β, w i⟫ := by
    -- Expand the variational inequality.
    -- This is pure inner-product algebra.
    -- One robust script is:
    --   rw [zero_sub, inner_neg_left, inner_sub_right, neg_nonpos] at hineq
    --   rw [real_inner_self_eq_norm_sq] at hineq
    --   exact hineq
    rw [zero_sub, inner_neg_left, inner_sub_right] at hineq
    have hineq' : 0 ≤ ⟪combo w β, w i⟫ - ⟪combo w β, combo w β⟫ := by
      linarith
    rw [real_inner_self_eq_norm_sq] at hineq'
    linarith
  have hnormsq_pos : 0 < ‖combo w β‖ ^ 2 := by
    exact sq_pos_of_ne_zero (by simpa using hx_ne_zero)
  exact lt_of_lt_of_le hnormsq_pos hle

end ProofsInTheBook.Ch13FiniteConeAxis
```

The proof above is close to compiling, and the named APIs are real Mathlib declarations.  The most likely compile adjustments are:

* `Convex.image` may require the argument order `(convex_stdSimplex ℝ ι).image (comboLinear w)` exactly as written, or a continuous-linear-map coercion.
* `hKcompact.isComplete` may be named through a namespace instance in the pinned revision; if it fails, replace the Hilbert-projection minimizer by compact-continuous minimization over `K`.
* The `single_mem_stdSimplex` simp of `combo w (Pi.single i 1)` may need a helper lemma using `Finset.sum_eq_single`.

## 4. Epsilon bump lemma

This part is finite algebra.  It is less API-sensitive than the closest-point step.

```lean
namespace ProofsInTheBook.Ch13FiniteConeAxis

/-- Finite positive lower bound for a positive function on a finite nonempty type. -/
lemma exists_pos_le_all_of_pos {f : ι → ℝ} (hf : ∀ i, 0 < f i) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ i, δ ≤ f i := by
  classical
  let s : Finset ι := Finset.univ
  have hsne : s.Nonempty := Finset.univ_nonempty
  refine ⟨s.inf' hsne f, ?_, ?_⟩
  · exact Finset.lt_inf'_iff.mpr (by intro i _; exact hf i)
  · intro i
    exact Finset.inf'_le _ _ (by simp [s])

/-- If `x` is strictly positive against every generator, then a small positive
bump in the direction `∑ w_i` preserves all strict inequalities. -/
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
  rcases exists_pos_le_all_of_pos (f := r) hrpos with ⟨δ, hδpos, hδle⟩
  refine ⟨δ / 2, half_pos hδpos, ?_⟩
  intro i
  have hδle_i : δ / 2 ≤ r i := by linarith [hδle i]
  have hnonneg : 0 ≤ δ / 2 := le_of_lt (half_pos hδpos)
  have hinner :
      ⟪x + (δ / 2) • s, w i⟫ = ⟪x, w i⟫ + (δ / 2) * ⟪s, w i⟫ := by
    rw [inner_add_left, real_inner_smul_left]
  rw [hinner]
  by_cases hb : 0 ≤ ⟪s, w i⟫
  · have : 0 ≤ (δ / 2) * ⟪s, w i⟫ := mul_nonneg hnonneg hb
    linarith [hx i]
  · have hbneg : ⟪s, w i⟫ < 0 := lt_of_not_ge hb
    have habs_pos : 0 < |⟪s, w i⟫| := abs_pos.mpr (ne_of_lt hbneg)
    have hbound : (δ / 2) * |⟪s, w i⟫| ≤ ⟪x, w i⟫ / 2 := by
      have hmul := mul_le_mul_of_nonneg_right hδle_i (abs_nonneg _)
      dsimp [r] at hmul
      have hfrac :
          (⟪x, w i⟫ / (2 * (1 + |⟪s, w i⟫|))) * |⟪s, w i⟫| ≤
            ⟪x, w i⟫ / 2 := by
        have hxpos := hx i
        have hdenpos : 0 < 2 * (1 + |⟪s, w i⟫|) := by positivity
        -- Since `|b|/(1+|b|) ≤ 1`.
        have hratio : |⟪s, w i⟫| / (1 + |⟪s, w i⟫|) ≤ 1 := by
          have hden : 0 < 1 + |⟪s, w i⟫| := by positivity
          rw [div_le_one hden]
          linarith [abs_nonneg (⟪s, w i⟫)]
        field_simp [show (2 : ℝ) ≠ 0 by norm_num,
          show 1 + |⟪s, w i⟫| ≠ 0 by positivity]
        nlinarith [mul_nonneg (le_of_lt hxpos) hratio]
      exact le_trans hmul hfrac
    have hrewrite_neg : (δ / 2) * ⟪s, w i⟫ = -((δ / 2) * |⟪s, w i⟫|) := by
      rw [abs_of_neg hbneg]
      ring
    rw [hrewrite_neg]
    have hxhalf : 0 < ⟪x, w i⟫ / 2 := half_pos (hx i)
    linarith

end ProofsInTheBook.Ch13FiniteConeAxis
```

The epsilon proof is also close to compiling.  The highest-risk line is the `field_simp`/`nlinarith` proof of `hfrac`; if it fails, replace it with a separate lemma:

```lean
lemma mul_abs_div_one_add_abs_le_half {A b : ℝ} (hA : 0 ≤ A) :
    (A / (2 * (1 + |b|))) * |b| ≤ A / 2 := by ...
```

## 5. Final theorem assembly

```lean
namespace ProofsInTheBook.Ch13FiniteConeAxis

theorem exists_strict_copositive_combo_from_pointed
    (w : ι → E3)
    (hpointed : ∀ β : ι → ℝ,
      (∀ i, 0 ≤ β i) →
      (∑ i, β i • w i = 0) →
      ∀ i, β i = 0) :
    ∃ α : ι → ℝ,
      (∀ i, 0 < α i) ∧
      ∀ i, (0 : ℝ) < ⟪(∑ j, α j • w j), w i⟫ := by
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
    exact add_pos_of_nonneg_of_pos (stdSimplex.zero_le ⟨β, hβsimp⟩ i) hεpos
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

## 6. What must be checked in Lean

The projection/simplex APIs cited above are real documented Mathlib declarations.  The remaining compile-risk is not mathematical; it is Lean-normal-form work around:

* `Convex.image` for the linear image of `stdSimplex`;
* `IsCompact.isComplete` for passing compactness to completeness;
* simplifying `combo w (Pi.single i 1)`;
* the small `field_simp`/`nlinarith` inequality in the bump lemma.

If this were being committed as a proof file, I would first add and compile these four helper lemmas independently:

```lean
lemma combo_single (w : ι → E3) (i : ι) : combo w (Pi.single i 1) = w i := by ...
lemma comboSet_convex (w : ι → E3) : Convex ℝ (comboSet w) := by ...
lemma comboSet_compact (w : ι → E3) : IsCompact (comboSet w) := by ...
lemma small_bump_bound ... := by ...
```

Then the final theorem is a short assembly.  Without a Lean executable in this session, I cannot truthfully label the code above as compiled, but it is the concrete closest-point proof with the exact Mathlib lemmas that should be used.
