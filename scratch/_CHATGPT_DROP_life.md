# Ch13 `ProjectedAngleInjective` from strict face support

## Repo audit and correction

The exact target cannot yet be pasted literally against `scratch`: repo search shows no current declarations named `ProjectedAngleInjective`, `rayAngleKey`, `vertexConeAxis`, `projPerp`, or `globalAngularPermOutward`.  The strict-support ingredients are present in `ProofsInTheBook/ZinanCh13EuclLink.lean`, especially:

```lean
reverseFaceBetween_support_edgeVec_le
reverseFaceBetween_support_edgeVec_lt
face_plane_head_sub_tail
face_plane_head_sigma_symm_sub_tail
faceVertex_eq_tail_or_head_or_tail_phi2_of_dartFace_eq
tail_phi_phi_eq_head_sigma_symm_of_triangular_euclidean
reverseLink_nonincident_of_simple
```

One mathematical correction is essential: the proof needs the axis as a **strict positive cone combination** of the incident rays, not just `∀ d, 0 < ⟪a, w_d⟫`.  The needed axis package is:

```lean
a = ∑ d : {d : D // M.tail d = v}, β d • edgeVec P d.1
∀ d, 0 < β d
```

This is exactly the form produced by the minimum-norm/Stiemke axis route.

## Proof kernel

If two projected rays are positively collinear, then one edge vector differs from a positive multiple of the other by an axis component.  A support face through the first ray but not the second proves that the axis coefficient is positive; a support face through the second ray but not the first then gives the contradiction.

```lean
import ProofsInTheBook.ZinanCh13EuclLink
import Mathlib.Analysis.InnerProductSpace.PiL2

noncomputable section

open scoped Classical RealInnerProductSpace BigOperators
open ProofsInTheBook.PlanarMap
open ProofsInTheBook.PlanarMap.CombMap
open ProofsInTheBook.Ch13Euclidean
open ProofsInTheBook.Ch13EuclLink

namespace ProofsInTheBook.Ch13ProjectedAngleInjectiveDraft

abbrev E3 : Type := EuclideanSpace ℝ (Fin 3)

def projPerp (a x : E3) : E3 :=
  x - ((⟪x, a⟫ : ℝ) / (⟪a, a⟫ : ℝ)) • a

lemma eq_axis_component_of_projPerp_collinear {a x y : E3} {c : ℝ}
    (h : projPerp a y = c • projPerp a x) :
    y = c • x +
      (((⟪y, a⟫ : ℝ) / (⟪a, a⟫ : ℝ) -
        c * ((⟪x, a⟫ : ℝ) / (⟪a, a⟫ : ℝ))) • a := by
  classical
  dsimp [projPerp] at h ⊢
  calc
    y = (y - ((⟪y, a⟫ : ℝ) / (⟪a, a⟫ : ℝ)) • a) +
          ((⟪y, a⟫ : ℝ) / (⟪a, a⟫ : ℝ)) • a := by
          module
    _ = c • (x - ((⟪x, a⟫ : ℝ) / (⟪a, a⟫ : ℝ)) • a) +
          ((⟪y, a⟫ : ℝ) / (⟪a, a⟫ : ℝ)) • a := by
          rw [h]
    _ = c • x +
        (((⟪y, a⟫ : ℝ) / (⟪a, a⟫ : ℝ) -
          c * ((⟪x, a⟫ : ℝ) / (⟪a, a⟫ : ℝ))) • a := by
          module

lemma support_negative_on_axis_of_positive_combo {ι : Type*} [Fintype ι]
    (w : ι → E3) (β : ι → ℝ) {a n : E3}
    (ha : a = ∑ i, β i • w i)
    (hβ : ∀ i, 0 < β i)
    (hle : ∀ i, (⟪n, w i⟫ : ℝ) ≤ 0)
    (hlt : ∃ i, (⟪n, w i⟫ : ℝ) < 0) :
    (⟪n, a⟫ : ℝ) < 0 := by
  classical
  have hinner : (⟪n, a⟫ : ℝ) = ∑ i, β i * (⟪n, w i⟫ : ℝ) := by
    calc
      (⟪n, a⟫ : ℝ) = ⟪n, ∑ i, β i • w i⟫ := by rw [ha]
      _ = ∑ i, (⟪n, β i • w i⟫ : ℝ) := by rw [inner_sum]
      _ = ∑ i, β i * (⟪n, w i⟫ : ℝ) := by
            apply Finset.sum_congr rfl
            intro i _
            rw [real_inner_smul_right]
  have hle_terms : ∀ i ∈ (Finset.univ : Finset ι), β i * (⟪n, w i⟫ : ℝ) ≤ 0 := by
    intro i _
    exact mul_nonpos_of_nonneg_of_nonpos (le_of_lt (hβ i)) (hle i)
  obtain ⟨i0, hi0⟩ := hlt
  have hlt_terms : ∃ i ∈ (Finset.univ : Finset ι), β i * (⟪n, w i⟫ : ℝ) < 0 := by
    refine ⟨i0, by simp, ?_⟩
    exact mul_neg_of_pos_of_neg (hβ i0) hi0
  have hsumlt : (∑ i, β i * (⟪n, w i⟫ : ℝ)) < ∑ _i : ι, (0 : ℝ) :=
    Finset.sum_lt_sum hle_terms hlt_terms
  rw [hinner]
  simpa using hsumlt

/-- Core contradiction used by `ProjectedAngleInjective`. -/
theorem no_pos_collinear_proj_of_two_supports
    {a x y n m : E3} {c : ℝ}
    (hc : 0 < c)
    (hproj : projPerp a y = c • projPerp a x)
    (hnx : (⟪n, x⟫ : ℝ) = 0)
    (hny : (⟪n, y⟫ : ℝ) < 0)
    (hna : (⟪n, a⟫ : ℝ) < 0)
    (hmy : (⟪m, y⟫ : ℝ) = 0)
    (hmx : (⟪m, x⟫ : ℝ) < 0)
    (hma : (⟪m, a⟫ : ℝ) < 0) :
    False := by
  classical
  let μ : ℝ := (⟪y, a⟫ : ℝ) / (⟪a, a⟫ : ℝ) -
    c * ((⟪x, a⟫ : ℝ) / (⟪a, a⟫ : ℝ))
  have hdecomp : y = c • x + μ • a := by
    simpa [μ] using eq_axis_component_of_projPerp_collinear (a := a) (x := x) (y := y)
      (c := c) hproj
  have hμpos : 0 < μ := by
    have hny_eq : (⟪n, y⟫ : ℝ) = μ * (⟪n, a⟫ : ℝ) := by
      calc
        (⟪n, y⟫ : ℝ) = ⟪n, c • x + μ • a⟫ := by rw [hdecomp]
        _ = c * (⟪n, x⟫ : ℝ) + μ * (⟪n, a⟫ : ℝ) := by
              rw [inner_add_right, real_inner_smul_right, real_inner_smul_right]
        _ = μ * (⟪n, a⟫ : ℝ) := by rw [hnx]; ring
    by_contra hnot
    have hμle : μ ≤ 0 := le_of_not_gt hnot
    have hprod_nonneg : 0 ≤ μ * (⟪n, a⟫ : ℝ) :=
      mul_nonneg_of_nonpos_of_nonpos hμle (le_of_lt hna)
    nlinarith
  have hmy_eq : (⟪m, y⟫ : ℝ) = c * (⟪m, x⟫ : ℝ) + μ * (⟪m, a⟫ : ℝ) := by
    calc
      (⟪m, y⟫ : ℝ) = ⟪m, c • x + μ • a⟫ := by rw [hdecomp]
      _ = c * (⟪m, x⟫ : ℝ) + μ * (⟪m, a⟫ : ℝ) := by
            rw [inner_add_right, real_inner_smul_right, real_inner_smul_right]
  have hsum_neg : c * (⟪m, x⟫ : ℝ) + μ * (⟪m, a⟫ : ℝ) < 0 := by
    exact add_neg (mul_neg_of_pos_of_neg hc hmx) (mul_neg_of_pos_of_neg hμpos hma)
  nlinarith

structure ProjectedSeparationData {ι : Type*} (w : ι → E3) (a : E3) : Prop where
  sep : ∀ {d e : ι}, d ≠ e →
    ∃ n m : E3,
      (⟪n, w d⟫ : ℝ) = 0 ∧ (⟪n, w e⟫ : ℝ) < 0 ∧ (⟪n, a⟫ : ℝ) < 0 ∧
      (⟪m, w e⟫ : ℝ) = 0 ∧ (⟪m, w d⟫ : ℝ) < 0 ∧ (⟪m, a⟫ : ℝ) < 0

structure RayAngleKeySpec {κ : Type*} (a : E3) (key : E3 → κ) : Prop where
  eq_imp_pos_collinear : ∀ {x y : E3}, key x = key y →
    ∃ c : ℝ, 0 < c ∧ projPerp a y = c • projPerp a x

/-- Abstract injectivity theorem; instantiate `key = rayAngleKey a` when that API exists. -/
theorem projectedAngleInjective_of_separationData
    {ι κ : Type*} {w : ι → E3} {a : E3} {key : E3 → κ}
    (hsep : ProjectedSeparationData w a)
    (hkey : RayAngleKeySpec a key) :
    Function.Injective (fun d : ι => key (w d)) := by
  intro d e hkey_eq
  by_cases hde : d = e
  · exact hde
  · exfalso
    obtain ⟨c, hc, hproj⟩ := hkey.eq_imp_pos_collinear hkey_eq
    obtain ⟨n, m, hnx, hny, hna, hmy, hmx, hma⟩ := hsep.sep hde
    exact no_pos_collinear_proj_of_two_supports
      (a := a) (x := w d) (y := w e) (n := n) (m := m) (c := c)
      hc hproj hnx hny hna hmy hmx hma

end ProofsInTheBook.Ch13ProjectedAngleInjectiveDraft
```

## Geometry adapter to add in the repo

For a fixed vertex use the outgoing-dart subtype:

```lean
def OutDart (M : CombMap D) (v : M.Vertex) := {d : D // M.tail d = v}
```

The missing finite-incidence lemma is:

```lean
noncomputable def supportDartExcluding
    {M : CombMap D} {v : M.Vertex} (d e : OutDart M v) : D :=
  if e.1 = M.σ.symm d.1 then M.σ d.1 else d.1

/-- The selected face contains `d`, excludes `e`, and supports all incident rays. -/
theorem supportDartExcluding_spec
    (P : TriangulatedEuclideanPolyhedron M) (hsimple : M.IsSimpleGraph)
    {v : M.Vertex} (d e : OutDart M v) (hne : d ≠ e) :
    let s := supportDartExcluding d e
    let n := P.outward_normal (M.dartFace s)
    (⟪n, edgeVec P d.1⟫ : ℝ) = 0 ∧
    (⟪n, edgeVec P e.1⟫ : ℝ) < 0 ∧
    (∀ q : OutDart M v, (⟪n, edgeVec P q.1⟫ : ℝ) ≤ 0)
```

Proof obligations for `supportDartExcluding_spec` are exactly the existing strict-support lemmas:

* false branch `e.1 ≠ M.σ.symm d.1`: use the face `M.dartFace d.1`; zero is `face_plane_head_sub_tail`, strict negativity is `reverseFaceBetween_support_edgeVec_lt P d.1 e.1`, and nonpositivity is `reverseFaceBetween_support_edgeVec_le P d.1 q.1`.
* true branch `e.1 = M.σ.symm d.1`: use the other face `M.dartFace (M.σ d.1)`; zero on `d` is `face_plane_head_sigma_symm_sub_tail P (M.σ d.1)` after rewriting `M.σ.symm (M.σ d.1) = d.1`, strict negativity is `reverseFaceBetween_support_edgeVec_lt P (M.σ d.1) e.1`, and nonpositivity is `reverseFaceBetween_support_edgeVec_le P (M.σ d.1) q.1`.
* the off-face proofs are discharged by `faceVertex_eq_tail_or_head_or_tail_phi2_of_dartFace_eq`, `tail_phi_phi_eq_head_sigma_symm_of_triangular_euclidean`, and `hsimple.no_loop/no_parallel` via the existing `reverseLink_nonincident_of_simple` pattern.

Given `supportDartExcluding_spec` and the positive-combo axis data, `ProjectedSeparationData` is immediate by applying `supportDartExcluding_spec d e` and `supportDartExcluding_spec e d`, then using `support_negative_on_axis_of_positive_combo` to prove the two inequalities `⟪n,a⟫ < 0` and `⟪m,a⟫ < 0`.

## Final target shape

Once `rayAngleKey` exists, the final theorem should be:

```lean
theorem ProjectedAngleInjective
    (P : TriangulatedEuclideanPolyhedron M) (hsimple : M.IsSimpleGraph)
    {v : M.Vertex} (A : VertexConeAxisData P v) :
    Function.Injective
      (fun d : OutDart M v => rayAngleKey A.a (edgeVec P d.1)) := by
  apply projectedAngleInjective_of_separationData
  · exact projectedSeparationData_of_strict_face_support P hsimple A
  · exact rayAngleKey_spec A
```

Here `rayAngleKey_spec` is the standard nonzero-`Complex.arg` fact: equality of angle keys implies positive collinearity of the perpendicular projections.  The proof above shows that strict face support rules that out for distinct outgoing darts.