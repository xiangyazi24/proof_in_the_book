# Cauchy ch13 angular `turn_pos` chain: no compile target in connected repo

I rechecked the connected repository surface before answering this request.  The named angular-order API is still not present in the repo visible through the GitHub connector:

```text
ProofsInTheBook/ZinanCh13AngularOrder.lean        -- fetch_file: Not Found
ProofsInTheBook/ZinanCh13ConeAxis.lean            -- fetch/search: Not Found
rayAngleKey                                      -- repo search: no hits
angularList                                      -- repo search: no hits
angularNextPerm                                  -- repo search: no hits
SurroundsAxisPlane                               -- repo search: no hits
vertexConeAxis                                   -- repo search: no hits
```

`formPerm` does exist elsewhere in the repo, but not in an angular-order development that exposes the definitions named in the request.  Therefore there is no concrete Lean namespace/API against which a complete compiling proof can be written.  Any no-`sorry` proof mentioning those constants would fail at elaboration in the connected repo.

There is also a mathematical dependency-order issue in item (1):

> `ProjectedAngleInjective` for the angular-sort proof cannot be derived from the `StrictConvexSphPolygon` that is itself supposed to be produced using the angular `turn_pos` theorem.  That would make the elimination of `RotationFaithful` circular.

The injectivity/no-duplicate-projection lemma must be proved from raw vertex-cone extremality and axis-interior data, before building the oriented spherical link.

## Correct noncircular architecture

The `turn_pos` chain should be split into three layers.

### Layer A: raw edge-ray extremality from strict support

This layer belongs next to `ZinanCh13EuclLink`.  It uses only `TriangulatedEuclideanPolyhedron`, triangular face bookkeeping, and `M.IsSimpleGraph`.

For an incident edge ray `e` at vertex `v`, the two incident supporting faces through `e` certify that `edgeVec P e` is an extreme ray of the tangent cone at `v`.  The formal statement should be:

```lean
import ProofsInTheBook.ZinanCh13EuclLink
import ProofsInTheBook.SphericalKernel

noncomputable section
open scoped Classical RealInnerProductSpace BigOperators
open ProofsInTheBook.PlanarMap ProofsInTheBook.PlanarMap.CombMap
open ProofsInTheBook.Ch13Euclidean
open ProofsInTheBook.Ch13EuclLink
open ProofsInTheBook.SphericalKernel

namespace ProofsInTheBook.Ch13AngularTurnFree

variable {D : Type*} [Fintype D] [DecidableEq D]
variable {M : CombMap D}

/-- Raw extremality of an outgoing edge ray in the tangent cone.

This is the noncircular replacement for trying to get projected-angle injectivity
from an already-oriented spherical polygon. -/
theorem edgeRay_extreme_of_face_support_strict
    (P : TriangulatedEuclideanPolyhedron M)
    (hsimple : M.IsSimpleGraph)
    {v : M.Vertex} {e : D}
    (he_tail : M.tail e = v)
    {β : {d : D // M.tail d = v} → ℝ}
    (hβ_nonneg : ∀ d, 0 ≤ β d)
    (hrepr : edgeVec P e = ∑ d, β d • edgeVec P d.1) :
    ∀ d : {d : D // M.tail d = v}, d.1 ≠ e → β d = 0 := by
  -- This theorem is the real missing raw-geometry lemma.
  -- Proof outline:
  -- * Let the two faces incident to `e` at `v` be `dartFace e` and the other
  --   face across `e` (combinatorially `dartFace (M.α e)` or the correct dart
  --   in the fan convention).
  -- * `face_plane_dart` gives zero on `edgeVec P e` for both normals.
  -- * For any other incident edge ray at `v`, at least one of those two face
  --   normals is strictly negative by `face_support_strict` plus the existing
  --   face-vertex classifier:
  --     `faceVertex_eq_tail_or_head_or_tail_phi2_of_dartFace_eq`
  --     `tail_phi_phi_eq_head_sigma_symm_of_triangular_euclidean`
  --     `reverseLink_nonincident_of_simple`
  -- * Dot `hrepr` with the appropriate normal.  The left side is zero and the
  --   right side is a sum of nonpositive terms with the target coefficient
  --   appearing in a strictly negative term.  Since all coefficients are
  --   nonnegative, that coefficient must be zero.
  --
  -- A complete proof depends on a precise lemma naming the second face adjacent
  -- to `e` and a fan-side classifier.  Those are not present as a single API in
  -- the connected repo surface.
  sorry

end ProofsInTheBook.Ch13AngularTurnFree
```

Once this lemma exists, projected positive-collinearity is impossible for distinct edge rays when the axis is in the interior of the edge cone.

### Layer B: no duplicate projected angular directions

This layer consumes the axis-interior certificate.  It should not reference `StrictConvexSphPolygon`.

```lean
namespace ProofsInTheBook.Ch13AngularTurnFree

/-- No two distinct projected edge rays lie on the same positive half-line.

This is the geometric source of `ProjectedAngleInjective`.  It follows from:
* axis interior: `axis = ∑ λ_i w_i`, `λ_i > 0`;
* dual positivity: `0 < ⟪axis,w_i⟫`;
* raw edge extremality from strict support.
-/
theorem projectedExtremeNoDuplicate_of_axisInterior
    (P : TriangulatedEuclideanPolyhedron M)
    (hsimple : M.IsSimpleGraph)
    {v : M.Vertex}
    (axis : E3)
    (haxisCone : ∃ λ : {d : D // M.tail d = v} → ℝ,
      (∀ d, 0 < λ d) ∧ axis = ∑ d, λ d • edgeVec P d.1)
    (haxisDual : ∀ d : D, M.tail d = v → 0 < inner ℝ axis (edgeVec P d)) :
    ∀ d e : {d : D // M.tail d = v}, d ≠ e →
      ¬ ∃ c : ℝ, 0 < c ∧
        projPerp axis (edgeVec P e.1) = c • projPerp axis (edgeVec P d.1) := by
  -- This proof requires the concrete `projPerp` API, which is not present in
  -- the connected repo.  The algebra is:
  --   proj e = c • proj d
  -- implies
  --   w_e = c • w_d + t • axis.
  -- If `t ≥ 0`, this expresses `w_e` as a nonnegative combination of tangent
  -- cone rays containing `w_d`, contradicting `edgeRay_extreme_of_face_support_strict`.
  -- If `t < 0`, rearrange to express `w_d` as a nonnegative combination
  -- containing `w_e`, and use extremality of `w_d`.
  sorry

/-- Angle-key injectivity is a corollary of no positive collinear projected rays.

This proof requires the concrete `rayAngleKey = Complex.arg` and coordinate-frame
lemmas. -/
theorem projectedAngleInjective_of_projectedExtremeNoDuplicate
    (P : TriangulatedEuclideanPolyhedron M)
    {v : M.Vertex} (axis : E3)
    (hproj : ∀ d : {d : D // M.tail d = v}, projPerp axis (edgeVec P d.1) ≠ 0)
    (hNoDup : ∀ d e : {d : D // M.tail d = v}, d ≠ e →
      ¬ ∃ c : ℝ, 0 < c ∧
        projPerp axis (edgeVec P e.1) = c • projPerp axis (edgeVec P d.1)) :
    Function.Injective
      (fun d : {d : D // M.tail d = v} => rayAngleKey axis (edgeVec P d.1)) := by
  -- Need a concrete lemma from the `Complex.arg` implementation:
  -- same arg for nonzero projected vectors iff one is a positive scalar of the other.
  sorry

end ProofsInTheBook.Ch13AngularTurnFree
```

### Layer C: angular gap and cyclic determinant sign

Once the actual angular API exists, the corrected theorem statements are:

```lean
namespace ProofsInTheBook.Ch13AngularTurnFree

/-- Cyclic forward angle gap from `u` to `v`. -/
noncomputable def cyclicRayGap (axis u v : E3) : ℝ :=
  if rayAngleKey axis u ≤ rayAngleKey axis v then
    rayAngleKey axis v - rayAngleKey axis u
  else
    rayAngleKey axis v + 2 * Real.pi - rayAngleKey axis u

/-- Surround plus angle injectivity implies every sorted cyclic consecutive gap
is in `(0,π)`. -/
theorem consecutive_cyclicRayGap_pos_lt_pi_of_surrounds
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (w : ι → E3) (axis : E3)
    (hsur : SurroundsAxisPlane w axis)
    (hproj : ∀ i, projPerp axis (w i) ≠ 0)
    (hangleInj : Function.Injective (fun i => rayAngleKey axis (w i))) :
    ∀ i : ι,
      0 < cyclicRayGap axis (w ((angularNextPerm w axis).symm i)) (w i) ∧
      cyclicRayGap axis (w ((angularNextPerm w axis).symm i)) (w i) < Real.pi := by
  -- This proof cannot elaborate until `rayAngleKey`, `angularNextPerm`, and
  -- `SurroundsAxisPlane` exist in the repo.
  -- Required concrete lemmas:
  -- * `angularList_sorted`: keys are sorted by `<` or `≤`.
  -- * `angularList_nodup`: no duplicate indices.
  -- * `formPerm_pred_adjacent`: `angularNextPerm.symm i` is the predecessor in
  --   the cyclic sorted list.
  -- * `no_key_in_open_gap`: no angular key lies in the open cyclic arc from a
  --   predecessor to its successor.
  -- * frame/trig lemma: if all keys avoid an arc of length ≥ π, the midpoint
  --   frame vector gives a closed halfspace containing every projection.
  -- * `SurroundsAxisPlane` contradicts that closed halfspace.
  sorry

/-- Sine-factor version of the determinant formula, including the wrap case. -/
lemma det3_eq_posFactor_mul_sin_cyclicGap
    {axis u v : E3}
    (hu : projPerp axis u ≠ 0)
    (hv : projPerp axis v ≠ 0) :
    ∃ K : ℝ, 0 < K ∧
      det3 u v axis = K * Real.sin (cyclicRayGap axis u v) := by
  -- This is the coordinate calculation underlying the existing non-wrap turn
  -- lemma `det3_pos_of_rayAngleKey_lt_of_sub_lt_pi`, but with the branch cut
  -- handled by `cyclicRayGap`.
  -- It requires the concrete right-handed frame lemmas for `rayAngleKey`.
  sorry

/-- Cyclic determinant positivity. -/
theorem det3_pos_cyclic
    {axis u v : E3}
    (hu : projPerp axis u ≠ 0)
    (hv : projPerp axis v ≠ 0)
    (hgap0 : 0 < cyclicRayGap axis u v)
    (hgappi : cyclicRayGap axis u v < Real.pi) :
    0 < det3 u v axis := by
  rcases det3_eq_posFactor_mul_sin_cyclicGap
      (axis := axis) (u := u) (v := v) hu hv with
    ⟨K, hK, hdet⟩
  rw [hdet]
  exact mul_pos hK (Real.sin_pos_of_pos_of_lt_pi hgap0 hgappi)

/-- Final predecessor-to-current turn positivity for the angular permutation. -/
theorem turn_pos_pred_current_of_angularNextPerm_of_surrounds
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (w : ι → E3) (axis : E3)
    (hsur : SurroundsAxisPlane w axis)
    (hproj : ∀ i, projPerp axis (w i) ≠ 0)
    (hangleInj : Function.Injective (fun i => rayAngleKey axis (w i))) :
    ∀ i : ι,
      0 < det3 (w ((angularNextPerm w axis).symm i)) (w i) axis := by
  intro i
  rcases consecutive_cyclicRayGap_pos_lt_pi_of_surrounds
      (w := w) (axis := axis) hsur hproj hangleInj i with
    ⟨hgap0, hgappi⟩
  exact det3_pos_cyclic
    (axis := axis)
    (u := w ((angularNextPerm w axis).symm i))
    (v := w i)
    (hu := hproj ((angularNextPerm w axis).symm i))
    (hv := hproj i)
    hgap0 hgappi

end ProofsInTheBook.Ch13AngularTurnFree
```

The last two theorems are complete once the cyclic sine-factor lemma and the gap lemma are present.  The gap lemma and sine-factor lemma cannot be filled in generically: they depend on the concrete `Complex.arg` branch, frame orientation, and `List.formPerm` construction.

## Required additions before a no-`sorry` proof can exist

A compiling proof file requires these declarations in `ZinanCh13AngularOrder.lean` or equivalent:

```lean
projPerp : E3 → E3 → E3
rayAngleKey : E3 → E3 → ℝ
angularList : (ι → E3) → E3 → List ι
angularNextPerm : (ι → E3) → E3 → Equiv.Perm ι
SurroundsAxisPlane : (ι → E3) → E3 → Prop
```

and the API lemmas:

```lean
rayAngleKey_range
same_rayAngleKey_iff_pos_smul_projPerp
angularList_sorted
angularList_nodup
angularNextPerm_pred_is_cyclic_adjacent
no_key_in_open_gap_of_cyclic_adjacent
angleFrameVec_mem_perp
angleFrameVec_ne_zero
inner_projPerp_angleFrameVec
closed_halfspace_of_gap_ge_pi
det3_eq_posFactor_mul_sin_cyclicGap
```

Without those definitions and lemmas in the connected repo, a “complete compiling” proof would be fictional.  The most direct noncircular path is to first add Layer A and Layer B above, then add the concrete angular API lemmas, and finally the final `turn_pos` theorem is the short assembly in Layer C.
