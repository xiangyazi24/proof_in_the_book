# Cauchy ch13: wiring out `RotationFaithful`

This is the architecture I would implement to actually remove the carried orientation field from `ConvexEuclideanPolyhedron`.

The current pipeline is:

```text
ConvexEuclideanPolyhedron.faithful : RotationFaithful P.toTri
  → ZinanCh13EuclLink.orientedTriangleSupport_of_rotationFaithful
  → ZinanCh13EuclLink.vertexLinkGeometryOfEuclidean
  → VertexLinkGeometry.toVertexStar
  → Ch13VertexStar.VertexStar.vertexLink_strictArm.closed_convex
  → ch13 Cauchy assembly
```

The end-state should be:

```text
face support + simple fan + degree≥3 + derived self-dual axis + angular/fan turn positivity
  → rotationFaithful_of_convex : RotationFaithful P
  → old downstream pipeline unchanged, except `P.faithful` is replaced by the theorem call
```

The minimal patch is therefore **not** to rewrite the whole Cauchy pipeline.  Prove `RotationFaithful` as a theorem, drop it as a structure field, and keep the existing consumers of `RotationFaithful` alive through the derived theorem.

There is one dependency-order warning:

> Do not prove the needed per-dart turn sign from the same `StrictConvexSphPolygon` that currently depends on `RotationFaithful`.  That would be circular.  The turn sign used to prove `RotationFaithful` must come from the independent axis/angular-sort/fan-alignment layer: positive cone axis → projected rays surround → angular consecutive gaps `< π` → reverse-`σ` consecutive turn sign.

After `rotationFaithful_of_convex` is proved, the old `VertexStar.vertexLink_strictArm.closed_convex` route can be reused freely.

## 1. Is `RotationFaithful` exactly the per-dart sign?

Almost.  Syntactically, `RotationFaithful` is a vector equality:

```lean
structure RotationFaithful {M : CombMap D}
    (P : TriangulatedEuclideanPolyhedron M) : Prop where
  outward_normal_eq_pos_smul_reverse_cross :
    ∀ d : D,
      ∃ lam : ℝ, 0 < lam ∧
        P.outward_normal (reverseFaceBetween M d) =
          lam • cross (edgeVec P (M.σ.symm d)) (edgeVec P d)
```

But once the face-plane facts and face nondegeneracy are available, this vector equality is equivalent to a single scalar orientation sign.  For a dart `d`, set

```text
N  := P.outward_normal (M.dartFace d)
Wd := edgeVec P d
Ws := edgeVec P (M.σ.symm d)
C  := cross Ws Wd
```

The face-plane lemmas already in `ZinanCh13EuclLink` give

```lean
face_plane_head_sub_tail P d
face_plane_head_sigma_symm_sub_tail P d
```

so `N ⟂ Wd` and `N ⟂ Ws`.  Face nondegeneracy gives `Wd, Ws` independent, hence `C ≠ 0`; strict support against an off-face vertex gives `N ≠ 0`.  Therefore `C` and `N` are parallel.  Under these nondegeneracy facts,

```text
∃ λ > 0, N = λ • C
```

is equivalent to any of the following scalar signs:

```text
0 < ⟪N, C⟫,
0 < det3 N Ws Wd,
0 < det3 Wd Ws A  together with  ⟪N,A⟫ < 0,
```

where `A` is the chosen self-dual axis at `tail d`.  The last form is the one that matches the new architecture.

### Exact derivation from the axis

Let `A` be the self-dual axis at `v = M.tail d`, with

```text
A = ∑ e incident to v, α_e • edgeVec P e,      α_e > 0.
```

For the face `f = M.dartFace d`, face support gives

```text
⟪N, edgeVec P e⟫ ≤ 0
```

for every incident edge `e` at `v`, and strict support gives `< 0` for any incident edge whose head is not one of the three vertices of `f`.  Such an edge exists from the local degree `≥ 3` and the simple fan bookkeeping.  Hence

```text
⟪N,A⟫ = ∑ e, α_e * ⟪N, edgeVec P e⟫ < 0.
```

The independent angular/fan layer gives the positive turn for the reverse-`σ` consecutive face edge:

```text
0 < det3 Wd Ws A = ⟪cross Wd Ws, A⟫.
```

Since `cross Wd Ws` is parallel to `N`, write

```text
cross Wd Ws = ρ • N.
```

Then

```text
0 < ⟪cross Wd Ws, A⟫ = ρ * ⟪N,A⟫.
```

Because `⟪N,A⟫ < 0`, we get `ρ < 0`.  Therefore

```text
cross Ws Wd = - cross Wd Ws = (-ρ) • N,     0 < -ρ,
```

and hence

```text
N = ((-ρ)⁻¹) • cross Ws Wd,
```

with positive scalar.  This is exactly the `RotationFaithful` field for dart `d`.

So the answer is:

* `orientedTriangleSupport_of_axisFace` contains enough information to prove `RotationFaithful`, **provided** it exposes that its `normal` is the stored outward normal up to positive rescaling, or provided the cross/normal equality is proved immediately before packaging the `OrientedTriangleSupport`.
* Axis existence alone is not enough.  You also need the independent reverse-`σ` turn sign, or equivalently angular-order alignment between the geometry-sorted link and the combinatorial reverse-`σ` fan.

## 2. The theorem surfaces I would add

Put these near `ZinanCh13EuclLink`, or in a small successor file imported by `ZinanCh13Cauchy3D` before `ConvexEuclideanPolyhedron` is used.

```lean
import ProofsInTheBook.ZinanCh13EuclLink
import ProofsInTheBook.SphericalConeMembership
import ProofsInTheBook.Ch13VertexStar

noncomputable section
open scoped Classical RealInnerProductSpace BigOperators
open ProofsInTheBook.PlanarMap ProofsInTheBook.PlanarMap.CombMap
open ProofsInTheBook.Ch13Euclidean
open ProofsInTheBook.Ch13EuclLink
open ProofsInTheBook.SphericalKernel
open ProofsInTheBook.SphericalConeMembership

namespace ProofsInTheBook.Ch13RotationFaithfulFree

variable {D : Type*} [Fintype D] [DecidableEq D]
variable {M : CombMap D}

/-- A local self-dual axis certificate at one vertex.

The final implementation can use whatever `AxisPositiveConeForEdge` structure has
already landed.  The important fields for this wiring layer are:

* `axis_eq_posCone`: `axis` is a strictly positive combination of incident edge rays;
* `edge_pos`: `axis` is in the dual interior, used by the angular-sort layer;
* `reverseSigma_turn_pos`: the independent angular/fan theorem that the reverse-`σ`
  consecutive pair has positive turn about `axis`.
-/
structure VertexSelfDualAxis
    (P : TriangulatedEuclideanPolyhedron M) (v : M.Vertex) where
  axis : E3
  axis_ne : axis ≠ 0
  axis_eq_posCone :
    ∃ μ : {d : D // M.tail d = v} → ℝ,
      (∀ d, 0 < μ d) ∧
        axis = ∑ d : {d : D // M.tail d = v}, μ d • edgeVec P d.1
  edge_pos : ∀ d : D, M.tail d = v → 0 < inner ℝ axis (edgeVec P d)
  reverseSigma_turn_pos :
    ∀ d : D, M.tail d = v →
      0 < det3 (edgeVec P d) (edgeVec P (M.σ.symm d)) axis

/-- The finite-cone theorem: construct the self-dual axis at `v` from convexity.

This is where the Stiemke/Gordan proof belongs.  The proof uses:

1. the already-proved dual positive/pointedness witness for the incident edge cone;
2. finite-dimensional Stiemke/Gordan on the Gram matrix;
3. positive-span of projections and angular sorting;
4. alignment of the angular fan with the reverse-`σ` face fan.

It should not depend on `RotationFaithful` or on `StrictConvexSphPolygon` produced
by `VertexStar.vertexLink_strictArm`; otherwise the architecture is circular.
-/
theorem selfDualAxis_of_convex
    (P : TriangulatedEuclideanPolyhedron M)
    (hsimple : M.IsSimpleGraph)
    (hdeg : ∀ v : M.Vertex, 3 ≤ vDeg P v)
    (v : M.Vertex) :
    VertexSelfDualAxis P v := by
  -- Stiemke/Gordan + angular-sort/fan-alignment layer.
  -- No use of `RotationFaithful`.
  sorry

/-- A supporting face normal is strictly negative on the self-dual axis.

This is the summation of face support over the positive-cone expression for the
axis.  The strict summand comes from an off-face incident edge, supplied by
`exists_fin_not_incident_edge`, `reverseLink_nonincident_of_simple`, and the
triangular face-vertex classifier.
-/
theorem outward_normal_axis_neg
    (P : TriangulatedEuclideanPolyhedron M)
    (hsimple : M.IsSimpleGraph)
    (hdeg : ∀ v : M.Vertex, 3 ≤ vDeg P v)
    (A : ∀ v : M.Vertex, VertexSelfDualAxis P v)
    (d : D) :
    inner ℝ (P.outward_normal (M.dartFace d)) ((A (M.tail d)).axis) < 0 := by
  -- Expand `(A (M.tail d)).axis_eq_posCone`.
  -- For each incident edge use `face_support_from_dart_tail P d e`.
  -- For one nonincident edge use strict support; the current code in
  -- `vertexLinkGeometryOfEuclidean` already contains the off-face witness
  -- construction:
  --   exists_fin_not_incident_edge
  --   reverseLink_nonincident_of_simple
  --   faceVertex_eq_tail_or_head_or_tail_phi2_of_dartFace_eq
  --   tail_phi_phi_eq_head_sigma_symm_of_triangular_euclidean
  sorry

/-- Per-dart positive scalar relation between the outward normal and the reversed
cross product.  This is the local theorem that replaces the old carried field.
-/
theorem outward_normal_eq_pos_smul_reverse_cross_of_axis
    (P : TriangulatedEuclideanPolyhedron M)
    (hsimple : M.IsSimpleGraph)
    (hdeg : ∀ v : M.Vertex, 3 ≤ vDeg P v)
    (A : ∀ v : M.Vertex, VertexSelfDualAxis P v)
    (d : D) :
    ∃ lam : ℝ, 0 < lam ∧
      P.outward_normal (reverseFaceBetween M d) =
        lam • cross (edgeVec P (M.σ.symm d)) (edgeVec P d) := by
  -- Let `N := P.outward_normal (M.dartFace d)`, `Wd := edgeVec P d`,
  -- `Ws := edgeVec P (M.σ.symm d)`, and `a := (A (M.tail d)).axis`.
  --
  -- 1. `N ⟂ Wd` from `face_plane_head_sub_tail P d`.
  -- 2. `N ⟂ Ws` from `face_plane_head_sigma_symm_sub_tail P d`.
  -- 3. `N ≠ 0` from strict support against an off-face incident edge.
  -- 4. `cross_parallel_of_perp` gives
  --      cross Wd Ws = ρ • N.
  -- 5. `(A (M.tail d)).reverseSigma_turn_pos d rfl` gives
  --      0 < det3 Wd Ws a = inner ℝ (cross Wd Ws) a.
  -- 6. `outward_normal_axis_neg` gives `inner ℝ N a < 0`.
  -- 7. Therefore `ρ < 0`, so `cross Ws Wd = (-ρ) • N` with `0 < -ρ`.
  -- 8. Take `lam = (-ρ)⁻¹`.
  sorry

/-- The carried `RotationFaithful` field is derivable from the convex geometric
payload.  This is the theorem downstream code should call after the field is
dropped from `ConvexEuclideanPolyhedron`.
-/
theorem rotationFaithful_of_convex
    (P : TriangulatedEuclideanPolyhedron M)
    (hsimple : M.IsSimpleGraph)
    (hdeg : ∀ v : M.Vertex, 3 ≤ vDeg P v) :
    RotationFaithful P := by
  let A : ∀ v : M.Vertex, VertexSelfDualAxis P v :=
    fun v => selfDualAxis_of_convex P hsimple hdeg v
  refine ⟨?_⟩
  intro d
  exact outward_normal_eq_pos_smul_reverse_cross_of_axis P hsimple hdeg A d

end ProofsInTheBook.Ch13RotationFaithfulFree
```

If the landed axis certificate is named `AxisPositiveConeForEdge`, then `VertexSelfDualAxis` should disappear and `selfDualAxis_of_convex` should return that structure or a thin adapter around it.  What matters is that the rotation-faithful proof consumes these three facts:

```text
axis is a positive combination of incident edge rays,
axis is dual-positive on incident edge rays,
reverse-σ consecutive turn is positive about the axis.
```

The third item must come from the independent angular-sort/fan-alignment proof, not from the post-`RotationFaithful` vertex-star link.

## 3. `orientedTriangleSupport_of_axisFace` vs `rotationFaithful_of_convex`

There are two equivalent ways to wire the local proof.

### Option A: prove `RotationFaithful` first, keep existing consumers unchanged

This is the smallest code diff.

```lean
theorem rotationFaithful_of_convex ... : RotationFaithful P
```

Then keep using the existing theorem:

```lean
vertexLinkGeometryOfEuclidean P (rotationFaithful_of_convex P hsimple hdeg) hsimple v (hdeg v)
```

This lets all of the following existing code remain unchanged:

* `ZinanCh13EuclLink.link_side_support_of_rotationFaithful`
* `ZinanCh13EuclLink.link_side_strict_of_rotationFaithful`
* `ZinanCh13EuclLink.orientedTriangleSupport_of_rotationFaithful`
* `ZinanCh13EuclLink.vertexLinkGeometryOfEuclidean`
* `ZinanCh13EuclLink.VertexLinkGeometry.toVertexStar`
* `Ch13VertexStar.VertexStar.vertexLink_strictArm`

### Option B: bypass `RotationFaithful` in `VertexLinkGeometry`

This is conceptually clean but touches more code.  Add:

```lean
noncomputable def vertexLinkGeometryOfEuclidean_axis
    (P : TriangulatedEuclideanPolyhedron M)
    (hsimple : M.IsSimpleGraph)
    (hdeg : 3 ≤ vDeg P v)
    (A : VertexSelfDualAxis P v) :
    VertexLinkGeometry P v := by
  -- identical to `vertexLinkGeometryOfEuclidean`, except the `oriented` field
  -- calls `orientedTriangleSupport_of_axisFace` instead of
  -- `orientedTriangleSupport_of_rotationFaithful`.
  sorry
```

Then prove `RotationFaithful` as a corollary of the same local cross/normal sign theorem.  This option is fine, but I would not choose it as the first patch because the current pipeline already factors around `RotationFaithful` and can be preserved with a single theorem call.

## 4. Dropping the field from `ConvexEuclideanPolyhedron`

Current structure in `ZinanCh13Cauchy3D`:

```lean
structure ConvexEuclideanPolyhedron (M : CombMap D)
    extends TriangulatedEuclideanPolyhedron M where
  degree_ge_three :
    ∀ (v : M.Vertex), 3 ≤ vDeg toTriangulatedEuclideanPolyhedron v
  faithful : RotationFaithful toTriangulatedEuclideanPolyhedron
  sphere : M.IsSphereMap
  triangle : M.FaceRegular 3
  isSimple : M.IsSimpleGraph
```

End-state structure:

```lean
structure ConvexEuclideanPolyhedron (M : CombMap D)
    extends TriangulatedEuclideanPolyhedron M where
  degree_ge_three :
    ∀ (v : M.Vertex), 3 ≤ vDeg toTriangulatedEuclideanPolyhedron v
  sphere : M.IsSphereMap
  triangle : M.FaceRegular 3       -- optional/redundant with `toTri.every_face_triangle`
  isSimple : M.IsSimpleGraph
```

Then add a derived theorem/abbrev in the namespace:

```lean
namespace ConvexEuclideanPolyhedron

abbrev toTri (P : ConvexEuclideanPolyhedron M) :
    TriangulatedEuclideanPolyhedron M :=
  P.toTriangulatedEuclideanPolyhedron

/-- Derived replacement for the removed field. -/
theorem rotationFaithful (P : ConvexEuclideanPolyhedron M) :
    RotationFaithful P.toTri :=
  ProofsInTheBook.Ch13RotationFaithfulFree.rotationFaithful_of_convex
    P.toTri P.isSimple P.degree_ge_three

/-- The derived local vertex-link geometry at a vertex. -/
def linkGeom (P : ConvexEuclideanPolyhedron M) (v : M.Vertex)
    (hdeg : 3 ≤ vDeg P.toTri v) : VertexLinkGeometry P.toTri v :=
  vertexLinkGeometryOfEuclidean P.toTri P.rotationFaithful P.isSimple v hdeg

/-- The derived vertex-link geometry with the stored degree lower bound supplied. -/
def linkGeomAt (P : ConvexEuclideanPolyhedron M) (v : M.Vertex) :
    VertexLinkGeometry P.toTri v :=
  P.linkGeom v (P.degree_ge_three v)

/-- The Euclidean vertex star attached to a convex Euclidean polyhedron. -/
def vertexStar (P : ConvexEuclideanPolyhedron M) (v : M.Vertex) : VertexStar :=
  vertexStarOfEuclidean P.toTri v (P.linkGeomAt v)

end ConvexEuclideanPolyhedron
```

The regular tetrahedron instance becomes:

```lean
def tetraConvexEuclideanPolyhedron : ConvexEuclideanPolyhedron tetraMap where
  toTriangulatedEuclideanPolyhedron := tetraEuclideanPolyhedron
  degree_ge_three := tetra_vDeg_ge_three
  sphere := tetraMap_isSphereMap
  triangle := tetraMap_faceRegular_three
  isSimple := ProofsInTheBook.Ch13ComponentClose.tetraMap_isSimpleGraph
```

The old theorem `tetra_rotationFaithful` can remain as a diagnostic, but it is no longer a field assignment.

## 5. Does the self-dual axis require a new field?

No, provided the Stiemke/Gordan finite cone theorem is proved.

The self-dual axis should be a **derived local theorem**, not a field of `ConvexEuclideanPolyhedron`:

```lean
theorem selfDualAxis_of_convex
    (P : TriangulatedEuclideanPolyhedron M)
    (hsimple : M.IsSimpleGraph)
    (hdeg : ∀ v : M.Vertex, 3 ≤ vDeg P v)
    (v : M.Vertex) :
    VertexSelfDualAxis P v
```

The proof uses only existing geometric payload:

* `pos`, `face_plane`, `face_supporting_halfspace`, `face_support_strict`, `face_nondegenerate`, `edge_nondegenerate` from `TriangulatedEuclideanPolyhedron`;
* the local fan/noncollision facts from `M.IsSimpleGraph`;
* the local degree hypothesis `degree_ge_three`.

The finite-cone theorem supplies existence of `a_v = ∑ αᵢ wᵢ` with `αᵢ > 0` and `0 < ⟪a_v,wᵢ⟫`.  The angular-sort layer supplies `reverseSigma_turn_pos`.

So the axis should not be stored.  Storing it would just replace one carried geometry witness by another.

## 6. Is `4 ≤ V` needed?

Not as the local hypothesis for this proof.

The strict support step needs, for every link edge `(i,i+1)`, an incident edge `j` with

```lean
j ≠ i ∧ j ≠ i + 1.
```

The repo already has the local combinatorial lemma:

```lean
theorem exists_fin_not_incident_edge {n : ℕ} (hn : 2 ≤ n) (i : Fin (n + 1)) :
    ∃ j : Fin (n + 1), j ≠ i ∧ j ≠ i + 1
```

and the simple-graph bookkeeping:

```lean
reverseLink_nonincident_of_simple
reverseLinkNbr_injective_of_simple
reverseLinkNbr_eq_apex_false_of_simple
```

Thus the local input is `degree_ge_three`, i.e. `2 ≤ starN P v`, not global `4 ≤ M.V`.

A global `4 ≤ M.Vertex` theorem is true for a simple triangulated sphere and may be useful as a sanity theorem or for deriving other global facts, but it is not the right field to add for this architecture.  It is also not sufficient by itself: one vertex could have bad local degree in an abstract structure unless you also know the local degree lower bound.

Recommended field policy:

* Drop `faithful`.
* Keep `degree_ge_three` for now.
* Do not add `4≤V` as a field.
* Later, if you prove `degree_ge_three` from `M.IsSphereMap + M.FaceRegular 3 + M.IsSimpleGraph`, then drop `degree_ge_three` too.
* Consider dropping `triangle : M.FaceRegular 3` because `TriangulatedEuclideanPolyhedron.every_face_triangle` already stores the same property, but that is orthogonal to `RotationFaithful`.

## 7. End-state theorem signatures

The derived orientation theorem should be stated for the raw triangulated realization, because it is useful below and outside `ConvexEuclideanPolyhedron`:

```lean
namespace ProofsInTheBook.Ch13RotationFaithfulFree

/-- Derived orientation compatibility: no carried `RotationFaithful` field. -/
theorem rotationFaithful_of_convex
    (P : TriangulatedEuclideanPolyhedron M)
    (hsimple : M.IsSimpleGraph)
    (hdeg : ∀ v : M.Vertex, 3 ≤ vDeg P v) :
    RotationFaithful P := by
  sorry

end ProofsInTheBook.Ch13RotationFaithfulFree
```

If the angular/fan-alignment proof needs the sphere-map hypothesis, use this slightly wider signature:

```lean
theorem rotationFaithful_of_convex
    (P : TriangulatedEuclideanPolyhedron M)
    (hsphere : M.IsSphereMap)
    (hsimple : M.IsSimpleGraph)
    (hdeg : ∀ v : M.Vertex, 3 ≤ vDeg P v) :
    RotationFaithful P := by
  sorry
```

I would start without `hsphere`; add it only if the independent angular-order alignment theorem genuinely consumes it.

The headline Cauchy theorem does **not** need a new signature once `ConvexEuclideanPolyhedron` is changed.  It remains:

```lean
theorem chapter13_cauchy_rigidity
    (P Q : ConvexEuclideanPolyhedron M)
    (hcong : CongruentFaces P.toTri Q.toTri)
    (v : M.Vertex)
    (i : Fin ((rotatedStarP P.toTri (fun w => P.linkGeomAt w)
      (adaptiveOffset P.toTri Q.toTri
        (fun w => P.linkGeomAt w) (fun w => Q.linkGeomAt w)) v).n - 1)) :
    (rotatedStarP P.toTri (fun w => P.linkGeomAt w)
        (adaptiveOffset P.toTri Q.toTri
          (fun w => P.linkGeomAt w) (fun w => Q.linkGeomAt w)) v).dihedral i =
      (rotatedStarQ P.toTri Q.toTri
        (fun w => P.linkGeomAt w) (fun w => Q.linkGeomAt w)
        (adaptiveOffset P.toTri Q.toTri
          (fun w => P.linkGeomAt w) (fun w => Q.linkGeomAt w)) v).dihedral
        (Fin.cast (by
          change (P.linkGeomAt v).n - 1 = (Q.linkGeomAt v).n - 1
          exact congrArg (fun n => n - 1)
            (vertexLinkGeometry_n_eq P.toTri Q.toTri
              (fun w => P.linkGeomAt w) (fun w => Q.linkGeomAt w) v).symm) i)
```

The semantic change is only that `P.linkGeomAt` and `Q.linkGeomAt` now call `rotationFaithful_of_convex` internally instead of projecting a stored field.

## 8. Concrete edit list

1. Add the new orientation-free theorem layer, preferably in a new file such as:

   ```lean
   ProofsInTheBook/ZinanCh13RotationFree.lean
   ```

   with public theorem:

   ```lean
   rotationFaithful_of_convex
   ```

2. Import that file in `ZinanCh13Cauchy3D.lean`.

3. Remove this field from `ConvexEuclideanPolyhedron`:

   ```lean
   faithful : RotationFaithful toTriangulatedEuclideanPolyhedron
   ```

4. Add the namespace theorem:

   ```lean
   theorem ConvexEuclideanPolyhedron.rotationFaithful
       (P : ConvexEuclideanPolyhedron M) : RotationFaithful P.toTri :=
     rotationFaithful_of_convex P.toTri P.isSimple P.degree_ge_three
   ```

   or with `P.sphere` if the theorem surface includes it.

5. Change `linkGeom` from:

   ```lean
   vertexLinkGeometryOfEuclidean P.toTri P.faithful P.isSimple v hdeg
   ```

   to:

   ```lean
   vertexLinkGeometryOfEuclidean P.toTri P.rotationFaithful P.isSimple v hdeg
   ```

6. Remove `faithful := tetra_rotationFaithful` from `tetraConvexEuclideanPolyhedron`.

7. Keep every downstream theorem unchanged unless Lean asks for unfolding help around the new theorem name.

## 9. Bottom line

`RotationFaithful` can be dropped as a field, but the theorem replacing it must be proved at the correct layer:

```text
self-dual axis + independent reverse-σ angular turn + face support
  ⇒ outward_normal = positive scalar • reverse cross
  ⇒ RotationFaithful
```

Then the current repo pipeline can remain structurally unchanged:

```text
rotationFaithful_of_convex
  → vertexLinkGeometryOfEuclidean
  → VertexStar
  → vertexLink_strictArm.closed_convex
  → chapter13_cauchy_rigidity
```

No new axis field is needed.  No `4≤V` field is needed for the local proof.  The only local well-formedness already needed is `degree_ge_three` plus `M.IsSimpleGraph`; `M.IsSphereMap` should be threaded only if the independent angular/fan-alignment theorem consumes it.
