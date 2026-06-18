# Cauchy ch13: deriving `StrictConvexSphPolygon` for the vertex link

This note handles the part independent of the choice of angular-sort axis.  The companion axis result should provide an axis `A` in the **interior of the positive cone of the outgoing edge rays**, plus the angular-order/positive-turn facts for consecutive projected rays.  Given that, the vertex-link strict convexity should be derived from the face supporting halfspaces by building oriented supporting triangles and then reusing `Ch13VertexStar`.

The important convention first:

> `StrictConvexSphPolygon` should be proved for the **normalised original edge rays**
>
> `Q i = (‖w_i‖⁻¹) • w_i : S2`,
>
> ordered by the angular order of their **projections** to `Aᗮ`.

If `Q` instead means the normalised projected vectors `proj_{Aᗮ}(w_i) / ‖proj_{Aᗮ}(w_i)‖`, then the face-halfspace proof below does not apply: `⟪N_f, proj_{Aᗮ}(w)⟫` is not controlled by `⟪N_f,w⟫` unless `⟪N_f,A⟫ = 0`, and the resulting points lie on an equator, so the repo’s `open_hemisphere` field is generally the wrong predicate.  Projections are sort keys; the spherical link is the normalised raw rays.

## 1. What the `StrictConvexSphPolygon` fields mean here

The definition is in `ProofsInTheBook.SphericalKernel`:

```lean
structure StrictConvexSphPolygon {n : ℕ} [NeZero n] (P : Fin n → S2) : Prop where
  three_le : 3 ≤ n
  edge_short : ∀ i : Fin n, ShortArc (P i) (P (i + 1))
  edge_support : ∀ i j : Fin n, 0 ≤ sOrient (P i) (P (i + 1)) (P j)
  strict_nonincident : ∀ i j : Fin n, j ≠ i → j ≠ i + 1 →
      0 < sOrient (P i) (P (i + 1)) (P j)
  open_hemisphere : ∃ h : E3, ‖h‖ = 1 ∧ ∀ i : Fin n, 0 < ⟪h, (P i : E3)⟫
```

For a vertex `v`, write the cyclically ordered outgoing edge vectors as

```text
W i = pos (nbr i) - pos v.
```

The fields are discharged as follows.

* `three_le`: exactly the degree hypothesis `3 ≤ degree(v)`.
* `open_hemisphere`: the chosen axis `A` gives `0 < ⟪A, W i⟫`; normalise `A` to unit length and use the positive rescaling `Q i = ‖W i‖⁻¹ • W i`.
* `edge_support`: for the face `f_i` through `v`, `nbr i`, `nbr (i+1)`, prove an oriented-support identity

  ```text
  det3 (W i) (W (i+1)) z = - c_i * ⟪N_i, z⟫,     c_i > 0,
  ```

  where `N_i = outward_normal f_i`.  Then the supporting halfspace gives `⟪N_i, W j⟫ ≤ 0`, hence `0 ≤ det3 (W i) (W (i+1)) (W j)`, and normalising the three rays transfers the sign to `sOrient (Q i) (Q (i+1)) (Q j)`.
* `strict_nonincident`: same face and same identity, but if `j ≠ i` and `j ≠ i+1`, then `nbr j` is not a vertex of `f_i`, so `face_support_strict` gives `⟪N_i, W j⟫ < 0`, hence strict positivity of the determinant and of `sOrient`.
* `edge_short`: either prove directly from face nondegeneracy of the triangle `(v,nbr i,nbr (i+1))`, or reuse the existing `VertexStar` route: once `turn_strict` exists, `Ch13VertexStar.VertexStar.edgeDir_shortArc` proves consecutive normalised directions are neither equal nor antipodal.

So yes: `edge_support` and `strict_nonincident` are exactly face support and strict face support, **after** one signed determinant/normal bridge is in place.

## 2. The signed determinant/normal bridge is the real local core

For the face `f_i` through the consecutive edge rays `W_i,W_{i+1}`, face-plane data gives

```text
⟪N_i, W_i⟫ = 0,
⟪N_i, W_{i+1}⟫ = 0.
```

Face nondegeneracy gives `W_i,W_{i+1}` linearly independent, so `cross W_i W_{i+1} ≠ 0`, and both `N_i` and `cross W_i W_{i+1}` span the one-dimensional orthogonal complement of `span{W_i,W_{i+1}}`.  Thus

```text
cross W_i W_{i+1} = ρ_i • N_i,      ρ_i ≠ 0.
```

The axis fixes the sign of `ρ_i`.  Because `A` lies in the positive cone of the edge rays,

```text
A = ∑ j, λ j • W j,      λ j > 0.
```

For the supporting face `f_i`, all terms satisfy `⟪N_i,W_j⟫ ≤ 0`, the two incident terms are zero, and at least one nonincident link edge exists.  For that nonincident edge, strict support gives `< 0`.  Therefore

```text
⟪N_i, A⟫ = ∑ j, λ j * ⟪N_i,W_j⟫ < 0.
```

The angular order is chosen so that consecutive projected rays turn positively around `A`, i.e.

```text
0 < det3 W_i W_{i+1} A = ⟪cross W_i W_{i+1}, A⟫.
```

Combining with `cross W_i W_{i+1} = ρ_i • N_i` and `⟪N_i,A⟫ < 0` gives `ρ_i < 0`.  Put `c_i = -ρ_i > 0`.  Then

```text
cross W_i W_{i+1} = - c_i • N_i
```

and hence

```text
∀ z, det3 W_i W_{i+1} z = - c_i * ⟪N_i,z⟫.
```

This is the exact sign convention already used by the repo’s Euclidean bridge: determinant support is positive because the outward normal points to the negative side of all other vertices.

A good theorem surface is:

```lean
import ProofsInTheBook.ZinanCh13EuclLink
import ProofsInTheBook.Ch13VertexStar
import ProofsInTheBook.PolygonTurning

noncomputable section
open scoped Classical RealInnerProductSpace BigOperators
open ProofsInTheBook.SphericalKernel
open ProofsInTheBook.Ch13VertexStar
open ProofsInTheBook.Ch13Euclidean
open ProofsInTheBook.Ch13EuclLink
open ProofsInTheBook.PlanarMap ProofsInTheBook.PlanarMap.CombMap

namespace ProofsInTheBook.Ch13VertexLinkConvexityDesign

variable {D : Type*} [Fintype D] [DecidableEq D]
variable {M : CombMap D}

/-- New replacement for `orientedTriangleSupport_of_rotationFaithful`.

The old theorem used `RotationFaithful` to orient the cross product.  The new
one should use:
* face-plane data to prove `cross (edgeVec P d) (edgeVec P (σ⁻¹ d))` is
  parallel to `outward_normal (dartFace d)`;
* `A` in the positive edge cone to prove `⟪N,A⟫ < 0`;
* angular-order positivity `0 < det3 (edgeVec P d) (edgeVec P (σ⁻¹ d)) A`
  to choose the sign.
-/
theorem orientedTriangleSupport_of_axisFace
    (P : TriangulatedEuclideanPolyhedron M)
    (A : E3) (d : D)
    -- `A` is the chosen axis.  In production this should be your landed
    -- `AxisPositiveConeForEdge`/positive-cone certificate at `tail d`.
    (haxis_pos_cone : True)
    -- Angular order convention for the consecutive pair.
    (hturnA : 0 < det3 (edgeVec P d) (edgeVec P (M.σ.symm d)) A)
    -- There is a nonincident edge in the positive cone, used to prove
    -- `⟪outward_normal (dartFace d), A⟫ < 0`.
    (hoff_exists : True) :
    OrientedTriangleSupport P (M.tail d) (M.head d) (M.head (M.σ.symm d)) := by
  -- Proof skeleton:
  -- 1. Let `N := P.outward_normal (M.dartFace d)`.
  -- 2. Use `face_plane_head_sub_tail P d` and
  --    `face_plane_head_sigma_symm_sub_tail P d` to show `N ⟂ W_i,W_{i+1}`.
  -- 3. Use face nondegeneracy to show `W_i,W_{i+1}` are linearly independent,
  --    hence `cross W_i W_{i+1} ≠ 0`.
  -- 4. Use the 3D orthogonal-complement/parallel lemma to obtain
  --    `cross W_i W_{i+1} = ρ • N`.
  -- 5. Prove `⟪N,A⟫ < 0` from the positive-cone expression for `A` and
  --    `face_support_from_dart_tail`/`face_support_strict` for an off-face edge.
  -- 6. Combine with `hturnA` to prove `ρ < 0`; set `c = -ρ`.
  -- 7. Fill the `OrientedTriangleSupport` fields:
  --    * `det_eq` from `cross = -c • N` and `det3_eq_inner_cross`;
  --    * `support` from `face_support_from_dart_tail`;
  --    * `eq_iff` from `face_support_strict` plus
  --      `faceVertex_eq_tail_or_head_or_tail_phi2_of_dartFace_eq` and
  --      `tail_phi_phi_eq_head_sigma_symm_of_triangular_euclidean`.
  -- This theorem is intentionally a surface for the replacement proof.
  sorry

end ProofsInTheBook.Ch13VertexLinkConvexityDesign
```

The placeholders `True` in this design surface should be replaced by your actual axis-positive-cone certificate and the already-proved angular-turn lemma for consecutive sorted rays.

## 3. Reuse the existing `VertexLinkGeometry` / `VertexStar` pipeline

Do **not** rebuild `StrictConvexSphPolygon` field-by-field at the final site.  The repo already has a clean two-stage bridge:

1. `ZinanCh13EuclLink.VertexLinkGeometry` packages:
   * `nbr : Fin (n+1) → Vertex`,
   * `oriented : ∀ i, OrientedTriangleSupport P v (nbr i) (nbr (i+1))`,
   * `nbr_apex_ne`,
   * `nonincident`.

2. `VertexLinkGeometry.toVertexStar` derives the raw `VertexStar.turn_support`, `turn_strict`, and `open_hemi` fields.

3. `Ch13VertexStar.VertexStar.vertexLink_strictArm` derives the spherical link.  Its `closed_convex` field is exactly the desired `StrictConvexSphPolygon`.

The small extraction lemma is:

```lean
import ProofsInTheBook.ZinanCh13EuclLink
import ProofsInTheBook.Ch13VertexStar

noncomputable section
open scoped Classical RealInnerProductSpace BigOperators
open ProofsInTheBook.SphericalKernel
open ProofsInTheBook.Ch13VertexStar
open ProofsInTheBook.Ch13EuclLink
open ProofsInTheBook.PlanarMap ProofsInTheBook.PlanarMap.CombMap

namespace ProofsInTheBook.Ch13VertexLinkConvexityDesign

variable {D : Type*} [Fintype D] [DecidableEq D]
variable {M : CombMap D}
variable {P : TriangulatedEuclideanPolyhedron M} {v : M.Vertex}

/-- Once local oriented face supports are packaged as `VertexLinkGeometry`,
the repo already proves the strict convex spherical link. -/
theorem strictConvexSphPolygon_of_vertexLinkGeometry
    (LG : VertexLinkGeometry P v) :
    StrictConvexSphPolygon (LG.toVertexStar.vertexLink) :=
  LG.toVertexStar.vertexLink_strictArm.closed_convex

/-- Even more abstractly: any `VertexStar` immediately gives the closed strict
convex spherical polygon of normalised raw edge directions. -/
theorem strictConvexSphPolygon_of_vertexStar (S : VertexStar) :
    StrictConvexSphPolygon S.vertexLink :=
  S.vertexLink_strictArm.closed_convex

end ProofsInTheBook.Ch13VertexLinkConvexityDesign
```

This is the cleanest final target.  Your new work should only replace the old `RotationFaithful` constructor of `VertexLinkGeometry`:

```lean
vertexLinkGeometryOfEuclidean
  (P : TriangulatedEuclideanPolyhedron M)
  (hfaith : RotationFaithful P) ... : VertexLinkGeometry P v
```

by a constructor of the same shape that takes the axis/fan-orientation certificate instead of `hfaith`:

```lean
noncomputable def vertexLinkGeometryOfEuclidean_axis
    (P : TriangulatedEuclideanPolyhedron M)
    (hsimple : M.IsSimpleGraph)
    (v : M.Vertex) (hdeg : 3 ≤ vDeg P v)
    (haxis : AxisPositiveConeForEdge P v)          -- your landed certificate
    (halign : AngularOrderMatchesReverseSigma P v haxis) :
    VertexLinkGeometry P v := by
  classical
  refine
    { n := starN P v
      hn := starN_ge_two P v hdeg
      nbr := reverseLinkNbr P v hdeg
      nbr_is_sigma := ?_
      oriented := ?_
      nbr_apex_ne := reverseLinkNbr_apex_ne P v hdeg
      nonincident := reverseLink_nonincident_of_simple P hsimple v hdeg }
  · refine ⟨hdeg, rfl, ?_⟩
    intro i
    rfl
  · intro i
    -- Let `d := reverseLinkDart P v hdeg i`.  The existing fan lemma gives
    -- `reverseLinkDart P v hdeg (i+1) = M.σ.symm d`.
    -- Feed `d`, the axis sign for this adjacent pair, and the off-face witness
    -- into `orientedTriangleSupport_of_axisFace`.
    sorry
```

The body is almost identical to the current `vertexLinkGeometryOfEuclidean`; only the `oriented` field changes.  All the nonincident bookkeeping is already present.

## 4. Cyclic indexing: reverse-`σ` is the correct face fan order

The repo has the relevant fan lemmas already in `ZinanCh13EuclLink`.

Use the reverse-`σ` order:

```lean
def reverseLinkDart (P : TriangulatedEuclideanPolyhedron M) (v : M.Vertex)
    (hdeg : 3 ≤ vDeg P v) (i : Fin (starN P v + 1)) : D :=
  incidentDartOfStarIndex P v hdeg (Fin.rev i)
```

The successor theorem is:

```lean
theorem reverseLinkDart_add_one
    (P : TriangulatedEuclideanPolyhedron M) (v : M.Vertex)
    (hdeg : 3 ≤ vDeg P v) (i : Fin (starN P v + 1)) :
    reverseLinkDart P v hdeg (i + 1) = M.σ.symm (reverseLinkDart P v hdeg i)
```

For a triangular face, the third face vertex is the head of that reverse successor:

```lean
theorem tail_phi_phi_eq_head_sigma_symm_of_triangular_euclidean
    (P : TriangulatedEuclideanPolyhedron M) (d : D) :
    M.tail (M.φ (M.φ d)) = M.head (M.σ.symm d)
```

And the face vertices are classified by:

```lean
theorem faceVertex_eq_tail_or_head_or_tail_phi2_of_dartFace_eq
    (P : TriangulatedEuclideanPolyhedron M) {f : M.Face} {e : D}
    (he : M.dartFace e = f) (k : Fin 3) :
    P.faceVertex f k = M.tail e ∨
      P.faceVertex f k = M.head e ∨
      P.faceVertex f k = M.tail (M.φ (M.φ e))
```

Together these say exactly:

```text
face f_i = dartFace d_i
has vertices v, head d_i, head d_{i+1}
where d_{i+1} = σ⁻¹ d_i.
```

That is the face fan needed for `StrictConvexSphPolygon`.

### Aligning this with the angular order

There are two clean options.

**Preferred option:** define the link tuple using `reverseLinkDart`, then prove separately that the angular sort returns this tuple up to cyclic shift.  Since all subsequent Cauchy data is cyclic, a shift is cheap and avoids threading sorted-list details through the geometry proof.

The useful statement is:

```lean
structure AngularOrderMatchesReverseSigma
    (P : TriangulatedEuclideanPolyhedron M) (v : M.Vertex)
    (haxis : AxisPositiveConeForEdge P v) : Prop where
  shift : Fin (vDeg P v)
  sorted_eq_shifted_reverseSigma : True
```

Replace `True` by the actual equality between your angular sorted dart list and
`fun i => reverseLinkDart P v hdeg (i + shift)`.

**Alternative option:** if the sorted angular tuple is already fixed as `d_geo : Fin N → D`, package the fan alignment directly:

```lean
structure AngularFaceFan
    (P : TriangulatedEuclideanPolyhedron M) (v : M.Vertex)
    {N : ℕ} (d_geo : Fin N → D) : Prop where
  three_le : 3 ≤ N
  tail : ∀ i, M.tail (d_geo i) = v
  succ : ∀ i, d_geo (i + 1) = M.σ.symm (d_geo i)
  nodup_or_injective : Function.Injective d_geo
```

Then the `oriented` field for index `i` uses `d_geo i`, and `succ` identifies `d_geo (i+1)` with `σ⁻¹(d_geo i)`.

The key point is that the `StrictConvexSphPolygon` proof should consume this alignment as a small combinatorial certificate.  The proof of alignment itself belongs next to the angular-sort code, not inside the face-support-to-spherical-convexity bridge.

## 5. Is `strict_nonincident` exactly `face_support_strict`?

Yes.  For the edge `(i,i+1)` of the link, `strict_nonincident` asks:

```lean
j ≠ i → j ≠ i + 1 →
  0 < sOrient (Q i) (Q (i + 1)) (Q j)
```

Under the oriented support identity, this is exactly:

```text
j not an endpoint of face edge
⇒ nbr j not in the triangular face f_i
⇒ ⟪N_i,W_j⟫ < 0                         -- face_support_strict
⇒ det3 W_i W_{i+1} W_j > 0
⇒ sOrient Q_i Q_{i+1} Q_j > 0.
```

What is needed to prove `nbr j` is off the face?

* `M.IsSimpleGraph`, via the existing
  `reverseLinkNbr_injective_of_simple` and
  `reverseLink_nonincident_of_simple`, to rule out loops and repeated neighbor vertices.
* The triangular face classification
  `faceVertex_eq_tail_or_head_or_tail_phi2_of_dartFace_eq`, plus
  `tail_phi_phi_eq_head_sigma_symm_of_triangular_euclidean`, to identify the three face vertices as
  `v`, `nbr i`, and `nbr (i+1)`.

A separate global `4 ≤ V` hypothesis is not the right local requirement.  The local requirement is degree `≥ 3`, i.e. `n + 1 ≥ 3`; the repo already has

```lean
theorem exists_fin_not_incident_edge {n : ℕ} (hn : 2 ≤ n) (i : Fin (n + 1)) :
    ∃ j : Fin (n + 1), j ≠ i ∧ j ≠ i + 1
```

and `VertexStar.exists_noninc`.  This gives an off-face edge for each face, including the triangle-degree case where there is exactly one.  Global `4 ≤ V` follows in many embedded triangulations, but it should not be threaded as the formal local hypothesis.

## 6. Where `PolygonTurning` fits

For this proof, `PolygonTurning` is not the main tool.  Its public names such as

```lean
ProofsInTheBook.PolygonTurning.extAngle
ProofsInTheBook.PolygonTurning.turning
ProofsInTheBook.PolygonTurning.turning_closed_eq_zero
```

are for the Ch36 planar simple-polygon turning-number development.  They do not discharge `StrictConvexSphPolygon.edge_support` or `strict_nonincident`; those are face-halfspace facts plus determinant sign transfer.

Use `PolygonTurning` only if you decide to prove a global theorem that the angularly sorted projected fan has the same cyclic order as the CombMap fan by a planar polygon/Umlaufsatz route.  That is overkill here.  The local bridge should instead use:

* `ZinanCh13EuclLink.reverseLinkDart_add_one`,
* `ZinanCh13EuclLink.reverseLinkNbr_add_one`,
* `ZinanCh13EuclLink.faceVertex_eq_tail_or_head_or_tail_phi2_of_dartFace_eq`,
* `ZinanCh13EuclLink.tail_phi_phi_eq_head_sigma_symm_of_triangular_euclidean`,
* `ZinanCh13EuclLink.reverseLink_nonincident_of_simple`,
* `ZinanCh13EuclLink.OrientedTriangleSupport`,
* `ZinanCh13EuclLink.VertexLinkGeometry.toVertexStar`, and
* `Ch13VertexStar.VertexStar.vertexLink_strictArm`.

## 7. Recommended implementation route

1. **Keep the link points raw-normalised.**
   Define the spherical link as `VertexStar.edgeDir`, not normalised projections.  The angular projections only choose the cyclic order.

2. **Prove one new local theorem replacing `RotationFaithful`:**

   ```lean
   orientedTriangleSupport_of_axisFace
   ```

   It should build `OrientedTriangleSupport P v (nbr i) (nbr (i+1))` from:
   * face-plane perpendicularity,
   * face nondegeneracy,
   * axis positive-cone membership,
   * positive angular turn about the axis, and
   * face support/strict support.

3. **Build `VertexLinkGeometry` in reverse-σ/angular order.**
   Copy the current `vertexLinkGeometryOfEuclidean` constructor, but replace the `hfaith` call in the `oriented` field by the new theorem.

4. **Do not reprove the spherical fields.**
   Finish with:

   ```lean
   exact (vertexLinkGeometryOfEuclidean_axis P hsimple v hdeg haxis halign).toVertexStar
     |>.vertexLink_strictArm
     |>.closed_convex
   ```

5. **If the final theorem is stated for the angular sorted tuple**, add a cyclic-shift/definitional equality lemma between the angular tuple and the reverse-σ tuple.  Keep that as an order-alignment lemma, separate from the face-support convexity proof.

Bottom line: the face supporting halfspaces prove the `edge_support` and `strict_nonincident` fields exactly, but only after the signed identity

```text
det3 W_i W_{i+1} z = -c_i * ⟪outward_normal f_i,z⟫,   c_i>0
```

has been derived.  The correct axis supplies the sign of `c_i`; `M.IsSimpleGraph` and the triangular face-fan lemmas supply the off-face/nonincident bookkeeping; `Ch13VertexStar` already converts the resulting raw `VertexStar` into `StrictConvexSphPolygon`.
