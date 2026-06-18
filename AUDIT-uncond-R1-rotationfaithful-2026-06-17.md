Yes: **Option A is the clean Lean fix.** Do **not** try to derive the sign from face halfspaces alone. Add a small orientation-faithfulness hypothesis saying that the combinatorial rotation `σ` is the one induced by the outward geometric orientation. Then derive `VertexLinkGeometry`; do not carry it.

The decisive point is the sign convention. With your support convention

```lean
⟪outward_normal F, pos w - face_point F⟫ ≤ 0
```

and with link convexity wanted as

```lean
0 ≤ det3 edgeDir_i edgeDir_{i+1} edgeDir_j
-- strict for j not i or i+1
```

the outward face normal for the face between `d` and `σ d` must point along the **reversed** cross product:

```lean
edgeVec (σ d) × edgeVec d
```

not along

```lean
edgeVec d × edgeVec (σ d)
```

unless your `det3` convention is the opposite.

## 1. Minimal field

Use Option A. The clean field is per dart / per face-corner:

```lean
/-- The combinatorial rotation `σ` agrees with the outward geometric orientation.

Here `faceBetween d` is the face whose boundary contains `α d` followed by `σ d`,
so it is the triangular face incident to the two outgoing darts `d` and `σ d`
at `tail d`.

With the halfspace convention `normal · (w - facePoint) ≤ 0`, this is the
sign needed to prove

  `det3 (edgeDir d) (edgeDir (σ d)) (edgeDir e) ≥ 0`.

-/
structure RotationFaithful (P : TriangulatedEuclideanPolyhedron) : Prop where
  outward_normal_eq_pos_smul_rev_cross :
    ∀ d : P.Dart,
      ∃ λ : ℝ, 0 < λ ∧
        P.outwardNormal (P.faceBetween d)
          =
        λ • (P.edgeVec (P.σ d) ×₃ P.edgeVec d)
```

If you prefer the truly minimal mathematical axiom, store only the sign:

```lean
structure RotationFaithful (P : TriangulatedEuclideanPolyhedron) : Prop where
  outward_normal_pos_rev_cross :
    ∀ d : P.Dart,
      0 <
        ⟪ P.outwardNormal (P.faceBetween d),
          P.edgeVec (P.σ d) ×₃ P.edgeVec d ⟫
```

Given `face_plane`, nondegeneracy, and the fact that both vectors are normals to the same triangular face plane, the dot-product version implies the positive-smul version. But in Lean, the positive-smul version is usually much easier downstream. It is not carrying link convexity; it is only carrying the missing orientation sign.

So my recommendation is:

```lean
outward_normal_eq_pos_smul_rev_cross
```

as the field, or add the dot field plus immediately prove:

```lean
lemma outward_normal_eq_pos_smul_rev_cross_of_faithful :
  ∀ d, ∃ λ : ℝ, 0 < λ ∧
    outwardNormal (faceBetween d)
      =
    λ • (edgeVec (σ d) ×₃ edgeVec d)
```

Then use only the positive-smul lemma in the link proof.

This is a genuine convex-polytope property. A real convex polytope boundary has a canonical outward orientation, and the cyclic order of edge germs at each vertex is induced by that orientation. Your field says that the stored `σ` is that cyclic order. Without such a field, reversing the cyclic order changes all link determinants’ signs while preserving the unoriented face-support data, so the desired theorem is simply false.

Option B, “connectedness plus one base orientation propagates globally,” is mathematically fine only after you have a serious oriented-map propagation library. In Lean it is not the clean path. You can later prove:

```lean
theorem RotationFaithful.of_connected_oriented_boundary
  ...
  (hbase : base_orientation_sign) :
  RotationFaithful P
```

but Chapter 13 should consume `RotationFaithful`, not reprove global orientation propagation.

## 2. Derivation of global link convexity

Fix a vertex `v`, a dart `d` with `tail d = v`, and let

```lean
a := edgeVec d
b := edgeVec (σ d)
F := faceBetween d
n := outwardNormal F
```

Let `e` be any other incident dart at `v`, and set

```lean
x := edgeVec e
```

The face `F` is the face between the consecutive link edges `d` and `σ d`. Since `F` is a global supporting face, for every vertex `w`,

```lean
⟪n, pos w - facePoint F⟫ ≤ 0
```

and strictly `< 0` when `w` is off `F`.

Because `v = tail d` lies on `F`, you get the translated version

```lean
⟪n, pos (head e) - pos v⟫ ≤ 0
```

that is,

```lean
⟪n, edgeVec e⟫ ≤ 0.
```

If `e` is not `d` and not `σ d`, then `head e` is not a vertex of the triangular face `F`, so strict support gives

```lean
⟪n, edgeVec e⟫ < 0.
```

Now use faithfulness:

```lean
n = λ • (b ×₃ a),  with  0 < λ.
```

Therefore the non-strict support inequality becomes:

```lean
⟪λ • (b ×₃ a), x⟫ ≤ 0
```

so

```lean
λ * ⟪b ×₃ a, x⟫ ≤ 0.
```

Since `λ > 0`,

```lean
⟪b ×₃ a, x⟫ ≤ 0.
```

Using anticommutativity of cross product,

```lean
b ×₃ a = -(a ×₃ b),
```

so

```lean
0 ≤ ⟪a ×₃ b, x⟫.
```

Equivalently,

```lean
0 ≤ det3 a b x.
```

For strict support, the same argument gives:

```lean
⟪n, x⟫ < 0
```

hence

```lean
⟪b ×₃ a, x⟫ < 0
```

hence

```lean
0 < ⟪a ×₃ b, x⟫
```

that is,

```lean
0 < det3 a b x.
```

Then normalize. Since

```lean
edgeDir d = ‖edgeVec d‖⁻¹ • edgeVec d
```

and all edge lengths are positive,

```lean
det3 (edgeDir d) (edgeDir (σ d)) (edgeDir e)
  =
(‖a‖⁻¹ * ‖b‖⁻¹ * ‖x‖⁻¹) * det3 a b x
```

with positive scalar factor. So nonnegativity and strict positivity survive normalization.

The important Lean theorem should look like this:

```lean
lemma link_side_support
    (P : TriangulatedEuclideanPolyhedron)
    (hfaith : RotationFaithful P)
    (d e : P.Dart)
    (he_tail : P.tail e = P.tail d) :
    0 ≤
      det3
        (P.edgeDir d)
        (P.edgeDir (P.σ d))
        (P.edgeDir e) := by
  -- use support of `faceBetween d`
  -- use `hfaith.outward_normal_eq_pos_smul_rev_cross d`
  -- flip `edgeVec (σ d) × edgeVec d` to `-(edgeVec d × edgeVec (σ d))`
  -- divide by positive norms
  ...
```

and the strict version:

```lean
lemma link_side_strict
    (P : TriangulatedEuclideanPolyhedron)
    (hfaith : RotationFaithful P)
    (d e : P.Dart)
    (he_tail : P.tail e = P.tail d)
    (hne_left : e ≠ d)
    (hne_right : e ≠ P.σ d) :
    0 <
      det3
        (P.edgeDir d)
        (P.edgeDir (P.σ d))
        (P.edgeDir e) := by
  -- same proof, but use `face_support_strict`
  ...
```

The one required combinatorial lemma is:

```lean
lemma head_not_mem_faceBetween_of_incident_ne
    (d e : P.Dart)
    (he_tail : P.tail e = P.tail d)
    (hne_left : e ≠ d)
    (hne_right : e ≠ P.σ d) :
    P.head e ∉ P.verticesOfFace (P.faceBetween d)
```

or the equivalent indexed-link statement:

```lean
lemma link_vertex_off_faceBetween
    {v : P.Vertex} {i j : Fin (P.valence v)}
    (hj₁ : j ≠ i)
    (hj₂ : j ≠ i + 1) :
    P.linkNeighbor v j ∉ P.verticesOfFace (P.faceBetween (P.linkDart v i))
```

This is not a new convexity assumption. It is just the triangulation/no-duplicate-neighbor fact saying that the triangular face between consecutive darts at `v` has exactly the two corresponding neighboring vertices.

So the global convexity proof does **not** compose local turns around the vertex. It is simpler: each consecutive pair of link vertices comes from an actual supporting face of the polyhedron, and that supporting plane contains **all** vertices on the inward side. Intersect that global halfspace with the unit sphere centered at `v`, and you get the supporting great circle for the spherical link edge.

## 3. Non-vacuity: regular tetrahedron

Yes, the strengthened structure is inhabited.

For the tetrahedron with vertices

```text
A = ( 1,  1,  1)
B = ( 1, -1, -1)
C = (-1,  1, -1)
D = (-1, -1,  1)
```

take the σ-order at `A` compatible with positive link determinants as

```text
C → B → D → C
```

up to cyclic rotation.

For the side `C → B`, set

```text
a = C - A = (-2,  0, -2)
b = B - A = ( 0, -2, -2)
```

Then

```text
b × a = (4, 4, -4),
```

which is an outward normal to face `ABC`: the remaining vertex `D` satisfies

```text
(4, 4, -4) · (D - A) = -16 < 0.
```

Also the link determinant against the remaining direction `D - A` is positive:

```text
det3 (C - A) (B - A) (D - A) = 16 > 0.
```

The other two corners at `A` work the same way:

```text
B → D :  (D - A) × (B - A) = ( 4, -4,  4)
D → C :  (C - A) × (D - A) = (-4,  4,  4)
```

Those are the outward normals to `ABD` and `ACD`, respectively. The same verification holds at the other vertices by symmetry.

So if your “standard rotation” is the one used by your hand-built `tetraVertexLinkGeometry`, then yes, it satisfies the faithfulness field. If your stored σ-order at `A` is instead `B → C → D`, then it is the opposite convention: either your `det3` convention is reversed, or that σ is the inward/reversed rotation for the field above.

## 4. Where to put the field

Do **not** add this directly to the raw `TriangulatedEuclideanPolyhedron` if that record is used broadly by `b1`, `b2`, `R1`–`R4`, examples, and intermediate constructions. That will ripple everywhere.

The cleanest low-ripple design is:

```lean
structure RotationFaithful (P : TriangulatedEuclideanPolyhedron) : Prop where
  outward_normal_eq_pos_smul_rev_cross :
    ∀ d : P.Dart,
      ∃ λ : ℝ, 0 < λ ∧
        P.outwardNormal (P.faceBetween d)
          =
        λ • (P.edgeVec (P.σ d) ×₃ P.edgeVec d)
```

Then put it on the convex/geometric level that currently needs link geometry:

```lean
structure ConvexEuclideanPolyhedron extends TriangulatedEuclideanPolyhedron where
  rotation_faithful : RotationFaithful toTriangulatedEuclideanPolyhedron
  -- existing face_supporting_halfspace
  -- existing face_support_strict
  -- existing nondegeneracy / triangulation fields
```

If you currently have a field like

```lean
vertexLinkGeom : ∀ v, VertexLinkGeometry ...
```

replace it by

```lean
rotation_faithful : RotationFaithful ...
```

and then define:

```lean
noncomputable def vertexLinkGeometryOfEuclidean
    (P : ConvexEuclideanPolyhedron)
    (v : P.Vertex) :
    VertexLinkGeometry (P.edgeDirAt v) := by
  refine
  { unit := ?_
    turn_support := ?_
    turn_strict := ?_
    -- other fields
  }
  · -- unit directions from normalization
    ...
  · -- use `link_side_support`
    ...
  · -- use `link_side_strict`
    ...
```

For downstream compatibility, you can restore dot notation:

```lean
namespace ConvexEuclideanPolyhedron

noncomputable def vertexLinkGeom
    (P : ConvexEuclideanPolyhedron)
    (v : P.Vertex) :
    VertexLinkGeometry (P.edgeDirAt v) :=
  vertexLinkGeometryOfEuclidean P v

end ConvexEuclideanPolyhedron
```

Then much existing code can still say:

```lean
P.vertexLinkGeom v
```

but it is now derived, not carried.

So the final recommendation is:

1. Keep raw `TriangulatedEuclideanPolyhedron` unchanged.
2. Add `RotationFaithful` as a small `Prop` mixin or field at the convex polyhedron level.
3. Remove the carried `vertexLinkGeom` field.
4. Prove `vertexLinkGeometryOfEuclidean` from:
   - `face_supporting_halfspace`,
   - `face_support_strict`,
   - triangulation/no-duplicate-neighbor lemmas,
   - positive edge lengths,
   - `RotationFaithful`.
5. Reintroduce `P.vertexLinkGeom v` as a derived def for bounded rework.

That gives exactly what you want: Chapter 13 no longer assumes vertex-link convexity as extra data. It derives it from face-level convexity plus the honest missing fact that `σ` is the outward geometric rotation system.
