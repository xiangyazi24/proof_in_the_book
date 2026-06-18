# Ch13 orientation audit: determined sign vs irreducible orientation agreement

## Executive answer

The fresh-angle challenge is valid: the strongest possible statement is **not** that `RotationFaithful` is independent of the full realized object.  For a fixed realization in the fixed oriented ambient space `EuclideanSpace ℝ (Fin 3)`, with fixed coordinates, fixed outward normals, and fixed `M.σ`, the sign in `RotationFaithful` is determined.

The correct irreducibility statement is narrower and sharper:

> `RotationFaithful` is determined by the oriented data `(P.pos, P.outward_normal, M.σ)`, but it is not derivable from the mirror-invariant/unoriented convex support data.  The irreducible input for an externally supplied combinatorial map is the agreement that the supplied `M.σ` is the geometric angular rotation, rather than the reverse angular rotation.

So there is no loophole in the mirror argument when it is used against derivability from **unoriented invariants**.  There is a loophole only if the claim is overstated as “independent of the object.”  It is not independent of the full object.

## 1. For fixed `(coords + normal + σ)`, `RotationFaithful` is determined

For one dart `d`, abbreviate

```text
u := edgeVec P (M.σ.symm d)
v := edgeVec P d
n := P.outward_normal (M.dartFace d)
```

The repo convention is

```text
∃ λ : ℝ, 0 < λ ∧ n = λ • cross u v.
```

Under the existing triangular-face nondegeneracy hypotheses, `cross u v ≠ 0`.  The face-plane facts put both `n` and `cross u v` in the normal line to the same triangular face.  Thus there is a scalar `μ` with

```text
n = μ • cross u v.
```

Then the sign of `μ` is read off from the oriented dot product

```text
inner n (cross u v)
```

because

```text
inner n (cross u v) = μ * ‖cross u v‖².
```

Since `‖cross u v‖² > 0`, we have

```text
μ > 0  ↔  inner n (cross u v) > 0.
```

Equivalently, with the repo’s `det3` convention, this is a scalar-triple-product sign check.  Therefore for a fixed `P` and fixed `M.σ`, the winding sign is a concrete proposition determined by the data.  In Lean, a fully general real-coordinate sign may not be computationally decidable without extra numeric certificates, but under classical logic it is a definite proposition; for concrete rational-coordinate examples, it can be proved by case splits and arithmetic normalization.

A useful local lemma to add later is the sign equivalence:

```lean
-- Schematic statement only; names will depend on the final local API.
theorem rotationFaithfulAt_iff_cross_dot_pos
    (P : TriangulatedEuclideanPolyhedron M) (d : D)
    (hcross : cross (edgeVec P (M.σ.symm d)) (edgeVec P d) ≠ 0)
    (hline : ∃ μ : ℝ,
      P.outward_normal (M.dartFace d) =
        μ • cross (edgeVec P (M.σ.symm d)) (edgeVec P d)) :
    (∃ λ : ℝ, 0 < λ ∧
      P.outward_normal (M.dartFace d) =
        λ • cross (edgeVec P (M.σ.symm d)) (edgeVec P d))
    ↔
    0 < inner ℝ (P.outward_normal (M.dartFace d))
      (cross (edgeVec P (M.σ.symm d)) (edgeVec P d))
```

This lemma is deterministic algebra.  It is not where the irreducible orientation content lives.

## 2. What the orientation-reversal argument really proves

Let `R` be an orientation-reversing linear isometry of `ℝ³`, for example reflection in one coordinate.  Transport a realization by

```text
pos' v = R (pos v)
outward_normal' f = R (outward_normal f).
```

Every inner product is preserved:

```text
inner (R x) (R y) = inner x y.
```

Therefore all support and strict-support facts that only mention inner products are preserved:

```text
face_supporting_halfspace
face_support_strict
edge_nondegenerate
face_nondegenerate
positive cone inequalities such as 0 < inner a_v w_d
```

But the cross product changes sign under an orientation-reversing isometry:

```text
cross (R u) (R v) = - R (cross u v).
```

Thus if the original oriented object satisfies

```text
n = λ • cross u v,   λ > 0,
```

then the transported object satisfies

```text
R n = -λ • cross (R u) (R v).
```

For the same stored `M.σ`, the scalar has the opposite sign.  Assuming nondegeneracy, the positive-λ `RotationFaithful` relation fails in the orientation-reversed realization.

This proves:

> No theorem whose hypotheses are all invariant under orientation reversal can imply `RotationFaithful` for an externally supplied `M.σ`.

It does **not** prove:

> `RotationFaithful` is unknowable or independent once the full oriented coordinates and normal field are included.

The orientation-reversed realization is a different point configuration.  It is a counterexample to derivability from invariant hypotheses, not a proof that the fixed object has no determined sign.

## 3. Role of the stored outward normal

The stored outward normal chooses **outside versus inside** of a supporting plane.  That choice is still expressible by inner products:

```text
inner (outward_normal f) (pos v - face_point f) ≤ 0
```

and strict support makes this strict for off-face vertices.  These inequalities survive orientation reversal when normals are transported with the coordinates.

What they do not determine is whether the ordered pair

```text
(edgeVec P (M.σ.symm d), edgeVec P d)
```

has its cross product pointing along the outward normal or against it.  That is exactly the missing agreement between the combinatorial rotation and the oriented embedding.

So the outward normal field reduces `RotationFaithful` to a sign check, but it does not make the sign follow from the unoriented support facts.

## 4. Defining outward normals from coordinates

Yes, the normal field can be defined from coordinates if the face is given as an ordered triangle and an interior point is available.

Given face vertices `p₀,p₁,p₂`, set

```text
rawNormal = cross (p₁ - p₀) (p₂ - p₀).
```

Given an interior point `c`, choose the sign by requiring the interior point to lie in the negative halfspace:

```text
outwardNormal =
  if inner rawNormal (c - p₀) < 0 then rawNormal else -rawNormal.
```

This removes `outward_normal` as an independent stored vector field.  It does not remove the orientation issue, because the ordered triangle and the supplied vertex rotation still have to be compatible.  After normals are defined from coordinates, the remaining field is still one of the following, depending on the convention chosen for the angular order:

```text
M.σ = globalAngularPermOutward P
```

or

```text
M.σ.symm = globalAngularPermPositive P.
```

If `σ` is constructed from the coordinates, then this field becomes true by definition.  That is the construct-`σ` route.

## 5. Is the residual orientation only one Boolean?

Only after a prior theorem has shown that the supplied map is already the correct embedded rotation system up to global reversal.

For a connected orientable sphere embedding, once the unoriented incidence and local cyclic orders are known up to reversal, the remaining coherent choice is essentially one global bit:

```text
σ_geo  versus  σ_geo.symm.
```

But a general stored `M.σ` is an arbitrary permutation.  It could have the wrong local cyclic order at a vertex, not just the wrong global orientation.  Reducing to one Boolean therefore requires a nontrivial unoriented-agreement theorem first.

So the hierarchy is:

1. Arbitrary supplied `σ`: orientation agreement is a full equality `M.σ = σ_geo` or inverse variant.
2. Supplied rotation known correct up to global reversal: remaining choice is one Boolean.
3. `σ` defined as `σ_geo`: no orientation input remains.

## 6. The construct-`σ` endpoint

If the map is constructed from geometry by

```text
σ := globalAngularPermOutward P,
```

then the orientation field disappears.  The remaining obligations are structural:

```text
φ = σ * α matches the triangular face list
FaceRegular 3
IsSimpleGraph
IsSphereMap
```

That is the only way to eliminate orientation input entirely.  Every route that keeps an externally supplied `M.σ` must carry or prove some agreement statement saying that this `σ` is the geometric angular rotation, not the reverse.

## 7. Answers to the questions

### Question 1

The independence is airtight when stated as independence from unoriented or mirror-invariant convex data.  There is no loophole there.

But for a fixed oriented realization with fixed coordinates, fixed outward normals, and fixed `σ`, the sign is determined.  It is read off from

```text
inner (P.outward_normal (M.dartFace d))
  (cross (edgeVec P (M.σ.symm d)) (edgeVec P d)).
```

Thus `RotationFaithful` is a concrete property of `(coords + normal + σ)`, not a separate unknowable structure.

### Question 2

Yes, `outward_normal` can be defined from coordinates, an ordered face, and an interior point.  This removes one stored field.  It does not remove the need for the supplied `σ` to match the oriented embedding.

If the supplied `σ` is already known to be the geometric order up to reversal, the remaining choice is essentially a global Boolean.  If `σ` is constructed canonically from coordinates, even that Boolean disappears.

### Question 3

The sharp true statement is:

> `RotationFaithful` is determined by the oriented realization and the supplied combinatorial rotation.  It is not derivable from the unoriented convex data.  The irreducible input is the agreement that the supplied `M.σ` equals the outward geometric angular rotation, unless `σ` is constructed from the geometry.

Therefore, beyond construct-`σ`, the best reduction is not to keep the old large `RotationFaithful` field.  Replace it by the smaller and more honest field

```text
hgeo : M.σ = globalAngularPermOutward P
```

with the convention fixed by the tetra non-vacuity theorem

```text
tetraMap.σ = globalAngularPermOutward tetraEuclideanPolyhedron.
```

Then prove `RotationFaithful` from `hgeo` by deterministic cross/normal algebra.

## Bottom line

Do not say:

> `RotationFaithful` is independent of the object.

Say:

> For a fixed oriented object, `RotationFaithful` is determined and checkable.  What is not forced by the unoriented convex data is that an externally supplied `σ` is the oriented geometric rotation.  Mirror reflection preserves the support data and flips exactly that agreement.

This is the architecture-relevant conclusion: the orientation input can be reduced to an equality with `σ_geo`, or to a global orientation bit after an up-to-reversal theorem, but it cannot be eliminated for an externally supplied `σ` without constructing `σ` from the coordinates.