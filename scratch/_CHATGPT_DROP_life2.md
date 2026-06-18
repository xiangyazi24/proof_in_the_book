# Ch13 orientation audit: what exactly is irreducible?

## Executive answer

The mirror argument is airtight only for hypotheses that are invariant under orientation reversal.  It does not mean that `RotationFaithful` is independent of the full realized object once that object includes actual coordinates in the fixed oriented space `EuclideanSpace ℝ (Fin 3)`, a concrete outward-normal field, and a concrete permutation `M.σ`.

For a fixed realization `P : TriangulatedEuclideanPolyhedron M`, the truth of `RotationFaithful P` is mathematically determined.  It is the concrete check that the stored predecessor `M.σ.symm d`, the current dart `d`, and the outward normal of `M.dartFace d` have the chosen handedness.

The sharp statement is therefore:

> `RotationFaithful` is determined by `(P.pos, P.outward_normal, M.σ)`, but it is not derivable from the mirror-invariant convex/support data.  The irreducible datum is the agreement that the supplied `M.σ` is the geometric angular rotation rather than its reverse.

So the sloppy statement “`RotationFaithful` is independent of the object” is false.  The precise statement “`RotationFaithful` is independent of the unoriented convex data” is true.

## 1. Fixed coordinates, fixed normals, fixed `σ`: the sign is determined

For one dart `d`, write

```text
u = edgeVec P (M.σ.symm d)
v = edgeVec P d
n = P.outward_normal (M.dartFace d)
```

The current repo convention is

```text
there exists λ > 0 such that n = λ • cross u v.
```

Under the usual triangular face nondegeneracy facts, `cross u v` is nonzero.  The face-plane facts say that both `n` and `cross u v` are normal to the same face plane, so they lie on the same one-dimensional line.  Thus the only remaining datum is the sign of the scalar.

That sign is determined by the dot product

```text
inner n (cross u v)
```

or equivalently by the scalar triple product `det3 u v n`.  If `n = λ • cross u v`, then

```text
inner n (cross u v) = λ * ‖cross u v‖².
```

Since the squared norm is positive, `λ > 0` is equivalent to positivity of that dot product.

So for a fixed `P` and fixed `M.σ`, `RotationFaithful P` is not mysterious.  It is a concrete orientation check.  In Lean, for arbitrary real coordinates this is not automatically decidable by typeclass search, but it is a determined real proposition.  For concrete rational-coordinate witnesses like the tetrahedron, it can often be closed by finite case splits and arithmetic normalization, as the existing tetra proofs do.

## 2. What the mirror argument proves

Let `R` be an orientation-reversing linear isometry of `E3`, such as reflection in one coordinate.  Define a mirrored realization by transporting both coordinates and normals:

```text
pos' v = R (pos v)
outward_normal' f = R (outward_normal f)
```

All inner products are preserved, so the mirror preserves the support and strict-support facts:

```text
face_supporting_halfspace
face_support_strict
edge_nondegenerate
face_nondegenerate
positive cone inequalities such as 0 < inner a_v w_d
```

But an orientation-reversing isometry changes the cross product sign:

```text
cross (R u) (R v) = - R (cross u v).
```

Therefore, if the original realization satisfies

```text
n = λ cross u v with λ > 0,
```

then the mirrored realization satisfies

```text
R n = -λ cross (R u) (R v).
```

The same stored `M.σ` now gives the negative scalar.  The positive-λ form fails, assuming the face is nondegenerate.

This proves exactly that no theorem using only mirror-invariant hypotheses can imply `RotationFaithful` for a supplied `M.σ`.  It does not prove that `RotationFaithful` is unknowable once the oriented coordinates and normals are part of the object.

## 3. The outward normal field does not remove the orientation issue

The current Euclidean structure stores an outward normal field.  This field chooses outside versus inside, but not clockwise versus counterclockwise around the face.

The support condition says

```text
inner (outward_normal f) (pos v - face_point f) ≤ 0
```

and strict support says this is strict for off-face vertices.  These statements use only inner products.  They are preserved by mirror reflection if the normals are reflected too.

Thus the stored outward normal lets us formulate the sign check concretely:

```text
0 < inner (outward_normal (dartFace d))
    (cross (edgeVec (σ⁻¹ d)) (edgeVec d)).
```

But the support inequalities themselves do not force this sign.  They do not know whether the supplied cyclic order `σ` is the geometric order or the reverse geometric order.

## 4. Can normals be defined from coordinates?

Yes.  If a face is supplied as an ordered triple `p₀,p₁,p₂` and we have an interior point `c`, define

```text
rawNormal = cross (p₁ - p₀) (p₂ - p₀).
```

Then choose the sign so that the interior point lies in the negative halfspace.  In prose:

```text
if inner rawNormal (c - p₀) < 0, use rawNormal;
otherwise use -rawNormal.
```

This removes `outward_normal` as an independent field.  It does not remove the orientation problem.  The ordered face triple is itself orientation-sensitive, and an independently supplied `M.σ` still has to match the geometric angular order determined by the coordinates.

After defining normals from coordinates, the remaining orientation statement is still one of these, depending on convention:

```text
M.σ = globalAngularPermOutward P
```

or

```text
M.σ.symm = globalAngularPermPositive P.
```

If `σ` is also defined from coordinates, then the orientation input disappears.  That is exactly the construct-`σ` route.

## 5. Is the remaining datum only a Boolean?

After the unoriented embedded rotation system has already been proved correct up to global reversal, yes: on a connected orientable sphere embedding the remaining choice is essentially the global choice between `σ_geo` and `σ_geo.symm`.

But the current `M : CombMap D` stores an arbitrary permutation `σ`.  Before reducing the residue to one Boolean, one must know that the supplied vertex cycles are the correct geometric cycles at every vertex, merely read in one of the two directions.  That agreement is not part of the pure convex support fields.

So the Boolean description is valid only after a substantial “unoriented agreement” theorem has already established that the supplied map is the right embedded map up to reversal.

## 6. Can the Boolean be removed by defining `σ` from geometry?

Yes.  Define the rotation by geometry:

```text
σ := globalAngularPermOutward P.
```

Then the orientation agreement is true by definition.  The remaining work is no longer the winding sign; it is proving that the constructed map has the expected faces and sphere-map properties:

```text
φ = σ * α matches the triangular face list
FaceRegular 3
IsSimpleGraph
IsSphereMap
```

This is the construct-`σ` route.  It is the only route that truly eliminates the orientation input rather than checking or assuming it.

## 7. Answers to the questions

### Question 1

The independence argument is airtight if stated as independence from mirror-invariant convex data.  There is no contradiction with the fact that `ℝ³` has a fixed standard orientation.  For a fixed coordinate realization with fixed normal field and fixed `σ`, the sign is determined by the scalar triple product.

So `RotationFaithful` is a deterministic property of the full oriented object.  It is not derivable from the unoriented support and strict-support hypotheses alone.

### Question 2

Yes, one can define `outward_normal` from coordinates, an ordered face, and an interior point.  That removes the normal field as separate data.  But the remaining content is exactly that the supplied `σ` is the correctly oriented rotation.  If `σ` is not constructed from coordinates, this remains an orientation agreement field.

If `σ` is constructed from coordinates, the field disappears, but the burden moves to proving that the constructed map agrees with the face list and is a sphere map.

### Question 3

The sharp true statement is:

> `RotationFaithful` is determined by the oriented realization and the supplied combinatorial rotation.  It is not derivable from the unoriented convex data.  The irreducible input for an externally supplied map is the agreement that `M.σ` equals the outward geometric angular rotation, not the scalar equation itself.

The best refactor is therefore to replace the large field

```text
RotationFaithful P
```

by the smaller and more honest orientation-agreement field

```text
M.σ = globalAngularPermOutward P
```

and then prove `RotationFaithful` from that equality plus deterministic cross/normal algebra.

The non-vacuity guard remains the tetra theorem:

```text
tetraMap.σ = globalAngularPermOutward tetraEuclideanPolyhedron
```

with the already-audited convention that `globalAngularPermOutward` is the outward-face-compatible angular successor.

## Bottom line

Do not say “`RotationFaithful` is independent of the object.”  Say:

> For a fixed oriented realization and a fixed `σ`, `RotationFaithful` is determined and checkable.  But a supplied `σ` matching the oriented embedding is not forced by unoriented convexity.  Mirror reflection preserves the support data and flips exactly that match.

Therefore, beyond construct-`σ`, the orientation input can be reduced to a single clean agreement statement, but it cannot be eliminated for an externally supplied combinatorial rotation.