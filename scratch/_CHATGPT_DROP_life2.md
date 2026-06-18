# Ch13 §3.3 satisfiability audit for `hgeo`

## Verdict

`hgeo : M.σ = globalAngularPermOutward P` is satisfiable for the existing tetrahedron witness **if and only if** `globalAngularPermOutward` uses the same “outward face” convention as the current repo’s `RotationFaithful` theorem.

For the current tetra data, the stored `tetraMap.σ` is the cycle order

```lean
0 ↦ 1 ↦ 2 ↦ 0
```

at the vertex carried by darts `0,1,2`.  With the **interior** cone axis `a_v`, this is the order for which

```text
det(a_v, edgeVec d, edgeVec (σ d)) < 0.
```

Equivalently, it is the order for which

```lean
outward_normal (dartFace (σ d))
  = positive_scalar • cross (edgeVec d) (edgeVec (σ d))
```

or, in the repo’s existing reverse-predecessor form,

```lean
outward_normal (dartFace d)
  = positive_scalar • cross (edgeVec (σ.symm d)) (edgeVec d)
```

This is exactly the convention certified by the existing theorem

```lean
tetra_rotationFaithful : RotationFaithful tetraEuclideanPolyhedron
```

which proves, for every tetra dart `d`,

```lean
P.outward_normal (reverseFaceBetween tetraMap d)
  = (1 / 4 : ℝ) • cross (edgeVec P (tetraMap.σ.symm d)) (edgeVec P d)
```

So: if `globalAngularPermOutward` is the angular successor in this outward-face-compatible direction, the tetra should satisfy the literal field

```lean
hgeo_tetra : tetraMap.σ = globalAngularPermOutward tetraEuclideanPolyhedron
```

If instead `globalAngularPermOutward` means the usual right-handed positive angular order around the **interior** axis, i.e. the successor with

```text
det(a_v, edgeVec d, edgeVec next) > 0,
```

then the tetra satisfies the inverse relation, not the literal one:

```lean
tetraMap.σ.symm = globalAngularPermPositive tetraEuclideanPolyhedron
-- equivalently
(tetraMap.σ = (globalAngularPermPositive tetraEuclideanPolyhedron).symm)
```

That convention distinction must be frozen before replacing `RotationFaithful` by `hgeo`.

## Concrete tetra check at vertex `tetraPoint₀`

The repo’s tetra coordinates are:

```lean
def tetraPoint₀ : E3 := !₂[(1 : ℝ), 1, 1]
def tetraPoint₁ : E3 := !₂[(1 : ℝ), -1, -1]
def tetraPoint₂ : E3 := !₂[(-1 : ℝ), 1, -1]
def tetraPoint₃ : E3 := !₂[(-1 : ℝ), -1, 1]
```

The dart-to-vertex assignment is constant on the stored `σ`-cycles:

```lean
0, 1, 2     ↦ tetraPoint₀
3, 4, 5     ↦ tetraPoint₁
6, 7, 8     ↦ tetraPoint₂
9, 10, 11   ↦ tetraPoint₃
```

The edge involution begins:

```lean
α 0 = 3
α 1 = 6
α 2 = 9
```

so the outgoing edge rays at `tetraPoint₀` are

```text
w₀ = edgeVec 0 = tetraPoint₁ - tetraPoint₀ = ( 0, -2, -2)
w₁ = edgeVec 1 = tetraPoint₂ - tetraPoint₀ = (-2,  0, -2)
w₂ = edgeVec 2 = tetraPoint₃ - tetraPoint₀ = (-2, -2,  0)
```

The stored vertex rotation is, by `List.formPerm [0,1,2]`,

```text
σ 0 = 1,  σ 1 = 2,  σ 2 = 0,
σ.symm 0 = 2,  σ.symm 1 = 0,  σ.symm 2 = 1.
```

A canonical interior cone axis is the positive sum of the outgoing rays:

```text
a₀ = w₀ + w₁ + w₂ = (-4,-4,-4),
```

or any positive scalar multiple of `(-1,-1,-1)`.  It is strictly inside the tangent cone because

```text
⟪a₀,w₀⟫ = 16,  ⟪a₀,w₁⟫ = 16,  ⟪a₀,w₂⟫ = 16.
```

More generally, if the Stiemke/Gordan construction returns

```text
a = β₀ w₀ + β₁ w₁ + β₂ w₂,   β₀, β₁, β₂ > 0,
```

then the cyclic signs are independent of the exact positive coefficients:

```text
det(a, w₀, w₁) = β₂ det(w₂,w₀,w₁) = -16 β₂ < 0
det(a, w₁, w₂) = β₀ det(w₀,w₁,w₂) = -16 β₀ < 0
det(a, w₂, w₀) = β₁ det(w₁,w₂,w₀) = -16 β₁ < 0.
```

Therefore the stored `σ` order `w₀ → w₁ → w₂ → w₀` is the **negative determinant** angular order around the interior axis.  The positive determinant order around the same interior axis is the reverse order:

```text
w₀ → w₂ → w₁ → w₀.
```

This is the whole satisfiability issue in one line:

```text
interior axis + det < 0  ==> stored tetra σ
interior axis + det > 0  ==> stored tetra σ⁻¹
```

## Cross-product / outward-normal check

The repo’s current `RotationFaithful` convention is not ambiguous.  At dart `0`, the predecessor in the stored cycle is `σ.symm 0 = 2`.  Compute:

```text
cross(w₂,w₀) = cross((-2,-2,0), (0,-2,-2)) = (4,-4,4)
             = 4 · (1,-1,1)
             = 4 · (-tetraPoint₂).
```

The face `dartFace 0` is the triangular face through `tetraPoint₀`, `tetraPoint₁`, and `tetraPoint₃`; the missing tetra vertex is `tetraPoint₂`, so the outward normal is `-tetraPoint₂ = (1,-1,1)`.  Thus

```text
outward_normal (dartFace 0) = (1/4) · cross(edgeVec (σ.symm 0), edgeVec 0).
```

Equivalently, using the successor dart `σ 0 = 1`,

```text
cross(w₀,w₁) = cross((0,-2,-2), (-2,0,-2)) = (4,4,-4)
             = 4 · (1,1,-1)
             = 4 · (-tetraPoint₃),
```

which is the outward normal of the face `dartFace 1`, the face through `tetraPoint₀`, `tetraPoint₂`, and `tetraPoint₁` whose missing vertex is `tetraPoint₃`.

So the stored `σ` is exactly the successor that makes `cross(current,next)` point outward for the triangular face between the two rays.  That is the intended `globalAngularPermOutward` convention.

## Exact satisfiable form of the field

The safe definition is:

```lean
/-- Geometric angular successor with the repo's outward-face convention.
For an interior cone axis `a_v`, this is the successor with negative determinant
around `a_v`, equivalently positive determinant around `-a_v`. -/
noncomputable def globalAngularPermOutward
    {D : Type*} [Fintype D] [DecidableEq D]
    {M : CombMap D} (P : TriangulatedEuclideanPolyhedron M) : Equiv.Perm D :=
  -- per-vertex angular successor satisfying the outward-face convention
  --   det3 (vertexConeAxis P v) (edgeVec P d) (edgeVec P next) < 0
  -- or equivalently
  --   0 < det3 (-vertexConeAxis P v) (edgeVec P d) (edgeVec P next)
  -- for consecutive rays.
  -- Implementation supplied by the Route-A angular-order layer.
  by
    classical
    exact 1  -- placeholder in this note only; not intended as repo code
```

The field should then be literally:

```lean
hgeo : M.σ = globalAngularPermOutward P
```

provided the implementation of `globalAngularPermOutward` is tied to this sign convention by a theorem like:

```lean
/-- Characterization of the outward angular successor. -/
theorem globalAngularPermOutward_spec
    {D : Type*} [Fintype D] [DecidableEq D]
    {M : CombMap D} (P : TriangulatedEuclideanPolyhedron M) (d : D) :
    let e := globalAngularPermOutward P d
    M.tail e = M.tail d ∧
    IsOutwardAngularNext P d e := by
  -- `IsOutwardAngularNext` should encode the negative-det / outward-cross convention.
  -- This theorem is where the convention must be frozen.
  -- Do not leave this as an informal property of the name.
  skip
```

A more concrete convention-free predicate is:

```lean
/-- Successor direction compatible with the existing reverse-`σ` normal formula. -/
def IsOutwardAngularNext
    {D : Type*} [Fintype D] [DecidableEq D]
    {M : CombMap D} (P : TriangulatedEuclideanPolyhedron M) (d e : D) : Prop :=
  M.tail e = M.tail d ∧
  ∃ lam : ℝ, 0 < lam ∧
    P.outward_normal (M.dartFace e) =
      lam • cross (edgeVec P d) (edgeVec P e)
```

Then the tetra satisfiability theorem should target:

```lean
/-- Expected finite satisfiability test once `globalAngularPermOutward` exists. -/
theorem tetra_sigma_eq_globalAngularPermOutward :
    tetraMap.σ = globalAngularPermOutward tetraEuclideanPolyhedron := by
  -- Prove by `ext d`; each dart reduces to one of the four stored 3-cycles.
  -- The local geometric sign checks are exactly the ones already normalized by
  -- `tetra_rotationFaithful`, plus the successor/predecessor rewrite.
  -- This theorem should be added as the non-vacuity guard for `hgeo`.
  ext d
  -- fin_cases d; close with the outward angular successor uniqueness API.
  -- No proof term can be completed in this note because `globalAngularPermOutward`
  -- is not present in the connected repo surface yet.
  skip
```

If the implementation instead defines the angular order by the positive right-handed determinant around `vertexConeAxis`, then the correct satisfiable field is not `hgeo` but one of these:

```lean
hgeo_pos : M.σ.symm = globalAngularPermPositive P
-- or equivalently
hgeo_pos' : M.σ = (globalAngularPermPositive P).symm
```

Do not use a field whose truth for the tetra depends on remembering an informal convention.

## Mirror test: `hgeo` is a genuine orientation datum

`hgeo` is a real orientation field, not a tautology.

Let `R : E3 ≃ₗᵢ[ℝ] E3` be an orientation-reversing isometry, for example reflection in one coordinate.  It preserves the unoriented metric and convex-support data, but reverses every scalar triple product:

```text
det(R a, R u, R v) = - det(a,u,v).
```

So if `globalAngularPermOutward P` gives the stored tetra order `σ`, then for the mirrored realization `R(P)` the same angular rule gives the inverse order:

```text
globalAngularPermOutward (R(P)) = σ⁻¹
```

at every degree-3 vertex.  Since the tetra vertex cycles are genuine 3-cycles, `σ ≠ σ⁻¹`.  Hence

```lean
M.σ = globalAngularPermOutward P
```

holds for one orientation and fails for its mirror.  This is exactly what we need: it is the irreducible orientation input isolated as one field.

The field is therefore neither vacuously true nor vacuously false.  It is satisfiable by the correctly oriented tetra witness under the outward convention, and it is violated by the mirror realization with the same stored combinatorial map.

## Recommended guardrail before using `hgeo`

Before wiring

```lean
rotationFaithful_of_sigma_eq_geo
```

into the ch13 spine, add a tetra non-vacuity theorem to the angular-order file:

```lean
theorem tetra_hgeo_outward :
    tetraMap.σ = globalAngularPermOutward tetraEuclideanPolyhedron := by
  -- finite check + angular successor uniqueness
```

and add the negative test/documented convention lemma:

```lean
/-- Around the interior cone axis, the repo's outward order is the negative-det order. -/
theorem globalAngularPermOutward_det_sign
    {D : Type*} [Fintype D] [DecidableEq D]
    {M : CombMap D} (P : TriangulatedEuclideanPolyhedron M) (d : D) :
    det3 (vertexConeAxis P (M.tail d))
      (edgeVec P d)
      (edgeVec P (globalAngularPermOutward P d)) < 0 := by
  -- This is the convention-free audit hook.
  -- If the theorem proves with `> 0` instead, replace `hgeo` by the inverse form.
  skip
```

That one sign theorem is the best way to prevent a silent inverse-convention bug.

## Bottom line

* For the existing tetra orientation, stored `tetraMap.σ` is `0→1→2` at `tetraPoint₀`.
* With the interior cone axis, this is the negative determinant / outward-face order.
* The existing `tetra_rotationFaithful` theorem confirms the same convention globally on all 12 darts.
* Therefore `hgeo : M.σ = globalAngularPermOutward P` is satisfiable for the tetra **only if** `globalAngularPermOutward` is defined as the outward-face-compatible angular successor.
* If `globalAngularPermOutward` was implemented as the positive right-handed angular order around the interior axis, then the correct field is the inverse form `M.σ.symm = globalAngularPermPositive P`.
* Under the correct convention, `hgeo` is a genuine orientation field: the mirror realization violates it.