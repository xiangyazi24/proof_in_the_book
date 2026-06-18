Your current face-level convexity is **enough for `open_hemi` if paired with the usual finite vertex/star-incidence facts**, but it is **not enough by itself for `turn_support/turn_strict` unless you also connect the oriented face normals to the σ-order of the two incident edge-vectors**.

The clean design is: do **not** posit `turn_strict` directly. Instead add a small, geometric, per-oriented-face certificate saying “the oriented triangle `(v,pᵢ,pᵢ₊₁)` is a supporting face with the correct determinant orientation.” Then `turn_support/turn_strict` are one-line specializations to the neighbor list.

## 1. Does face-level convexity imply `open_hemi`?

Yes, for a finite triangulated convex polyhedron, the usual face halfspaces imply a strict exposing functional at each vertex. You do **not** need to add strict vertex exposure as a primitive if you already have:

```lean
-- For every triangular face f with outward normal n_f:
support :
  ∀ w, inner ℝ n_f (pos w - pos (some vertex of f)) ≤ 0

eq_iff :
  inner ℝ n_f (pos w - pos (some vertex of f)) = 0 ↔ w ∈ f.vertices
```

and the combinatorial star fact:

```lean
∀ w ≠ v, ∃ f ∈ incidentFaces v, w ∉ f.vertices
```

Then define:

```lean
N_v := ∑ f ∈ incidentFaces v, n_f
h_v := - (‖N_v‖)⁻¹ • N_v
```

For any vertex `w ≠ v`, each incident face through `v` gives

```lean
inner ℝ n_f (pos w - pos v) ≤ 0
```

and at least one incident face gives a strict inequality because `w ∉ f.vertices`. Therefore

```lean
inner ℝ N_v (pos w - pos v) < 0
```

so `N_v ≠ 0`, and after normalization:

```lean
inner ℝ h_v (pos w - pos v) > 0.
```

Specializing to incident neighbors gives your `open_hemi`.

Lean skeleton:

```lean
lemma strict_exposing_sum_incident_normals
    (v : Vertex)
    (hstar_sep :
      ∀ w, w ≠ v → ∃ f ∈ incidentFaces v, w ∉ faceVerts f)
    (hsupport :
      ∀ f ∈ incidentFaces v, ∀ w,
        inner ℝ (normal f) (pos w - pos v) ≤ 0)
    (hstrict :
      ∀ f ∈ incidentFaces v, ∀ w,
        inner ℝ (normal f) (pos w - pos v) = 0 ↔ w ∈ faceVerts f) :
    ∃ h : ℝ3, ‖h‖ = 1 ∧
      ∀ w, w ≠ v → 0 < inner ℝ h (pos w - pos v) := by
  classical
  let N : ℝ3 := ∑ f in (incidentFaces v), normal f

  have hN_neg : ∀ w, w ≠ v → inner ℝ N (pos w - pos v) < 0 := by
    intro w hw
    rw [inner_sum]
    -- all summands ≤ 0 by `hsupport`
    -- one summand < 0 by `hstar_sep` + `hstrict`

  have hN_ne : N ≠ 0 := by
    -- pick any neighbor or any w ≠ v; hN_neg w hw contradicts inner 0 = 0
    ...

  refine ⟨-(‖N‖)⁻¹ • N, ?_, ?_⟩
  · simp [norm_smul, hN_ne]
  · intro w hw
    have := hN_neg w hw
    -- inner (-norm⁻¹ • N) (pos w - pos v) = -norm⁻¹ * inner N ...
    positivity
```

If you want `IsExposed` in Mathlib’s sense, Mathlib has an analytic `IsExposed A B` for exposed sets/points, defined via maximizers of a continuous linear functional; it also provides `Set.exposedPoints` and `IsExposed.isExtreme`. But Mathlib explicitly says it reserves “face” for a future polytope-face notion, so this is not yet a complete polytope-face API. citeturn320149view0

For your current `VertexStar.open_hemi`, I would **derive it from incident normals**, not add it as a field.

## 2. Does face-level convexity imply `turn_support/turn_strict`?

Not from the halfspace inequalities alone. You also need an **orientation bridge**:

For the oriented incident face

```lean
(v, pᵢ, pᵢ₊₁)
```

you need to know that its outward normal is aligned with the determinant functional

```lean
z ↦ det3 (pos pᵢ - pos v) (pos pᵢ₊₁ - pos v) z
```

with the correct sign.

Concretely, if your outward normal satisfies

```lean
det3 (pos pᵢ - pos v) (pos pᵢ₊₁ - pos v) z
  = - cᵢ * inner ℝ n_f z
```

for some `0 < cᵢ`, then the face supporting inequality

```lean
inner ℝ n_f (pos w - pos v) ≤ 0
```

immediately gives

```lean
0 ≤ det3 (pos pᵢ - pos v)
         (pos pᵢ₊₁ - pos v)
         (pos w - pos v)
```

and the equality-iff-face condition gives strict positivity for vertices not in that face.

So the local bridge is:

```lean
structure OrientedFaceSupport
    (v a b : Vertex) (f : Face) where
  face_is : faceVerts f = {v, a, b} -- or membership equivalence
  c : ℝ
  c_pos : 0 < c
  det_eq_normal :
    ∀ z : ℝ3,
      det3 (pos a - pos v) (pos b - pos v) z
        = - c * inner ℝ (normal f) z
  support :
    ∀ w, inner ℝ (normal f) (pos w - pos v) ≤ 0
  eq_iff :
    ∀ w, inner ℝ (normal f) (pos w - pos v) = 0 ↔ w ∈ faceVerts f
```

Then for the neighbor sequence:

```lean
lemma turn_support_of_oriented_face_support
    (H : ∀ i, OrientedFaceSupport v (nbr i) (nbr (i+1)) (face i)) :
    ∀ i j,
      0 ≤ det3 (pos (nbr i) - pos v)
               (pos (nbr (i+1)) - pos v)
               (pos (nbr j) - pos v) := by
  intro i j
  have hi := H i
  rw [hi.det_eq_normal]
  have hs := hi.support (nbr j)
  nlinarith [hi.c_pos, hs]

lemma turn_strict_of_oriented_face_support
    (H : ∀ i, OrientedFaceSupport v (nbr i) (nbr (i+1)) (face i))
    (hnbr_not_in_face :
      ∀ i j, j ≠ i → j ≠ i+1 → nbr j ∉ faceVerts (face i)) :
    ∀ i j, j ≠ i → j ≠ i+1 →
      0 < det3 (pos (nbr i) - pos v)
                (pos (nbr (i+1)) - pos v)
                (pos (nbr j) - pos v) := by
  intro i j hji hjnext
  have hi := H i
  rw [hi.det_eq_normal]
  have hs_le := hi.support (nbr j)
  have hs_ne : inner ℝ (normal (face i)) (pos (nbr j) - pos v) ≠ 0 := by
    intro hz
    have : nbr j ∈ faceVerts (face i) := (hi.eq_iff (nbr j)).1 hz
    exact hnbr_not_in_face i j hji hjnext this
  have hs_lt : inner ℝ (normal (face i)) (pos (nbr j) - pos v) < 0 := lt_of_le_of_ne hs_le hs_ne
  nlinarith [hi.c_pos, hs_lt]
```

This avoids proving a general “σ-order equals geometric angular order” theorem. You only need the already-combinatorial fact that `(nbr i, nbr (i+1))` is the face adjacent in σ-order, plus the oriented support certificate for that face.

Can the link be reflex without extra convexity? For a genuine convex polyhedron, no. But in Lean, with only a combinatorial map plus coordinates and weak face halfspaces, you can fail to connect the map’s σ-order to the geometric orientation of the realized triangles. The determinant-orientation certificate is the minimal honest bridge.

## 3. Recommended design

Use option **A**, but make the certificate slightly more local than “pointed convex edge cone with extreme-ray order.”

I would not store `turn_support` / `turn_strict` directly. Store this instead:

```lean
structure LocalVertexConvexity (v : Vertex) where
  nbr : Fin k → Vertex
  face : Fin k → Face

  -- The combinatorial link data:
  nbr_is_sigma_order :
    nbr = combinatorialNeighborsInSigmaOrder M v

  incident_face :
    ∀ i, faceVerts (face i) = {v, nbr i, nbr (i+1)}

  -- The geometric oriented support data:
  oriented_support :
    ∀ i, OrientedFaceSupport pos v (nbr i) (nbr (i+1)) (face i)

  -- The non-adjacent neighbor is not on that triangular face:
  neighbor_not_in_nonincident_face :
    ∀ i j, j ≠ i → j ≠ i+1 → nbr j ∉ faceVerts (face i)
```

Then derive:

```lean
def toVertexStar (LC : LocalVertexConvexity v) : VertexStar := ...
```

with:

* `open_hemi` from the sum of incident normals;
* `turn_support` from `oriented_support.support`;
* `turn_strict` from `oriented_support.eq_iff` plus `neighbor_not_in_nonincident_face`.

This is mathematically honest because `OrientedFaceSupport` is just “this oriented triangle is a supporting face with a specified outward normal.” It is a genuine convex-polytope property, and it is easy to prove for a concrete tetrahedron by determinant arithmetic.

A full `edge-cone extreme rays exactly the neighbors in order` certificate is also honest, but it is heavier than necessary. Mathlib has cone structures, but it does not have an extreme-ray library ready for this purpose.

## 4. Existing Mathlib API

Current Mathlib gives you useful foundations but not the complete bridge.

### Convexity / exposed faces

`Convex` is a predicate for sets closed under segments, with standard closure lemmas and halfspace convexity lemmas such as `convex_halfSpace_le`, `convex_halfSpace_lt`, and `convex_hyperplane` listed in the docs. citeturn229515view0

`convexHull` exists, with lemmas such as `convexHull_pair`, linear/affine image lemmas, and affine-span compatibility. citeturn135049view0

`Set.extremePoints` and `IsExtreme` exist. There are useful characterizations like `mem_extremePoints_iff_forall_segment` and `Convex.mem_extremePoints_iff_convex_sdiff`. citeturn320149view2

`IsExposed` exists and is defined by a continuous linear functional whose maximizers are exactly the exposed set. The docs explicitly say exposed sets are sometimes called faces, but Mathlib reserves “face” for a future polytope-face notion. citeturn320149view0

### Cones

`ConvexCone` exists as a bundled set closed under positive scalar multiplication and addition. The docs also define `Pointed`, `Blunt`, `Flat`, and `Salient` cones. citeturn995947view0

`PointedCone` exists, but note the naming: it is a submodule over nonnegative scalars, i.e. a cone containing `0`, not necessarily “pointed” in the convex-geometry sense of “salient/no line.” The docs say `PointedCone` is equivalent to a convex cone containing `0`. citeturn912601view0

`ProperCone` exists as a closed pointed cone, with the docs describing it as a closed `PointedCone`; the API is aimed at conic programming/Farkas-style duality. citeturn395481view0

I did not find a ready-made extreme-ray API for polyhedral cones. You will likely define your own “ray generated by `u` is extreme among this finite conic hull” if you go that route.

### Angles / Euclidean geometry

`EuclideanSpace ℝ (Fin 3)` is available through the Euclidean geometry/inner-product space API; the docs frame Euclidean geometry in terms of real inner-product spaces and Euclidean affine spaces. citeturn314326view2

`InnerProductGeometry.angle` exists for unoriented vector angles, with `cos_angle`, `angle_comm`, `angle_nonneg`, `angle_le_pi`, normalization/smul lemmas, and sine/cosine formulas. citeturn426047view0

`Orientation.oangle` exists for oriented angles, but the API is for real inner-product spaces with `Module.finrank ℝ V = 2`, not directly for 3D dihedral angles. citeturn314326view1

### Determinants / orientation signs

`Matrix.det` exists with determinant lemmas, including `Matrix.det_fin_three`. The determinant file defines `Matrix.det` as the square matrix determinant and exposes permutation/sign formulas and determinant manipulation lemmas. citeturn755693view0

For `det3`, I would define locally:

```lean
def det3 (u v w : EuclideanSpace ℝ (Fin 3)) : ℝ :=
  Matrix.det (fun i j : Fin 3 =>
    match j with
    | 0 => u i
    | 1 => v i
    | 2 => w i)
```

or use rows instead of columns consistently. Then prove the few needed multilinear/alternating lemmas locally, or use `Matrix.detRowAlternating` if row-based is more convenient.

Mathlib does not give you a complete spherical convex polygon / spherical link order API. Your `VertexStar` and arm lemma should remain repo-local.

## 5. The clean derivation path

I would structure the bridge like this.

### Step 1: Oriented supporting triangular face

```lean
structure OrientedTriangleSupport
    (pos : Vertex → ℝ3) (v a b : Vertex) (face : Face) where
  face_verts : faceVerts face = {v, a, b}
  normal : ℝ3
  normal_unit : ‖normal‖ = 1
  c : ℝ
  c_pos : 0 < c
  det_eq :
    ∀ z : ℝ3,
      det3 (pos a - pos v) (pos b - pos v) z =
        - c * inner ℝ normal z
  support :
    ∀ w : Vertex,
      inner ℝ normal (pos w - pos v) ≤ 0
  eq_iff :
    ∀ w : Vertex,
      inner ℝ normal (pos w - pos v) = 0 ↔ w ∈ faceVerts face
```

This is not circular: it is just your face halfspace plus the missing orientation relation.

### Step 2: Local vertex certificate

```lean
structure VertexLinkGeometry (v : Vertex) where
  nbrs : List Vertex
  faces : List Face
  cyclic_faces :
    ∀ i, faceVerts (faces[i]) = {v, nbrs[i], nbrs[(i+1)%n]}
  oriented :
    ∀ i, OrientedTriangleSupport pos v nbrs[i] nbrs[(i+1)%n] faces[i]
  nbrs_nodup : nbrs.Nodup
  nonincident :
    ∀ i j, j ≠ i → j ≠ (i+1)%n → nbrs[j] ∉ faceVerts faces[i]
```

### Step 3: Derive `VertexStar`

```lean
def VertexLinkGeometry.toVertexStar : VertexStar where
  o := pos v
  pts := nbrs.map pos
  open_hemi := strict_exposure_from_sum_normals ...
  turn_support := by
    intro i j
    exact turn_support_of_oriented_face_support (oriented i) j
  turn_strict := by
    intro i j hji hjnext
    exact turn_strict_of_oriented_face_support (oriented i) j hji hjnext
```

### Step 4: Later derive `VertexLinkGeometry` from richer convex-polytope data

Only after the bridge works should you try to prove the local certificate from a general `convexHull`/polytope boundary theory.

## 6. Answer to the design choice

Pick **A**, but use the minimal certificate:

```lean
per oriented incident face:
  supporting halfspace + equality iff face vertices + determinant orientation
```

rather than a full extreme-ray cone theory.

Do **not** try B yet. Deriving σ-order, edge-cone extreme rays, strict exposed vertices, and spherical convexity from only face halfspaces is mathematically true for a well-formed convex polyhedron, but formalizing it requires a substantial polyhedral-boundary theory that Mathlib does not currently provide. The per-oriented-face support certificate is honest, non-vacuous, local, and directly checkable for tetrahedra and explicit examples.
