# Ch13 construct-`σ` design: make the rotation geometric, not an input

## Executive verdict

The clean bounded route is **not**:

```lean
-- bad first move
σ := globalAngularPermOutward a_v
-- then try to rediscover the face cycles from σ and α
```

That direction makes the face theorem unnecessarily hard, because `φ = σ * α` is then a theorem about angular order.

The clean route is:

1. Build the dart type from the **outward-oriented triangular face list**:
   `Dart := Σ f : FaceId, Fin 3`.
2. Define the face successor `φ_face` by moving to the next side of the same oriented triangle.
3. Define the edge involution `α` by the unique opposite oriented side of the same geometric edge.
4. Define the combinatorial rotation forced by the face list:

   ```lean
   σ_face := φ_face * α
   ```

5. Prove the local angular agreement theorem:

   ```lean
   σ_geo = σ_face
   ```

6. Instantiate the final `CombMap` with `σ := σ_geo`, `α := α`.  The face agreement is then pure group algebra:

   ```lean
   M.φ = M.σ * M.α = (φ_face * α) * α = φ_face
   ```

This means the faces of the constructed map are exactly the supplied triangles by construction.  The only genuinely geometric theorem in the construct-`σ` layer is the local statement that the angular successor around each vertex is the face-list successor across the opposite dart.  No general “embedded planar graph gives a combinatorial map” theorem is needed for that part.

The major caveat is `IsSphereMap`.  Proving `Connected ∧ eulerChar = 2` from raw convex-supporting-halfspace geometry is a different project.  If the face list carries explicit connectivity and Euler/cardinality certificates, this is bounded.  If those are to be derived from “convex polytope boundary in ℝ³” inside Mathlib, this becomes a major topology/cell-complex development.

## Existing repo interface this should target

The current map core is already exactly the right target:

```lean
structure CombMap (D : Type*) [Fintype D] [DecidableEq D] where
  α : Equiv.Perm D
  σ : Equiv.Perm D
  α_invol : α * α = 1
  α_no_fixed : ∀ d, α d ≠ d

namespace CombMap

def φ (M : CombMap D) : Equiv.Perm D := M.σ * M.α

def Connected (M : CombMap D) : Prop :=
  ∀ a b : D, Relation.ReflTransGen M.dartStep a b

def IsSphereMap (M : CombMap D) : Prop :=
  M.Connected ∧ M.eulerChar = 2

def FaceRegular (M : CombMap D) (p : ℕ) : Prop :=
  ∀ Q : Quotient (cycleSetoid M.φ),
    (Finset.univ.filter (fun x => Quotient.mk (cycleSetoid M.φ) x = Q)).card = p

structure IsSimpleGraph (M : CombMap D) : Prop where
  no_loop : ∀ d : D, M.tail d ≠ M.head d
  no_parallel : ∀ {d e : D}, M.dartEdge d = M.dartEdge e → M.α.SameCycle d e
```

The current Euclidean witness still stores `RotationFaithful`:

```lean
structure RotationFaithful {M : CombMap D}
    (P : TriangulatedEuclideanPolyhedron M) : Prop where
  outward_normal_eq_pos_smul_reverse_cross :
    ∀ d : D,
      ∃ lam : ℝ, 0 < lam ∧
        P.outward_normal (reverseFaceBetween M d) =
          lam • cross (edgeVec P (M.σ.symm d)) (edgeVec P d)
```

The construct-`σ` route should replace this field by a construction theorem.  The downstream `ConvexEuclideanPolyhedron` should eventually receive a constructed `M_geo : CombMap Dart`, plus proofs of `sphere`, `triangle`, and `isSimple`, rather than an externally supplied `M` and a `faithful : RotationFaithful` field.

## Recommended raw data structure

Use face-sides as darts.  Do not introduce an abstract edge set unless another part of the repo already needs it.  The edge set is the `α`-orbit quotient for free.

The following is a design skeleton.  The names are intentionally isolated so the final file can be introduced without touching the existing ch13 spine until the agreement theorem is ready.

```lean
import ProofsInTheBook.PlanarMapSimple
import ProofsInTheBook.ZinanCh13Euclidean
import ProofsInTheBook.SphericalKernel

noncomputable section
open scoped Classical RealInnerProductSpace BigOperators
open ProofsInTheBook.PlanarMap
open ProofsInTheBook.PlanarMap.CombMap

namespace ProofsInTheBook.Ch13ConstructSigma

abbrev E3 : Type := EuclideanSpace ℝ (Fin 3)

/-- A side of an outward-oriented triangular face.  The side `(f,k)` runs from
`tri f k` to `tri f (k+1)`. -/
structure FaceSide (F : Type*) where
  f : F
  k : Fin 3
  deriving DecidableEq

instance {F} [Fintype F] : Fintype (FaceSide F) := by
  classical
  infer_instance

/-- Data for an oriented triangular convex boundary, before any `CombMap` is chosen.

The important point is that `σ` is absent.  We store only the oriented triangular
face successor `φ_face`, the edge pairing `α`, and the geometric angular successor
`σ_geo` to be proved equal to `φ_face * α`. -/
structure OrientedTriBoundaryData
    (V F : Type*) [Fintype V] [DecidableEq V] [Fintype F] [DecidableEq F] where
  pos : V → E3

  /-- Vertices of each triangular face, already ordered so that the normal is outward. -/
  tri : F → Fin 3 → V
  tri_inj : ∀ f, Function.Injective (tri f)

  outward_normal : F → E3
  face_point : F → E3
  face_plane : ∀ f i,
    inner ℝ (outward_normal f) (pos (tri f i) - face_point f) = 0
  face_supporting_halfspace : ∀ f v,
    inner ℝ (outward_normal f) (pos v - face_point f) ≤ 0
  face_support_strict : ∀ f v,
    (∀ i, v ≠ tri f i) →
      inner ℝ (outward_normal f) (pos v - face_point f) < 0

  /-- The cyclic successor inside one oriented triangular face. -/
  φ_face : Equiv.Perm (FaceSide F)
  φ_face_f : ∀ d, (φ_face d).f = d.f
  φ_face_k : ∀ d, (φ_face d).k = d.k + 1

  /-- The unique opposite oriented side of the same geometric edge. -/
  α : Equiv.Perm (FaceSide F)
  α_invol : α * α = 1
  α_no_fixed : ∀ d, α d ≠ d

  /-- Endpoint functions for face sides.  These can be definitions instead of fields
  in the final implementation. -/
  tailV : FaceSide F → V
  headV : FaceSide F → V
  tailV_eq : ∀ d, tailV d = tri d.f d.k
  headV_eq : ∀ d, headV d = tri d.f (d.k + 1)

  /-- Edge pairing reverses endpoints. -/
  α_tail : ∀ d, tailV (α d) = headV d
  α_head : ∀ d, headV (α d) = tailV d

  /-- No two distinct unoriented geometric sides represent different map edges.
  This is the exact certificate that will become `IsSimpleGraph.no_parallel`. -/
  edge_unique : ∀ {d e},
    (tailV d = tailV e ∧ headV d = headV e) ∨
    (tailV d = headV e ∧ headV d = tailV e) →
      α.SameCycle d e

  /-- Geometric angular successor around each vertex, built from the interior cone
  axis `a_v` and the outward winding convention. -/
  σ_geo : Equiv.Perm (FaceSide F)
  σ_geo_tail : ∀ d, tailV (σ_geo d) = tailV d

  /-- The key local geometry theorem.  It is the per-dart winding-sign result:
  the angular successor is the side following the opposite dart in the outward
  oriented triangle. -/
  σ_geo_eq_φ_face_mul_α : σ_geo = φ_face * α

namespace OrientedTriBoundaryData

variable {V F : Type*} [Fintype V] [DecidableEq V] [Fintype F] [DecidableEq F]
variable (X : OrientedTriBoundaryData V F)

/-- The constructed map.  The stored rotation is geometric. -/
def toCombMap : CombMap (FaceSide F) where
  α := X.α
  σ := X.σ_geo
  α_invol := X.α_invol
  α_no_fixed := X.α_no_fixed

/-- The face permutation of the constructed map is the face-list successor. -/
theorem phi_toCombMap_eq_φ_face : X.toCombMap.φ = X.φ_face := by
  calc
    X.toCombMap.φ = X.σ_geo * X.α := by
      rfl
    _ = (X.φ_face * X.α) * X.α := by
      rw [X.σ_geo_eq_φ_face_mul_α]
    _ = X.φ_face * (X.α * X.α) := by
      rw [mul_assoc]
    _ = X.φ_face := by
      rw [X.α_invol, mul_one]

end OrientedTriBoundaryData
end ProofsInTheBook.Ch13ConstructSigma
```

That theorem is the central architectural reason to define `σ_face := φ_face * α` first.  Once `σ_geo = σ_face` is proved, the face agreement theorem is a three-line group calculation, not a spherical-planar topology theorem.

## What exactly must the angular agreement theorem prove?

The agreement theorem should be local at one vertex and one dart.  A good final statement is:

```lean
/-- Local angular successor theorem.

For a side `d` with tail vertex `v`, the next outgoing side in the positive
outward angular order around the interior cone axis at `v` is the face successor
of the opposite side `α d`. -/
theorem angular_next_eq_faceSucc_alpha
    (X : OrientedTriBoundaryData V F) (d : FaceSide F) :
    X.σ_geo d = X.φ_face (X.α d) := by
  -- proof uses:
  -- 1. α reverses endpoints, so `φ_face (α d)` again starts at `tailV d`;
  -- 2. the oriented face containing `α d` supplies the supporting wedge at `tailV d`;
  -- 3. strict support puts every other incident edge ray outside the open wedge;
  -- 4. `SurroundsAxisPlane` + det3 bridge identifies this wedge as the positive
  --    angular-next sector around the Stiemke/Gordan axis `a_v`;
  -- 5. angular successor uniqueness returns `φ_face (α d)`.
  admit

/-- Permutation-level form used by `phi_toCombMap_eq_φ_face`. -/
theorem sigmaGeo_eq_faceSucc_mul_alpha
    (X : OrientedTriBoundaryData V F) :
    X.σ_geo = X.φ_face * X.α := by
  ext d
  simpa [Equiv.Perm.coe_mul, Function.comp_apply]
    using angular_next_eq_faceSucc_alpha X d
```

In the real proof, the `admit` above should be a named local wedge lemma.  The mathematically precise lemma is:

```lean
/-- The two edge rays `d` and `φ_face (α d)` are consecutive in the positive
angular order around `tailV d`. -/
theorem face_wedge_is_empty_open_sector
    (X : OrientedTriBoundaryData V F)
    (d e : FaceSide F)
    (he_tail : X.tailV e = X.tailV d)
    (he_ne_left : e ≠ d)
    (he_ne_right : e ≠ X.φ_face (X.α d)) :
    ¬ OrientedBetweenAroundAxis
        (axisAt X (X.tailV d))
        (edgeRay X d)
        (edgeRay X e)
        (edgeRay X (X.φ_face (X.α d))) := by
  -- This is the hard local geometry lemma, not a global sphere-topology lemma.
  -- It should be proved from the supporting halfspace of the face containing `α d`:
  -- all incident edge rays at `tailV d` lie in the closed half-plane determined
  -- by that face, and strict support excludes every ray except the two boundary
  -- rays from lying on the boundary.
  admit
```

The exact predicate names will depend on the already-clean `SurroundsAxisPlane`, `det3` bridge, and `globalAngularPermOutward` APIs.  The essential shape should not change.

### Convention warning

With the repo convention `φ = σ * α`, the formula should be

```lean
σ = φ_face * α
```

provided `φ_face` follows the same outward face orientation used to define the geometric angular rotation.  If the existing `globalAngularPermOutward` was defined in the reverse-`σ` order used by the current vertex-link builder, then the theorem will instead identify `σ_geo.symm` with `φ_face * α`, or identify `σ_geo` with `φ_face.symm * α`.  Freeze this with one convention lemma near the definition of `globalAngularPermOutward`; do not let both conventions leak downstream.

The current `RotationFaithful` comment says the old link builder reads neighbours in reverse `σ` order.  That is exactly the place where this convention can flip.  The construct-`σ` object should define the final `σ` so that `M.φ = φ_face`; all later reverse-link conventions can use `M.σ.symm` explicitly as they already do.

## Proving the faces are exactly the supplied triangles

Once `M.φ = φ_face`, this is easy and purely finite.

Recommended API:

```lean
namespace ProofsInTheBook.Ch13ConstructSigma

variable {V F : Type*} [Fintype V] [DecidableEq V] [Fintype F] [DecidableEq F]
variable (X : OrientedTriBoundaryData V F)

abbrev Mgeo : CombMap (FaceSide F) := X.toCombMap

/-- The quotient of `φ`-orbits is equivalent to the input face index type. -/
noncomputable def faceOrbitEquiv :
    Quotient (cycleSetoid X.Mgeo.φ) ≃ F := by
  -- Use `X.phi_toCombMap_eq_φ_face`, `φ_face_f`, and the fact that on each fixed
  -- face the `Fin 3` successor is a 3-cycle.
  -- Implementation pattern:
  --   forward: quotient-lift `(fun d => d.f)` because `φ_face` preserves `f`;
  --   inverse: `fun f => Quotient.mk _ ⟨f, 0⟩`;
  --   prove left inverse by `fin_cases d.k` plus same-cycle witnesses 0,1,2.
  admit

/-- Every constructed face has exactly the three sides of one supplied triangle. -/
theorem faceRegular_three : X.Mgeo.FaceRegular 3 := by
  -- Transport each `φ`-orbit to a fixed `f : F` via `faceOrbitEquiv`.
  -- The fiber is `{⟨f,0⟩, ⟨f,1⟩, ⟨f,2⟩}`.
  admit

/-- A representative dart for the input triangle `f`. -/
def faceDartOfInput (f : F) : FaceSide F := ⟨f, 0⟩

/-- The three vertices of the constructed map face are the input triangle vertices. -/
theorem constructed_face_vertices_eq_input
    (f : F) :
    ![X.Mgeo.tail (faceDartOfInput X f),
      X.Mgeo.tail (X.Mgeo.φ (faceDartOfInput X f)),
      X.Mgeo.tail (X.Mgeo.φ (X.Mgeo.φ (faceDartOfInput X f)))]
    =
    ![Quotient.mk (cycleSetoid X.Mgeo.σ) (⟨f, 0⟩ : FaceSide F),
      Quotient.mk (cycleSetoid X.Mgeo.σ) (⟨f, 1⟩ : FaceSide F),
      Quotient.mk (cycleSetoid X.Mgeo.σ) (⟨f, 2⟩ : FaceSide F)] := by
  -- This is mostly `rfl`/`simp` after `Mgeo.φ = φ_face` and the `Fin 3`
  -- successor normal forms are available.
  admit

end ProofsInTheBook.Ch13ConstructSigma
```

These proofs are tractable.  They are finite orbit bookkeeping, not topology.

## Constructing `TriangulatedEuclideanPolyhedron` from the constructed map

The main nuisance is that `TriangulatedEuclideanPolyhedron` wants coordinates on `M.Vertex`, where `M.Vertex` is a quotient of darts by `σ`.  Your raw data has coordinates on the explicit vertex type `V`.  So prove an equivalence between constructed `σ`-orbits and explicit vertices.

Target:

```lean
/-- The `σ`-orbit quotient of constructed darts is the explicit vertex set. -/
noncomputable def vertexOrbitEquiv
    (X : OrientedTriBoundaryData V F) : X.Mgeo.Vertex ≃ V := by
  -- forward: quotient-lift `tailV`; use `σ_geo_tail`.
  -- inverse: choose any incident side at `v`; this needs either a field
  -- `incident_side : ∀ v, {d // tailV d = v}` or a proof that every listed
  -- vertex appears in some face.
  -- left inverse: all sides with the same `tailV` are in the same σ-cycle.
  -- This needs a vertex-fan connectedness/cyclicity certificate, or follows from
  -- the angular permutation construction if `σ_geo` was defined as one cycle on
  -- each tail fiber.
  admit
```

Then define:

```lean
noncomputable def constructedPos
    (X : OrientedTriBoundaryData V F) : X.Mgeo.Vertex → E3 :=
  fun q => X.pos (vertexOrbitEquiv X q)
```

This quotient bridge is moderate, not hard, if `globalAngularPermOutward` already proves that each tail fiber is exactly one `σ_geo`-cycle.  If it only gives a permutation preserving tail fibers, then you still need a “one cycle per vertex star” lemma.

## `IsSphereMap`, `FaceRegular 3`, `IsSimpleGraph`: what is easy and what is not?

### Easy if carried by the face list

The following are straightforward if the raw data includes the corresponding finite certificates:

* `CombMap`: immediate from `α_invol` and `α_no_fixed`.
* `M.φ = φ_face`: immediate from `σ_geo = φ_face * α`.
* `FaceRegular 3`: finite proof from `M.φ = φ_face` and the `Fin 3` cycle.
* `M.F = Fintype.card F`: quotient-orbit equivalence from `φ_face` to face IDs.
* `M.E = Fintype.card Dart / 2`: already follows from `CombMap.two_mul_E_eq_card`; for `Dart = F × Fin 3`, this is `2E = 3F`.
* `no_loop`: from `tri_inj`, because side endpoints `tri f k` and `tri f (k+1)` are distinct.
* `no_parallel`: from an `edge_unique` certificate saying the face list contains exactly two oriented sides per geometric edge.
* `Connected`: from an explicit connectedness certificate for the vertex-edge incidence graph, or directly for `M.dartStep`.
* `eulerChar = 2`: from an explicit cardinal certificate:

  ```lean
  ((Fintype.card V : ℤ) - (edgeCount X : ℤ) + (Fintype.card F : ℤ) = 2)
  ```

  transported through `vertexOrbitEquiv`, `faceOrbitEquiv`, and `two_mul_E_eq_card`.

### Not derivable from handshakes alone

`FaceRegular 3` gives `3F = 2E`, and `Connected` says the graph is one piece.  These do **not** imply Euler characteristic `2`.  Triangulated maps on a torus also satisfy triangle handshakes and connectedness.  So a proof of `IsSphereMap` needs either:

1. an Euler/cardinality certificate in the input face-list structure, or
2. a genuine theorem that the boundary complex of the convex body is a sphere.

There is no shortcut here through `3F = 2E`.

### Hard from raw convex geometry

Deriving these from only `pos`, supporting planes, strict support, and a face list is much harder:

* “Every boundary edge appears in exactly two faces.”
* “The vertex-fan around each vertex is one cyclic component.”
* “The full boundary graph is connected.”
* “`V - E + F = 2`.”

Mathematically these are standard facts about 3D convex polytopes, but the Lean route would require a formal boundary-complex/topology layer that this repo and Mathlib do not currently expose as a ready theorem.

The precise Mathlib gap is not one lemma; it is the absence of a packaged theorem like:

```lean
/-- Missing high-level theorem, schematic only. -/
theorem convex_polytope_boundary_triangulation_euler_two
    (P : ConvexPolytope3D)
    (T : TriangulationOfBoundary P) :
    T.connected ∧ T.eulerChar = 2 := by
  -- would require: boundary of a compact 3D convex polytope is homeomorphic to S²,
  -- or an equivalent shelling/fan proof of Euler for its face lattice.
  admit
```

Implementing this honestly means developing enough of finite 2-dimensional cell complexes or simplicial complexes, their Euler characteristic, and the relation between the convex boundary and that complex.  That is a multi-month campaign if pursued from raw geometry.

## Difficulty ranking

Ranked from easiest to hardest, assuming the angular-order machinery mentioned in the prompt exists cleanly.

### 1. Define face-side darts, `φ_face`, and edge-pairing `α`

Difficulty: low.

Expected work: hours to one day.

Proof burden:

```lean
α * α = 1
∀ d, α d ≠ d
```

If `α` is supplied as an `Equiv.Perm` plus those two proofs, `CombMap` construction is immediate.

### 2. Prove `M.φ = φ_face`

Difficulty: low.

Expected work: minutes once `σ_geo = φ_face * α` is available.

Core proof:

```lean
theorem phi_eq_faceSucc
    (hσ : σ_geo = φ_face * α) (hα : α * α = 1) :
    (CombMap.mk α σ_geo hα hα_no_fixed).φ = φ_face := by
  calc
    _ = σ_geo * α := rfl
    _ = (φ_face * α) * α := by rw [hσ]
    _ = φ_face * (α * α) := by rw [mul_assoc]
    _ = φ_face := by rw [hα, mul_one]
```

### 3. Prove `FaceRegular 3` and face-orbit agreement

Difficulty: low to moderate.

Expected work: one to two days, mostly quotient/fiber bookkeeping.

No geometry is involved.  Use `M.φ = φ_face`, then prove every `φ_face`-orbit is `{(f,0),(f,1),(f,2)}`.

### 4. Build the vertex quotient equivalence `M.Vertex ≃ V`

Difficulty: moderate.

Expected work: two to four days if `globalAngularPermOutward` already packages “one cyclic orbit per tail vertex”.

Needed facts:

```lean
∀ d, tailV (σ_geo d) = tailV d
∀ d e, tailV d = tailV e → σ_geo.SameCycle d e
∀ v, ∃ d, tailV d = v
```

The second line is the only real content.  It is local fan cyclicity, not global topology.

### 5. Prove `IsSimpleGraph`

Difficulty: low to moderate with certificates; hard if derived from geometry.

`no_loop` is easy from triangle vertex injectivity.  `no_parallel` should be an input face-list uniqueness certificate unless you want to prove a convex-polytope edge uniqueness theorem.

Recommended field:

```lean
edge_unique : ∀ {d e},
  ((tailV d = tailV e ∧ headV d = headV e) ∨
   (tailV d = headV e ∧ headV d = tailV e)) →
    α.SameCycle d e
```

This maps almost directly to `IsSimpleGraph.no_parallel` after the vertex quotient equivalence.

### 6. Prove the local angular agreement `σ_geo = φ_face * α`

Difficulty: hard but bounded.

Expected work: several days to two weeks, depending on how polished the current `SurroundsAxisPlane`, det3 bridge, and angular successor uniqueness APIs are.

This is the single hardest piece **inside the construct-σ layer**.  It does not need a global planar/spherical graph development.  It needs a strong local theorem:

* the face containing `α d` determines a supporting tangent half-plane at `tailV d`;
* the two boundary rays are `d` and `φ_face (α d)`;
* all other incident rays are strictly outside the open wedge;
* the per-dart winding sign says this is the positive angular-next wedge.

That is exactly where the already-reduced “single per-dart winding sign” belongs.

### 7. Prove `Connected` from geometry

Difficulty: easy with a connectivity certificate; hard from raw convexity.

If the face-list data has

```lean
connected_dartStep : ∀ a b, Relation.ReflTransGen M.dartStep a b
```

then this is immediate.  If it must be proved from convex support alone, you need a theorem that the boundary/1-skeleton of the convex polytope is connected.  That is standard but not currently a one-line Mathlib route.

### 8. Prove `eulerChar = 2` from geometry

Difficulty: easy with an Euler certificate; hardest from raw convexity.

This is the main Mathlib gap.  A face-list cardinal certificate is cheap.  A proof from convex geometry is a real convex-polytope-boundary Euler theorem.

## Answer to question 1: agreement theorem tractability

The agreement theorem is tractable **if phrased locally**:

```lean
σ_geo d = φ_face (α d)
```

for every face-side dart `d`.  This avoids a full “embedded planar/spherical graph ⇒ combinatorial map” development.

It becomes intractable if phrased globally as:

> Given only a geometric embedded graph, discover all faces and prove the `φ=σ α` orbits are the boundary triangles.

Do not do that.  The face list is already part of the convex polytope data, so use it to define `φ_face`.  The angular proof should only show that the geometric cyclic order around each vertex is compatible with this already-known face adjacency.

The cleanest theorem stack is:

```lean
-- local theorem, geometric
angular_next_eq_faceSucc_alpha : ∀ d, σ_geo d = φ_face (α d)

-- permutation theorem, finite extensionality
sigmaGeo_eq_faceSucc_mul_alpha : σ_geo = φ_face * α

-- map theorem, group algebra
constructed_phi_eq_faceSucc : Mgeo.φ = φ_face

-- face theorem, finite orbit bookkeeping
constructed_faces_exactly_input_triangles : FaceOrbit Mgeo ≃ F
constructed_faceRegular_three : Mgeo.FaceRegular 3
```

## Answer to question 2: `IsSphereMap`, `FaceRegular 3`, `IsSimpleGraph` from geometry

`FaceRegular 3` is easy from the constructed face permutation.  It should not use convexity.

`IsSimpleGraph` is easy if the input face list includes edge uniqueness and triangle nondegeneracy.  Without that, `no_parallel` is a convex-polytope edge theorem and becomes substantially harder.

`IsSphereMap` splits:

```lean
M.Connected       -- connectivity of the dart graph
M.eulerChar = 2   -- Euler characteristic
```

Connectivity is moderate if the boundary incidence graph is given connected.  Euler is the serious issue.  There is no valid derivation from `3F = 2E` plus connectedness.  The practical Lean path is to store an Euler/cardinality certificate in the raw boundary data and transport it through the constructed map.

Recommended field:

```lean
structure OrientedTriBoundaryData ... where
  -- previous fields
  every_vertex_incident : ∀ v : V, ∃ d : FaceSide F, tailV d = v
  tail_fiber_one_sigma_cycle : ∀ {d e}, tailV d = tailV e → σ_geo.SameCycle d e
  connected_cert : ∀ a b : FaceSide F,
    Relation.ReflTransGen (toCombMap.dartStep) a b
  euler_cert :
    ((Fintype.card V : ℤ) - (edgeCount : ℤ) + (Fintype.card F : ℤ) = 2)
```

Then `IsSphereMap` is finite transport, not topology.

## Answer to question 3: honest scope

There are two very different scopes.

### Bounded project

If the new raw data structure includes:

* oriented triangular face list;
* edge pairing `α` with involution/no-fixed/reversed endpoints;
* edge uniqueness/no-parallel certificate;
* tail-fiber cyclicity for `σ_geo`;
* connectedness certificate;
* Euler/cardinality certificate;
* the per-dart angular-next theorem, or enough already-proved local geometry to derive it;

then the construct-`σ` map and agreement layer is a bounded development.  I would expect days to a couple of weeks, with the angular-next theorem dominating.

### Major campaign

If all of the following must be derived from raw convex geometry alone:

* every boundary side has a unique opposite side;
* the listed boundary is connected;
* vertex stars are single cyclic fans;
* no parallel duplicate edges;
* Euler characteristic is `2`;

then this is a multi-month campaign.  The hardest piece is not the angular order; it is the missing convex-polytope-boundary/Euler infrastructure.

The precise missing Mathlib/repo layer is:

> A finite boundary complex of a compact 3D convex polytope, proved to be a triangulated sphere with Euler characteristic `2`, and connected to the face/edge/vertex incidence counts used by `CombMap`.

Without that, any “from geometry alone” proof of `M.IsSphereMap` will either smuggle in an Euler certificate or reimplement the missing topology.

## Is there a shorter path by keeping the given `M`?

Yes, but it is only shorter if the goal is incremental integration, not a fully orientation-input-free theorem.

Suppose the existing `M : CombMap D` is still supplied with:

```lean
hsphere : M.IsSphereMap
htri : M.FaceRegular 3
hsimple : M.IsSimpleGraph
```

Then one can try to prove:

```lean
theorem sigma_eq_globalAngularPermOutward
    (P : TriangulatedEuclideanPolyhedron M)
    (hface_oriented : FaceCycleOutwardOriented P)
    (hlocal : LocalAngularAgreement P) :
    M.σ = globalAngularPermOutward P := by
  ext d
  -- local wedge theorem at `M.tail d`
  exact hlocal d
```

This avoids rebuilding `IsSphereMap`, `FaceRegular 3`, and `IsSimpleGraph`, because they remain assumptions on `M`.  But it does **not** avoid orientation.  Without some independent oriented face-cycle agreement, this theorem is equivalent in strength to `RotationFaithful`; the mirror-realization obstruction applies exactly here.

A useful intermediate replacement for `RotationFaithful` is therefore:

```lean
/-- The supplied combinatorial face cycles agree with the outward-oriented geometric
triangle list.  This is weaker/more primitive than saying the vertex rotation is
faithful, because `σ` can then be computed as `φ_face * α`. -/
structure FaceCycleOutwardOriented
    {D : Type*} [Fintype D] [DecidableEq D]
    {M : CombMap D} (P : TriangulatedEuclideanPolyhedron M) : Prop where
  face_cycle_normal_positive :
    ∀ d,
      ∃ lam : ℝ, 0 < lam ∧
        P.outward_normal (M.dartFace d) =
          lam • cross
            (P.pos (M.tail (M.φ (M.φ d))) - P.pos (M.tail d))
            (P.pos (M.tail (M.φ d)) - P.pos (M.tail d))
```

Then prove:

```lean
theorem rotationFaithful_of_faceCycleOutward_and_angularAgreement
    (P : TriangulatedEuclideanPolyhedron M)
    (hface : FaceCycleOutwardOriented P)
    (hang : M.σ = globalAngularPermOutward P) :
    RotationFaithful P := by
  -- This should become a bridge lemma, not an assumption.
  -- It rewrites `M.φ = M.σ * M.α`, uses `hang`, and matches the existing
  -- reverse-σ cross-product convention.
  admit
```

This is a good stepping stone, but it still keeps `M` and an orientation/agreement hypothesis.  The truly orientation-input-free version is the construct-`σ` object where `M` itself is built from the outward-oriented face list and angular successor.

## Final recommendation

For the next Lean file, introduce a new construction layer rather than altering `ConvexEuclideanPolyhedron` immediately:

```lean
ProofsInTheBook/Ch13ConstructSigma.lean
```

Suggested theorem milestones:

```lean
-- finite construction
def OrientedTriBoundaryData.toCombMap : CombMap (FaceSide F)

theorem phi_toCombMap_eq_faceSucc : X.toCombMap.φ = X.φ_face

theorem faceRegular_three : X.toCombMap.FaceRegular 3

noncomputable def faceOrbitEquiv :
  Quotient (cycleSetoid X.toCombMap.φ) ≃ F

noncomputable def vertexOrbitEquiv :
  X.toCombMap.Vertex ≃ V

-- simple graph, with edge uniqueness certificate
theorem isSimpleGraph : X.toCombMap.IsSimpleGraph

-- sphere, with connectivity + Euler certificates
theorem isSphereMap : X.toCombMap.IsSphereMap

-- Euclidean realization carried by the constructed map
noncomputable def toTriangulatedEuclideanPolyhedron :
  TriangulatedEuclideanPolyhedron X.toCombMap

-- final bridge into the current spine
theorem constructed_rotationFaithful :
  RotationFaithful X.toTriangulatedEuclideanPolyhedron
```

The best order is:

1. `FaceSide`, `φ_face`, `α`, `toCombMap`.
2. `σ_geo = φ_face * α` as an assumed field first; prove `M.φ = φ_face` and `FaceRegular 3`.
3. Add vertex quotient equivalence and constructed `TriangulatedEuclideanPolyhedron`.
4. Add `IsSimpleGraph` from `edge_unique`.
5. Add `IsSphereMap` from explicit connectedness/Euler certificates.
6. Only then replace the assumed `σ_geo = φ_face * α` field with the real local angular proof using `SurroundsAxisPlane` and the per-dart winding sign.

This staging gives immediate compileable finite infrastructure while isolating the single geometric residue.  It also avoids committing to a full convex-polytope topology formalization unless the project explicitly chooses that larger scope.