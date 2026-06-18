# Ch13 Euler from convex boundary: shortest concrete route

## Verdict

The shortest route is a **generic-height / discrete Morse count** on the convex boundary.  It is a local form of the planar-embedding route, but it avoids building a full planar subdivision, avoids homology, avoids spherical area, and avoids a tree-cotree theorem.

The core identity is:

```text
V - E + F
  = ∑ vertices v (1 - #lower_edges_at_v + #faces_for_which_v_is_highest).
```

For a generic linear height function on a convex polytope:

* there is exactly one global minimum vertex and one global maximum vertex;
* at every other vertex, the lower neighbours form one nonempty proper consecutive block in the cyclic vertex link;
* if `k` lower neighbours form a proper consecutive block, then exactly `k - 1` incident triangular faces have `v` as their highest vertex;
* at the minimum the contribution is `1`; at the maximum the contribution is `1`; every other vertex contributes `0`.

Hence the sum is `2`.

This is the path with the least new infrastructure because all global topology is replaced by one local convex-link lemma:

```text
A linear halfspace cuts a strictly convex cyclic vertex link in a cyclic interval.
```

That lemma is already close to the existing ch13 local geometry (`VertexLinkGeometry`, `turn_support`, `turn_strict`, strict face support).  No central projection theorem, no shelling of the whole boundary, and no dual-tree/Jordan theorem is needed.

## Recommended theorem stack

### Layer 1: pure finite counting

This layer is independent of Euclidean geometry except for a height function and a local interval property.

```lean
import ProofsInTheBook.ZinanCh13EuclLink
import ProofsInTheBook.PlanarMapSimple

noncomputable section

open scoped Classical BigOperators RealInnerProductSpace
open ProofsInTheBook.PlanarMap
open ProofsInTheBook.PlanarMap.CombMap
open ProofsInTheBook.Ch13Euclidean
open ProofsInTheBook.Ch13EuclLink

namespace ProofsInTheBook.Ch13EulerFromHeight

variable {D : Type*} [Fintype D] [DecidableEq D]
variable {M : CombMap D}

/-- Outgoing darts at a combinatorial vertex. -/
abbrev OutDart (M : CombMap D) (v : M.Vertex) : Type _ :=
  {d : D // M.tail d = v}

/-- A cyclic-interval certificate for a Boolean predicate on the cyclic dart order
around a vertex.  The final implementation can define this using `Equiv.Perm.toList`
or using indices `Fin (vDeg P v)`. -/
structure CyclicIntervalOnVertex (M : CombMap D) (v : M.Vertex)
    (p : OutDart M v → Prop) : Prop where
  /-- Number of elements in the lower block. -/
  k : ℕ
  /-- `k = 0`, `k = degree`, or the true darts are one consecutive proper block. -/
  interval_cases : Prop

/-- Height/Morse data sufficient for Euler.  This is the exact finite residue that
convexity must supply. -/
structure HeightMorseData (M : CombMap D) where
  h : M.Vertex → ℝ

  /-- Adjacent vertices have distinct heights. -/
  edge_ne : ∀ d : D, h (M.tail d) ≠ h (M.head d)

  /-- Every face has a unique highest vertex.  For triangular faces this follows
  from `edge_ne` plus no loops/no repeated face vertices. -/
  face_unique_high :
    ∀ f : M.Face, ∃! v : M.Vertex,
      (∃ d : D, M.dartFace d = f ∧ M.tail d = v) ∧
      ∀ w : M.Vertex,
        (∃ d : D, M.dartFace d = f ∧ M.tail d = w) → h w ≤ h v

  /-- At every vertex, the lower neighbours form a cyclic interval in the vertex link. -/
  lower_interval : ∀ v : M.Vertex,
    CyclicIntervalOnVertex M v
      (fun d : OutDart M v => h (M.head d.1) < h v)

  /-- There is a unique global minimum and maximum vertex. -/
  unique_min : ∃! v : M.Vertex, ∀ w : M.Vertex, h v ≤ h w
  unique_max : ∃! v : M.Vertex, ∀ w : M.Vertex, h w ≤ h v

/-- Lower outgoing darts at `v`. -/
def lowerDarts (H : HeightMorseData M) (v : M.Vertex) : Finset D :=
  Finset.univ.filter (fun d => M.tail d = v ∧ H.h (M.head d) < H.h v)

/-- Number of lower outgoing edges at `v`. -/
def lowerDegree (H : HeightMorseData M) (v : M.Vertex) : ℕ :=
  (H.lowerDarts v).card

/-- A dart `d` is the corner at which `tail d` is the highest vertex of the
triangular face `dartFace d`.  In the repo's face convention, the two other
vertices of that face are `head d` and `head (σ⁻¹ d)`. -/
def highCorner (H : HeightMorseData M) (d : D) : Prop :=
  H.h (M.head d) < H.h (M.tail d) ∧
  H.h (M.head (M.σ.symm d)) < H.h (M.tail d)

/-- Number of triangular faces whose highest vertex is `v`, counted by their
unique high corner at `v`. -/
def highFaceCount (H : HeightMorseData M) (v : M.Vertex) : ℕ :=
  (Finset.univ.filter (fun d : D => M.tail d = v ∧ H.highCorner d)).card

/-- Every edge is counted exactly once, at its higher endpoint. -/
theorem sum_lowerDegree_eq_E
    (H : HeightMorseData M) :
    (∑ v : M.Vertex, H.lowerDegree v) = M.E := by
  -- Proof plan:
  -- * Use α-orbits as edges.
  -- * For every dart `d`, exactly one of `d` and `α d` has lower head:
  --     `H.h (M.head d) < H.h (M.tail d)` xor the reverse.
  -- * `edge_ne d` rules out equality.
  -- * Then each α-orbit contributes one lower dart.
  -- Existing count tool: `CombMap.two_mul_E_eq_card` and `alpha_sameCycle_iff`.
  -- The final proof is finite `Finset` fiber bookkeeping.
  omega

/-- Every triangular face is counted exactly once, at its unique highest vertex. -/
theorem sum_highFaceCount_eq_F
    (H : HeightMorseData M) :
    (∑ v : M.Vertex, H.highFaceCount v) = M.F := by
  -- Proof plan:
  -- * Use `H.face_unique_high f` to choose the unique highest vertex of each face.
  -- * For a triangular face, the high vertex has a unique dart/corner `d` with
  --   `tail d = v` and `dartFace d = f`.
  -- * At that dart, the other two face vertices are `head d` and `head (σ.symm d)`.
  --   In the current repo this is backed by
  --     `tail_phi_phi_eq_head_sigma_symm_of_triangular_euclidean`
  --   and the face-vertex classifier.
  -- * Count faces by this chosen high corner.
  omega

/-- Local convex-link counting.  If the lower neighbours of `v` form one cyclic
interval, then the local Morse contribution is `1` at a strict local min/max and
`0` otherwise. -/
theorem local_morse_contribution
    (H : HeightMorseData M) (v : M.Vertex) :
    ((1 : ℤ) - (H.lowerDegree v : ℤ) + (H.highFaceCount v : ℤ)) =
      if (∀ w : M.Vertex, H.h v ≤ H.h w) ∨ (∀ w : M.Vertex, H.h w ≤ H.h v)
      then 1 else 0 := by
  -- Let `n` be the degree of `v`, and let `k = lowerDegree H v`.
  -- The triangular faces having highest vertex `v` are exactly adjacent pairs
  -- of lower darts in the cyclic order around `v`.
  -- For a cyclic interval of length `k` in a cycle of length `n`:
  --   k = 0        => adjacent-lower-pair count = 0      (minimum)
  --   0 < k < n    => adjacent-lower-pair count = k - 1  (regular vertex)
  --   k = n        => adjacent-lower-pair count = n      (maximum)
  -- Therefore `1 - k + highFaceCount` is 1 only in the first and last cases.
  -- The interval cases come from `H.lower_interval v`.
  by_cases hExt :
      (∀ w : M.Vertex, H.h v ≤ H.h w) ∨ (∀ w : M.Vertex, H.h w ≤ H.h v)
  · simp [hExt]
    -- prove contribution = 1 from k=0 or k=n
    omega
  · simp [hExt]
    -- prove contribution = 0 from 0<k<n and highFaceCount=k-1
    omega

/-- Euler from height/Morse data. -/
theorem eulerChar_eq_two_of_heightMorseData
    (H : HeightMorseData M) :
    M.eulerChar = 2 := by
  classical
  have hE := sum_lowerDegree_eq_E (M := M) H
  have hF := sum_highFaceCount_eq_F (M := M) H
  have hsum :
      M.eulerChar =
        ∑ v : M.Vertex,
          ((1 : ℤ) - (H.lowerDegree v : ℤ) + (H.highFaceCount v : ℤ)) := by
    -- Expand `CombMap.eulerChar`; use
    --   `∑ v, 1 = V`, `sum_lowerDegree_eq_E`, `sum_highFaceCount_eq_F`.
    unfold CombMap.eulerChar
    -- Finset/Int normalization.
    omega
  rw [hsum]
  have hlocal := fun v => local_morse_contribution (M := M) H v
  -- Substitute the local formula.  Unique min and unique max imply exactly two
  -- vertices have contribution 1.
  -- `H.unique_min` and `H.unique_max` are distinct because an edge exists in a
  -- nondegenerate boundary; handle the tetra/nonempty edge hypothesis here.
  omega

end ProofsInTheBook.Ch13EulerFromHeight
```

The `omega` placeholders mark finite arithmetic/bookkeeping goals, not new geometric ideas.  The only real geometric input is `lower_interval`.

### Layer 2: convex geometry supplies `HeightMorseData`

Use a generic affine height

```lean
h v = inner ℝ g (P.pos v)
```

where `g` is chosen so no two vertices have the same height.  Since the vertex set is finite, this is a finite hyperplane-avoidance lemma.

```lean
namespace ProofsInTheBook.Ch13EulerFromHeight

variable {D : Type*} [Fintype D] [DecidableEq D]
variable {M : CombMap D}

structure GenericHeightVector (P : TriangulatedEuclideanPolyhedron M) where
  g : E3
  vertex_injective : Function.Injective (fun v : M.Vertex => inner ℝ g (P.pos v))

/-- Finite hyperplane avoidance: choose a vector not orthogonal to any difference
of two distinct vertex positions. -/
theorem exists_genericHeightVector
    (P : TriangulatedEuclideanPolyhedron M)
    (hpos_inj : Function.Injective P.pos) :
    ∃ G : GenericHeightVector P := by
  -- Use finite avoidance of the hyperplanes
  --   {g | inner g (P.pos u - P.pos v) = 0}
  -- for `u ≠ v`.
  -- In `ℝ³`, each forbidden set is a proper hyperplane because `P.pos u ≠ P.pos v`.
  -- A concrete constructive proof can pick a line `g(t) = b0 + t b1 + t^2 b2`
  -- and avoid finitely many polynomial roots; or use existing topological facts
  -- about finite unions of closed sets with empty interior if preferred.
  -- For the first implementation, it is acceptable to make `GenericHeightVector`
  -- a field of the convex-boundary object and prove this theorem later.
  exact by
    classical
    -- implementation residue: finite hyperplane avoidance
    exact False.elim (by contradiction)

/-- Local geometric lemma: a linear halfspace cuts a strictly convex vertex link
in a cyclic interval.  This is the central lemma of the route. -/
theorem lower_interval_of_strict_convex_vertexLink
    (P : TriangulatedEuclideanPolyhedron M)
    (hsimple : M.IsSimpleGraph)
    (hlink : ∀ v : M.Vertex, VertexLinkGeometry P v)
    (G : GenericHeightVector P)
    (v : M.Vertex) :
    CyclicIntervalOnVertex M v
      (fun d : OutDart M v =>
        inner ℝ G.g (P.pos (M.head d.1)) < inner ℝ G.g (P.pos v)) := by
  -- Convert lower-neighbour condition to a linear inequality on edge vectors:
  --   inner g (edgeVec P d) < 0.
  -- The vertex link is a strict convex cyclic polygon in an affine plane after
  -- projecting to the link plane.  Intersecting a strict convex polygon with a
  -- linear halfspace gives a connected interval of its boundary vertices.
  -- Existing local ingredients:
  --   `VertexLinkGeometry.turn_support`
  --   `VertexLinkGeometry.turn_strict`
  --   `VertexLinkGeometry.open_hemi`
  --   strict support lemmas in `ZinanCh13EuclLink`.
  -- This is local 2D convexity, not global topology.
  exact by
    classical
    -- implementation residue: cyclic interval lemma for strict convex vertex links
    exact False.elim (by contradiction)

/-- Convex boundary geometry produces the height/Morse data needed for Euler. -/
theorem heightMorseData_of_convex_boundary
    (P : TriangulatedEuclideanPolyhedron M)
    (hsimple : M.IsSimpleGraph)
    (hpos_inj : Function.Injective P.pos)
    (hlink : ∀ v : M.Vertex, VertexLinkGeometry P v)
    (G : GenericHeightVector P) :
    HeightMorseData M where
  h := fun v => inner ℝ G.g (P.pos v)
  edge_ne := by
    intro d hEq
    have htail_head : P.pos (M.tail d) = P.pos (M.head d) :=
      G.vertex_injective hEq
    exact P.edge_nondegenerate d htail_head
  face_unique_high := by
    intro f
    -- A triangular face has three distinct vertices; generic height is injective,
    -- so the finite set of its vertices has a unique maximum.
    -- Use `P.face_vertices_match`, `P.face_nondegenerate f`, and the face vertex
    -- classifier already in `ZinanCh13Euclidean/ZinanCh13EuclLink`.
    exact by
      classical
      -- finite max over three vertices
      exact False.elim (by contradiction)
  lower_interval := by
    intro v
    exact lower_interval_of_strict_convex_vertexLink P hsimple hlink G v
  unique_min := by
    -- finite type + injective height gives unique minimum.
    exact by
      classical
      -- `Finset.exists_minimal`/`Finset.min'` style proof
      exact False.elim (by contradiction)
  unique_max := by
    -- finite type + injective height gives unique maximum.
    exact by
      classical
      -- `Finset.exists_maximal`/`Finset.max'` style proof
      exact False.elim (by contradiction)

/-- Final convex-boundary Euler theorem, after the local link convexity and generic
height data are supplied. -/
theorem convex_boundary_eulerChar_eq_two
    (P : TriangulatedEuclideanPolyhedron M)
    (hsimple : M.IsSimpleGraph)
    (hpos_inj : Function.Injective P.pos)
    (hlink : ∀ v : M.Vertex, VertexLinkGeometry P v)
    (G : GenericHeightVector P) :
    M.eulerChar = 2 := by
  exact eulerChar_eq_two_of_heightMorseData
    (heightMorseData_of_convex_boundary P hsimple hpos_inj hlink G)

end ProofsInTheBook.Ch13EulerFromHeight
```

In the current repo, `VertexLinkGeometry P v` is produced by `vertexLinkGeometryOfEuclidean` from `RotationFaithful` and `IsSimpleGraph`.  For the construct-`σ` route, the same local link geometry should be produced from `σ = σ_geo` instead of the old `RotationFaithful` field.  Euler itself only needs the unoriented cyclic interval property, so this is weaker than the full signed winding theorem.

## Why this beats the four proposed routes

### Rank 1: generic-height / Morse count, a local variant of route #3

This is the recommended path.

**Input needed from convex geometry**

```lean
P : TriangulatedEuclideanPolyhedron M
hsimple : M.IsSimpleGraph
hpos_inj : Function.Injective P.pos
hlink : ∀ v, VertexLinkGeometry P v        -- or weaker: lower interval for generic heights
G : GenericHeightVector P
```

The geometric payload is one local theorem:

```lean
lower_interval_of_strict_convex_vertexLink
```

**Mathlib/repo gap**

There is no existing cyclic-interval theorem for cutting a strict convex vertex link by a linear halfspace.  But this is a small local convex-polygon lemma over a finite cyclic list, and it reuses the ch13 vertex-link machinery.  It does not require a global planar embedding theorem.

**Approximate size**

* finite counting layer: 300--600 lines;
* cyclic interval definitions and list lemmas: 300--700 lines;
* local convex-link halfspace lemma: 400--900 lines;
* generic height choice: 100--300 lines, or zero initially if carried as data.

This is the least new infrastructure route.

### Rank 2: shelling of the convex boundary (#2)

A shelling route is also clean:

1. choose an outer face `f∞`;
2. line-shell the remaining triangular faces;
3. prove each new triangle attaches along one boundary edge or two adjacent boundary edges;
4. track Euler by induction.

The induction invariant is:

```lean
structure TriDiskShellingState where
  usedFaces : Finset M.Face
  boundaryEdges : Finset M.Edge
  chi_disk : ℤ
  boundary_is_cycle : Prop
```

For a triangular shelling step:

```text
attach along one edge:  ΔV=1, ΔE=2, ΔF=1, Δχ=0, boundary length +1
attach along two edges: ΔV=0, ΔE=1, ΔF=1, Δχ=0, boundary length -1
```

Start with one triangle: `χ = 1`.  After all faces except `f∞` are attached, the boundary is the three edges of `f∞`, still `χ = 1`.  Adding `f∞` increases `F` by `1`, so `χ = 2`.

**Input needed from convex geometry**

A line shelling certificate:

```lean
structure BoundaryShelling (M : CombMap D) where
  outer : M.Face
  order : List M.Face
  nodup_order : order.Nodup
  covers : order.toFinset = Finset.univ.erase outer
  attach_kind : ∀ f ∈ order, AttachOneEdgeOrTwoAdjacentEdges f
  boundary_final_outer : Prop
```

**Mathlib/repo gap**

The missing piece is proving `BoundaryShelling` from convexity, usually via a Schlegel diagram or line shelling.  This is still elementary, but it needs more global bookkeeping than the height/Morse count.

**Approximate size**

1k--2.5k lines after the face/edge API is stable.

### Rank 3: tree-cotree / planar graph route (#3 in its strict form)

The tree-cotree proof is elegant once a planar embedding certificate is available:

```lean
structure TreeCotreeCertificate (M : CombMap D) where
  primalTreeEdges : Finset M.Edge
  dualTreeEdges : Finset M.Edge
  disjoint : Disjoint primalTreeEdges dualTreeEdges
  cover_edges : primalTreeEdges ∪ dualTreeEdges = Finset.univ
  primal_card : primalTreeEdges.card = M.V - 1
  dual_card : dualTreeEdges.card = M.F - 1
```

Then Euler is immediate:

```lean
theorem euler_of_treeCotree (C : TreeCotreeCertificate M) :
    M.eulerChar = 2 := by
  -- E = (V-1) + (F-1), hence V - E + F = 2.
```

**Input needed from convex geometry**

A planar embedding strong enough to prove that the complement of a primal spanning tree is a dual spanning tree.  A Schlegel projection can supply the embedding, but proving the no-crossing and dual-connectivity/cut-cycle facts is the main work.

**Mathlib/repo gap**

The repo has `CombMap`, `PlaneSimpleGraph`, and bridges, but no tree-cotree theorem that derives Euler from a planar drawing.  `PlaneSimpleGraph.toCombMap_isSphereMap` transports an already supplied `P.IsSphereMap`; it does not prove it.

**Approximate size**

2k--4k lines if a straight-line planar drawing certificate is built from convexity.  It is elementary, but more global than the height/Morse count.

### Rank 4: central projection / spherical triangulation / angle defect (#1)

Central projection from an interior point to `S²` is geometrically natural, but it does not currently give the shortest Lean path.

Two subroutes:

**Spherical triangulation Euler.**  Project each boundary triangle to a spherical triangle and prove the result is a triangulation of `S²`.  Then use Euler for triangulations of `S²`.

This immediately needs a theorem of the form:

```lean
theorem euler_of_finite_spherical_triangulation : V - E + F = 2
```

which is essentially the original topological problem.

**Angle defect / Descartes.**  Prove

```text
∑ vertices (2π - sum incident face angles) = 4π.
```

For triangular faces, `∑ face angles = π F`, so this gives

```text
2π V - π F = 4π,
```

and with `3F = 2E` it implies `V - E + F = 2`.

The issue is proving total defect `4π`.  The clean proof uses the spherical normal fan and area of the unit sphere, or Gauss-Bonnet.  That requires spherical area/measure infrastructure and a partition theorem for normal cones.

**Input needed from convex geometry**

Interior point, radial projection, spherical triangle nonoverlap/coverage, or normal fan area partition.

**Mathlib/repo gap**

No ready repo theorem for finite spherical triangulation Euler or Descartes angle defect.  Mathlib has Euclidean angle and convexity tools, but not a packaged convex-polytope boundary Euler theorem or a spherical area Gauss-Bonnet theorem usable here.

**Approximate size**

Several thousand lines; more analysis/topology than necessary.

### Rank 5: direct Mathlib convex-polytope API (#4)

I do not see a ready theorem in the repo or exposed by the current imports of the form:

```lean
convex_polytope_boundary_eulerChar_eq_two
polytope_boundary_is_sphere
EulerCharacteristic_of_polytope_boundary
```

The project currently models the needed object directly as `TriangulatedEuclideanPolyhedron M`, not through a Mathlib `Polytope.faces` API.  The practical reuse from Mathlib is lower-level:

* finite `Finset` sums and cardinals;
* Euclidean inner products, affine independence, convexity/supporting halfspaces;
* finite graph connectivity/tree lemmas if using tree-cotree later.

So #4 is not the shortest route unless a new Mathlib theorem is introduced upstream.

## Concrete reduction to implement first

Implement this minimal theorem before any projection/shelling/topology layer:

```lean
/-- Euler formula for a convex triangulated boundary from generic-height Morse data. -/
theorem eulerChar_eq_two_of_convex_height
    (P : TriangulatedEuclideanPolyhedron M)
    (hsimple : M.IsSimpleGraph)
    (H : HeightMorseData M) :
    M.eulerChar = 2 :=
  eulerChar_eq_two_of_heightMorseData H
```

Then prove the two geometry-producing lemmas:

```lean
theorem exists_genericHeightVector
    (P : TriangulatedEuclideanPolyhedron M)
    (hpos_inj : Function.Injective P.pos) :
    ∃ G : GenericHeightVector P

theorem lower_interval_of_strict_convex_vertexLink
    (P : TriangulatedEuclideanPolyhedron M)
    (hsimple : M.IsSimpleGraph)
    (hlink : ∀ v : M.Vertex, VertexLinkGeometry P v)
    (G : GenericHeightVector P)
    (v : M.Vertex) :
    CyclicIntervalOnVertex M v
      (fun d : OutDart M v =>
        inner ℝ G.g (P.pos (M.head d.1)) < inner ℝ G.g (P.pos v))
```

After those, `M.eulerChar = 2` is a finite sum proof.

## Why this is the right endpoint for ch13

Cauchy ch13 already has local convex vertex-link machinery because the arm lemma needs it.  Euler from height uses the same local structure and asks only for a cyclic interval cut by a linear inequality.  It does not need a global homeomorphism to `S²`.

So the route is:

```text
strict face support
  ⇒ strict convex vertex links
  ⇒ lower neighbours form a cyclic interval for generic height
  ⇒ local Morse contribution is 0 except min/max
  ⇒ V - E + F = 2.
```

This is the shortest concrete formalization path I would put into the repo.