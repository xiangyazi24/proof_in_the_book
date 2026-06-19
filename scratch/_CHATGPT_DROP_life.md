# Ch13 Euler from a convex triangulated boundary: shortest concrete formalization route

## Bottom-line ranking

The shortest Lean route is **route #3, but in a height-sweep / discrete-Morse form rather than a full tree-cotree development**.

It proves

```lean
M.eulerChar = 2
```

from convex geometry by choosing a generic linear height function and doing a finite local count over vertices.  It avoids proving that a central projection is a triangulation of `S²`, avoids spherical area/Gauss-Bonnet, avoids a global shelling construction, and avoids building the full planar drawing/tree-cotree theorem.

The key identity is finite:

```text
V - E + F
  = ∑ v, (1 - lowerDegree(v) + highFaceCount(v)).
```

For a convex boundary and a generic height:

```text
global minimum contributes 1
global maximum contributes 1
every other vertex contributes 0
```

so the sum is `2`.

The only geometric theorem this route needs is local:

> At each convex vertex, a generic linear halfspace cuts the strictly convex cyclic vertex link in one cyclic interval.

This is much smaller than formalizing “the boundary is homeomorphic to `S²`.”  It fits the existing ch13 local machinery: strict face support, vertex links, cyclic orders, and strict convexity of the link.

## Route assessment

### Rank 1 — route #3 refined: generic-height / discrete-Morse count

This is the route I would implement first.

Instead of building a planar drawing and proving a tree-cotree theorem, prove Euler by counting lower edges and highest faces.  This is a purely combinatorial consequence of a local convex-link interval property.

#### Geometry input

For `P : TriangulatedEuclideanPolyhedron M`, supply or derive:

```lean
hsimple : M.IsSimpleGraph
hpos_inj : Function.Injective P.pos
htri : M.FaceRegular 3
hlink : ∀ v : M.Vertex, StrictConvexCyclicVertexLink P v
G : GenericHeightVector P
```

`GenericHeightVector P` means a vector `g : E3` such that `v ↦ ⟪g, P.pos v⟫` is injective on vertices.

The local convex-link theorem is:

```lean
lower neighbours at v form one cyclic interval in the cyclic vertex link.
```

That is the geometric payload.

#### Mathlib/repo gap

No ready theorem is needed about topological spheres.  The missing lemma is a finite convex-polygon lemma:

```lean
linear_halfspace_cut_of_strict_convex_cyclic_link_is_cyclic_interval
```

The repo already has the right local raw material in `ZinanCh13EuclLink.lean`: strict support lemmas, face-vertex classifiers, and `VertexLinkGeometry` with `turn_support`/`turn_strict` style fields.

#### Size

Expected new infrastructure:

```text
finite height-count layer:        300--700 lines
cyclic interval/list lemmas:       300--800 lines
local convex-link interval lemma:  500--1200 lines
generic height vector, if proved:  150--400 lines
```

The generic-height vector can initially be a field/certificate and proved later by finite hyperplane avoidance.

### Rank 2 — route #2 shelling

Convex polytopes are shellable, and shelling gives Euler cleanly.  A Lean version would choose a line shelling of all faces except one outer face, build a disk face-by-face, then add the outer face.

#### Geometry input

You need a shelling certificate:

```lean
structure BoundaryShelling (M : CombMap D) where
  outer : M.Face
  order : List M.Face
  nodup_order : order.Nodup
  covers : order.toFinset = Finset.univ.erase outer
  attach_kind : ∀ f ∈ order, AttachesAlongOneEdgeOrTwoAdjacentEdges M f
  final_boundary_is_outer : Prop
```

For triangular faces, each shelling step has one of two count types:

```text
attach along one boundary edge:       ΔV=1, ΔE=2, ΔF=1, Δχ=0
attach along two adjacent edges:      ΔV=0, ΔE=1, ΔF=1, Δχ=0
```

Start with one triangle, `χ = 1`.  After attaching all other faces except `outer`, still `χ = 1` for a disk.  Add the outer face: `χ = 2`.

#### Mathlib/repo gap

The count induction is straightforward once the shelling certificate exists.  The geometric work is proving line-shellability from convex support data.  That proof is global: it must order the faces as seen by a sweeping plane or a Schlegel projection and prove the attachment condition at every step.

#### Size

Likely:

```text
shelling certificate/count induction: 600--1200 lines
line-shelling from convexity:         1000--2500 lines
```

This is clean but more global than the height-Morse count.

### Rank 3 — route #3 literal tree-cotree

The tree-cotree proof is elementary once a planar cellular embedding is in hand.  It says: choose a primal spanning tree; the complementary non-tree edges form a dual spanning tree; hence

```text
E = (V - 1) + (F - 1)
```

and therefore `V - E + F = 2`.

#### Geometry input

You need a certificate like:

```lean
structure TreeCotreeCertificate (M : CombMap D) where
  primalTreeEdges : Finset M.Edge
  dualTreeEdges : Finset M.Edge
  disjoint : Disjoint primalTreeEdges dualTreeEdges
  cover : primalTreeEdges ∪ dualTreeEdges = Finset.univ
  primal_card : primalTreeEdges.card = M.V - 1
  dual_card : dualTreeEdges.card = M.F - 1
```

Then Euler is immediate:

```lean
theorem euler_of_treeCotree (C : TreeCotreeCertificate M) :
    M.eulerChar = 2 := by
  -- E = (V - 1) + (F - 1)
  -- rearrange in integers.
```

But to get `TreeCotreeCertificate` from geometry, you need a planar/cellular embedding theorem strong enough to prove that the complement of a primal spanning tree is a dual tree.  A convex polytope can supply such an embedding via a Schlegel diagram or central projection, but formalizing “noncrossing cellular planar drawing” plus the cut-cycle duality theorem is the main work.

#### Mathlib/repo gap

The repo has `CombMap` and `PlaneSimpleGraph` infrastructure, but no theorem deriving Euler from a tree-cotree certificate and no producer of the certificate from convex geometry.  `PlaneSimpleGraph.toCombMap_isSphereMap` transports an existing `P.IsSphereMap`; it does not produce Euler.

#### Size

Likely:

```text
tree/cotree finite theorem:       400--900 lines
planar embedding/cut-cycle proof: 1500--3500 lines
geometry-to-planar certificate:   800--2000 lines
```

This is elementary, but it introduces more global embedding infrastructure than the height-count route.

### Rank 4 — route #1 central projection / spherical triangulation / angle defect

Central projection from an interior point to the unit sphere is mathematically natural:

```text
x ↦ (x - c) / ‖x - c‖.
```

The boundary maps to a spherical triangulation.  Then Euler follows from a theorem that finite triangulations of `S²` have Euler characteristic `2`.

#### Geometry input

You need:

```lean
c : E3                         -- strict interior point
radialMap : boundary → sphere
radialMap_bijective_on_faces
spherical_triangles_disjoint_except_edges
spherical_triangles_cover_sphere
```

Then either:

1. use an Euler theorem for spherical triangulations, or
2. prove Descartes/Gauss-Bonnet angle defect:

```text
∑_v (2π - sum incident face angles at v) = 4π.
```

For triangular faces, the angle-defect route gives Euler from:

```text
∑ face angles = πF
3F = 2E
∑ defects = 4π
```

#### Mathlib/repo gap

There is no ready theorem in the repo of the form:

```lean
euler_of_finite_spherical_triangulation
sum_angle_defects_convex_polytope_eq_four_pi
boundary_of_convex_polytope_homeomorphic_sphere
```

The angle-defect route requires spherical area or a normal-fan area partition.  That brings in analytic geometry and measure-like reasoning.  It is elegant but not the shortest Lean path.

#### Size

Likely several thousand lines unless a strong spherical triangulation/Euler theorem already exists upstream.  In the current repo shape, it is not the shortest route.

### Rank 5 — route #4 Mathlib `Polytope`/faces API

I would not base the ch13 proof on a Mathlib polytope API right now.

The repo’s object is already custom:

```lean
TriangulatedEuclideanPolyhedron M
```

with face normals and support inequalities tied to `CombMap`.  I do not see a ready imported theorem matching:

```lean
convex_polytope_boundary_eulerChar_eq_two
polytope_boundary_is_sphere
EulerCharacteristic_of_polytope_boundary
```

Mathlib is still useful for finite sums, Euclidean inner products, affine independence, convexity, finite graph facts, and hyperplane avoidance, but not as a one-line Euler source for this exact structure.

## Recommended concrete theorem stack

### Step A: define height data and finite counts

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

abbrev OutDart (M : CombMap D) (v : M.Vertex) : Type _ :=
  {d : D // M.tail d = v}

/-- The interval property for a predicate on outgoing darts at one vertex.  The
implementation can use `M.σ.toList` or the `incidentDarts` API from
`ZinanCh13EuclLink`. -/
structure CyclicIntervalOnVertex (M : CombMap D) (v : M.Vertex)
    (p : OutDart M v → Prop) : Prop where
  card_true : ℕ
  is_empty_or_full_or_proper_interval : Prop

/-- Height data needed to run the finite Morse count. -/
structure HeightMorseData (M : CombMap D) where
  h : M.Vertex → ℝ

  /-- No edge is horizontal. -/
  edge_ne : ∀ d : D, h (M.tail d) ≠ h (M.head d)

  /-- Each triangular face has a unique highest vertex. -/
  face_unique_high :
    ∀ f : M.Face, ∃! v : M.Vertex,
      (∃ d : D, M.dartFace d = f ∧ M.tail d = v) ∧
      ∀ w : M.Vertex,
        (∃ d : D, M.dartFace d = f ∧ M.tail d = w) → h w ≤ h v

  /-- Lower neighbours form a cyclic interval around each vertex. -/
  lower_interval : ∀ v : M.Vertex,
    CyclicIntervalOnVertex M v
      (fun d : OutDart M v => h (M.head d.1) < h v)

  unique_min : ∃! v : M.Vertex, ∀ w : M.Vertex, h v ≤ h w
  unique_max : ∃! v : M.Vertex, ∀ w : M.Vertex, h w ≤ h v

namespace HeightMorseData

def lowerDarts (H : HeightMorseData M) (v : M.Vertex) : Finset D :=
  Finset.univ.filter (fun d => M.tail d = v ∧ H.h (M.head d) < H.h v)

def lowerDegree (H : HeightMorseData M) (v : M.Vertex) : ℕ :=
  (H.lowerDarts v).card

/-- `tail d` is the highest vertex of `dartFace d`.  For a triangular face, the
other two vertices at this corner are `head d` and `head (σ⁻¹ d)`. -/
def highCorner (H : HeightMorseData M) (d : D) : Prop :=
  H.h (M.head d) < H.h (M.tail d) ∧
  H.h (M.head (M.σ.symm d)) < H.h (M.tail d)

def highFaceCount (H : HeightMorseData M) (v : M.Vertex) : ℕ :=
  (Finset.univ.filter (fun d : D => M.tail d = v ∧ H.highCorner d)).card

end HeightMorseData
```

### Step B: finite counting lemmas

```lean
namespace HeightMorseData

/-- Each unoriented edge is counted exactly once by the higher endpoint. -/
theorem sum_lowerDegree_eq_E
    (H : HeightMorseData M) :
    (∑ v : M.Vertex, H.lowerDegree v) = M.E := by
  -- Use α-orbits as edges.
  -- For every dart `d`, exactly one of `d` or `M.α d` is lower, by `H.edge_ne d`.
  -- Then count one chosen dart per α-orbit.
  -- Existing tools: `CombMap.alpha_sameCycle_iff`, `CombMap.two_mul_E_eq_card`.
  sorry

/-- Each triangular face is counted exactly once by its highest corner. -/
theorem sum_highFaceCount_eq_F
    (H : HeightMorseData M)
    (P : TriangulatedEuclideanPolyhedron M) :
    (∑ v : M.Vertex, H.highFaceCount v) = M.F := by
  -- Use `H.face_unique_high` to choose the highest vertex of each face.
  -- Use triangular face API to identify the unique dart/corner at that vertex.
  -- Existing repo lemmas:
  --   `faceVertex_eq_tail_or_head_or_tail_phi2_of_dartFace_eq`
  --   `tail_phi_phi_eq_head_sigma_symm_of_triangular_euclidean`
  --   `P.every_face_triangle`.
  sorry

/-- Local Morse contribution.  For a cyclic interval of lower neighbours, the
number of high faces at `v` is:
`0` at a minimum, `k-1` for a proper lower block of length `k`, and `degree` at a maximum. -/
theorem local_morse_contribution
    (H : HeightMorseData M) (v : M.Vertex) :
    ((1 : ℤ) - (H.lowerDegree v : ℤ) + (H.highFaceCount v : ℤ)) =
      if (∀ w : M.Vertex, H.h v ≤ H.h w) ∨ (∀ w : M.Vertex, H.h w ≤ H.h v)
      then 1 else 0 := by
  -- Pure cyclic-list lemma using `H.lower_interval v`.
  -- If lower block length k:
  --   k=0      => min, highFaceCount=0, contribution=1
  --   0<k<n    => highFaceCount=k-1, contribution=0
  --   k=n      => max, highFaceCount=n, contribution=1
  sorry

/-- Euler from height-Morse data. -/
theorem eulerChar_eq_two_of_heightMorseData
    (H : HeightMorseData M)
    (P : TriangulatedEuclideanPolyhedron M) :
    M.eulerChar = 2 := by
  classical
  have hE := H.sum_lowerDegree_eq_E
  have hF := H.sum_highFaceCount_eq_F P
  have hsum :
      M.eulerChar =
        ∑ v : M.Vertex,
          ((1 : ℤ) - (H.lowerDegree v : ℤ) + (H.highFaceCount v : ℤ)) := by
    -- Expand `CombMap.eulerChar`, rewrite the lower-edge and high-face sums.
    -- `∑ v, 1 = M.V` by `CombMap.V` definition.
    sorry
  rw [hsum]
  -- Use `local_morse_contribution`, then unique min and unique max.
  -- The min and max are distinct for a nondegenerate boundary with at least one edge.
  sorry

end HeightMorseData
```

### Step C: get `HeightMorseData` from convex geometry

```lean
/-- A generic height vector: no two vertices have equal height. -/
structure GenericHeightVector (P : TriangulatedEuclideanPolyhedron M) where
  g : Ch13Euclidean.E3
  height_injective : Function.Injective (fun v : M.Vertex => inner ℝ g (P.pos v))

/-- Generic height exists by finite hyperplane avoidance.  This can be carried as
input first, then proved later. -/
theorem exists_genericHeightVector
    (P : TriangulatedEuclideanPolyhedron M)
    (hpos_inj : Function.Injective P.pos) :
    ∃ G : GenericHeightVector P := by
  -- Avoid finitely many hyperplanes
  -- `{g | inner g (P.pos u - P.pos v) = 0}` for `u ≠ v`.
  -- A concrete proof can use a polynomial curve
  -- `g(t) = b0 + t • b1 + t^2 • b2` and avoid finitely many roots.
  sorry

/-- The central geometric lemma: cutting a strict convex vertex link by a linear
height inequality gives one cyclic interval. -/
theorem lower_interval_of_strict_convex_vertexLink
    (P : TriangulatedEuclideanPolyhedron M)
    (hsimple : M.IsSimpleGraph)
    (hlink : ∀ v : M.Vertex, VertexLinkGeometry P v)
    (G : GenericHeightVector P)
    (v : M.Vertex) :
    CyclicIntervalOnVertex M v
      (fun d : OutDart M v =>
        inner ℝ G.g (P.pos (M.head d.1)) < inner ℝ G.g (P.pos v)) := by
  -- Rewrite as `inner G.g (edgeVec P d.1) < 0`.
  -- Use strict convexity of the cyclic vertex link: a line/halfspace intersects
  -- the boundary of a strict convex polygon in a connected interval.
  -- Existing local inputs are the link's cyclic order and strict turn/support lemmas.
  sorry

/-- Build the height-Morse package from convex geometry. -/
def heightMorseData_of_convex_boundary
    (P : TriangulatedEuclideanPolyhedron M)
    (hsimple : M.IsSimpleGraph)
    (hlink : ∀ v : M.Vertex, VertexLinkGeometry P v)
    (G : GenericHeightVector P) :
    HeightMorseData M where
  h := fun v => inner ℝ G.g (P.pos v)
  edge_ne := by
    intro d hEq
    have htail_head : P.pos (M.tail d) = P.pos (M.head d) :=
      G.height_injective hEq
    exact P.edge_nondegenerate d htail_head
  face_unique_high := by
    intro f
    -- finite maximum over the three face vertices, uniqueness by `G.height_injective`.
    sorry
  lower_interval := by
    intro v
    exact lower_interval_of_strict_convex_vertexLink P hsimple hlink G v
  unique_min := by
    -- finite type + injective height => unique minimum.
    sorry
  unique_max := by
    -- finite type + injective height => unique maximum.
    sorry

/-- Final Euler theorem from the convex-boundary package. -/
theorem convex_boundary_eulerChar_eq_two
    (P : TriangulatedEuclideanPolyhedron M)
    (hsimple : M.IsSimpleGraph)
    (hlink : ∀ v : M.Vertex, VertexLinkGeometry P v)
    (G : GenericHeightVector P) :
    M.eulerChar = 2 := by
  exact HeightMorseData.eulerChar_eq_two_of_heightMorseData
    (heightMorseData_of_convex_boundary P hsimple hlink G) P

end ProofsInTheBook.Ch13EulerFromHeight
```

## Why the local interval lemma is the right geometry target

At a convex vertex, the incident neighbours form a strict convex polygon in the tangent/link plane.  A linear height inequality cuts that polygon by a line.  The vertices below the line occur consecutively along the polygon boundary.

This is the same elementary fact used in computational geometry when clipping a convex polygon by a halfplane.  In Lean, phrase it over the finite cyclic list produced by `VertexLinkGeometry`, not over arbitrary subsets of the plane.

A good final statement is:

```lean
theorem StrictConvexCyclicLink.lower_set_is_cyclic_interval
    (L : StrictConvexCyclicLink E3)
    (ℓ : E3 →L[ℝ] ℝ)
    (hgeneric : ∀ i, ℓ (L.p i) ≠ 0) :
    CyclicInterval (fun i => ℓ (L.p i) < 0)
```

Then instantiate

```lean
ℓ x = inner ℝ G.g (x - P.pos v)
```

for the vertex link.

## Interaction with existing ch13 code

The current repo has:

```lean
VertexLinkGeometry P v
```

with fields giving neighbour vertices in cyclic order and oriented triangle supports.  It can produce a `VertexStar`; it also proves strict turn/support facts.  Use this, or a weaker extracted structure, to prove the local interval lemma.

For the construct-`σ` route, produce `VertexLinkGeometry` from `σ = σ_geo` rather than from old `RotationFaithful`.  The Euler proof does not care about the old orientation field; it only needs the cyclic convex link.

## Final recommendation

Implement in this order:

1. `HeightMorseData` and the finite theorem `eulerChar_eq_two_of_heightMorseData`.
2. `CyclicInterval` lemmas for a Boolean predicate on a cyclic list.
3. The local strict-convex-link halfspace lemma.
4. `GenericHeightVector`, first as an input field, later by finite hyperplane avoidance.
5. The wrapper `convex_boundary_eulerChar_eq_two`.

This gives `M.eulerChar = 2` from the convex triangulated boundary with the smallest new global infrastructure.  It is the concrete path I would take before central projection, shelling, or tree-cotree.