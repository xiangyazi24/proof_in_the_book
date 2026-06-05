# File 7 public API: `ProofsInTheBook/PlanarMapBoundaryFan.lean`

Verified with:

```bash
/data/home/xhuan5/.elan/bin/lake build ProofsInTheBook.PlanarMapNearTriangulation
/data/home/xhuan5/.elan/bin/lake env lean ProofsInTheBook/PlanarMapBoundaryFan.lean
```

The file imports only:

```lean
import ProofsInTheBook.PlanarMapNearTriangulation
```

Important design note: the current File 3 API does not expose a normalized
vertex-rotation list or the theorem constructing the boundary fan from that
rotation.  Therefore this file introduces a certificate type
`BoundaryVertexFan`; all public lemmas prove consequences of such a certificate
without `sorry`/`axiom`/`admit`.

Main definitions, all under
`ProofsInTheBook.PlanarMap.CombMap.NearTriangulation`:

```lean
def IsBaseTriangle (hNT : NearTriangulation M) : Prop
def consecutivePairs {α : Type*} (xs : List α) : List (α × α)
def fanPath (x : M.Vertex) (interior : List M.Vertex) (w : M.Vertex) :
  List M.Vertex
def FaceIncidentAtVertex (M : CombMap D) (f : M.Face) (v : M.Vertex) : Prop
```

Fan triangle and exact-face certificates:

```lean
structure FanTriangle (hNT : NearTriangulation M)
  (v0 a b : M.Vertex)

FanTriangle.face
FanTriangle.face_ne_outer
FanTriangle.faceLen_eq_three
FanTriangle.vertices_pairwiseDistinct

structure NeighborRotationOrder (M : CombMap D) (v0 : M.Vertex)
  (neighbors : List M.Vertex)

structure IncidentNonOuterFacesExactly (hNT : NearTriangulation M)
  (v0 : M.Vertex) (path : List M.Vertex)
```

Boundary fan certificate:

```lean
structure BoundaryVertexFan (hNT : NearTriangulation M) (v0 : M.Vertex)

BoundaryVertexFan.path
BoundaryVertexFan.t
```

Fields include endpoints `x,w`, interior list `z_1,...,z_t`, proofs that
`v0,x,w` are old boundary vertices, the neighbor rotation-order certificate,
the exact incident non-outer face certificate, and the chordless consequences:
path nodup, interior vertices not on the old boundary, and
`interior = [] ↔ hNT.IsBaseTriangle`.

Public lemmas:

```lean
theorem boundaryVertex_fan_exists
  (fan : BoundaryVertexFan hNT v0) :
    ∃ (x : M.Vertex) (zs : List M.Vertex) (w : M.Vertex),
      hNT.outerCycle.IsBoundaryVertex v0 ∧
      hNT.outerCycle.IsBoundaryVertex x ∧
      hNT.outerCycle.IsBoundaryVertex w ∧
      Nonempty (NeighborRotationOrder M v0 (fanPath x zs w)) ∧
      Nonempty (IncidentNonOuterFacesExactly hNT v0 (fanPath x zs w))

def boundaryVertex_fan_faces_exact
  (fan : BoundaryVertexFan hNT v0) :
    IncidentNonOuterFacesExactly hNT v0 fan.path

theorem fan_path_simple_of_chordless
  (fan : BoundaryVertexFan hNT v0)
  (hchordless : BoundaryChordless hNT.outerCycle) :
    fan.path.Nodup

theorem fan_interior_vertices_not_boundary_of_chordless
  (fan : BoundaryVertexFan hNT v0)
  (hchordless : BoundaryChordless hNT.outerCycle) :
    ∀ z : M.Vertex, z ∈ fan.interior →
      ¬ hNT.outerCycle.IsBoundaryVertex z

theorem fan_interior_vertices_nodup_of_chordless
  (fan : BoundaryVertexFan hNT v0)
  (hchordless : BoundaryChordless hNT.outerCycle) :
    fan.interior.Nodup

theorem fan_interior_vertices_ne_boundary_endpoints_of_chordless
  (fan : BoundaryVertexFan hNT v0)
  (hchordless : BoundaryChordless hNT.outerCycle) :
    ∀ z : M.Vertex, z ∈ fan.interior →
      z ≠ v0 ∧ z ≠ fan.x ∧ z ≠ fan.w

theorem fan_path_meets_old_boundary_only_at_ends
  (fan : BoundaryVertexFan hNT v0)
  (hchordless : BoundaryChordless hNT.outerCycle) :
    ∀ y : M.Vertex, y ∈ fan.path →
      hNT.outerCycle.IsBoundaryVertex y →
        y = fan.x ∨ y = fan.w

theorem fan_nonempty_of_chordless_of_not_triangle
  (fan : BoundaryVertexFan hNT v0)
  (hchordless : BoundaryChordless hNT.outerCycle)
  (hnot_base : 3 < M.V) :
    1 ≤ fan.t

theorem fan_empty_iff_base_triangle_of_chordless
  (fan : BoundaryVertexFan hNT v0)
  (hchordless : BoundaryChordless hNT.outerCycle) :
    fan.t = 0 ↔ hNT.IsBaseTriangle
```

No `sorry`, `axiom`, or `admit` occurs in
`PlanarMapBoundaryFan.lean`.
