# File 3 public API: `ProofsInTheBook/PlanarMapNearTriangulation.lean`

Verified with:

```bash
/data/home/xhuan5/.elan/bin/lake env lean ProofsInTheBook/PlanarMapNearTriangulation.lean
```

The file imports only:

```lean
import ProofsInTheBook.PlanarMapBoundary
```

Main structure:

```lean
ProofsInTheBook.PlanarMap.CombMap.NearTriangulation
  (M : CombMap D) : Type _
```

Fields:

```lean
sphere       : M.IsSphereMap
simpleGraph  : M.IsSimpleGraph
outerFace    : M.Face
outerCycle   : BoundaryCycle M outerFace
outer_simple : outerCycle.VertexNodup
outer_len    : 3 ≤ outerCycle.length
inner_tri    : ∀ f : M.Face, f ≠ outerFace → M.faceLen f = 3
```

General orbit/cardinality helpers:

```lean
CombMap.dartFace_phi
CombMap.dartFace_phi_symm
CombMap.phi_ne_self_of_isSimpleGraph
CombMap.vertexDegree_tail_eq_card_support_cycleOf
CombMap.faceLen_dartFace_eq_card_support_cycleOf
CombMap.card_support_cycleOf_eq_two_of_apply_apply_eq_self
CombMap.BoundaryCycle.faceLen_eq_length
CombMap.BoundaryCycle.tail_injective_on_darts
CombMap.faceLen_three_phi_cube_eq_self
CombMap.faceLen_three_isFaceTriangle
CombMap.faceLen_three_vertices_pairwiseDistinct
```

Near-triangulation facts:

```lean
NearTriangulation.outer_faceLen_eq_outerCycle_length
NearTriangulation.boundary_dart_no_loop
NearTriangulation.boundary_dart_sigma_ne
NearTriangulation.boundary_vertex_degree_ge_two
NearTriangulation.inner_faceLen_eq_three
NearTriangulation.inner_face_isFaceTriangle
NearTriangulation.inner_face_vertices_pairwiseDistinct
NearTriangulation.chord_endpoints_nonadjacent_on_boundary
NearTriangulation.same_face_edge_is_boundary_edge
NearTriangulation.no_bridges
NearTriangulation.edge_faces_distinct_or_boundary_edge
```

Bridge formulation exposed for deletion:

```lean
lemma NearTriangulation.no_bridges {d : D}
    (hsame : M.dartFace d = M.dartFace (M.α d)) :
    hNT.outerCycle.IsBoundaryEdge (M.dartEdge d)

lemma NearTriangulation.edge_faces_distinct_or_boundary_edge (d : D) :
    M.dartFace d ≠ M.dartFace (M.α d) ∨
      hNT.outerCycle.IsBoundaryEdge (M.dartEdge d)
```

No `sorry`, `axiom`, or `admit` occurs in `PlanarMapNearTriangulation.lean`.
