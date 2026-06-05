# File 2 public API: `ProofsInTheBook/PlanarMapBoundary.lean`

Verified with:

```bash
/data/home/xhuan5/.elan/bin/lake env lean ProofsInTheBook/PlanarMapBoundary.lean
```

I also built only the new module to materialize the `.olean` for API checks:

```bash
/data/home/xhuan5/.elan/bin/lake build ProofsInTheBook.PlanarMapBoundary
```

The file imports only:

```lean
import ProofsInTheBook.PlanarMapSimple
```

Main public declarations:

```lean
ProofsInTheBook.PlanarMap.CombMap.cyclicNext
  {n : ℕ} (h : 0 < n) (i : Fin n) : Fin n

ProofsInTheBook.PlanarMap.CombMap.faceOrbitFinset
  {D : Type u} [Fintype D] [DecidableEq D]
  (M : CombMap D) (f : M.Face) : Finset D

ProofsInTheBook.PlanarMap.CombMap.NormalizedCyclicDartList
  (M : CombMap D) (f : M.Face) (root : D) (darts : List D) : Prop

ProofsInTheBook.PlanarMap.CombMap.BoundaryPath
  (M : CombMap D) (u v : M.Vertex) : Type u

ProofsInTheBook.PlanarMap.CombMap.BoundaryPath.internalVertices
ProofsInTheBook.PlanarMap.CombMap.BoundaryPath.HasInternalVertex
ProofsInTheBook.PlanarMap.CombMap.BoundaryPath.length

ProofsInTheBook.PlanarMap.CombMap.BoundaryArcSplit
  (M : CombMap D) (boundaryVertices : List M.Vertex)
  (boundaryEdges : List (Sym2 M.Vertex)) (u v : M.Vertex) : Type u

ProofsInTheBook.PlanarMap.CombMap.BoundaryCycle
  (M : CombMap D) (f : M.Face) : Type u
```

`BoundaryCycle` stores:

```lean
root : D
darts : List D
vertices : List M.Vertex
edges : List (Sym2 M.Vertex)
normalized : NormalizedCyclicDartList M f root darts
vertices_eq : vertices = darts.map M.tail
edges_eq : edges = darts.map M.dartEdge
consecutive_phi :
  ∀ i : Fin darts.length,
    darts.get (cyclicNext normalized.length_pos i) = M.φ (darts.get i)
consecutive_vertex :
  ∀ i : Fin darts.length,
    M.tail (darts.get (cyclicNext normalized.length_pos i)) = M.head (darts.get i)
arcSplit :
  ∀ ⦃u v : M.Vertex⦄,
    u ≠ v → u ∈ vertices → v ∈ vertices →
      BoundaryArcSplit M vertices edges u v
```

Boundary-cycle predicates and accessors:

```lean
BoundaryCycle.IsBoundaryVertex (C : BoundaryCycle M f) (v : M.Vertex) : Prop
BoundaryCycle.IsBoundaryEdge (C : BoundaryCycle M f) (e : Sym2 M.Vertex) : Prop
BoundaryCycle.ProperBoundaryPair (C : BoundaryCycle M f) (u v : M.Vertex) : Prop
BoundaryCycle.VertexNodup (C : BoundaryCycle M f) : Prop
BoundaryCycle.EdgeNodup (C : BoundaryCycle M f) : Prop
BoundaryCycle.length (C : BoundaryCycle M f) : ℕ
```

Core lemmas:

```lean
BoundaryCycle.mem_darts_iff
  (C : BoundaryCycle M f) (d : D) : d ∈ C.darts ↔ M.dartFace d = f

BoundaryCycle.consecutive_dart_vertex_matching
  (C : BoundaryCycle M f) (i : Fin C.darts.length) :
    M.tail (C.darts.get (cyclicNext C.normalized.length_pos i)) =
      M.head (C.darts.get i)

boundary_cycle_two_arcs
  (C : BoundaryCycle M f) {u v : M.Vertex}
  (hne : u ≠ v) (hu : C.IsBoundaryVertex u) (hv : C.IsBoundaryVertex v) :
    BoundaryArcSplit M C.vertices C.edges u v

BoundaryCycle.two_arcs
  (C : BoundaryCycle M f) {u v : M.Vertex}
  (hne : u ≠ v) (hu : C.IsBoundaryVertex u) (hv : C.IsBoundaryVertex v) :
    BoundaryArcSplit M C.vertices C.edges u v
```

Chord API:

```lean
BoundaryCycle.Chord (C : BoundaryCycle M f) (u v : M.Vertex) : Prop
BoundaryChord (C : BoundaryCycle M f) (u v : M.Vertex) : Prop
BoundaryChordless (C : BoundaryCycle M f) : Prop

BoundaryCycle.Chord.proper (h : C.Chord u v) :
  C.ProperBoundaryPair u v

BoundaryCycle.chord_not_boundary_edge (h : C.Chord u v) :
  ¬ C.IsBoundaryEdge s(u, v)

chord_not_boundary_edge (h : C.Chord u v) :
  ¬ C.IsBoundaryEdge s(u, v)
```

Arc-split bookkeeping for strict decrease:

```lean
BoundaryArcSplit.path₁_internal_iff_proper_boundary
  (S : BoundaryArcSplit M C.vertices C.edges u v) :
    S.path₁.HasInternalVertex ↔ C.ProperBoundaryPair u v

BoundaryArcSplit.path₂_internal_iff_proper_boundary
  (S : BoundaryArcSplit M C.vertices C.edges u v) :
    S.path₂.HasInternalVertex ↔ C.ProperBoundaryPair u v

BoundaryCycle.arc₁_internal_iff_proper
  (S : BoundaryArcSplit M C.vertices C.edges u v) :
    S.path₁.HasInternalVertex ↔ C.ProperBoundaryPair u v

BoundaryCycle.arc₂_internal_iff_proper
  (S : BoundaryArcSplit M C.vertices C.edges u v) :
    S.path₂.HasInternalVertex ↔ C.ProperBoundaryPair u v

BoundaryCycle.two_arcs_internally_nonempty_of_chord
  (h : C.Chord u v) :
    ∃ S : BoundaryArcSplit M C.vertices C.edges u v,
      S.path₁.HasInternalVertex ∧ S.path₂.HasInternalVertex
```

No `sorry`, `axiom`, or `admit` occurs in `PlanarMapBoundary.lean`.
