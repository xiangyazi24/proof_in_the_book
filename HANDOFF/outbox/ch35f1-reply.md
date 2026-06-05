# File 1 public API: `ProofsInTheBook/PlanarMapSimple.lean`

Verified with:

```bash
/data/home/xhuan5/.elan/bin/lake env lean ProofsInTheBook/PlanarMapSimple.lean
```

The file imports only:

```lean
import ProofsInTheBook.PlanarMapEuler
```

Public declarations:

```lean
ProofsInTheBook.PlanarMap.CombMap.Vertex.{u_1}
  {D : Type u_1} [Fintype D] [DecidableEq D] (M : CombMap D) : Type u_1

ProofsInTheBook.PlanarMap.CombMap.Face.{u_1}
  {D : Type u_1} [Fintype D] [DecidableEq D] (M : CombMap D) : Type u_1

ProofsInTheBook.PlanarMap.CombMap.tail.{u_1}
  {D : Type u_1} [Fintype D] [DecidableEq D] (M : CombMap D) (d : D) :
  M.Vertex

ProofsInTheBook.PlanarMap.CombMap.head.{u_1}
  {D : Type u_1} [Fintype D] [DecidableEq D] (M : CombMap D) (d : D) :
  M.Vertex

ProofsInTheBook.PlanarMap.CombMap.dartFace.{u_1}
  {D : Type u_1} [Fintype D] [DecidableEq D] (M : CombMap D) (d : D) :
  M.Face

ProofsInTheBook.PlanarMap.CombMap.dartEdge.{u_1}
  {D : Type u_1} [Fintype D] [DecidableEq D] (M : CombMap D) (d : D) :
  Sym2 M.Vertex

ProofsInTheBook.PlanarMap.CombMap.alpha_alpha.{u_1}
  {D : Type u_1} [Fintype D] [DecidableEq D] (M : CombMap D) (d : D) :
  M.α (M.α d) = d

ProofsInTheBook.PlanarMap.CombMap.tail_sigma.{u_1}
  {D : Type u_1} [Fintype D] [DecidableEq D] (M : CombMap D) (d : D) :
  M.tail (M.σ d) = M.tail d

ProofsInTheBook.PlanarMap.CombMap.tail_phi.{u_1}
  {D : Type u_1} [Fintype D] [DecidableEq D] (M : CombMap D) (d : D) :
  M.tail (M.φ d) = M.head d

ProofsInTheBook.PlanarMap.CombMap.tail_alpha.{u_1}
  {D : Type u_1} [Fintype D] [DecidableEq D] (M : CombMap D) (d : D) :
  M.tail (M.α d) = M.head d

ProofsInTheBook.PlanarMap.CombMap.head_alpha.{u_1}
  {D : Type u_1} [Fintype D] [DecidableEq D] (M : CombMap D) (d : D) :
  M.head (M.α d) = M.tail d

ProofsInTheBook.PlanarMap.CombMap.dartEdge_alpha.{u_1}
  {D : Type u_1} [Fintype D] [DecidableEq D] (M : CombMap D) (d : D) :
  M.dartEdge (M.α d) = M.dartEdge d

ProofsInTheBook.PlanarMap.CombMap.Adj.{u_1}
  {D : Type u_1} [Fintype D] [DecidableEq D] (M : CombMap D)
  (u v : M.Vertex) : Prop

ProofsInTheBook.PlanarMap.CombMap.adj_symm.{u_1}
  {D : Type u_1} [Fintype D] [DecidableEq D] (M : CombMap D)
  {u v : M.Vertex} (h : M.Adj u v) : M.Adj v u

ProofsInTheBook.PlanarMap.CombMap.adj_of_dart.{u_1}
  {D : Type u_1} [Fintype D] [DecidableEq D] (M : CombMap D) (d : D) :
  M.Adj (M.tail d) (M.head d)

ProofsInTheBook.PlanarMap.CombMap.toSimpleGraph.{u_1}
  {D : Type u_1} [Fintype D] [DecidableEq D] (M : CombMap D) :
  SimpleGraph M.Vertex

ProofsInTheBook.PlanarMap.CombMap.toSimpleGraph_adj.{u_1}
  {D : Type u_1} [Fintype D] [DecidableEq D] (M : CombMap D)
  (u v : M.Vertex) : M.toSimpleGraph.Adj u v ↔ u ≠ v ∧ M.Adj u v

ProofsInTheBook.PlanarMap.CombMap.IsSimpleGraph.{u_1}
  {D : Type u_1} [Fintype D] [DecidableEq D] (M : CombMap D) : Prop

ProofsInTheBook.PlanarMap.CombMap.IsSimpleGraph.no_loop.{u_1}
  {D : Type u_1} [Fintype D] [DecidableEq D] {M : CombMap D}
  (self : M.IsSimpleGraph) (d : D) : M.tail d ≠ M.head d

ProofsInTheBook.PlanarMap.CombMap.IsSimpleGraph.no_parallel.{u_1}
  {D : Type u_1} [Fintype D] [DecidableEq D] {M : CombMap D}
  (self : M.IsSimpleGraph) {d e : D} :
  M.dartEdge d = M.dartEdge e → M.α.SameCycle d e

ProofsInTheBook.PlanarMap.CombMap.toSimpleGraph_adj_of_dart.{u_1}
  {D : Type u_1} [Fintype D] [DecidableEq D]
  (M : CombMap D) (hM : M.IsSimpleGraph) (d : D) :
  M.toSimpleGraph.Adj (M.tail d) (M.head d)

ProofsInTheBook.PlanarMap.CombMap.noLoopAt_of_isSimpleGraph.{u_1}
  {D : Type u_1} [Fintype D] [DecidableEq D]
  (M : CombMap D) (hM : M.IsSimpleGraph) (v : M.Vertex) (d : D) :
  M.tail d = v → M.head d ≠ v

ProofsInTheBook.PlanarMap.CombMap.noLoopAt_dart_of_isSimpleGraph.{u_1}
  {D : Type u_1} [Fintype D] [DecidableEq D]
  (M : CombMap D) (hM : M.IsSimpleGraph) (v d : D)
  (hd : M.σ.SameCycle v d) : ¬M.σ.SameCycle v (M.α d)

ProofsInTheBook.PlanarMap.CombMap.alpha_sameCycle_of_dartEdge_eq.{u_1}
  {D : Type u_1} [Fintype D] [DecidableEq D]
  (M : CombMap D) (hM : M.IsSimpleGraph) {d e : D}
  (h : M.dartEdge d = M.dartEdge e) : M.α.SameCycle d e

ProofsInTheBook.PlanarMap.CombMap.alpha_sameCycle_of_same_endpoints.{u_1}
  {D : Type u_1} [Fintype D] [DecidableEq D]
  (M : CombMap D) (hM : M.IsSimpleGraph) {d e : D}
  (htail : M.tail d = M.tail e) (hhead : M.head d = M.head e) :
  M.α.SameCycle d e

ProofsInTheBook.PlanarMap.CombMap.alpha_sameCycle_of_same_endpoints_symm.{u_1}
  {D : Type u_1} [Fintype D] [DecidableEq D]
  (M : CombMap D) (hM : M.IsSimpleGraph) {d e : D}
  (htail : M.tail d = M.head e) (hhead : M.head d = M.tail e) :
  M.α.SameCycle d e

ProofsInTheBook.PlanarMap.CombMap.IsFaceTriangle.{u_1}
  {D : Type u_1} [Fintype D] [DecidableEq D] (M : CombMap D)
  (d₀ d₁ d₂ : D) : Prop

ProofsInTheBook.PlanarMap.CombMap.dartEdge_eq_mk_tail_tail_phi.{u_1}
  {D : Type u_1} [Fintype D] [DecidableEq D]
  (M : CombMap D) (d : D) : M.dartEdge d = s(M.tail d, M.tail (M.φ d))

ProofsInTheBook.PlanarMap.CombMap.isFaceTriangle_vertices_pairwiseDistinct.{u_1}
  {D : Type u_1} [Fintype D] [DecidableEq D]
  (M : CombMap D) (hM : M.IsSimpleGraph) {d₀ d₁ d₂ : D}
  (htri : M.IsFaceTriangle d₀ d₁ d₂) :
  M.tail d₀ ≠ M.tail d₁ ∧ M.tail d₁ ≠ M.tail d₂ ∧ M.tail d₂ ≠ M.tail d₀

ProofsInTheBook.PlanarMap.CombMap.isFaceTriangle_boundaryEdges_pairwiseDistinct.{u_1}
  {D : Type u_1} [Fintype D] [DecidableEq D]
  (M : CombMap D) (hM : M.IsSimpleGraph) {d₀ d₁ d₂ : D}
  (htri : M.IsFaceTriangle d₀ d₁ d₂) :
  M.dartEdge d₀ ≠ M.dartEdge d₁ ∧
  M.dartEdge d₁ ≠ M.dartEdge d₂ ∧
  M.dartEdge d₂ ≠ M.dartEdge d₀
```

Compatibility note: this file does not redefine `CombMap.NoLoopAt`, `vertexDarts`, or any
deletion API from `PlanarMapDelete`.  The available no-loop consequences are
`noLoopAt_of_isSimpleGraph` and `noLoopAt_dart_of_isSimpleGraph`; the latter is the one to
bridge into the existing deletion `NoLoopAt` after importing `PlanarMapDelete`.
