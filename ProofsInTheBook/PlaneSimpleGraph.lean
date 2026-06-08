import ProofsInTheBook.PlanarMap

/-!
# Plane simple graphs (Layer 3, toward the Five Color Theorem)

A simple graph together with a cellular sphere embedding (a rotation system). This is the
object the Five Color Theorem operates on: it has vertices, adjacency, and the embedding data
(`tail`/`head`/`α`/`σ`) needed for vertex deletion and Kempe-chain arguments. It maps to a
`CombMap` (forgetting the simple-graph layer) so the Euler-characteristic machinery applies.
-/

namespace ProofsInTheBook.PlanarMap

open ProofsInTheBook.PlanarMap

/-- A finite simple graph with a cellular sphere embedding given by a rotation system on darts. -/
structure PlaneSimpleGraph (V D : Type*) [Fintype V] [DecidableEq V]
    [Fintype D] [DecidableEq D] where
  /-- The underlying simple graph. -/
  G : SimpleGraph V
  /-- Tail vertex of a dart. -/
  tail : D → V
  /-- Head vertex of a dart. -/
  head : D → V
  /-- Edge involution. -/
  α : Equiv.Perm D
  /-- Vertex rotation. -/
  σ : Equiv.Perm D
  α_invol : α * α = 1
  α_no_fixed : ∀ d, α d ≠ d
  reverse_tail : ∀ d, tail (α d) = head d
  reverse_head : ∀ d, head (α d) = tail d
  dart_edge : ∀ d, G.Adj (tail d) (head d)
  edge_darts : ∀ {u v : V}, G.Adj u v → ∃! d : D, tail d = u ∧ head d = v
  σ_preserves_tail : ∀ d, tail (σ d) = tail d
  σ_vertex_cycle : ∀ d e : D, tail d = tail e → σ.SameCycle d e
  connected : G.Connected

namespace PlaneSimpleGraph

variable {V D : Type*} [Fintype V] [DecidableEq V] [Fintype D] [DecidableEq D]

/-- The underlying combinatorial map (forgetting the simple-graph layer). -/
def toCombMap (M : PlaneSimpleGraph V D) : CombMap D where
  α := M.α
  σ := M.σ
  α_invol := M.α_invol
  α_no_fixed := M.α_no_fixed

/-- Number of vertices (of the simple graph). -/
def numVertices (M : PlaneSimpleGraph V D) : ℕ := Fintype.card V

/-- Number of edges = darts / 2. -/
def numEdges (M : PlaneSimpleGraph V D) : ℕ := Fintype.card D / 2

/-- Number of faces = number of `φ = σ * α` orbits. -/
def numFaces (M : PlaneSimpleGraph V D) : ℕ := M.toCombMap.F

/-- Euler characteristic of the embedding. -/
def eulerChar (M : PlaneSimpleGraph V D) : ℤ :=
  (M.numVertices : ℤ) - (M.numEdges : ℤ) + (M.numFaces : ℤ)

/-- The embedding is a sphere (plane) embedding: Euler characteristic `2`. -/
def IsSphereMap (M : PlaneSimpleGraph V D) : Prop :=
  M.eulerChar = 2

end PlaneSimpleGraph

end ProofsInTheBook.PlanarMap
