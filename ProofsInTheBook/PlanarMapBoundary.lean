import ProofsInTheBook.PlanarMapSimple

/-!
# Boundary cycles and boundary chords for combinatorial maps

This file is the boundary layer over `PlanarMapSimple`.  A boundary cycle is
deliberately data: it stores a normalized cyclic list of darts for a chosen
face, the induced cyclic vertex and edge lists, and the arc-splitting
bookkeeping used by the chord split construction.
-/

namespace ProofsInTheBook.PlanarMap

open Equiv

namespace CombMap

variable {D : Type*} [Fintype D] [DecidableEq D]

/-- Cyclic successor on a nonempty finite index type. -/
def cyclicNext {n : ℕ} (h : 0 < n) (i : Fin n) : Fin n :=
  ⟨(i.1 + 1) % n, Nat.mod_lt _ h⟩

@[simp]
lemma cyclicNext_val {n : ℕ} (h : 0 < n) (i : Fin n) :
    (cyclicNext h i).1 = (i.1 + 1) % n :=
  rfl

/-- The dart set of a face, as a finite orbit set. -/
def faceOrbitFinset (M : CombMap D) (f : M.Face) : Finset D :=
  Finset.univ.filter fun d => M.dartFace d = f

@[simp]
lemma mem_faceOrbitFinset_iff (M : CombMap D) (f : M.Face) (d : D) :
    d ∈ faceOrbitFinset M f ↔ M.dartFace d = f := by
  simp [faceOrbitFinset]

/-- A normalized cyclic dart list for a selected face orbit.

The `root` chooses one representative and fixes the cyclic rotation.  The
`toFinset_eq` field says the list enumerates exactly the selected `φ`-orbit.
-/
structure NormalizedCyclicDartList (M : CombMap D) (f : M.Face)
    (root : D) (darts : List D) : Prop where
  head_eq : darts.head? = some root
  root_face : M.dartFace root = f
  nodup : darts.Nodup
  length_pos : 0 < darts.length
  toFinset_eq : darts.toFinset = faceOrbitFinset M f

/-- A boundary arc/path between two boundary vertices. -/
structure BoundaryPath (M : CombMap D) (u v : M.Vertex) where
  /-- Vertices in path order, including both endpoints. -/
  vertices : List M.Vertex
  /-- Edges in path order.  For boundary arcs these are boundary-cycle edges. -/
  edges : List (Sym2 M.Vertex)
  /-- The first listed vertex is the initial endpoint. -/
  starts_at : vertices.head? = some u
  /-- The last listed vertex is the terminal endpoint. -/
  ends_at : vertices.getLast? = some v
  /-- The arc is simple as a vertex list. -/
  simple : vertices.Nodup

namespace BoundaryPath

variable {M : CombMap D} {u v : M.Vertex}

/-- Interior vertices of a path: endpoints removed. -/
def internalVertices (P : BoundaryPath M u v) : List M.Vertex :=
  P.vertices.tail.dropLast

/-- A path has at least one internal vertex. -/
def HasInternalVertex (P : BoundaryPath M u v) : Prop :=
  P.internalVertices ≠ []

@[simp]
lemma hasInternalVertex_iff (P : BoundaryPath M u v) :
    P.HasInternalVertex ↔ P.internalVertices ≠ [] :=
  Iff.rfl

/-- The number of listed vertices on the path. -/
def length (P : BoundaryPath M u v) : ℕ :=
  P.vertices.length

@[simp]
lemma length_eq (P : BoundaryPath M u v) : P.length = P.vertices.length :=
  rfl

end BoundaryPath

/-- The two boundary arcs determined by a pair of distinct boundary vertices. -/
structure BoundaryArcSplit (M : CombMap D)
    (boundaryVertices : List M.Vertex) (boundaryEdges : List (Sym2 M.Vertex))
    (u v : M.Vertex) where
  /-- The arc from `u` to `v`. -/
  path₁ : BoundaryPath M u v
  /-- The complementary arc from `v` back to `u`. -/
  path₂ : BoundaryPath M v u
  /-- `path₁` uses only boundary vertices. -/
  path₁_boundary_vertices :
    ∀ ⦃w : M.Vertex⦄, w ∈ path₁.vertices → w ∈ boundaryVertices
  /-- `path₂` uses only boundary vertices. -/
  path₂_boundary_vertices :
    ∀ ⦃w : M.Vertex⦄, w ∈ path₂.vertices → w ∈ boundaryVertices
  /-- Together the two arcs cover the boundary vertex list. -/
  boundary_vertices_covered :
    ∀ w : M.Vertex, w ∈ boundaryVertices ↔ w ∈ path₁.vertices ∨ w ∈ path₂.vertices
  /-- The internal vertices of the two arcs are disjoint. -/
  internally_disjoint :
    ∀ ⦃w : M.Vertex⦄,
      w ∈ path₁.internalVertices → w ∈ path₂.internalVertices → False
  /-- The first arc is nontrivial exactly when the endpoint pair is not a boundary edge. -/
  path₁_internal_iff_proper :
    path₁.HasInternalVertex ↔ s(u, v) ∉ boundaryEdges
  /-- The second arc is nontrivial exactly when the endpoint pair is not a boundary edge. -/
  path₂_internal_iff_proper :
    path₂.HasInternalVertex ↔ s(u, v) ∉ boundaryEdges

/-- A boundary cycle for the selected face `f`.

The dart list is a normalized cyclic enumeration of the `φ`-orbit of `f`.
The vertex and edge lists are exposed so later files can reason about the
boundary without repeatedly unfolding quotient-orbit facts.
-/
structure BoundaryCycle (M : CombMap D) (f : M.Face) where
  /-- Chosen dart representative fixing the cyclic rotation. -/
  root : D
  /-- Normalized cyclic dart list enumerating the selected face orbit. -/
  darts : List D
  /-- Cyclic boundary vertex list. -/
  vertices : List M.Vertex
  /-- Cyclic boundary edge list. -/
  edges : List (Sym2 M.Vertex)
  /-- The dart list is normalized and exactly enumerates the selected face orbit. -/
  normalized : NormalizedCyclicDartList M f root darts
  /-- Boundary vertices are the tails of the cyclic dart list. -/
  vertices_eq : vertices = darts.map M.tail
  /-- Boundary edges are the graph edges represented by the cyclic dart list. -/
  edges_eq : edges = darts.map M.dartEdge
  /-- The cyclic order agrees with the face permutation. -/
  consecutive_phi :
    ∀ i : Fin darts.length,
      darts.get (cyclicNext normalized.length_pos i) = M.φ (darts.get i)
  /-- Consecutive boundary darts match at their common boundary vertex. -/
  consecutive_vertex :
    ∀ i : Fin darts.length,
      M.tail (darts.get (cyclicNext normalized.length_pos i)) = M.head (darts.get i)
  /-- Arc-splitting certificate for any two distinct listed boundary vertices. -/
  arcSplit :
    ∀ ⦃u v : M.Vertex⦄,
      u ≠ v → u ∈ vertices → v ∈ vertices →
        BoundaryArcSplit M vertices edges u v

namespace BoundaryCycle

variable {M : CombMap D} {f : M.Face}

/-- Boundary vertices are represented by the exposed cyclic vertex list. -/
def IsBoundaryVertex (C : BoundaryCycle M f) (v : M.Vertex) : Prop :=
  v ∈ C.vertices

/-- Boundary edges are represented by the exposed cyclic edge list. -/
def IsBoundaryEdge (C : BoundaryCycle M f) (e : Sym2 M.Vertex) : Prop :=
  e ∈ C.edges

/-- Boundary endpoint pairs that are not consecutive on the boundary. -/
def ProperBoundaryPair (C : BoundaryCycle M f) (u v : M.Vertex) : Prop :=
  ¬ C.IsBoundaryEdge s(u, v)

/-- The boundary vertex list is simple. -/
def VertexNodup (C : BoundaryCycle M f) : Prop :=
  C.vertices.Nodup

/-- The boundary edge list has no repeated edge. -/
def EdgeNodup (C : BoundaryCycle M f) : Prop :=
  C.edges.Nodup

/-- Boundary length, measured in darts/edges. -/
def length (C : BoundaryCycle M f) : ℕ :=
  C.darts.length

@[simp]
lemma length_eq (C : BoundaryCycle M f) : C.length = C.darts.length :=
  rfl

lemma darts_nodup (C : BoundaryCycle M f) : C.darts.Nodup :=
  C.normalized.nodup

lemma darts_length_pos (C : BoundaryCycle M f) : 0 < C.darts.length :=
  C.normalized.length_pos

lemma root_mem_darts (C : BoundaryCycle M f) : C.root ∈ C.darts := by
  rw [← List.mem_toFinset, C.normalized.toFinset_eq]
  simp [C.normalized.root_face]

lemma dart_list_eq_orbit (C : BoundaryCycle M f) :
    C.darts.toFinset = faceOrbitFinset M f :=
  C.normalized.toFinset_eq

lemma mem_darts_iff (C : BoundaryCycle M f) (d : D) :
    d ∈ C.darts ↔ M.dartFace d = f := by
  rw [← List.mem_toFinset, C.normalized.toFinset_eq]
  simp

lemma dartFace_of_mem_darts (C : BoundaryCycle M f) {d : D} (hd : d ∈ C.darts) :
    M.dartFace d = f :=
  (C.mem_darts_iff d).mp hd

lemma vertices_eq_tail (C : BoundaryCycle M f) :
    C.vertices = C.darts.map M.tail :=
  C.vertices_eq

lemma edges_eq_dartEdge (C : BoundaryCycle M f) :
    C.edges = C.darts.map M.dartEdge :=
  C.edges_eq

lemma vertices_length (C : BoundaryCycle M f) :
    C.vertices.length = C.length := by
  simp [length, C.vertices_eq]

lemma edges_length (C : BoundaryCycle M f) :
    C.edges.length = C.length := by
  simp [length, C.edges_eq]

lemma consecutive_dart_vertex_matching (C : BoundaryCycle M f) :
    ∀ i : Fin C.darts.length,
      M.tail (C.darts.get (cyclicNext C.normalized.length_pos i)) =
        M.head (C.darts.get i) :=
  C.consecutive_vertex

/-- A boundary chord is an ambient graph edge between boundary vertices that is
not one of the boundary-cycle edges. -/
structure Chord (C : BoundaryCycle M f) (u v : M.Vertex) : Prop where
  endpoints_ne : u ≠ v
  left_boundary : C.IsBoundaryVertex u
  right_boundary : C.IsBoundaryVertex v
  adj : M.toSimpleGraph.Adj u v
  not_boundary_edge : ¬ C.IsBoundaryEdge s(u, v)

namespace Chord

variable {C : BoundaryCycle M f} {u v : M.Vertex}

lemma proper (h : C.Chord u v) : C.ProperBoundaryPair u v :=
  h.not_boundary_edge

end Chord

end BoundaryCycle

/-- Top-level alias for boundary chords. -/
abbrev BoundaryChord {M : CombMap D} {f : M.Face}
    (C : BoundaryCycle M f) (u v : M.Vertex) : Prop :=
  C.Chord u v

/-- A boundary is chordless if no boundary chord exists. -/
def BoundaryChordless {M : CombMap D} {f : M.Face} (C : BoundaryCycle M f) : Prop :=
  ∀ ⦃u v : M.Vertex⦄, ¬ C.Chord u v

namespace BoundaryArcSplit

variable {M : CombMap D} {f : M.Face} {C : BoundaryCycle M f} {u v : M.Vertex}

lemma path₁_internal_iff_proper_boundary (S : BoundaryArcSplit M C.vertices C.edges u v) :
    S.path₁.HasInternalVertex ↔ C.ProperBoundaryPair u v := by
  simpa [BoundaryCycle.ProperBoundaryPair, BoundaryCycle.IsBoundaryEdge] using
    S.path₁_internal_iff_proper

lemma path₂_internal_iff_proper_boundary (S : BoundaryArcSplit M C.vertices C.edges u v) :
    S.path₂.HasInternalVertex ↔ C.ProperBoundaryPair u v := by
  simpa [BoundaryCycle.ProperBoundaryPair, BoundaryCycle.IsBoundaryEdge] using
    S.path₂_internal_iff_proper

lemma path₁_internal_of_chord (S : BoundaryArcSplit M C.vertices C.edges u v)
    (h : C.Chord u v) : S.path₁.HasInternalVertex :=
  (S.path₁_internal_iff_proper_boundary).2 h.proper

lemma path₂_internal_of_chord (S : BoundaryArcSplit M C.vertices C.edges u v)
    (h : C.Chord u v) : S.path₂.HasInternalVertex :=
  (S.path₂_internal_iff_proper_boundary).2 h.proper

end BoundaryArcSplit

/-- Two distinct boundary vertices split a boundary cycle into two internally
disjoint simple arcs. -/
def boundary_cycle_two_arcs {M : CombMap D} {f : M.Face}
    (C : BoundaryCycle M f) {u v : M.Vertex}
    (hne : u ≠ v) (hu : C.IsBoundaryVertex u) (hv : C.IsBoundaryVertex v) :
    BoundaryArcSplit M C.vertices C.edges u v :=
  C.arcSplit hne hu hv

namespace BoundaryCycle

variable {M : CombMap D} {f : M.Face} {C : BoundaryCycle M f} {u v : M.Vertex}

def two_arcs (C : BoundaryCycle M f) {u v : M.Vertex}
    (hne : u ≠ v) (hu : C.IsBoundaryVertex u) (hv : C.IsBoundaryVertex v) :
    BoundaryArcSplit M C.vertices C.edges u v :=
  boundary_cycle_two_arcs C hne hu hv

/-- A chord edge is not one of the boundary-cycle edges. -/
lemma chord_not_boundary_edge (h : C.Chord u v) :
    ¬ C.IsBoundaryEdge s(u, v) :=
  h.not_boundary_edge

/-- For a chord, both boundary arcs have an internal vertex.  This is the
strict-decrease bookkeeping used by later chord-split files. -/
lemma two_arcs_internally_nonempty_of_chord (h : C.Chord u v) :
    ∃ S : BoundaryArcSplit M C.vertices C.edges u v,
      S.path₁.HasInternalVertex ∧ S.path₂.HasInternalVertex := by
  let S : BoundaryArcSplit M C.vertices C.edges u v :=
    boundary_cycle_two_arcs C h.endpoints_ne h.left_boundary h.right_boundary
  exact ⟨S, S.path₁_internal_of_chord h, S.path₂_internal_of_chord h⟩

lemma arc₁_internal_iff_proper (S : BoundaryArcSplit M C.vertices C.edges u v) :
    S.path₁.HasInternalVertex ↔ C.ProperBoundaryPair u v :=
  S.path₁_internal_iff_proper_boundary

lemma arc₂_internal_iff_proper (S : BoundaryArcSplit M C.vertices C.edges u v) :
    S.path₂.HasInternalVertex ↔ C.ProperBoundaryPair u v :=
  S.path₂_internal_iff_proper_boundary

end BoundaryCycle

lemma chord_not_boundary_edge {M : CombMap D} {f : M.Face}
    {C : BoundaryCycle M f} {u v : M.Vertex} (h : C.Chord u v) :
    ¬ C.IsBoundaryEdge s(u, v) :=
  BoundaryCycle.chord_not_boundary_edge h

end CombMap

end ProofsInTheBook.PlanarMap
