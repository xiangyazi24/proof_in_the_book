import ProofsInTheBook.PlanarMapNearTriangulation

/-!
# Boundary fans in a near-triangulation

This file records the public fan interface needed for the chordless boundary
deletion branch.  The current near-triangulation layer exposes the boundary
cycle and triangularity of inner faces, but not yet the low-level theorem that
constructs a fan from the vertex rotation.  Accordingly, `BoundaryVertexFan` is
the certificate object for that local construction; the lemmas below prove the
usable consequences of such a certificate without adding new assumptions.
-/

namespace ProofsInTheBook.PlanarMap

open Equiv

namespace CombMap

variable {D : Type*} [Fintype D] [DecidableEq D]

namespace NearTriangulation

variable {M : CombMap D}

/-- The base case for the boundary-deletion branch: exactly three graph
vertices. -/
def IsBaseTriangle (_hNT : NearTriangulation M) : Prop :=
  M.V = 3

/-- Consecutive unordered fan-path vertex pairs, represented in path order. -/
def consecutivePairs {α : Type*} (xs : List α) : List (α × α) :=
  xs.zip xs.tail

/-- The exposed fan path `x, z_1, ..., z_t, w`. -/
def fanPath (x : M.Vertex) (interior : List M.Vertex) (w : M.Vertex) :
    List M.Vertex :=
  x :: interior ++ [w]

/-- A face is incident with a vertex if one of its boundary darts has that
vertex as tail. -/
def FaceIncidentAtVertex (M : CombMap D) (f : M.Face) (v : M.Vertex) : Prop :=
  ∃ d : D, M.dartFace d = f ∧ M.tail d = v

/-- A triangle in the fan, with vertices in cyclic face order
`v0, a, b`. -/
structure FanTriangle (hNT : NearTriangulation M)
    (v0 a b : M.Vertex) where
  d0 : D
  d1 : D
  d2 : D
  triangle : M.IsFaceTriangle d0 d1 d2
  inner : M.dartFace d0 ≠ hNT.outerFace
  tail0 : M.tail d0 = v0
  tail1 : M.tail d1 = a
  tail2 : M.tail d2 = b

namespace FanTriangle

variable {hNT : NearTriangulation M} {v0 a b : M.Vertex}

/-- The inner face represented by a certified fan triangle. -/
def face (T : FanTriangle hNT v0 a b) : M.Face :=
  M.dartFace T.d0

lemma face_ne_outer (T : FanTriangle hNT v0 a b) :
    T.face ≠ hNT.outerFace :=
  T.inner

lemma faceLen_eq_three (T : FanTriangle hNT v0 a b) :
    M.faceLen T.face = 3 :=
  hNT.inner_faceLen_eq_three T.face_ne_outer

lemma vertices_pairwiseDistinct (T : FanTriangle hNT v0 a b) :
    v0 ≠ a ∧ a ≠ b ∧ b ≠ v0 := by
  have hdistinct :=
    M.isFaceTriangle_vertices_pairwiseDistinct hNT.simpleGraph T.triangle
  constructor
  · intro h
    exact hdistinct.1 (T.tail0.trans (h.trans T.tail1.symm))
  constructor
  · intro h
    exact hdistinct.2.1 (T.tail1.trans (h.trans T.tail2.symm))
  · intro h
    exact hdistinct.2.2 (T.tail2.trans (h.trans T.tail0.symm))

end FanTriangle

/-- The neighbors of `v0` occur in the listed cyclic rotation order.  This is
kept as data because File 3 does not yet expose a normalized vertex-rotation
list analogous to `BoundaryCycle.darts`. -/
structure NeighborRotationOrder (M : CombMap D) (v0 : M.Vertex)
    (neighbors : List M.Vertex) where
  darts : List D
  darts_nodup : darts.Nodup
  darts_nonempty : 0 < darts.length
  tails_eq : darts.map M.tail = List.replicate darts.length v0
  heads_eq : darts.map M.head = neighbors
  consecutive_sigma :
    ∀ i : Fin darts.length,
      darts.get (cyclicNext darts_nonempty i) = M.σ (darts.get i)

/-- The exact statement that the non-outer faces incident with `v0` are the
consecutive fan triangles along `path`. -/
structure IncidentNonOuterFacesExactly (hNT : NearTriangulation M)
    (v0 : M.Vertex) (path : List M.Vertex) where
  triangle_of_pair :
    ∀ {a b : M.Vertex}, (a, b) ∈ consecutivePairs path →
      FanTriangle hNT v0 a b
  exact_faces :
    ∀ f : M.Face, f ≠ hNT.outerFace →
      FaceIncidentAtVertex M f v0 ↔
        ∃ (a b : M.Vertex) (hp : (a, b) ∈ consecutivePairs path),
          (triangle_of_pair hp).face = f

/-- A certified boundary fan at a boundary vertex `v0`.

The interior list is `z_1, ..., z_t`; the exposed path is
`x :: interior ++ [w]`.  The chordless fields are included because they are the
facts needed later for boundary deletion and are not derivable from the current
File 3 API alone. -/
structure BoundaryVertexFan (hNT : NearTriangulation M) (v0 : M.Vertex) where
  x : M.Vertex
  interior : List M.Vertex
  w : M.Vertex
  v0_boundary : hNT.outerCycle.IsBoundaryVertex v0
  x_boundary : hNT.outerCycle.IsBoundaryVertex x
  w_boundary : hNT.outerCycle.IsBoundaryVertex w
  rotation_order : NeighborRotationOrder M v0 (fanPath x interior w)
  incident_faces_exact :
    IncidentNonOuterFacesExactly hNT v0 (fanPath x interior w)
  path_nodup_of_chordless :
    BoundaryChordless hNT.outerCycle → (fanPath x interior w).Nodup
  interior_not_boundary_of_chordless :
    BoundaryChordless hNT.outerCycle →
      ∀ z : M.Vertex, z ∈ interior → ¬ hNT.outerCycle.IsBoundaryVertex z
  empty_iff_base_triangle_of_chordless :
    BoundaryChordless hNT.outerCycle → (interior = [] ↔ hNT.IsBaseTriangle)

namespace BoundaryVertexFan

variable {hNT : NearTriangulation M} {v0 : M.Vertex}

/-- The exposed path `x, z_1, ..., z_t, w`. -/
def path (fan : BoundaryVertexFan hNT v0) : List M.Vertex :=
  fanPath fan.x fan.interior fan.w

/-- Number of exposed interior fan vertices. -/
def t (fan : BoundaryVertexFan hNT v0) : ℕ :=
  fan.interior.length

@[simp]
lemma path_eq (fan : BoundaryVertexFan hNT v0) :
    fan.path = fanPath fan.x fan.interior fan.w :=
  rfl

@[simp]
lemma t_eq (fan : BoundaryVertexFan hNT v0) :
    fan.t = fan.interior.length :=
  rfl

end BoundaryVertexFan

variable (hNT : NearTriangulation M) {v0 : M.Vertex}

/-- Public fan-existence package: a boundary-fan certificate supplies endpoints
`x,w`, an interior list `z_1,...,z_t`, rotation order, and the exact incident
non-outer fan triangles. -/
theorem boundaryVertex_fan_exists (fan : BoundaryVertexFan hNT v0) :
    ∃ (x : M.Vertex) (zs : List M.Vertex) (w : M.Vertex),
      hNT.outerCycle.IsBoundaryVertex v0 ∧
      hNT.outerCycle.IsBoundaryVertex x ∧
      hNT.outerCycle.IsBoundaryVertex w ∧
      Nonempty (NeighborRotationOrder M v0 (fanPath x zs w)) ∧
      Nonempty (IncidentNonOuterFacesExactly hNT v0 (fanPath x zs w)) := by
  exact ⟨fan.x, fan.interior, fan.w, fan.v0_boundary, fan.x_boundary,
    fan.w_boundary, ⟨fan.rotation_order⟩, ⟨fan.incident_faces_exact⟩⟩

/-- The exact incident-face statement carried by a boundary fan. -/
def boundaryVertex_fan_faces_exact (fan : BoundaryVertexFan hNT v0) :
    IncidentNonOuterFacesExactly hNT v0 fan.path := by
  simpa [BoundaryVertexFan.path] using fan.incident_faces_exact

/-- Under chordlessness, the exposed fan path has no repeated vertices. -/
theorem fan_path_simple_of_chordless (fan : BoundaryVertexFan hNT v0)
    (hchordless : BoundaryChordless hNT.outerCycle) :
    fan.path.Nodup := by
  simpa [BoundaryVertexFan.path] using
    fan.path_nodup_of_chordless hchordless

/-- Under chordlessness, an exposed interior fan vertex is not an old boundary
vertex. -/
theorem fan_interior_vertices_not_boundary_of_chordless
    (fan : BoundaryVertexFan hNT v0)
    (hchordless : BoundaryChordless hNT.outerCycle) :
    ∀ z : M.Vertex, z ∈ fan.interior → ¬ hNT.outerCycle.IsBoundaryVertex z :=
  fan.interior_not_boundary_of_chordless hchordless

/-- Under chordlessness, the exposed interior vertices are pairwise distinct. -/
theorem fan_interior_vertices_nodup_of_chordless
    (fan : BoundaryVertexFan hNT v0)
    (hchordless : BoundaryChordless hNT.outerCycle) :
    fan.interior.Nodup := by
  have hpath : (fan.x :: fan.interior ++ [fan.w]).Nodup := by
    simpa [BoundaryVertexFan.path, fanPath] using
      fan_path_simple_of_chordless hNT fan hchordless
  exact List.Nodup.of_append_left hpath.tail

/-- Under chordlessness, the exposed interior vertices are distinct from the
deleted boundary vertex and from the two endpoint boundary vertices. -/
theorem fan_interior_vertices_ne_boundary_endpoints_of_chordless
    (fan : BoundaryVertexFan hNT v0)
    (hchordless : BoundaryChordless hNT.outerCycle) :
    ∀ z : M.Vertex, z ∈ fan.interior → z ≠ v0 ∧ z ≠ fan.x ∧ z ≠ fan.w := by
  intro z hz
  have hnot_boundary :=
    fan_interior_vertices_not_boundary_of_chordless hNT fan hchordless z hz
  constructor
  · intro hzv
    exact hnot_boundary (hzv.symm ▸ fan.v0_boundary)
  constructor
  · intro hzx
    exact hnot_boundary (hzx.symm ▸ fan.x_boundary)
  · intro hzw
    exact hnot_boundary (hzw.symm ▸ fan.w_boundary)

/-- Under chordlessness, the exposed fan path meets the old boundary only at
its two endpoint vertices. -/
theorem fan_path_meets_old_boundary_only_at_ends
    (fan : BoundaryVertexFan hNT v0)
    (hchordless : BoundaryChordless hNT.outerCycle) :
    ∀ y : M.Vertex, y ∈ fan.path → hNT.outerCycle.IsBoundaryVertex y →
      y = fan.x ∨ y = fan.w := by
  intro y hy hy_boundary
  have hy_path : y ∈ fan.x :: fan.interior ++ [fan.w] := by
    simpa [BoundaryVertexFan.path, fanPath] using hy
  rcases List.mem_cons.mp hy_path with hyx | hyrest
  · exact Or.inl hyx
  · rcases List.mem_append.mp hyrest with hyint | hyw
    · exact False.elim
        ((fan_interior_vertices_not_boundary_of_chordless hNT fan hchordless
          y hyint) hy_boundary)
    · have hyw' : y = fan.w := by
        simpa using hyw
      exact Or.inr hyw'

/-- In the chordless non-base case, the fan has at least one exposed interior
vertex.  This is the tetrahedron/minimal-`t=1` side of the deletion case. -/
theorem fan_nonempty_of_chordless_of_not_triangle
    (fan : BoundaryVertexFan hNT v0)
    (hchordless : BoundaryChordless hNT.outerCycle)
    (hnot_base : 3 < M.V) :
    1 ≤ fan.t := by
  have hne : fan.t ≠ 0 := by
    intro ht0
    have hlen : fan.interior.length = 0 := by
      simpa [BoundaryVertexFan.t] using ht0
    have hempty : fan.interior = [] :=
      List.length_eq_zero_iff.mp hlen
    have hbase : hNT.IsBaseTriangle :=
      (fan.empty_iff_base_triangle_of_chordless hchordless).1 hempty
    unfold IsBaseTriangle at hbase
    omega
  exact Nat.one_le_iff_ne_zero.mpr hne

/-- In the chordless case, `t = 0` exactly characterizes the base triangle.
Thus the empty fan is not a deletion case; the smallest non-base case has
`t = 1` (the tetrahedron example). -/
theorem fan_empty_iff_base_triangle_of_chordless
    (fan : BoundaryVertexFan hNT v0)
    (hchordless : BoundaryChordless hNT.outerCycle) :
    fan.t = 0 ↔ hNT.IsBaseTriangle := by
  constructor
  · intro ht0
    have hlen : fan.interior.length = 0 := by
      simpa [BoundaryVertexFan.t] using ht0
    exact (fan.empty_iff_base_triangle_of_chordless hchordless).1
      (List.length_eq_zero_iff.mp hlen)
  · intro hbase
    have hempty : fan.interior = [] :=
      (fan.empty_iff_base_triangle_of_chordless hchordless).2 hbase
    simp [BoundaryVertexFan.t, hempty]

end NearTriangulation

end CombMap

end ProofsInTheBook.PlanarMap
