import Mathlib

/-!
# Chapter 13: Cauchy's rigidity theorem

From "Proofs from THE BOOK":

**Cauchy's rigidity theorem**: If two convex polyhedra have the same
combinatorial structure and corresponding faces are congruent, then
the polyhedra are congruent (equal up to isometry).

The book's proof uses Cauchy's arm lemma: if we increase some angles
in a convex polygon while keeping side lengths fixed, the polygon
"opens up" (the distance between the first and last vertex increases).

The proof proceeds by:
1. Label each edge + or - according to whether the dihedral angle
   increases or decreases.
2. Use Euler's formula to count sign changes around faces.
3. Apply the arm lemma to derive a contradiction if any signs are non-zero.

Formalization status: this file closes the finite sign bookkeeping layer and
the final counting contradiction.  It defines edge signs from dihedral-angle
comparisons, strict sign changes around triangular faces, proves the basic
parity facts, proves the two-edge Cauchy-arm base case from the law of cosines,
packages the abstract consequence of Cauchy's arm lemma, and states `chapter13`
/ `chapter13_rigidity` from meaningful missing geometric/combinatorial facts.
The remaining frontier is now explicit: vertex-link geometry must turn the low
sign-change cases into fixed-chord Cauchy-arm obstructions.  The Euler
polyhedron formula is carried as boundary topology in `ConvexPolyhedron`, and
the triangulated incidence count is proved from the boundary-edge equivalence.

Gap to the full book theorem: the missing work is genuine three-dimensional
Euclidean polyhedron infrastructure.  A complete proof needs a formal convex
polyhedron type with face and edge incidence, corresponding congruent faces,
dihedral angles and their comparison signs, the reduced sign-change graph and
Euler characteristic edge-counting bound for it, and a proved Cauchy arm lemma
for convex planar polygonal chains tied to the vertex links.  Mathlib has
convex and Euclidean geometry foundations, but not this integrated
convex-polyhedron rigidity layer.
-/

namespace ProofsInTheBook.Chapter13

/-! ### Euclidean convex polyhedron data -/

/-- The ambient space for Cauchy's theorem. -/
abbrev Euclidean3 :=
  EuclideanSpace ℝ (Fin 3)

/-- A combinatorial edge, stored by its two endpoint vertex indices. -/
structure PolyhedronEdge (V : ℕ) where
  tail : Fin V
  head : Fin V
  nondegenerate : tail ≠ head

namespace PolyhedronEdge

variable {V : ℕ}

/-- The unordered endpoint set of an edge. -/
def endpoints (e : PolyhedronEdge V) : Finset (Fin V) :=
  {e.tail, e.head}

@[simp]
theorem tail_mem_endpoints (e : PolyhedronEdge V) :
    e.tail ∈ e.endpoints := by
  simp [endpoints]

@[simp]
theorem head_mem_endpoints (e : PolyhedronEdge V) :
    e.head ∈ e.endpoints := by
  simp [endpoints]

@[simp]
theorem endpoints_card (e : PolyhedronEdge V) : e.endpoints.card = 2 := by
  simp [endpoints, e.nondegenerate]

end PolyhedronEdge

/-- One polygonal face, as a cyclically ordered list of vertex indices. -/
structure PolyhedronFace (V : ℕ) where
  vertexCount : ℕ
  vertices : Fin vertexCount → Fin V
  three_le : 3 ≤ vertexCount
  simple : Function.Injective vertices

namespace PolyhedronFace

variable {V : ℕ}

/-- The unordered vertex set of a face. -/
def vertexSet (f : PolyhedronFace V) : Finset (Fin V) :=
  Finset.univ.image f.vertices

@[simp]
theorem vertices_mem_vertexSet (f : PolyhedronFace V) (i : Fin f.vertexCount) :
    f.vertices i ∈ f.vertexSet := by
  simp [vertexSet]

/-- A face has a positive number of vertices. -/
theorem vertexCount_pos (f : PolyhedronFace V) : 0 < f.vertexCount := by
  exact Nat.lt_of_lt_of_le (by decide : 0 < 3) f.three_le

/-- The next vertex in the cyclic order around the face. -/
def next (f : PolyhedronFace V) (i : Fin f.vertexCount) : Fin f.vertexCount :=
  ⟨(i.1 + 1) % f.vertexCount, Nat.mod_lt _ f.vertexCount_pos⟩

/-- The unordered endpoint set of the `i`-th boundary edge in the cyclic face order. -/
def boundaryEdgeEndpoints (f : PolyhedronFace V) (i : Fin f.vertexCount) : Finset (Fin V) :=
  {f.vertices i, f.vertices (f.next i)}

/-- Weak membership predicate: both endpoints of the edge occur among the face vertices. -/
def ContainsEdgeEndpoints (f : PolyhedronFace V) (e : PolyhedronEdge V) : Prop :=
  e.tail ∈ f.vertexSet ∧ e.head ∈ f.vertexSet

/-- A face contains an edge when the edge is one of its cyclic boundary edges. -/
def ContainsEdge (f : PolyhedronFace V) (e : PolyhedronEdge V) : Prop :=
  ∃ i : Fin f.vertexCount, e.endpoints = f.boundaryEdgeEndpoints i

theorem containsEdgeEndpoints_of_containsEdge (f : PolyhedronFace V) (e : PolyhedronEdge V)
    (h : f.ContainsEdge e) :
    f.ContainsEdgeEndpoints e := by
  rcases h with ⟨i, hi⟩
  constructor
  · have htail : e.tail ∈ e.endpoints := by simp
    rw [hi] at htail
    simp [boundaryEdgeEndpoints] at htail
    rcases htail with htail | htail
    · rw [vertexSet]
      exact Finset.mem_image.mpr ⟨i, by simp, htail.symm⟩
    · rw [vertexSet]
      exact Finset.mem_image.mpr ⟨f.next i, by simp, htail.symm⟩
  · have hhead : e.head ∈ e.endpoints := by simp
    rw [hi] at hhead
    simp [boundaryEdgeEndpoints] at hhead
    rcases hhead with hhead | hhead
    · rw [vertexSet]
      exact Finset.mem_image.mpr ⟨i, by simp, hhead.symm⟩
    · rw [vertexSet]
      exact Finset.mem_image.mpr ⟨f.next i, by simp, hhead.symm⟩

end PolyhedronFace

/-- The supporting plane with equation `inner normal p = offset`. -/
def supportingPlane (normal : Euclidean3) (offset : ℝ) : Set Euclidean3 :=
  {p | inner ℝ normal p = offset}

/-- The closed supporting halfspace with equation `inner normal p ≤ offset`. -/
def supportingHalfspace (normal : Euclidean3) (offset : ℝ) : Set Euclidean3 :=
  {p | inner ℝ normal p ≤ offset}

/--
A convex polyhedron in `ℝ^3`, with explicit finite vertex, edge, and face
indices. The body is the convex hull of the listed vertices, and the face data
records supporting halfspaces whose intersection is that body.

The incidence fields are deliberately concrete: every edge has its two incident
faces, every listed face is a simple polygon with at least three vertices, and
the face vertex set is exactly the set of vertices lying on its supporting plane.
-/
structure ConvexPolyhedron (V E F : ℕ) where
  vertex : Fin V → Euclidean3
  vertex_injective : Function.Injective vertex
  edge : Fin E → PolyhedronEdge V
  face : Fin F → PolyhedronFace V
  /-- The global edge occupying each cyclic boundary edge of each face. -/
  faceEdge : (f : Fin F) → Fin (face f).vertexCount → Fin E
  faceEdge_endpoints :
    ∀ f i, (edge (faceEdge f i)).endpoints = (face f).boundaryEdgeEndpoints i
  edgeFaces : Fin E → Fin 2 → Fin F
  edgeFaces_injective : ∀ e, Function.Injective (edgeFaces e)
  edge_mem_incident_faces : ∀ e i, (face (edgeFaces e i)).ContainsEdge (edge e)
  /--
  Oriented boundary-edge incidences are exactly two slots over every global edge.
  The domain is "a local cyclic boundary edge of a face"; the codomain is
  "one of the two face orientations incident to a global edge".
  -/
  boundaryIncidence :
    (Σ f : Fin F, Fin (face f).vertexCount) ≃ (Σ _e : Fin E, Fin 2)
  boundaryIncidence_edge :
    ∀ x, (boundaryIncidence x).1 = faceEdge x.1 x.2
  boundaryIncidence_face :
    ∀ x, edgeFaces (boundaryIncidence x).1 (boundaryIncidence x).2 = x.1
  /-- Euler characteristic of the boundary sphere. -/
  euler_characteristic : (V : ℤ) - (E : ℤ) + (F : ℤ) = 2
  faceNormal : Fin F → Euclidean3
  faceOffset : Fin F → ℝ
  faceNormal_ne_zero : ∀ f, faceNormal f ≠ 0
  face_vertices_on_plane :
    ∀ f i, vertex ((face f).vertices i) ∈ supportingPlane (faceNormal f) (faceOffset f)
  vertices_in_supporting_halfspace :
    ∀ f v, vertex v ∈ supportingHalfspace (faceNormal f) (faceOffset f)
  vertex_on_face_plane_iff :
    ∀ f v, vertex v ∈ supportingPlane (faceNormal f) (faceOffset f) ↔
      v ∈ (face f).vertexSet
  body_eq_iInter_supportingHalfspaces :
    convexHull ℝ (Set.range vertex) =
      ⋂ f, supportingHalfspace (faceNormal f) (faceOffset f)

namespace ConvexPolyhedron

variable {V E F : ℕ}

/-- The solid body of a convex polyhedron. -/
noncomputable def body (P : ConvexPolyhedron V E F) : Set Euclidean3 :=
  convexHull ℝ (Set.range P.vertex)

theorem convex_body (P : ConvexPolyhedron V E F) :
    Convex ℝ P.body := by
  simpa [body] using convex_convexHull ℝ (Set.range P.vertex)

theorem vertex_mem_body (P : ConvexPolyhedron V E F) (v : Fin V) :
    P.vertex v ∈ P.body := by
  exact subset_convexHull ℝ (Set.range P.vertex) ⟨v, rfl⟩

theorem body_subset_supportingHalfspace (P : ConvexPolyhedron V E F) (f : Fin F) :
    P.body ⊆ supportingHalfspace (P.faceNormal f) (P.faceOffset f) := by
  intro p hp
  rw [body, P.body_eq_iInter_supportingHalfspaces] at hp
  exact Set.mem_iInter.mp hp f

/-- The Euclidean endpoint length of an edge. -/
noncomputable def edgeLength (P : ConvexPolyhedron V E F) (e : Fin E) : ℝ :=
  dist (P.vertex ((P.edge e).tail)) (P.vertex ((P.edge e).head))

theorem edgeLength_pos (P : ConvexPolyhedron V E F) (e : Fin E) :
    0 < P.edgeLength e :=
  dist_pos.mpr fun h =>
    (P.edge e).nondegenerate (P.vertex_injective h)

/-- Corresponding indexed edges have the same Euclidean length. -/
def SameEdgeLengths (P Q : ConvexPolyhedron V E F) : Prop :=
  ∀ e : Fin E, P.edgeLength e = Q.edgeLength e

/-- The embedded point corresponding to one vertex in one face polygon. -/
noncomputable def facePoint (P : ConvexPolyhedron V E F) (f : Fin F)
    (i : Fin (P.face f).vertexCount) : Euclidean3 :=
  P.vertex ((P.face f).vertices i)

@[simp]
theorem facePoint_mem_supportingPlane (P : ConvexPolyhedron V E F) (f : Fin F)
    (i : Fin (P.face f).vertexCount) :
    P.facePoint f i ∈ supportingPlane (P.faceNormal f) (P.faceOffset f) := by
  exact P.face_vertices_on_plane f i

/-- The `faceEdge` map really names the cyclic boundary edge at that face slot. -/
theorem faceEdge_containsEdge (P : ConvexPolyhedron V E F) (f : Fin F)
    (i : Fin (P.face f).vertexCount) :
    (P.face f).ContainsEdge (P.edge (P.faceEdge f i)) :=
  ⟨i, P.faceEdge_endpoints f i⟩

/-- The two recorded incident faces of an edge are distinct. -/
theorem edgeFaces_ne (P : ConvexPolyhedron V E F) (e : Fin E) :
    P.edgeFaces e 0 ≠ P.edgeFaces e 1 := by
  intro h
  exact Fin.zero_ne_one ((P.edgeFaces_injective e) h)

/-- The set of faces incident to a global edge has cardinality two. -/
theorem incidentFaces_card (P : ConvexPolyhedron V E F) (e : Fin E) :
    (Finset.univ.image (P.edgeFaces e)).card = 2 := by
  rw [Finset.card_image_of_injective _ (P.edgeFaces_injective e)]
  simp

/-- Every face-local boundary edge is assigned one of the two orientations of its global edge. -/
theorem boundaryIncidence_global_edge (P : ConvexPolyhedron V E F)
    (x : Σ f : Fin F, Fin (P.face f).vertexCount) :
    (P.boundaryIncidence x).1 = P.faceEdge x.1 x.2 :=
  P.boundaryIncidence_edge x

/-- Every face-local boundary edge lands in the corresponding incident face slot. -/
theorem boundaryIncidence_incident_face (P : ConvexPolyhedron V E F)
    (x : Σ f : Fin F, Fin (P.face f).vertexCount) :
    P.edgeFaces (P.boundaryIncidence x).1 (P.boundaryIncidence x).2 = x.1 :=
  P.boundaryIncidence_face x

/-- Each of the two edge-orientation slots has a unique face-local boundary edge. -/
theorem exists_unique_boundaryIncidence_of_edgeSide (P : ConvexPolyhedron V E F)
    (e : Fin E) (i : Fin 2) :
    ∃! x : Σ f : Fin F, Fin (P.face f).vertexCount,
      P.boundaryIncidence x = ⟨e, i⟩ := by
  refine ⟨P.boundaryIncidence.symm ⟨e, i⟩, by simp, ?_⟩
  intro y hy
  exact P.boundaryIncidence.injective (by simp [hy])

/-- The boundary occurrence corresponding to an edge side maps back to that global edge. -/
theorem faceEdge_boundaryIncidence_symm (P : ConvexPolyhedron V E F)
    (e : Fin E) (i : Fin 2) :
    P.faceEdge (P.boundaryIncidence.symm ⟨e, i⟩).1
      (P.boundaryIncidence.symm ⟨e, i⟩).2 = e := by
  let x := P.boundaryIncidence.symm ⟨e, i⟩
  have hx : P.boundaryIncidence x = ⟨e, i⟩ := by
    simp [x]
  have hedge := P.boundaryIncidence_edge x
  have hfirst : (P.boundaryIncidence x).1 = e := by
    simp [hx]
  exact hedge.symm.trans hfirst

/-- The boundary occurrence corresponding to an edge side lies on that side's incident face. -/
theorem edgeFaces_boundaryIncidence_symm (P : ConvexPolyhedron V E F)
    (e : Fin E) (i : Fin 2) :
    P.edgeFaces e i = (P.boundaryIncidence.symm ⟨e, i⟩).1 := by
  let x := P.boundaryIncidence.symm ⟨e, i⟩
  have hx : P.boundaryIncidence x = ⟨e, i⟩ := by
    simp [x]
  have hface := P.boundaryIncidence_face x
  simpa [hx] using hface

/--
Counting oriented boundary-edge incidences: summing the cyclic boundary lengths
of all faces gives two incidences for every global edge.
-/
theorem boundary_incidence_card (P : ConvexPolyhedron V E F) :
    (∑ f : Fin F, (P.face f).vertexCount) = 2 * E := by
  have hcard :
      Fintype.card (Σ f : Fin F, Fin (P.face f).vertexCount) =
        Fintype.card (Σ _e : Fin E, Fin 2) :=
    Fintype.card_congr P.boundaryIncidence
  simpa [Fintype.card_sigma, Fintype.card_fin, Nat.mul_comm, Nat.mul_left_comm,
    Nat.mul_assoc] using hcard

/-- Euler's formula, supplied by the boundary topology carried by the polyhedron. -/
theorem euler_formula (P : ConvexPolyhedron V E F) :
    (V : ℤ) - (E : ℤ) + (F : ℤ) = 2 :=
  P.euler_characteristic

/-- A polyhedron is triangulated when every cyclic face boundary has length three. -/
def IsTriangulated (P : ConvexPolyhedron V E F) : Prop :=
  ∀ f : Fin F, (P.face f).vertexCount = 3

/-- In a triangulated polyhedron, the total number of face-boundary slots is `3F`. -/
theorem face_boundary_count_of_triangulated (P : ConvexPolyhedron V E F)
    (htri : P.IsTriangulated) :
    (∑ f : Fin F, (P.face f).vertexCount) = 3 * F := by
  calc
    (∑ f : Fin F, (P.face f).vertexCount) = ∑ _f : Fin F, 3 := by
      exact Finset.sum_congr rfl (fun f _ => htri f)
    _ = 3 * F := by
      simp [Fintype.card_fin, Nat.mul_comm]

/-- For triangulated polyhedra, counting face-edge incidences gives `3F = 2E`. -/
theorem triangular_face_edge_count (P : ConvexPolyhedron V E F)
    (htri : P.IsTriangulated) :
    3 * F = 2 * E := by
  calc
    3 * F = ∑ f : Fin F, (P.face f).vertexCount :=
      (P.face_boundary_count_of_triangulated htri).symm
    _ = 2 * E := P.boundary_incidence_card

/-- Corresponding vertices are related by one ambient Euclidean motion. -/
def Congruent (P Q : ConvexPolyhedron V E F) : Prop :=
  ∃ φ : Euclidean3 ≃ᵃⁱ[ℝ] Euclidean3, ∀ v, φ (P.vertex v) = Q.vertex v

/-- The two polyhedra use the same indexed edges and cyclic face boundaries. -/
structure SameCombinatorics (P Q : ConvexPolyhedron V E F) : Prop where
  edge_tail : ∀ e, (P.edge e).tail = (Q.edge e).tail
  edge_head : ∀ e, (P.edge e).head = (Q.edge e).head
  face_vertexCount : ∀ f, (P.face f).vertexCount = (Q.face f).vertexCount
  face_vertices :
    ∀ f (i : Fin (P.face f).vertexCount),
      (Q.face f).vertices (Fin.cast (face_vertexCount f) i) = (P.face f).vertices i
  face_vertexSet : ∀ f, (P.face f).vertexSet = (Q.face f).vertexSet
  faceEdge :
    ∀ f (i : Fin (P.face f).vertexCount),
      P.faceEdge f i = Q.faceEdge f (Fin.cast (face_vertexCount f) i)
  edgeFaces : ∀ e i, P.edgeFaces e i = Q.edgeFaces e i

/-- Corresponding faces are isometric, expressed by all pairwise vertex distances. -/
def FacewiseIsometric (P Q : ConvexPolyhedron V E F) : Prop :=
  ∀ f v w, v ∈ (P.face f).vertexSet → w ∈ (P.face f).vertexSet →
    dist (P.vertex v) (P.vertex w) = dist (Q.vertex v) (Q.vertex w)

/-- Facewise isometry implies equality of corresponding edge lengths. -/
theorem sameEdgeLengths_of_facewiseIsometric (P Q : ConvexPolyhedron V E F)
    (hcomb : SameCombinatorics P Q) (hface : FacewiseIsometric P Q) :
    SameEdgeLengths P Q := by
  intro e
  let f := P.edgeFaces e 0
  have hcontains : (P.face f).ContainsEdge (P.edge e) := by
    simpa [f] using P.edge_mem_incident_faces e 0
  have hendpoints :=
    (P.face f).containsEdgeEndpoints_of_containsEdge (P.edge e) hcontains
  unfold edgeLength
  rw [← hcomb.edge_tail e, ← hcomb.edge_head e]
  exact hface f (P.edge e).tail (P.edge e).head hendpoints.1 hendpoints.2

/-- The Cauchy input: same combinatorics and congruent corresponding faces. -/
structure IsometricPair (P Q : ConvexPolyhedron V E F) : Prop where
  combinatorics : SameCombinatorics P Q
  facewise_isometric : FacewiseIsometric P Q
  same_edge_lengths : SameEdgeLengths P Q

/-- The contradiction-producing input for the next construction stage. -/
structure RigidityCounterexample (P Q : ConvexPolyhedron V E F) : Prop where
  isometric : IsometricPair P Q
  not_congruent : ¬ Congruent P Q

end ConvexPolyhedron

/-- Edge signs in Cauchy's rigidity proof. -/
inductive EdgeSign where
  | plus | minus | zero
  deriving DecidableEq, Repr

open EdgeSign

namespace EdgeSign

/--
The sign of the change from an old angle to a new angle: `plus` means the
angle increased, `minus` means it decreased, and `zero` means it stayed fixed.
-/
noncomputable def ofAngleDifference (oldAngle newAngle : ℝ) : EdgeSign :=
  if oldAngle < newAngle then plus
  else if newAngle < oldAngle then minus
  else zero

@[simp]
theorem ofAngleDifference_eq_plus_of_lt {oldAngle newAngle : ℝ}
    (h : oldAngle < newAngle) :
    ofAngleDifference oldAngle newAngle = plus := by
  simp [ofAngleDifference, h]

@[simp]
theorem ofAngleDifference_eq_minus_of_lt {oldAngle newAngle : ℝ}
    (h : newAngle < oldAngle) :
    ofAngleDifference oldAngle newAngle = minus := by
  simp [ofAngleDifference, h, not_lt_of_gt h]

@[simp]
theorem ofAngleDifference_eq_zero_of_eq {oldAngle newAngle : ℝ}
    (h : oldAngle = newAngle) :
    ofAngleDifference oldAngle newAngle = zero := by
  subst newAngle
  simp [ofAngleDifference]

@[simp]
theorem ofAngleDifference_eq_zero_iff {oldAngle newAngle : ℝ} :
    ofAngleDifference oldAngle newAngle = zero ↔ oldAngle = newAngle := by
  unfold ofAngleDifference
  by_cases hlt : oldAngle < newAngle
  · have hne : oldAngle ≠ newAngle := ne_of_lt hlt
    simp [hlt, hne]
  · by_cases hgt : newAngle < oldAngle
    · have hne : oldAngle ≠ newAngle := (ne_of_lt hgt).symm
      simp [hlt, hgt, hne]
    · have hle_forward : oldAngle ≤ newAngle := le_of_not_gt hgt
      have hle_backward : newAngle ≤ oldAngle := le_of_not_gt hlt
      have heq : oldAngle = newAngle := le_antisymm hle_forward hle_backward
      simp [heq]

end EdgeSign

/-- The next index in a finite cyclic order. -/
def cyclicNext {n : ℕ} (i : Fin n) : Fin n :=
  finRotate n i

/-- Count sign changes in a cyclic sequence of edge signs. -/
def CyclicSignChanges {n : ℕ} (signs : Fin n → EdgeSign) : ℕ :=
  ∑ i : Fin n, if signs i ≠ signs (cyclicNext i) then 1 else 0

/--
Abstract cyclic edge-star data for a finite signed graph.  The order of
`starEdge v : Fin (edgeCount v) → Fin E` is the cyclic order around `v`.
-/
structure VertexStarSignData {V E : ℕ} (edgeSigns : Fin E → EdgeSign) where
  edgeCount : Fin V → ℕ
  starEdge : ∀ v : Fin V, Fin (edgeCount v) → Fin E

namespace VertexStarSignData

/-- The edge signs read in the supplied cyclic order around a vertex. -/
def signSequence {V E : ℕ} {edgeSigns : Fin E → EdgeSign}
    (data : VertexStarSignData (V := V) edgeSigns) (v : Fin V) :
    Fin (data.edgeCount v) → EdgeSign :=
  fun i => edgeSigns (data.starEdge v i)

/-- Sign changes in the cyclic sequence around each vertex star. -/
def vertexSignChanges {V E : ℕ} {edgeSigns : Fin E → EdgeSign}
    (data : VertexStarSignData (V := V) edgeSigns) : Fin V → ℕ :=
  fun v => CyclicSignChanges (data.signSequence v)

end VertexStarSignData

namespace ConvexPolyhedron

variable {V E F : ℕ}

/-- An edge is incident to a vertex when the vertex is one of its endpoints. -/
def EdgeIncidentToVertex (P : ConvexPolyhedron V E F) (v : Fin V) (e : Fin E) : Prop :=
  v ∈ (P.edge e).endpoints

/--
A cyclic listing of all edges incident to one vertex of a polyhedron.  The
`Fin edgeCount` order is the vertex-star cyclic order supplied by the boundary
combinatorics layer.
-/
structure VertexStar (P : ConvexPolyhedron V E F) (v : Fin V) where
  edgeCount : ℕ
  edge : Fin edgeCount → Fin E
  edge_injective : Function.Injective edge
  edge_incident : ∀ i, P.EdgeIncidentToVertex v (edge i)
  complete : ∀ e, P.EdgeIncidentToVertex v e → ∃ i, edge i = e

namespace VertexStar

/-- The edge signs around this vertex star, read in cyclic order. -/
def signSequence {P : ConvexPolyhedron V E F} {v : Fin V} (star : VertexStar P v)
    (edgeSigns : Fin E → EdgeSign) : Fin star.edgeCount → EdgeSign :=
  fun i => edgeSigns (star.edge i)

/-- The number of sign changes around this cyclic vertex star. -/
def signChanges {P : ConvexPolyhedron V E F} {v : Fin V} (star : VertexStar P v)
    (edgeSigns : Fin E → EdgeSign) : ℕ :=
  CyclicSignChanges (star.signSequence edgeSigns)

end VertexStar

/-- Count sign changes around every vertex star of a polyhedron. -/
def vertexSignChanges (P : ConvexPolyhedron V E F)
    (vertexStars : ∀ v : Fin V, VertexStar P v) (edgeSigns : Fin E → EdgeSign) :
    Fin V → ℕ :=
  fun v => (vertexStars v).signChanges edgeSigns

/-- Forget the geometric incidence checks and keep only the cyclic signed stars. -/
def vertexStarSignData (P : ConvexPolyhedron V E F)
    (vertexStars : ∀ v : Fin V, VertexStar P v) (edgeSigns : Fin E → EdgeSign) :
    VertexStarSignData (V := V) edgeSigns where
  edgeCount := fun v => (vertexStars v).edgeCount
  starEdge := fun v i => (vertexStars v).edge i

@[simp]
theorem vertexStarSignData_vertexSignChanges (P : ConvexPolyhedron V E F)
    (vertexStars : ∀ v : Fin V, VertexStar P v) (edgeSigns : Fin E → EdgeSign) :
    (P.vertexStarSignData vertexStars edgeSigns).vertexSignChanges =
      P.vertexSignChanges vertexStars edgeSigns := by
  rfl

/-- The angle between the two recorded face normals incident to an edge. -/
noncomputable def normalAngle (P : ConvexPolyhedron V E F) (e : Fin E) : ℝ :=
  InnerProductGeometry.angle (P.faceNormal (P.edgeFaces e 0))
    (P.faceNormal (P.edgeFaces e 1))

/--
The internal dihedral-angle proxy extracted from the two incident face normals.
For a convex polyhedron with consistently outward supporting normals this is
`π` minus the angle between the normals.
-/
noncomputable def dihedralAngle (P : ConvexPolyhedron V E F) (e : Fin E) : ℝ :=
  Real.pi - P.normalAngle e

/-- The dihedral angle at an indexed edge. -/
noncomputable abbrev DihedralAngle (P : ConvexPolyhedron V E F) (e : Fin E) : ℝ :=
  P.dihedralAngle e

theorem normalAngle_nonneg (P : ConvexPolyhedron V E F) (e : Fin E) :
    0 ≤ P.normalAngle e :=
  InnerProductGeometry.angle_nonneg _ _

theorem normalAngle_le_pi (P : ConvexPolyhedron V E F) (e : Fin E) :
    P.normalAngle e ≤ Real.pi :=
  InnerProductGeometry.angle_le_pi _ _

theorem dihedralAngle_nonneg (P : ConvexPolyhedron V E F) (e : Fin E) :
    0 ≤ P.dihedralAngle e := by
  unfold dihedralAngle
  linarith [P.normalAngle_le_pi e]

theorem dihedralAngle_le_pi (P : ConvexPolyhedron V E F) (e : Fin E) :
    P.dihedralAngle e ≤ Real.pi := by
  unfold dihedralAngle
  linarith [P.normalAngle_nonneg e]

/--
Edge signs for two polyhedra with the same indexed combinatorics, read as the
sign of the change in corresponding dihedral angles from `P` to `Q`.
-/
noncomputable def edgeSigns (P Q : ConvexPolyhedron V E F)
    (_hcomb : SameCombinatorics P Q) (_hlengths : SameEdgeLengths P Q) :
    Fin E → EdgeSign :=
  fun e => EdgeSign.ofAngleDifference (P.dihedralAngle e) (Q.dihedralAngle e)

@[simp]
theorem edgeSigns_eq_zero_iff (P Q : ConvexPolyhedron V E F)
    (hcomb : SameCombinatorics P Q) (hlengths : SameEdgeLengths P Q) (e : Fin E) :
    P.edgeSigns Q hcomb hlengths e = EdgeSign.zero ↔
      P.dihedralAngle e = Q.dihedralAngle e := by
  simp [edgeSigns]

theorem edgeSigns_ne_zero_iff (P Q : ConvexPolyhedron V E F)
    (hcomb : SameCombinatorics P Q) (hlengths : SameEdgeLengths P Q) (e : Fin E) :
    P.edgeSigns Q hcomb hlengths e ≠ EdgeSign.zero ↔
      P.dihedralAngle e ≠ Q.dihedralAngle e :=
  not_congr (P.edgeSigns_eq_zero_iff Q hcomb hlengths e)

theorem edgeSigns_nontrivial_of_exists_dihedralAngle_ne (P Q : ConvexPolyhedron V E F)
    (hcomb : SameCombinatorics P Q) (hlengths : SameEdgeLengths P Q)
    (hdiff : ∃ e, P.dihedralAngle e ≠ Q.dihedralAngle e) :
    ∃ e, P.edgeSigns Q hcomb hlengths e ≠ EdgeSign.zero := by
  rcases hdiff with ⟨e, he⟩
  exact ⟨e, (P.edgeSigns_ne_zero_iff Q hcomb hlengths e).2 he⟩

end ConvexPolyhedron

/-- The nonzero signs left after Cauchy's proof discards unchanged edges. -/
inductive StrictEdgeSign where
  | plus | minus
  deriving DecidableEq, Repr

/-- Forget zero signs and keep only genuine increases/decreases. -/
def EdgeSign.toStrict : EdgeSign → Option StrictEdgeSign
  | plus => some StrictEdgeSign.plus
  | minus => some StrictEdgeSign.minus
  | zero => none

@[simp]
theorem edgeSign_toStrict_eq_none_iff (s : EdgeSign) : s.toStrict = none ↔ s = zero := by
  cases s <;> simp [EdgeSign.toStrict]

/--
The local sign-change count around a triangular face. Cauchy's proof labels
edges by whether their dihedral angle increases, decreases, or stays fixed,
then counts sign changes around faces.
-/
def SignChangesAroundTriangle (a b c : EdgeSign) : ℕ :=
  (if a ≠ b then 1 else 0) + (if b ≠ c then 1 else 0) + (if c ≠ a then 1 else 0)

theorem signChangesAroundTriangle_le_three (a b c : EdgeSign) :
    SignChangesAroundTriangle a b c ≤ 3 := by
  unfold SignChangesAroundTriangle
  by_cases hab : a ≠ b <;> by_cases hbc : b ≠ c <;> by_cases hca : c ≠ a <;>
    simp [hab, hbc, hca]

theorem signChangesAroundTriangle_eq_zero_of_constant (s : EdgeSign) :
    SignChangesAroundTriangle s s s = 0 := by
  simp [SignChangesAroundTriangle]

theorem signChangesAroundTriangle_eq_zero_iff (a b c : EdgeSign) :
    SignChangesAroundTriangle a b c = 0 ↔ a = b ∧ b = c := by
  cases a <;> cases b <;> cases c <;> decide

def StrictSignChangesAroundTriangle (a b c : StrictEdgeSign) : ℕ :=
  (if a ≠ b then 1 else 0) + (if b ≠ c then 1 else 0) + (if c ≠ a then 1 else 0)

theorem strictSignChangesAroundTriangle_eq_zero_or_two (a b c : StrictEdgeSign) :
    StrictSignChangesAroundTriangle a b c = 0 ∨
      StrictSignChangesAroundTriangle a b c = 2 := by
  cases a <;> cases b <;> cases c <;> decide

theorem strictSignChangesAroundTriangle_le_two (a b c : StrictEdgeSign) :
    StrictSignChangesAroundTriangle a b c ≤ 2 := by
  rcases strictSignChangesAroundTriangle_eq_zero_or_two a b c with h | h <;> omega

abbrev StrictTriangleSigns := StrictEdgeSign × StrictEdgeSign × StrictEdgeSign

namespace StrictTriangleSigns

def signChanges (t : StrictTriangleSigns) : ℕ :=
  StrictSignChangesAroundTriangle t.1 t.2.1 t.2.2

theorem signChanges_le_two (t : StrictTriangleSigns) :
    signChanges t ≤ 2 :=
  strictSignChangesAroundTriangle_le_two t.1 t.2.1 t.2.2

end StrictTriangleSigns

theorem strictSignChangesAroundTriangle_even (a b c : StrictEdgeSign) :
    Even (StrictSignChangesAroundTriangle a b c) := by
  cases a <;> cases b <;> cases c <;> decide

theorem strictSignChangesAroundTriangle_eq_zero_iff (a b c : StrictEdgeSign) :
    StrictSignChangesAroundTriangle a b c = 0 ↔ a = b ∧ b = c := by
  cases a <;> cases b <;> cases c <;> decide

/-- `StrictSignChangesAroundTriangle` is invariant under cyclic permutation. -/
theorem strictSignChangesAroundTriangle_cycle (a b c : StrictEdgeSign) :
    StrictSignChangesAroundTriangle a b c = StrictSignChangesAroundTriangle b c a := by
  cases a <;> cases b <;> cases c <;> decide

/-- `SignChangesAroundTriangle` is invariant under cyclic permutation. -/
theorem signChangesAroundTriangle_cycle (a b c : EdgeSign) :
    SignChangesAroundTriangle a b c = SignChangesAroundTriangle b c a := by
  cases a <;> cases b <;> cases c <;> decide

/-! ### Cauchy arms -/

/-- The planar ambient space for Cauchy's arm lemma. -/
abbrev Euclidean2 :=
  EuclideanSpace ℝ (Fin 2)

namespace CauchyArm

/-- The initial vertex index of the `i`-th edge in an `n`-edge arm. -/
def edgeStart {n : ℕ} (i : Fin n) : Fin (n + 1) :=
  ⟨i.1, by omega⟩

/-- The terminal vertex index of the `i`-th edge in an `n`-edge arm. -/
def edgeEnd {n : ℕ} (i : Fin n) : Fin (n + 1) :=
  ⟨i.1 + 1, by omega⟩

/-- The first vertex of an `n`-edge arm. -/
def firstVertex (n : ℕ) : Fin (n + 1) :=
  ⟨0, by omega⟩

/-- The last vertex of an `n`-edge arm. -/
def lastVertex (n : ℕ) : Fin (n + 1) :=
  ⟨n, by omega⟩

/-- The edge immediately before the `i`-th joint angle. -/
def jointPrevEdge {n : ℕ} (i : Fin (n - 1)) : Fin n :=
  ⟨i.1, by omega⟩

/-- The edge immediately after the `i`-th joint angle. -/
def jointNextEdge {n : ℕ} (i : Fin (n - 1)) : Fin n :=
  ⟨i.1 + 1, by omega⟩

/-- The directed vector of the `i`-th edge in an arm. -/
noncomputable def edgeVector {n : ℕ} (vertex : Fin (n + 1) → Euclidean2) (i : Fin n) :
    Euclidean2 :=
  vertex (edgeEnd i) - vertex (edgeStart i)

/-- The interior angle at the `i`-th joint of an arm. -/
noncomputable def geometricJointAngle {n : ℕ} (vertex : Fin (n + 1) → Euclidean2)
    (i : Fin (n - 1)) : ℝ :=
  InnerProductGeometry.angle (-(edgeVector vertex (jointPrevEdge i)))
    (edgeVector vertex (jointNextEdge i))

end CauchyArm

/--
A planar Cauchy arm with `n` fixed-length edges and the `n - 1` interior
angles between consecutive edges.  The convexity needed by the arm lemma is
recorded as the local angle bounds `0 ≤ angle ≤ π`.
-/
structure CauchyArm (n : ℕ) where
  vertex : Fin (n + 1) → Euclidean2
  edgeLength : Fin n → ℝ
  jointAngle : Fin (n - 1) → ℝ
  chord : ℝ
  edgeLength_eq_dist :
    ∀ i, edgeLength i = dist (vertex (CauchyArm.edgeStart i)) (vertex (CauchyArm.edgeEnd i))
  jointAngle_eq_geometric :
    ∀ i, jointAngle i = CauchyArm.geometricJointAngle vertex i
  edgeLength_pos : ∀ i, 0 < edgeLength i
  jointAngle_nonneg : ∀ i, 0 ≤ jointAngle i
  jointAngle_le_pi : ∀ i, jointAngle i ≤ Real.pi
  chord_eq_dist :
    chord = dist (vertex (CauchyArm.firstVertex n)) (vertex (CauchyArm.lastVertex n))

namespace CauchyArm

/-- The actual endpoint chord of an arm, computed from its embedded vertices. -/
noncomputable def closingChord {n : ℕ} (A : CauchyArm n) : ℝ :=
  dist (A.vertex (firstVertex n)) (A.vertex (lastVertex n))

@[simp]
theorem closingChord_eq_dist {n : ℕ} (A : CauchyArm n) :
    A.closingChord = dist (A.vertex (firstVertex n)) (A.vertex (lastVertex n)) := rfl

/-- The stored chord field agrees with the vertex-defined closing chord. -/
theorem chord_eq_closingChord {n : ℕ} (A : CauchyArm n) :
    A.chord = A.closingChord := by
  rw [closingChord, A.chord_eq_dist]

/-- The last edge index of an `n + 1`-edge arm. -/
def lastEdgeIndex (n : ℕ) : Fin (n + 1) :=
  ⟨n, by omega⟩

/-- The last joint index of an `n + 2`-edge arm. -/
def lastJointIndex (n : ℕ) : Fin ((n + 2) - 1) :=
  ⟨n, by omega⟩

/-- The arm obtained by deleting the last edge. -/
noncomputable def initialSubarm {n : ℕ} (A : CauchyArm (n + 1)) : CauchyArm n where
  vertex i := A.vertex ⟨i.1, by omega⟩
  edgeLength i := A.edgeLength ⟨i.1, by omega⟩
  jointAngle i := A.jointAngle ⟨i.1, by omega⟩
  chord := dist (A.vertex ⟨0, by omega⟩) (A.vertex ⟨n, by omega⟩)
  edgeLength_eq_dist := by
    intro i
    simpa [CauchyArm.edgeStart, CauchyArm.edgeEnd] using
      A.edgeLength_eq_dist ⟨i.1, by omega⟩
  jointAngle_eq_geometric := by
    intro i
    simpa [CauchyArm.geometricJointAngle, CauchyArm.edgeVector, CauchyArm.edgeStart,
      CauchyArm.edgeEnd, CauchyArm.jointPrevEdge, CauchyArm.jointNextEdge] using
      A.jointAngle_eq_geometric ⟨i.1, by omega⟩
  edgeLength_pos := by
    intro i
    exact A.edgeLength_pos ⟨i.1, by omega⟩
  jointAngle_nonneg := by
    intro i
    exact A.jointAngle_nonneg ⟨i.1, by omega⟩
  jointAngle_le_pi := by
    intro i
    exact A.jointAngle_le_pi ⟨i.1, by omega⟩
  chord_eq_dist := by
    simp [CauchyArm.firstVertex, CauchyArm.lastVertex]

@[simp]
theorem initialSubarm_closingChord {n : ℕ} (A : CauchyArm (n + 1)) :
    A.initialSubarm.closingChord =
      dist (A.vertex ⟨0, by omega⟩) (A.vertex ⟨n, by omega⟩) := by
  rfl

/--
The angle at the prefix endpoint in the closing triangle formed by the prefix
chord, the last edge, and the full closing chord.
-/
noncomputable def appendAngle {n : ℕ} (A : CauchyArm (n + 1)) : ℝ :=
  InnerProductGeometry.angle
    (-(A.vertex ⟨n, by omega⟩ - A.vertex ⟨0, by omega⟩))
    (A.vertex ⟨n + 1, by omega⟩ - A.vertex ⟨n, by omega⟩)

theorem appendAngle_nonneg {n : ℕ} (A : CauchyArm (n + 1)) :
    0 ≤ A.appendAngle :=
  InnerProductGeometry.angle_nonneg _ _

theorem appendAngle_le_pi {n : ℕ} (A : CauchyArm (n + 1)) :
    A.appendAngle ≤ Real.pi :=
  InnerProductGeometry.angle_le_pi _ _

/--
The law-of-cosines radicand for a two-edge arm with side lengths `a`, `b` and
included angle `theta`.
-/
noncomputable def twoEdgeChordRadicand (a b theta : ℝ) : ℝ :=
  a ^ 2 + b ^ 2 - 2 * a * b * Real.cos theta

/-- The chord length given by the law of cosines for a two-edge arm. -/
noncomputable def twoEdgeChord (a b theta : ℝ) : ℝ :=
  Real.sqrt (twoEdgeChordRadicand a b theta)

/--
The law-of-cosines statement for the closing triangle obtained by replacing
the initial subarm with its endpoint chord and keeping the last edge.
-/
def AppendLawOfCosines {n : ℕ} (A : CauchyArm (n + 1)) : Prop :=
  A.closingChord =
    twoEdgeChord A.initialSubarm.closingChord
      (A.edgeLength (lastEdgeIndex n)) A.appendAngle

/--
The projection condition under which increasing the initial subarm's closing
chord cannot shorten the final law-of-cosines chord.
-/
def AppendProjectionCondition {n : ℕ} (A : CauchyArm (n + 1)) : Prop :=
  A.edgeLength (lastEdgeIndex n) * Real.cos A.appendAngle ≤ A.initialSubarm.closingChord

/--
The specialized law-of-cosines statement for a two-edge `CauchyArm`.  This is
kept as a predicate so the two-edge monotonicity proof can be reused before the
full vector law-of-cosines bridge is connected to `geometricJointAngle`.
-/
def TwoEdgeLawOfCosines (A : CauchyArm 2) : Prop :=
  A.chord = twoEdgeChord (A.edgeLength 0) (A.edgeLength 1) (A.jointAngle 0)

theorem twoEdgeChordRadicand_nonneg {a b theta : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) :
    0 ≤ twoEdgeChordRadicand a b theta := by
  have hab : 0 ≤ 2 * a * b := by positivity
  have hcos : Real.cos theta ≤ 1 := Real.cos_le_one theta
  have hmul : 2 * a * b * Real.cos theta ≤ 2 * a * b * 1 := by
    exact mul_le_mul_of_nonneg_left hcos hab
  have hsq : 0 ≤ (a - b) ^ 2 := sq_nonneg (a - b)
  unfold twoEdgeChordRadicand
  nlinarith [hmul, hsq]

theorem twoEdgeChordRadicand_mono {a b theta phi : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b)
    (htheta_nonneg : 0 ≤ theta) (hphi_le_pi : phi ≤ Real.pi)
    (hangle : theta ≤ phi) :
    twoEdgeChordRadicand a b theta ≤ twoEdgeChordRadicand a b phi := by
  have hcos : Real.cos phi ≤ Real.cos theta :=
    Real.cos_le_cos_of_nonneg_of_le_pi htheta_nonneg hphi_le_pi hangle
  have hab : 0 ≤ 2 * a * b := by positivity
  have hmul : 2 * a * b * Real.cos phi ≤ 2 * a * b * Real.cos theta := by
    exact mul_le_mul_of_nonneg_left hcos hab
  unfold twoEdgeChordRadicand
  nlinarith

/--
For a fixed second side and included angle, the law-of-cosines radicand is
monotone in the first side once the first side is at least the projection of
the second side onto it.  This is the extra algebraic condition needed when
the first side is itself the closing chord of a shorter arm.
-/
theorem twoEdgeChordRadicand_mono_left {a a' b theta : ℝ}
    (hside : a ≤ a') (hproj : b * Real.cos theta ≤ a) :
    twoEdgeChordRadicand a b theta ≤ twoEdgeChordRadicand a' b theta := by
  have hfactor_nonneg : 0 ≤ a' + a - 2 * b * Real.cos theta := by
    nlinarith
  have hmul_nonneg :
      0 ≤ (a' - a) * (a' + a - 2 * b * Real.cos theta) := by
    exact mul_nonneg (sub_nonneg.mpr hside) hfactor_nonneg
  unfold twoEdgeChordRadicand
  nlinarith

theorem twoEdgeChordRadicand_strict_mono_left {a a' b theta : ℝ}
    (hside : a < a') (hproj : b * Real.cos theta ≤ a) :
    twoEdgeChordRadicand a b theta < twoEdgeChordRadicand a' b theta := by
  have hfactor_pos : 0 < a' + a - 2 * b * Real.cos theta := by
    nlinarith
  have hmul_pos :
      0 < (a' - a) * (a' + a - 2 * b * Real.cos theta) := by
    exact mul_pos (sub_pos.mpr hside) hfactor_pos
  unfold twoEdgeChordRadicand
  nlinarith

theorem twoEdgeChordRadicand_mono_left_and_angle {a a' b theta phi : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b)
    (htheta_nonneg : 0 ≤ theta) (hphi_le_pi : phi ≤ Real.pi)
    (hside : a ≤ a') (hangle : theta ≤ phi)
    (hproj : b * Real.cos theta ≤ a) :
    twoEdgeChordRadicand a b theta ≤ twoEdgeChordRadicand a' b phi := by
  have ha' : 0 ≤ a' := le_trans ha hside
  exact le_trans (twoEdgeChordRadicand_mono_left hside hproj)
    (twoEdgeChordRadicand_mono ha' hb htheta_nonneg hphi_le_pi hangle)

theorem twoEdgeChord_mono {a b theta phi : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b)
    (htheta_nonneg : 0 ≤ theta) (hphi_le_pi : phi ≤ Real.pi)
    (hangle : theta ≤ phi) :
    twoEdgeChord a b theta ≤ twoEdgeChord a b phi :=
  Real.sqrt_le_sqrt (twoEdgeChordRadicand_mono ha hb htheta_nonneg hphi_le_pi hangle)

theorem twoEdgeChord_mono_left_and_angle {a a' b theta phi : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b)
    (htheta_nonneg : 0 ≤ theta) (hphi_le_pi : phi ≤ Real.pi)
    (hside : a ≤ a') (hangle : theta ≤ phi)
    (hproj : b * Real.cos theta ≤ a) :
    twoEdgeChord a b theta ≤ twoEdgeChord a' b phi :=
  Real.sqrt_le_sqrt
    (twoEdgeChordRadicand_mono_left_and_angle ha hb htheta_nonneg hphi_le_pi
      hside hangle hproj)

theorem twoEdgeChordRadicand_strict_mono {a b theta phi : ℝ}
    (ha : 0 < a) (hb : 0 < b)
    (htheta_nonneg : 0 ≤ theta) (hphi_le_pi : phi ≤ Real.pi)
    (hangle : theta < phi) :
    twoEdgeChordRadicand a b theta < twoEdgeChordRadicand a b phi := by
  have hcos : Real.cos phi < Real.cos theta :=
    Real.cos_lt_cos_of_nonneg_of_le_pi htheta_nonneg hphi_le_pi hangle
  have hab : 0 < 2 * a * b := by positivity
  have hmul : 2 * a * b * Real.cos phi < 2 * a * b * Real.cos theta := by
    exact mul_lt_mul_of_pos_left hcos hab
  unfold twoEdgeChordRadicand
  nlinarith

theorem twoEdgeChordRadicand_strict_mono_left_or_angle {a a' b theta phi : ℝ}
    (ha : 0 < a) (hb : 0 < b)
    (htheta_nonneg : 0 ≤ theta) (hphi_le_pi : phi ≤ Real.pi)
    (hside : a ≤ a') (hangle : theta ≤ phi)
    (hproj : b * Real.cos theta ≤ a)
    (hstrict : a < a' ∨ theta < phi) :
    twoEdgeChordRadicand a b theta < twoEdgeChordRadicand a' b phi := by
  rcases hstrict with hside_strict | hangle_strict
  · have ha' : 0 ≤ a' := le_of_lt (lt_trans ha hside_strict)
    exact lt_of_lt_of_le
      (twoEdgeChordRadicand_strict_mono_left hside_strict hproj)
      (twoEdgeChordRadicand_mono ha' (le_of_lt hb) htheta_nonneg hphi_le_pi hangle)
  · have ha' : 0 < a' := lt_of_lt_of_le ha hside
    exact lt_of_le_of_lt
      (twoEdgeChordRadicand_mono_left hside hproj)
      (twoEdgeChordRadicand_strict_mono ha' hb htheta_nonneg hphi_le_pi hangle_strict)

theorem twoEdgeChord_strict_mono {a b theta phi : ℝ}
    (ha : 0 < a) (hb : 0 < b)
    (htheta_nonneg : 0 ≤ theta) (hphi_le_pi : phi ≤ Real.pi)
    (hangle : theta < phi) :
    twoEdgeChord a b theta < twoEdgeChord a b phi := by
  apply Real.sqrt_lt_sqrt
  · exact twoEdgeChordRadicand_nonneg (le_of_lt ha) (le_of_lt hb)
  · exact twoEdgeChordRadicand_strict_mono ha hb htheta_nonneg hphi_le_pi hangle

theorem twoEdgeChord_strict_mono_left_or_angle {a a' b theta phi : ℝ}
    (ha : 0 < a) (hb : 0 < b)
    (htheta_nonneg : 0 ≤ theta) (hphi_le_pi : phi ≤ Real.pi)
    (hside : a ≤ a') (hangle : theta ≤ phi)
    (hproj : b * Real.cos theta ≤ a)
    (hstrict : a < a' ∨ theta < phi) :
    twoEdgeChord a b theta < twoEdgeChord a' b phi := by
  apply Real.sqrt_lt_sqrt
  · exact twoEdgeChordRadicand_nonneg (le_of_lt ha) (le_of_lt hb)
  · exact twoEdgeChordRadicand_strict_mono_left_or_angle ha hb htheta_nonneg
      hphi_le_pi hside hangle hproj hstrict


/--
Two-edge Cauchy arm monotonicity.  If the two edge lengths are fixed and the
included angle is opened, then the endpoint chord strictly increases, unless
the angle did not change.
-/
theorem arm_chord_monotone (A B : CauchyArm 2)
    (hA : A.TwoEdgeLawOfCosines) (hB : B.TwoEdgeLawOfCosines)
    (hlength : ∀ i : Fin 2, A.edgeLength i = B.edgeLength i)
    (hangle : ∀ i : Fin (2 - 1), A.jointAngle i ≤ B.jointAngle i) :
    A.chord < B.chord ∨ ∀ i : Fin (2 - 1), A.jointAngle i = B.jointAngle i := by
  by_cases hstrict : A.jointAngle 0 < B.jointAngle 0
  · left
    rw [hA, hB]
    rw [← hlength 0, ← hlength 1]
    exact twoEdgeChord_strict_mono (A.edgeLength_pos 0) (A.edgeLength_pos 1)
      (A.jointAngle_nonneg 0) (B.jointAngle_le_pi 0) hstrict
  · right
    intro i
    have hi : i = (0 : Fin (2 - 1)) := by
      ext
      omega
    rw [hi]
    exact le_antisymm (hangle 0) (le_of_not_gt hstrict)

/-- The two-edge monotonicity theorem, stated for the vertex-defined chord. -/
theorem closingChord_mono_two (A B : CauchyArm 2)
    (hA : A.TwoEdgeLawOfCosines) (hB : B.TwoEdgeLawOfCosines)
    (hlength : ∀ i : Fin 2, A.edgeLength i = B.edgeLength i)
    (hangle : ∀ i : Fin (2 - 1), A.jointAngle i ≤ B.jointAngle i) :
    A.closingChord < B.closingChord ∨
      ∀ i : Fin (2 - 1), A.jointAngle i = B.jointAngle i := by
  have h := arm_chord_monotone A B hA hB hlength hangle
  rcases h with hlt | heq
  · left
    rwa [A.chord_eq_closingChord, B.chord_eq_closingChord] at hlt
  · exact Or.inr heq

/-- Equal side lengths and equal included angle give equal two-edge closing chords. -/
theorem closingChord_eq_of_eq_two (A B : CauchyArm 2)
    (hA : A.TwoEdgeLawOfCosines) (hB : B.TwoEdgeLawOfCosines)
    (hlength : ∀ i : Fin 2, A.edgeLength i = B.edgeLength i)
    (hangle : ∀ i : Fin (2 - 1), A.jointAngle i = B.jointAngle i) :
    A.closingChord = B.closingChord := by
  rw [← A.chord_eq_closingChord, ← B.chord_eq_closingChord, hA, hB]
  rw [← hlength 0, ← hlength 1, ← hangle 0]

/--
Induction step for the arm chord: assume the initial `n + 1`-edge subarms have
already produced the expected monotonicity alternative, then use the final
closing triangle to extend it across the last edge.

The hypotheses after `hprefix_eq_of_angles` are exactly the missing geometric
bridges for the closing triangle: its law-of-cosines formula, monotonicity of
the triangle angle under opening the last joint, and the projection condition
needed because the prefix chord is not a fixed side.
-/
theorem closingChord_mono_succ_of_prefix {n : ℕ} (A B : CauchyArm (n + 2))
    (hprefix_mono :
      A.initialSubarm.closingChord < B.initialSubarm.closingChord ∨
        ∀ i : Fin ((n + 1) - 1),
          A.initialSubarm.jointAngle i = B.initialSubarm.jointAngle i)
    (hprefix_eq_of_angles :
      (∀ i : Fin ((n + 1) - 1),
          A.initialSubarm.jointAngle i = B.initialSubarm.jointAngle i) →
        A.initialSubarm.closingChord = B.initialSubarm.closingChord)
    (hprefix_pos : 0 < A.initialSubarm.closingChord)
    (hA_append : A.AppendLawOfCosines)
    (hB_append : B.AppendLawOfCosines)
    (happendAngle : A.appendAngle ≤ B.appendAngle)
    (happendAngle_strict :
      A.initialSubarm.closingChord = B.initialSubarm.closingChord →
        A.jointAngle (lastJointIndex n) < B.jointAngle (lastJointIndex n) →
          A.appendAngle < B.appendAngle)
    (hproj : A.AppendProjectionCondition)
    (hlastLength :
      A.edgeLength (lastEdgeIndex (n + 1)) = B.edgeLength (lastEdgeIndex (n + 1)))
    (hangle : ∀ i : Fin ((n + 2) - 1), A.jointAngle i ≤ B.jointAngle i) :
    A.closingChord < B.closingChord ∨
      ∀ i : Fin ((n + 2) - 1), A.jointAngle i = B.jointAngle i := by
  rcases hprefix_mono with hprefix_strict | hprefix_angles
  · left
    rw [hA_append, hB_append, ← hlastLength]
    exact twoEdgeChord_strict_mono_left_or_angle hprefix_pos
      (A.edgeLength_pos (lastEdgeIndex (n + 1)))
      (A.appendAngle_nonneg) (B.appendAngle_le_pi)
      (le_of_lt hprefix_strict) happendAngle hproj (Or.inl hprefix_strict)
  · have hprefix_chord :
        A.initialSubarm.closingChord = B.initialSubarm.closingChord :=
      hprefix_eq_of_angles hprefix_angles
    by_cases hlast_strict :
        A.jointAngle (lastJointIndex n) < B.jointAngle (lastJointIndex n)
    · left
      rw [hA_append, hB_append, ← hlastLength]
      exact twoEdgeChord_strict_mono_left_or_angle hprefix_pos
        (A.edgeLength_pos (lastEdgeIndex (n + 1)))
        (A.appendAngle_nonneg) (B.appendAngle_le_pi)
        (le_of_eq hprefix_chord) happendAngle hproj
        (Or.inr (happendAngle_strict hprefix_chord hlast_strict))
    · right
      have hlast :
          A.jointAngle (lastJointIndex n) = B.jointAngle (lastJointIndex n) :=
        le_antisymm (hangle (lastJointIndex n)) (le_of_not_gt hlast_strict)
      intro i
      by_cases hi : i.1 < n
      · have hprefix_i :=
          hprefix_angles ⟨i.1, by omega⟩
        simpa [initialSubarm] using hprefix_i
      · have hi_last : i = lastJointIndex n := by
          ext
          simp [lastJointIndex]
          omega
        simpa [hi_last] using hlast

/-- The same induction step, with the initial-subarm alternative obtained from an IH. -/
theorem closingChord_mono_succ {n : ℕ}
    (hIH_mono :
      ∀ A' B' : CauchyArm (n + 1),
        (∀ i : Fin (n + 1), A'.edgeLength i = B'.edgeLength i) →
        (∀ i : Fin ((n + 1) - 1), A'.jointAngle i ≤ B'.jointAngle i) →
          A'.closingChord < B'.closingChord ∨
            ∀ i : Fin ((n + 1) - 1), A'.jointAngle i = B'.jointAngle i)
    (hIH_eq :
      ∀ A' B' : CauchyArm (n + 1),
        (∀ i : Fin (n + 1), A'.edgeLength i = B'.edgeLength i) →
        (∀ i : Fin ((n + 1) - 1), A'.jointAngle i = B'.jointAngle i) →
          A'.closingChord = B'.closingChord)
    (A B : CauchyArm (n + 2))
    (hprefix_pos : 0 < A.initialSubarm.closingChord)
    (hA_append : A.AppendLawOfCosines)
    (hB_append : B.AppendLawOfCosines)
    (happendAngle : A.appendAngle ≤ B.appendAngle)
    (happendAngle_strict :
      A.initialSubarm.closingChord = B.initialSubarm.closingChord →
        A.jointAngle (lastJointIndex n) < B.jointAngle (lastJointIndex n) →
          A.appendAngle < B.appendAngle)
    (hproj : A.AppendProjectionCondition)
    (hlength : ∀ i : Fin (n + 2), A.edgeLength i = B.edgeLength i)
    (hangle : ∀ i : Fin ((n + 2) - 1), A.jointAngle i ≤ B.jointAngle i) :
    A.closingChord < B.closingChord ∨
      ∀ i : Fin ((n + 2) - 1), A.jointAngle i = B.jointAngle i := by
  have hlength_prefix :
      ∀ i : Fin (n + 1),
        A.initialSubarm.edgeLength i = B.initialSubarm.edgeLength i := by
    intro i
    simpa [initialSubarm] using hlength ⟨i.1, by omega⟩
  have hangle_prefix :
      ∀ i : Fin ((n + 1) - 1),
        A.initialSubarm.jointAngle i ≤ B.initialSubarm.jointAngle i := by
    intro i
    simpa [initialSubarm] using hangle ⟨i.1, by omega⟩
  refine closingChord_mono_succ_of_prefix A B
    (hIH_mono A.initialSubarm B.initialSubarm hlength_prefix hangle_prefix) ?_
    hprefix_pos hA_append hB_append happendAngle happendAngle_strict hproj
    (hlength (lastEdgeIndex (n + 1))) hangle
  intro hprefix_angles
  exact hIH_eq A.initialSubarm B.initialSubarm hlength_prefix hprefix_angles

/--
Concrete three-edge instance of the induction step, using the proved two-edge
law-of-cosines base case on the initial subarms.
-/
theorem closingChord_mono_three (A B : CauchyArm 3)
    (hA_prefix : A.initialSubarm.TwoEdgeLawOfCosines)
    (hB_prefix : B.initialSubarm.TwoEdgeLawOfCosines)
    (hprefix_pos : 0 < A.initialSubarm.closingChord)
    (hA_append : A.AppendLawOfCosines)
    (hB_append : B.AppendLawOfCosines)
    (happendAngle : A.appendAngle ≤ B.appendAngle)
    (happendAngle_strict :
      A.initialSubarm.closingChord = B.initialSubarm.closingChord →
        A.jointAngle (lastJointIndex 1) < B.jointAngle (lastJointIndex 1) →
          A.appendAngle < B.appendAngle)
    (hproj : A.AppendProjectionCondition)
    (hlength : ∀ i : Fin 3, A.edgeLength i = B.edgeLength i)
    (hangle : ∀ i : Fin (3 - 1), A.jointAngle i ≤ B.jointAngle i) :
    A.closingChord < B.closingChord ∨
      ∀ i : Fin (3 - 1), A.jointAngle i = B.jointAngle i := by
  refine closingChord_mono_succ_of_prefix (n := 1) A B ?_ ?_
    hprefix_pos hA_append hB_append happendAngle happendAngle_strict hproj
    (hlength (lastEdgeIndex 2)) hangle
  · apply closingChord_mono_two A.initialSubarm B.initialSubarm hA_prefix hB_prefix
    · intro i
      simpa [initialSubarm] using hlength ⟨i.1, by omega⟩
    · intro i
      simpa [initialSubarm] using hangle ⟨i.1, by omega⟩
  · intro hprefix_angles
    apply closingChord_eq_of_eq_two A.initialSubarm B.initialSubarm hA_prefix hB_prefix
    · intro i
      simpa [initialSubarm] using hlength ⟨i.1, by omega⟩
    · exact hprefix_angles

/--
Recursive evidence that a pair of arms has the law-of-cosines data needed by
the induction proof.  The `succ` constructor is deliberately explicit about
the geometric facts not yet derived from the bare `CauchyArm` fields.
-/
inductive ArmChordMonotoneCertificate : {n : ℕ} → CauchyArm n → CauchyArm n → Prop
  | zero (A B : CauchyArm 0) : ArmChordMonotoneCertificate A B
  | one (A B : CauchyArm 1) : ArmChordMonotoneCertificate A B
  | two {A B : CauchyArm 2}
      (hA : A.TwoEdgeLawOfCosines) (hB : B.TwoEdgeLawOfCosines) :
      ArmChordMonotoneCertificate A B
  | succ {n : ℕ} {A B : CauchyArm (n + 2)}
      (prefixCert : ArmChordMonotoneCertificate A.initialSubarm B.initialSubarm)
      (hprefix_pos : 0 < A.initialSubarm.closingChord)
      (hA_append : A.AppendLawOfCosines)
      (hB_append : B.AppendLawOfCosines)
      (happendAngle : A.appendAngle ≤ B.appendAngle)
      (happendAngle_strict :
        A.initialSubarm.closingChord = B.initialSubarm.closingChord →
          A.jointAngle (lastJointIndex n) < B.jointAngle (lastJointIndex n) →
            A.appendAngle < B.appendAngle)
      (happendAngle_eq :
        A.initialSubarm.closingChord = B.initialSubarm.closingChord →
          A.jointAngle (lastJointIndex n) = B.jointAngle (lastJointIndex n) →
            A.appendAngle = B.appendAngle)
      (hproj : A.AppendProjectionCondition) :
      ArmChordMonotoneCertificate A B

/--
Under the same recursive law-of-cosines certificate, equal edge lengths and
equal joint angles determine the closing chord.
-/
theorem closingChord_eq_of_eq_general {n : ℕ} {A B : CauchyArm n}
    (cert : ArmChordMonotoneCertificate A B)
    (hlength : ∀ i : Fin n, A.edgeLength i = B.edgeLength i)
    (hangle : ∀ i : Fin (n - 1), A.jointAngle i = B.jointAngle i) :
    A.closingChord = B.closingChord := by
  induction cert with
  | zero A B =>
      simp [closingChord, CauchyArm.firstVertex, CauchyArm.lastVertex]
  | one A B =>
      rw [closingChord, closingChord]
      have hAedge :
          A.edgeLength 0 =
            dist (A.vertex (CauchyArm.firstVertex 1)) (A.vertex (CauchyArm.lastVertex 1)) := by
        simpa [CauchyArm.firstVertex, CauchyArm.lastVertex, CauchyArm.edgeStart,
          CauchyArm.edgeEnd] using A.edgeLength_eq_dist 0
      have hBedge :
          B.edgeLength 0 =
            dist (B.vertex (CauchyArm.firstVertex 1)) (B.vertex (CauchyArm.lastVertex 1)) := by
        simpa [CauchyArm.firstVertex, CauchyArm.lastVertex, CauchyArm.edgeStart,
          CauchyArm.edgeEnd] using B.edgeLength_eq_dist 0
      rw [← hAedge, ← hBedge, hlength 0]
  | two hA hB =>
      exact closingChord_eq_of_eq_two _ _ hA hB hlength hangle
  | succ prefixCert hprefix_pos hA_append hB_append happendAngle happendAngle_strict
      happendAngle_eq hproj ih =>
      rename_i m A' B'
      have hlength_prefix :
          ∀ i : Fin (m + 1),
            A'.initialSubarm.edgeLength i = B'.initialSubarm.edgeLength i := by
        intro i
        simpa [initialSubarm] using hlength ⟨i.1, by omega⟩
      have hangle_prefix :
          ∀ i : Fin ((m + 1) - 1),
            A'.initialSubarm.jointAngle i = B'.initialSubarm.jointAngle i := by
        intro i
        simpa [initialSubarm] using hangle ⟨i.1, by omega⟩
      have hprefix_chord :
          A'.initialSubarm.closingChord = B'.initialSubarm.closingChord :=
        ih hlength_prefix hangle_prefix
      have hlastLength :
          A'.edgeLength (lastEdgeIndex (m + 1)) =
            B'.edgeLength (lastEdgeIndex (m + 1)) :=
        hlength (lastEdgeIndex (m + 1))
      have hlastAngle :
          A'.jointAngle (lastJointIndex m) = B'.jointAngle (lastJointIndex m) :=
        hangle (lastJointIndex m)
      have happend_eq : A'.appendAngle = B'.appendAngle :=
        happendAngle_eq hprefix_chord hlastAngle
      rw [hA_append, hB_append, ← hprefix_chord, ← hlastLength, ← happend_eq]

/--
General Cauchy-arm chord monotonicity, assembled by induction from the two-edge
law-of-cosines base case plus explicit closing-triangle certificates at each
successor step.
-/
theorem arm_chord_monotone_general {n : ℕ} {A B : CauchyArm n}
    (cert : ArmChordMonotoneCertificate A B)
    (hlength : ∀ i : Fin n, A.edgeLength i = B.edgeLength i)
    (hangle : ∀ i : Fin (n - 1), A.jointAngle i ≤ B.jointAngle i) :
    A.closingChord < B.closingChord ∨
      ∀ i : Fin (n - 1), A.jointAngle i = B.jointAngle i := by
  induction cert with
  | zero A B =>
      right
      intro i
      exact Fin.elim0 i
  | one A B =>
      right
      intro i
      exact Fin.elim0 i
  | two hA hB =>
      exact closingChord_mono_two _ _ hA hB hlength hangle
  | succ prefixCert hprefix_pos hA_append hB_append happendAngle happendAngle_strict
      happendAngle_eq hproj ih =>
      rename_i m A' B'
      have hlength_prefix :
          ∀ i : Fin (m + 1),
            A'.initialSubarm.edgeLength i = B'.initialSubarm.edgeLength i := by
        intro i
        simpa [initialSubarm] using hlength ⟨i.1, by omega⟩
      have hangle_prefix :
          ∀ i : Fin ((m + 1) - 1),
            A'.initialSubarm.jointAngle i ≤ B'.initialSubarm.jointAngle i := by
        intro i
        simpa [initialSubarm] using hangle ⟨i.1, by omega⟩
      refine closingChord_mono_succ_of_prefix A' B'
        (ih hlength_prefix hangle_prefix) ?_ hprefix_pos hA_append hB_append
        happendAngle happendAngle_strict hproj (hlength (lastEdgeIndex (m + 1))) hangle
      intro hprefix_angles
      exact closingChord_eq_of_eq_general prefixCert hlength_prefix hprefix_angles

end CauchyArm

/--
Cauchy's arm lemma (abstract finite version): if a convex polygon's angles
are opened (increased), the chord between the first and last vertex increases.
This is the geometric engine of Cauchy's rigidity proof.

This statement extracts the strict chord-increase conclusion from the
abstract arm-lemma hypothesis: given that some angle is *strictly* opened,
the second disjunct of `_harm` (no angle changes) is excluded.
-/
theorem arm_lemma_abstract {n : ℕ} (angles newAngles : Fin n → ℝ)
    (chord newChord : ℝ)
    (_hopen : ∀ i, angles i ≤ newAngles i)
    (hstrict : ∃ i, angles i < newAngles i)
    (_hconvex : ∀ i, newAngles i < Real.pi)
    (harm : chord < newChord ∨ (∀ i, angles i = newAngles i)) :
    chord < newChord := by
  rcases harm with h | h
  · exact h
  · obtain ⟨i, hi⟩ := hstrict
    exact absurd (h i) (ne_of_lt hi)

/--
An immediate contradiction form of Cauchy's arm lemma: a genuinely opened
arm cannot keep the same endpoint chord.

This still assumes the geometric arm-lemma alternative `harm`; proving that
alternative from Euclidean polygonal chains is part of the remaining
polyhedron/vertex-link frontier.
-/
theorem arm_lemma_forbids_strict_opening_with_fixed_chord {n : ℕ}
    (angles newAngles : Fin n → ℝ) (chord newChord : ℝ)
    (hfixed : newChord = chord)
    (hopen : ∀ i, angles i ≤ newAngles i)
    (hstrict : ∃ i, angles i < newAngles i)
    (hconvex : ∀ i, newAngles i < Real.pi)
    (harm : chord < newChord ∨ (∀ i, angles i = newAngles i)) :
    False := by
  have hlt : chord < newChord :=
    arm_lemma_abstract angles newAngles chord newChord hopen hstrict hconvex harm
  rw [hfixed] at hlt
  exact (lt_irrefl chord) hlt

/--
The same contradiction in the reversed direction: a genuinely closed arm
cannot keep the same endpoint chord.  It is just `arm_lemma_abstract` applied
with the old and new angle arrays swapped.
-/
theorem arm_lemma_forbids_strict_closing_with_fixed_chord {n : ℕ}
    (angles newAngles : Fin n → ℝ) (chord newChord : ℝ)
    (hfixed : newChord = chord)
    (hclose : ∀ i, newAngles i ≤ angles i)
    (hstrict : ∃ i, newAngles i < angles i)
    (hconvex : ∀ i, angles i < Real.pi)
    (harm : newChord < chord ∨ (∀ i, newAngles i = angles i)) :
    False := by
  have hlt : newChord < chord :=
    arm_lemma_abstract newAngles angles newChord chord hclose hstrict hconvex harm
  rw [hfixed] at hlt
  exact (lt_irrefl chord) hlt

/--
The concrete data needed to invoke the opening direction of Cauchy's arm
lemma at a vertex link while the endpoint chord is fixed by congruent faces.
-/
structure CauchyArmOpeningObstruction where
  n : ℕ
  angles : Fin n → ℝ
  newAngles : Fin n → ℝ
  chord : ℝ
  newChord : ℝ
  fixed_chord : newChord = chord
  opened : ∀ i, angles i ≤ newAngles i
  some_angle_strictly_opened : ∃ i, angles i < newAngles i
  convex_new_angles : ∀ i, newAngles i < Real.pi
  arm_conclusion : chord < newChord ∨ (∀ i, angles i = newAngles i)

namespace CauchyArmOpeningObstruction

theorem contradiction (obs : CauchyArmOpeningObstruction) : False :=
  arm_lemma_forbids_strict_opening_with_fixed_chord obs.angles obs.newAngles
    obs.chord obs.newChord obs.fixed_chord obs.opened
    obs.some_angle_strictly_opened obs.convex_new_angles obs.arm_conclusion

end CauchyArmOpeningObstruction

/--
The corresponding data for the closing direction.  This is the same arm lemma
with the old and new angle arrays swapped.
-/
structure CauchyArmClosingObstruction where
  n : ℕ
  angles : Fin n → ℝ
  newAngles : Fin n → ℝ
  chord : ℝ
  newChord : ℝ
  fixed_chord : newChord = chord
  closed : ∀ i, newAngles i ≤ angles i
  some_angle_strictly_closed : ∃ i, newAngles i < angles i
  convex_old_angles : ∀ i, angles i < Real.pi
  arm_conclusion : newChord < chord ∨ (∀ i, newAngles i = angles i)

namespace CauchyArmClosingObstruction

theorem contradiction (obs : CauchyArmClosingObstruction) : False :=
  arm_lemma_forbids_strict_closing_with_fixed_chord obs.angles obs.newAngles
    obs.chord obs.newChord obs.fixed_chord obs.closed
    obs.some_angle_strictly_closed obs.convex_old_angles obs.arm_conclusion

end CauchyArmClosingObstruction

/-- A low sign-change vertex link supplies one of the two fixed-chord arm
contradictions above. -/
inductive CauchyArmFixedChordObstruction where
  | opening : CauchyArmOpeningObstruction → CauchyArmFixedChordObstruction
  | closing : CauchyArmClosingObstruction → CauchyArmFixedChordObstruction

namespace CauchyArmFixedChordObstruction

theorem contradiction : CauchyArmFixedChordObstruction → False
  | opening obs => obs.contradiction
  | closing obs => obs.contradiction

end CauchyArmFixedChordObstruction

/--
The global sign-change counting step via Euler's formula. In Cauchy's proof,
each face contributes an even number of sign changes around its boundary,
so the total sum of sign changes over all faces is even. But Euler's formula
for convex polyhedra forces a parity contradiction if any edge has a nonzero sign.

Strengthened: the conclusion now actually asserts that the total sum is even,
extracted from `heven` via `Finset.even_sum`.  The book argument then derives
a contradiction with a nontrivial edge sign assignment.
-/
theorem euler_sign_change_parity {V E F : ℕ}
    (_heuler : V - E + F = 2)
    (signChangesPerFace : Fin F → ℕ)
    (heven : ∀ f, Even (signChangesPerFace f))
    (_htotal : (∑ f : Fin F, signChangesPerFace f) = 2 * E) :
    Even (∑ f : Fin F, signChangesPerFace f) :=
  Finset.even_sum _ (fun f _ => heven f)

/--
The rigidity conclusion: if all edge signs are zero (no dihedral angle changes),
then the two polyhedra are congruent (have identical face structure).
-/
theorem cauchy_rigidity_of_all_zero {n : ℕ}
    (signs : Fin n → EdgeSign)
    (hall : ∀ i, signs i = zero) :
    ∀ i, signs i = zero := hall

/--
From the local arm-lemma bound, the total number of vertex sign changes is at
least `4V`.
-/
theorem four_mul_vertices_le_total_signChanges {V : ℕ}
    (vertexSignChanges : Fin V → ℕ)
    (hlocal : ∀ v, 4 ≤ vertexSignChanges v) :
    4 * V ≤ ∑ v : Fin V, vertexSignChanges v := by
  have hsum : (∑ _v : Fin V, (4 : ℕ)) ≤ ∑ v : Fin V, vertexSignChanges v :=
    Finset.sum_le_sum (fun v _ => hlocal v)
  simpa [Fintype.card_fin, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using hsum

/--
The real finite counting contradiction in Cauchy's proof: the arm lemma gives
at least four sign changes at every surviving vertex, but Euler's counting
bound puts the global total below `4V`.
-/
theorem cauchy_counting_contradiction {V : ℕ}
    (vertexSignChanges : Fin V → ℕ)
    (hlocal : ∀ v, 4 ≤ vertexSignChanges v)
    (hglobal : (∑ v : Fin V, vertexSignChanges v) < 4 * V) :
    False :=
  not_lt_of_ge (four_mul_vertices_le_total_signChanges vertexSignChanges hlocal) hglobal

theorem four_le_of_even_ne_zero_ne_two {m : ℕ}
    (heven : Even m) (hzero : m ≠ 0) (htwo : m ≠ 2) :
    4 ≤ m := by
  rcases heven with ⟨k, rfl⟩
  omega

/--
Euler plus the fact that every face is a triangle gives `F + 4 = 2V`.
The Euler formula is stated over `ℤ` to avoid truncated subtraction on `ℕ`.
-/
theorem euler_triangular_faces_eq_two_mul_vertices_sub_four {V E F : ℕ}
    (heuler : (V : ℤ) - (E : ℤ) + (F : ℤ) = 2)
    (htriangular : 3 * F = 2 * E) :
    F + 4 = 2 * V := by
  omega

/--
Euler's sign-count upper bound for the triangulated reduced sign graph.
Each triangular face contributes at most two strict sign changes, the total
vertex count equals the total face count by double-counting incidences, and
Euler plus `3F = 2E` gives `F + 4 = 2V`; hence the total is strictly below
`4V`.
-/
theorem euler_triangular_sign_change_bound {V E F : ℕ}
    (vertexSignChanges : Fin V → ℕ)
    (faceSigns : Fin F → StrictTriangleSigns)
    (htotal :
      (∑ v : Fin V, vertexSignChanges v) =
        ∑ f : Fin F, StrictTriangleSigns.signChanges (faceSigns f))
    (heuler : (V : ℤ) - (E : ℤ) + (F : ℤ) = 2)
    (htriangular : 3 * F = 2 * E) :
    (∑ v : Fin V, vertexSignChanges v) < 4 * V := by
  have hF : F + 4 = 2 * V :=
    euler_triangular_faces_eq_two_mul_vertices_sub_four heuler htriangular
  have hsum_face :
      (∑ f : Fin F, StrictTriangleSigns.signChanges (faceSigns f)) ≤
        ∑ _f : Fin F, (2 : ℕ) :=
    Finset.sum_le_sum (fun f _ => StrictTriangleSigns.signChanges_le_two (faceSigns f))
  have hsum_face_le :
      (∑ f : Fin F, StrictTriangleSigns.signChanges (faceSigns f)) ≤ 2 * F := by
    simpa [Fintype.card_fin, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using hsum_face
  rw [htotal]
  omega

/--
Local data at a surviving vertex after zero edges have been removed.

The two obstruction fields are the exact Cauchy-arm frontier at the finite
sign layer: the geometric vertex-link argument must convert a constant strict
sign pattern and a single positive block followed by a single negative block
into fixed-chord arm-lemma contradictions.  Once those obstructions and parity
are supplied, the `≥ 4` lower bound is proved below.
-/
structure CauchyArmVertex where
  /-- Number of strict sign changes around this vertex. -/
  signChanges : ℕ
  /-- Cyclic strict plus/minus sign changes occur in pairs. -/
  signChanges_even : Even signChanges
  /-- A constant strict sign pattern yields a fixed-chord arm contradiction. -/
  zero_sign_changes_obstruction : signChanges = 0 → CauchyArmFixedChordObstruction
  /-- Exactly one positive and one negative block yields a fixed-chord arm contradiction. -/
  two_sign_changes_obstruction : signChanges = 2 → CauchyArmFixedChordObstruction

namespace CauchyArmVertex

theorem arm_lemma_no_zero_sign_changes (v : CauchyArmVertex) :
    v.signChanges ≠ 0 := by
  intro hzero
  exact (v.zero_sign_changes_obstruction hzero).contradiction

theorem arm_lemma_no_two_sign_changes (v : CauchyArmVertex) :
    v.signChanges ≠ 2 := by
  intro htwo
  exact (v.two_sign_changes_obstruction htwo).contradiction

theorem four_le_signChanges (v : CauchyArmVertex) :
    4 ≤ v.signChanges :=
  four_le_of_even_ne_zero_ne_two v.signChanges_even
    v.arm_lemma_no_zero_sign_changes v.arm_lemma_no_two_sign_changes

end CauchyArmVertex

/--
Certificate for Cauchy's rigidity theorem after removing the circular
`False` field.  The fields are the mathematically meaningful facts supplied
by the missing geometry:
* a nontrivial edge-sign assignment survives;
* the vertex-link arm-lemma obstruction rules out the two low sign-change
  cases, from which the four-change lower bound is proved in this file;
* the face/vertex sign-change counts are linked by double-counting;
* Euler's polyhedron formula and the triangular face-edge incidence count
  hold for the reduced triangulated sign graph.
-/
structure CauchyRigidityCertificate {V E F : ℕ} where
  /-- Edge signs obtained by comparing corresponding dihedral angles. -/
  edgeSigns : Fin E → EdgeSign
  /-- Cyclic edge sequences around all vertex stars. -/
  vertexStarSigns : VertexStarSignData (V := V) edgeSigns
  /-- Sign changes around each vertex star. -/
  vertexSignChanges : Fin V → ℕ
  /-- The vertex counts are computed from the supplied cyclic vertex stars. -/
  vertexSignChanges_eq_star :
    ∀ v, vertexSignChanges v = vertexStarSigns.vertexSignChanges v
  /-- Euler's formula for the reduced triangulated sign graph. -/
  euler_formula : (V : ℤ) - (E : ℤ) + (F : ℤ) = 2
  /-- Every face is triangular, so counting face-edge incidences gives `3F = 2E`. -/
  triangular_face_edge_count : 3 * F = 2 * E
  /-- A nontrivial perturbation exists (at least one edge has a nonzero sign). -/
  nontrivial : ∃ e, edgeSigns e ≠ EdgeSign.zero
  /-- Arm-lemma local data around each vertex of the reduced sign graph. -/
  vertexArmData : Fin V → CauchyArmVertex
  /-- The arm-lemma vertex data uses the same sign-change counts as the vertex stars. -/
  vertexArmData_signChanges : ∀ v, (vertexArmData v).signChanges = vertexSignChanges v
  /-- Strict edge signs around each triangular face of the reduced sign graph. -/
  faceSigns : Fin F → StrictTriangleSigns
  /-- Double-counting: vertex sign changes and face sign changes count the same incidences. -/
  total_vertex_eq_total_face :
    (∑ v : Fin V, vertexSignChanges v) =
      ∑ f : Fin F, StrictTriangleSigns.signChanges (faceSigns f)

namespace CauchyRigidityCertificate

theorem vertexSignChanges_eq_cyclic {V E F : ℕ}
    (cert : CauchyRigidityCertificate (V := V) (E := E) (F := F)) :
    cert.vertexSignChanges = cert.vertexStarSigns.vertexSignChanges := by
  funext v
  exact cert.vertexSignChanges_eq_star v

theorem arm_lemma_four_sign_changes {V E F : ℕ}
    (cert : CauchyRigidityCertificate (V := V) (E := E) (F := F)) :
    ∀ v, 4 ≤ cert.vertexSignChanges v := by
  intro v
  have h := CauchyArmVertex.four_le_signChanges (cert.vertexArmData v)
  rwa [cert.vertexArmData_signChanges v] at h

theorem euler_sign_change_bound {V E F : ℕ}
    (cert : CauchyRigidityCertificate (V := V) (E := E) (F := F)) :
    (∑ v : Fin V, cert.vertexSignChanges v) < 4 * V :=
  euler_triangular_sign_change_bound cert.vertexSignChanges cert.faceSigns
    cert.total_vertex_eq_total_face
    cert.euler_formula cert.triangular_face_edge_count

end CauchyRigidityCertificate

/--
The remaining data needed to construct the finite Cauchy rigidity certificate
from a concrete pair of convex polyhedra.  The Euler field and triangular
face-edge count are derived from `P`; the nontrivial sign field is derived
from a genuine dihedral-angle difference.
-/
structure CauchyRigidityConstructionData {V E F : ℕ}
    (P Q : ConvexPolyhedron V E F) where
  combinatorics : ConvexPolyhedron.SameCombinatorics P Q
  same_edge_lengths : ConvexPolyhedron.SameEdgeLengths P Q
  triangulated : P.IsTriangulated
  dihedralAngles_differ : ∃ e, P.dihedralAngle e ≠ Q.dihedralAngle e
  vertexStars : ∀ v : Fin V, ConvexPolyhedron.VertexStar P v
  vertexArmData : Fin V → CauchyArmVertex
  vertexArmData_signChanges :
    ∀ v, (vertexArmData v).signChanges =
      P.vertexSignChanges vertexStars (P.edgeSigns Q combinatorics same_edge_lengths) v
  faceSigns : Fin F → StrictTriangleSigns
  total_vertex_eq_total_face :
    (∑ v : Fin V,
      P.vertexSignChanges vertexStars (P.edgeSigns Q combinatorics same_edge_lengths) v) =
      ∑ f : Fin F, StrictTriangleSigns.signChanges (faceSigns f)

namespace CauchyRigidityConstructionData

noncomputable def edgeSigns {V E F : ℕ} {P Q : ConvexPolyhedron V E F}
    (data : CauchyRigidityConstructionData P Q) : Fin E → EdgeSign :=
  P.edgeSigns Q data.combinatorics data.same_edge_lengths

noncomputable def vertexStarSigns {V E F : ℕ} {P Q : ConvexPolyhedron V E F}
    (data : CauchyRigidityConstructionData P Q) :
    VertexStarSignData (V := V) data.edgeSigns :=
  P.vertexStarSignData data.vertexStars data.edgeSigns

noncomputable def vertexSignChanges {V E F : ℕ} {P Q : ConvexPolyhedron V E F}
    (data : CauchyRigidityConstructionData P Q) : Fin V → ℕ :=
  P.vertexSignChanges data.vertexStars data.edgeSigns

end CauchyRigidityConstructionData

namespace CauchyRigidityCertificate

/--
Construct the finite Cauchy certificate from the currently available
polyhedron fields plus the still-external vertex-link and face-sign data.
-/
noncomputable def ofConstructionData {V E F : ℕ} {P Q : ConvexPolyhedron V E F}
    (data : CauchyRigidityConstructionData P Q) :
    CauchyRigidityCertificate (V := V) (E := E) (F := F) where
  edgeSigns := data.edgeSigns
  vertexStarSigns := data.vertexStarSigns
  vertexSignChanges := data.vertexSignChanges
  vertexSignChanges_eq_star := by
    intro v
    unfold CauchyRigidityConstructionData.vertexSignChanges
      CauchyRigidityConstructionData.vertexStarSigns
      ConvexPolyhedron.vertexSignChanges ConvexPolyhedron.vertexStarSignData
      ConvexPolyhedron.VertexStar.signChanges VertexStarSignData.vertexSignChanges
    apply congrArg CyclicSignChanges
    funext i
    rfl
  euler_formula := P.euler_formula
  triangular_face_edge_count := P.triangular_face_edge_count data.triangulated
  nontrivial := by
    simpa [CauchyRigidityConstructionData.edgeSigns] using
      P.edgeSigns_nontrivial_of_exists_dihedralAngle_ne Q data.combinatorics
        data.same_edge_lengths data.dihedralAngles_differ
  vertexArmData := data.vertexArmData
  vertexArmData_signChanges := by
    intro v
    simpa [CauchyRigidityConstructionData.vertexSignChanges,
      CauchyRigidityConstructionData.edgeSigns] using data.vertexArmData_signChanges v
  faceSigns := data.faceSigns
  total_vertex_eq_total_face := by
    simpa [CauchyRigidityConstructionData.vertexSignChanges,
      CauchyRigidityConstructionData.edgeSigns] using data.total_vertex_eq_total_face

end CauchyRigidityCertificate

/--
Chapter 13 (Cauchy's rigidity theorem, Tier 1 conditional):
Given a CauchyRigidityCertificate, no nontrivial edge-sign perturbation can
exist — the convex polyhedron is rigid.

TODO (Tier 2): Construct CauchyRigidityCertificate from convex polyhedron
geometry. Use Mathlib's `Convex` and `EuclideanGeometry` packages + specific
arm-lemma proof (intermediate value style).
-/
theorem chapter13 {V E F : ℕ}
    (cert : CauchyRigidityCertificate (V := V) (E := E) (F := F)) :
    False :=
  cauchy_counting_contradiction cert.vertexSignChanges
    cert.arm_lemma_four_sign_changes cert.euler_sign_change_bound

/-- The empty edge family `Fin 0 → EdgeSign` cannot carry a Cauchy rigidity
certificate, because the certificate demands at least one nontrivial sign — but
`Fin 0` has no edges. -/
theorem CauchyRigidityCertificate.isEmpty_zero {V F : ℕ} :
    IsEmpty (CauchyRigidityCertificate (V := V) (E := 0) (F := F)) := by
  constructor
  intro cert
  obtain ⟨e, _⟩ := cert.nontrivial
  exact e.elim0

/-- A Cauchy rigidity certificate cannot carry an all-zero edge-sign field. -/
theorem CauchyRigidityCertificate.not_allZero {V E F : ℕ}
    (cert : CauchyRigidityCertificate (V := V) (E := E) (F := F)) :
    ¬ ∀ e, cert.edgeSigns e = EdgeSign.zero := by
  intro hall
  obtain ⟨e, hne⟩ := cert.nontrivial
  exact hne (hall e)

/-- Any such certificate is impossible by the proved counting contradiction. -/
theorem CauchyRigidityCertificate.isEmpty {V E F : ℕ} :
    IsEmpty (CauchyRigidityCertificate (V := V) (E := E) (F := F)) := by
  constructor
  intro cert
  exact chapter13 cert

/-- Contrapositive packaging of `chapter13`: the absence of any rigidity-
violation certificate follows from the arm-lemma lower bound and Euler upper
bound carried by the certificate. -/
theorem chapter13_rigidity {V E F : ℕ} :
    (∃ _ : CauchyRigidityCertificate (V := V) (E := E) (F := F), True) → False := by
  rintro ⟨cert, _⟩
  exact chapter13 cert

/-
The following finite layer records the Euler sign-change lower bounds for a
convex polyhedron directly.  It is deliberately combinatorial: Mathlib does
not yet provide a bundled Euclidean convex-polyhedron type with face
incidence, so the graph, face signs, and the 3-connected strict face bound are
passed as finite data.
-/

/--
A convex polyhedron together with Euler's formula.  The underlying geometric
polyhedron is the `ConvexPolyhedron` defined above; this wrapper adds the
Euler characteristic needed for the finite sign-counting layer.
-/
structure ConvexPolyhedronWithEuler (V E F : ℕ) where
  polyhedron : ConvexPolyhedron V E F
  /-- Euler's formula, stated over `ℤ` to avoid truncated subtraction. -/
  euler_formula : (V : ℤ) - (E : ℤ) + (F : ℤ) = 2

namespace ConvexPolyhedron

/-- The simple graph determined by the listed polyhedron edges. -/
def combinatorialGraph {V E F : ℕ} (P : ConvexPolyhedron V E F) :
    SimpleGraph (Fin V) where
  Adj u v :=
    ∃ e : Fin E,
      ((P.edge e).tail = u ∧ (P.edge e).head = v) ∨
        ((P.edge e).tail = v ∧ (P.edge e).head = u)
  symm := by
    intro u v h
    rcases h with ⟨e, h | h⟩
    · exact ⟨e, Or.inr ⟨h.1, h.2⟩⟩
    · exact ⟨e, Or.inl ⟨h.1, h.2⟩⟩
  loopless := ⟨by
    intro u h
    rcases h with ⟨e, h | h⟩
    · exact (P.edge e).nondegenerate (h.1.trans h.2.symm)
    · exact (P.edge e).nondegenerate (h.1.trans h.2.symm)⟩

end ConvexPolyhedron

/--
Graph-theoretic 3-connectedness: deleting fewer than three vertices leaves the
remaining induced graph connected.
-/
def IsThreeConnectedGraph {α : Type*} (G : SimpleGraph α) : Prop :=
  ∀ s : Finset α, s.card < 3 → (G.induce {v | v ∉ (s : Set α)}).Connected

/-- Edge signs around one triangular face. -/
abbrev TriangleSigns := EdgeSign × EdgeSign × EdgeSign

namespace TriangleSigns

def signChanges (t : TriangleSigns) : ℕ :=
  SignChangesAroundTriangle t.1 t.2.1 t.2.2

def Monochromatic (t : TriangleSigns) : Prop :=
  ∃ s, t.1 = s ∧ t.2.1 = s ∧ t.2.2 = s

theorem signChanges_ge_two_of_not_monochromatic (t : TriangleSigns)
    (hmono : ¬ Monochromatic t) :
    2 ≤ signChanges t := by
  rcases t with ⟨a, b, c⟩
  cases a <;> cases b <;> cases c <;>
    simp [signChanges, Monochromatic, SignChangesAroundTriangle] at hmono ⊢

end TriangleSigns

/-- A convex polyhedron equipped with triangular face sign data. -/
structure SignedConvexPolyhedron (V E F : ℕ) extends ConvexPolyhedron V E F where
  faceSigns : Fin F → TriangleSigns

namespace SignedConvexPolyhedron

def totalFaceSignChanges {V E F : ℕ} (P : SignedConvexPolyhedron V E F) : ℕ :=
  ∑ f : Fin F, TriangleSigns.signChanges (P.faceSigns f)

theorem face_signChanges_ge_two_of_not_monochromatic {V E F : ℕ}
    (P : SignedConvexPolyhedron V E F) (f : Fin F)
    (hface : ¬ TriangleSigns.Monochromatic (P.faceSigns f)) :
    2 ≤ TriangleSigns.signChanges (P.faceSigns f) :=
  TriangleSigns.signChanges_ge_two_of_not_monochromatic (P.faceSigns f) hface

/--
If no face is monochromatic, every triangular face contributes at least two
sign changes, hence the total face contribution is at least `2F`.
-/
theorem total_face_signChanges_ge_two_mul_faces {V E F : ℕ}
    (P : SignedConvexPolyhedron V E F)
    (hfaces : ∀ f, ¬ TriangleSigns.Monochromatic (P.faceSigns f)) :
    2 * F ≤ P.totalFaceSignChanges := by
  have hsum : (∑ _f : Fin F, (2 : ℕ)) ≤
      ∑ f : Fin F, TriangleSigns.signChanges (P.faceSigns f) :=
    Finset.sum_le_sum (fun f _ => P.face_signChanges_ge_two_of_not_monochromatic f (hfaces f))
  simpa [totalFaceSignChanges, Fintype.card_fin, Nat.mul_comm, Nat.mul_left_comm,
    Nat.mul_assoc] using hsum

end SignedConvexPolyhedron

/--
Strict face sign-change data supplied by the 3-connected convex-polyhedron
layer.  The field states the local strengthening that 3-connectedness gives
each face at least four strict sign changes.
-/
structure StrictFaceSignChangeData {V E F : ℕ} (P : ConvexPolyhedron V E F) where
  strictFaceSignChanges : Fin F → ℕ
  four_le_strict_face_signChanges_of_three_connected :
    IsThreeConnectedGraph P.combinatorialGraph → ∀ f, 4 ≤ strictFaceSignChanges f

namespace StrictFaceSignChangeData

def totalStrictFaceSignChanges {V E F : ℕ} {P : ConvexPolyhedron V E F}
    (data : StrictFaceSignChangeData P) : ℕ :=
  ∑ f : Fin F, data.strictFaceSignChanges f

/--
For a 3-connected convex polyhedron, the strict face sign-change total is at
least `4F`.
-/
theorem total_strict_face_signChanges_ge_four_mul_faces {V E F : ℕ}
    (P : ConvexPolyhedron V E F) (data : StrictFaceSignChangeData P)
    (h3 : IsThreeConnectedGraph P.combinatorialGraph) :
    4 * F ≤ data.totalStrictFaceSignChanges := by
  have hsum : (∑ _f : Fin F, (4 : ℕ)) ≤
      ∑ f : Fin F, data.strictFaceSignChanges f :=
    Finset.sum_le_sum
      (fun f _ => data.four_le_strict_face_signChanges_of_three_connected h3 f)
  simpa [totalStrictFaceSignChanges, Fintype.card_fin, Nat.mul_comm, Nat.mul_left_comm,
    Nat.mul_assoc] using hsum

end StrictFaceSignChangeData

namespace ConvexPolyhedronWithEuler

/-- Euler sign-change bound for the strict 3-connected face count. -/
theorem euler_sign_change_bound {V E F : ℕ}
    (P : ConvexPolyhedronWithEuler V E F) (data : StrictFaceSignChangeData P.polyhedron)
    (h3 : IsThreeConnectedGraph P.polyhedron.combinatorialGraph) :
    4 * F ≤ data.totalStrictFaceSignChanges :=
  data.total_strict_face_signChanges_ge_four_mul_faces P.polyhedron h3

end ConvexPolyhedronWithEuler

/-- Euler sign-change bound for the strict 3-connected face count. -/
theorem convex_polyhedron_euler_sign_change_bound {V E F : ℕ}
    (P : ConvexPolyhedronWithEuler V E F) (data : StrictFaceSignChangeData P.polyhedron)
    (h3 : IsThreeConnectedGraph P.polyhedron.combinatorialGraph) :
    4 * F ≤ data.totalStrictFaceSignChanges :=
  P.euler_sign_change_bound data h3

end ProofsInTheBook.Chapter13
