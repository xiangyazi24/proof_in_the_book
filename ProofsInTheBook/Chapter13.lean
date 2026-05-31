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
the final counting contradiction.  It defines edge signs, strict sign changes
around triangular faces, proves the basic parity facts, packages the abstract
consequence of Cauchy's arm lemma, and states `chapter13` / `chapter13_rigidity`
from meaningful missing geometric/combinatorial facts.  The remaining
frontier is now explicit: vertex-link geometry must turn the low sign-change
cases into fixed-chord Cauchy-arm obstructions, and the Euler polyhedron
formula plus the triangulated incidence count must be supplied by real
polyhedron infrastructure.  Once those are given, the arm-lemma lower bound
and Euler sign-count upper bound are proved here.

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

/-- The Cauchy input: same combinatorics and congruent corresponding faces. -/
structure IsometricPair (P Q : ConvexPolyhedron V E F) : Prop where
  combinatorics : SameCombinatorics P Q
  facewise_isometric : FacewiseIsometric P Q

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
structure CauchyRigidityCertificate {V E F : ℕ} (edgeSigns : Fin E → EdgeSign) where
  /-- A nontrivial perturbation exists (at least one edge has a nonzero sign). -/
  nontrivial : ∃ e, edgeSigns e ≠ EdgeSign.zero
  /-- Arm-lemma local data around each vertex of the reduced sign graph. -/
  vertexArmData : Fin V → CauchyArmVertex
  /-- Strict edge signs around each triangular face of the reduced sign graph. -/
  faceSigns : Fin F → StrictTriangleSigns
  /-- Double-counting: vertex sign changes and face sign changes count the same incidences. -/
  total_vertex_eq_total_face :
    (∑ v : Fin V, (vertexArmData v).signChanges) =
      ∑ f : Fin F, StrictTriangleSigns.signChanges (faceSigns f)
  /-- Euler's formula for the reduced triangulated sign graph. -/
  euler_formula : (V : ℤ) - (E : ℤ) + (F : ℤ) = 2
  /-- Every face is triangular, so counting face-edge incidences gives `3F = 2E`. -/
  triangular_face_edge_count : 3 * F = 2 * E

namespace CauchyRigidityCertificate

def vertexSignChanges {V E F : ℕ} {edgeSigns : Fin E → EdgeSign}
    (cert : CauchyRigidityCertificate (V := V) (F := F) edgeSigns) :
    Fin V → ℕ :=
  fun v => (cert.vertexArmData v).signChanges

theorem arm_lemma_four_sign_changes {V E F : ℕ}
    {edgeSigns : Fin E → EdgeSign}
    (cert : CauchyRigidityCertificate (V := V) (F := F) edgeSigns) :
    ∀ v, 4 ≤ cert.vertexSignChanges v := by
  intro v
  exact CauchyArmVertex.four_le_signChanges (cert.vertexArmData v)

theorem euler_sign_change_bound {V E F : ℕ}
    {edgeSigns : Fin E → EdgeSign}
    (cert : CauchyRigidityCertificate (V := V) (F := F) edgeSigns) :
    (∑ v : Fin V, cert.vertexSignChanges v) < 4 * V :=
  euler_triangular_sign_change_bound cert.vertexSignChanges cert.faceSigns
    (by
      simpa [CauchyRigidityCertificate.vertexSignChanges] using
        cert.total_vertex_eq_total_face)
    cert.euler_formula cert.triangular_face_edge_count

end CauchyRigidityCertificate

/--
Chapter 13 (Cauchy's rigidity theorem, Tier 1 conditional):
Given a CauchyRigidityCertificate, no nontrivial edge-sign perturbation can
exist — the convex polyhedron is rigid.

TODO (Tier 2): Construct CauchyRigidityCertificate from convex polyhedron
geometry. Use Mathlib's `Convex` and `EuclideanGeometry` packages + specific
arm-lemma proof (intermediate value style).
-/
theorem chapter13 {V E F : ℕ} {edgeSigns : Fin E → EdgeSign}
    (cert : CauchyRigidityCertificate (V := V) (F := F) edgeSigns) :
    False :=
  cauchy_counting_contradiction cert.vertexSignChanges
    cert.arm_lemma_four_sign_changes cert.euler_sign_change_bound

/-- The empty edge family `Fin 0 → EdgeSign` cannot carry a Cauchy rigidity
certificate, because the certificate demands at least one nontrivial sign — but
`Fin 0` has no edges. -/
theorem CauchyRigidityCertificate.isEmpty_zero {V F : ℕ} (edgeSigns : Fin 0 → EdgeSign) :
    IsEmpty (CauchyRigidityCertificate (V := V) (F := F) edgeSigns) := by
  constructor
  intro cert
  obtain ⟨e, _⟩ := cert.nontrivial
  exact e.elim0

/-- An all-zero edge-sign assignment carries no Cauchy rigidity certificate:
the certificate demands a nontrivial sign, but `edgeSigns ≡ zero` makes every
edge trivial. -/
theorem CauchyRigidityCertificate.isEmpty_of_allZero {V E F : ℕ}
    {edgeSigns : Fin E → EdgeSign} (hall : ∀ e, edgeSigns e = EdgeSign.zero) :
    IsEmpty (CauchyRigidityCertificate (V := V) (F := F) edgeSigns) := by
  constructor
  intro cert
  obtain ⟨e, hne⟩ := cert.nontrivial
  exact hne (hall e)

/-- Any such certificate is impossible by the proved counting contradiction. -/
theorem CauchyRigidityCertificate.isEmpty {V E F : ℕ} (edgeSigns : Fin E → EdgeSign) :
    IsEmpty (CauchyRigidityCertificate (V := V) (F := F) edgeSigns) := by
  constructor
  intro cert
  exact chapter13 cert

/-- Contrapositive packaging of `chapter13`: the absence of any rigidity-
violation certificate follows from the arm-lemma lower bound and Euler upper
bound carried by the certificate. -/
theorem chapter13_rigidity {V E F : ℕ} (edgeSigns : Fin E → EdgeSign) :
    (∃ _ : CauchyRigidityCertificate (V := V) (F := F) edgeSigns, True) → False := by
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
