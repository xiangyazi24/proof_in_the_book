import ProofsInTheBook.PlanarMapFilteredRotation

/-!
# Chord-split data layer

This file is the *data* layer for the Chapter 35 chord split.  Given a
near-triangulation `M` with distinguished outer cycle `C = hNT.outerCycle` and a
boundary chord `e = uv` (a graph edge between two boundary-cycle vertices that is
not itself a boundary edge), it packages the combinatorial ingredients that the
two side maps (file 6, `PlanarMapChordSplit.lean`) consume:

* the chord's two darts and the two distinct **non-outer (triangular) faces** they
  lie in (`chord_incident_faces_distinct`);
* the **side face-sets**, defined as the reachability closures of the
  non-outer-face adjacency relation
  ("share an edge that is neither a boundary edge nor the chord"), seeded by the
  two chord-incident faces (`Side`, `Side1`, `Side2`);
* the two boundary arcs from `BoundaryCycle.two_arcs`, each with an internal
  vertex (the strict-decrease bookkeeping);
* the partition fact `chordSplit_side_darts_partition`.

## The honest status of disjointness / coverage

That the two side face-components are *disjoint* (equivalently: the two seeds are
not reachable from one another) is the genuine planarity input behind the chord
split.  It is exactly the statement that a closed curve formed by the chord and a
boundary arc separates the inner faces; combinatorially it is equivalent to the
side face classification + Euler count `F₁ + F₂ = F + 1` that the side-map file
(file 6) establishes once the side `CombMap`s exist.  It is *not* derivable at
this pre-construction data layer.

Per the design review (`HANDOFF/outbox/c35review-reply.md`, section "Chord split:
break points and corrected invariant"), it is therefore isolated as the single
named predicate `SidesDisjoint`, and everything that depends on it
(`chordSplit_side_darts_partition`, the disjointness of the two side face-dart
sets) is proved *conditionally* on it.  Everything else
(face-incidence distinctness, non-outerness of both sides, closure under
adjacency, seed membership, the seam darts landing in their own sides, and both
arcs being internally nonempty) is proved **unconditionally**.
-/

namespace ProofsInTheBook.PlanarMap

open Equiv

namespace CombMap

variable {D : Type*} [Fintype D] [DecidableEq D]

namespace NearTriangulation

variable {M : CombMap D} (hNT : NearTriangulation M)

/-! ## 1. The chord darts and their incident faces -/

section ChordDarts

variable {u v : M.Vertex} (h : hNT.outerCycle.Chord u v)

/-- A dart realizing the chord edge `s(u, v)` in the ambient map. -/
noncomputable def chordDart : D :=
  (h.adj.2).choose

/-- The chosen chord dart has unoriented endpoints `s(u, v)`. -/
lemma chordDart_edge : M.dartEdge (hNT.chordDart h) = s(u, v) :=
  (h.adj.2).choose_spec

/-- The chord's `α`-image dart has the same unoriented endpoints. -/
lemma chordDart_alpha_edge : M.dartEdge (M.α (hNT.chordDart h)) = s(u, v) := by
  rw [M.dartEdge_alpha, hNT.chordDart_edge h]

/-- The chord dart does **not** lie in the outer face: otherwise its edge would be
a boundary edge, contradicting the chord hypothesis. -/
lemma chordDart_not_outer :
    M.dartFace (hNT.chordDart h) ≠ hNT.outerFace := by
  intro hface
  apply h.not_boundary_edge
  have hmem : hNT.chordDart h ∈ hNT.outerCycle.darts :=
    (hNT.outerCycle.mem_darts_iff _).2 hface
  show s(u, v) ∈ hNT.outerCycle.edges
  rw [← hNT.chordDart_edge h, hNT.outerCycle.edges_eq]
  exact List.mem_map_of_mem hmem

/-- The chord's `α`-image dart does **not** lie in the outer face either. -/
lemma chordDart_alpha_not_outer :
    M.dartFace (M.α (hNT.chordDart h)) ≠ hNT.outerFace := by
  intro hface
  apply h.not_boundary_edge
  have hmem : M.α (hNT.chordDart h) ∈ hNT.outerCycle.darts :=
    (hNT.outerCycle.mem_darts_iff _).2 hface
  show s(u, v) ∈ hNT.outerCycle.edges
  rw [← hNT.chordDart_alpha_edge h, hNT.outerCycle.edges_eq]
  exact List.mem_map_of_mem hmem

/-- **Chord incident faces are distinct.**  The two darts of a boundary chord lie
in two *distinct* faces.  (Combined with `chordDart_not_outer` /
`chordDart_alpha_not_outer`, both faces are non-outer, hence triangular.)

Proof: by `edge_faces_distinct_or_boundary_edge`, either the two incident faces
are distinct or the edge is a boundary edge; the latter is excluded because the
chord is not a boundary edge. -/
lemma chord_incident_faces_distinct :
    M.dartFace (hNT.chordDart h) ≠ M.dartFace (M.α (hNT.chordDart h)) := by
  rcases hNT.edge_faces_distinct_or_boundary_edge (hNT.chordDart h) with hne | hbe
  · exact hne
  · exfalso
    apply h.not_boundary_edge
    rwa [hNT.chordDart_edge h] at hbe

/-- Both chord-incident faces are triangular. -/
lemma chord_incident_face_isFaceTriangle :
    M.IsFaceTriangle (hNT.chordDart h)
        (M.φ (hNT.chordDart h)) (M.φ (M.φ (hNT.chordDart h))) :=
  hNT.inner_face_isFaceTriangle (hNT.chordDart_not_outer h)

end ChordDarts

/-! ## 2. The non-outer-face adjacency relation -/

/-- Two faces are **chord-split adjacent** (relative to the chord `s(u, v)`) when
they share an edge that is neither a boundary edge nor the chord itself.  This is
the dual adjacency restricted to non-boundary, non-chord edges; reachability
across it never touches the outer face. -/
def ChordSplitAdj (u v : M.Vertex) (f g : M.Face) : Prop :=
  ∃ d : D,
    M.dartFace d = f ∧ M.dartFace (M.α d) = g ∧
      ¬ hNT.outerCycle.IsBoundaryEdge (M.dartEdge d) ∧
      M.dartEdge d ≠ s(u, v)

/-- The adjacency relation is symmetric. -/
lemma chordSplitAdj_symm {u v : M.Vertex} {f g : M.Face}
    (hfg : hNT.ChordSplitAdj u v f g) : hNT.ChordSplitAdj u v g f := by
  obtain ⟨d, hdf, hdg, hbe, hch⟩ := hfg
  refine ⟨M.α d, ?_, ?_, ?_, ?_⟩
  · exact hdg
  · rw [M.alpha_alpha]; exact hdf
  · rwa [M.dartEdge_alpha]
  · rwa [M.dartEdge_alpha]

/-- Across a chord-split adjacency, the second face is non-outer: if it were the
outer face, the shared edge would be a boundary edge. -/
lemma chordSplitAdj_target_not_outer {u v : M.Vertex} {f g : M.Face}
    (hfg : hNT.ChordSplitAdj u v f g) : g ≠ hNT.outerFace := by
  obtain ⟨d, _, hdg, hbe, _⟩ := hfg
  intro hg
  apply hbe
  have hmem : M.α d ∈ hNT.outerCycle.darts :=
    (hNT.outerCycle.mem_darts_iff _).2 (hdg.trans hg)
  show M.dartEdge d ∈ hNT.outerCycle.edges
  rw [← M.dartEdge_alpha d, hNT.outerCycle.edges_eq]
  exact List.mem_map_of_mem hmem

/-! ## 3. The two sides as reachability closures -/

/-- A **side** is the set of faces reachable from a seed face through the
chord-split adjacency relation (the reflexive–transitive closure). -/
def Side (u v : M.Vertex) (seed : M.Face) : Set M.Face :=
  {g | Relation.ReflTransGen (hNT.ChordSplitAdj u v) seed g}

/-- The seed face belongs to its own side. -/
lemma seed_mem_side {u v : M.Vertex} (seed : M.Face) :
    seed ∈ hNT.Side u v seed :=
  Relation.ReflTransGen.refl

/-- A side is closed under chord-split adjacency. -/
lemma side_closed {u v : M.Vertex} {seed f g : M.Face}
    (hf : f ∈ hNT.Side u v seed) (hfg : hNT.ChordSplitAdj u v f g) :
    g ∈ hNT.Side u v seed :=
  Relation.ReflTransGen.tail hf hfg

/-- Every face reached from a non-outer seed is non-outer.  (Non-outerness of any
face reached by at least one step is automatic from
`chordSplitAdj_target_not_outer`; combined with the seed being non-outer this
covers the whole side.) -/
lemma side_subset_nonouter {u v : M.Vertex} {seed : M.Face}
    (hseed : seed ≠ hNT.outerFace) {g : M.Face} (hg : g ∈ hNT.Side u v seed) :
    g ≠ hNT.outerFace := by
  induction hg with
  | refl => exact hseed
  | tail _ hstep _ => exact hNT.chordSplitAdj_target_not_outer hstep

/-! ## 4. The chord-split data structure -/

/-- The set of darts whose face lies in a side. -/
def sideFaceDarts (u v : M.Vertex) (seed : M.Face) : Set D :=
  {d | M.dartFace d ∈ hNT.Side u v seed}

/-- The named planarity keystone, deferred to the side-map file (file 6).

`SidesDisjoint h` says the two side face-components are disjoint, i.e. neither
chord-incident face is reachable from the other through the non-outer adjacency.
This is the Jordan/Euler separation input (combinatorially: the chord together
with a boundary arc separates the inner faces, equivalently `F₁ + F₂ = F + 1`
once the side maps exist).  It is not derivable at this pre-construction layer;
the side-map file establishes it from the side face classification.  All
disjointness-dependent conclusions here are stated conditionally on it. -/
def SidesDisjoint {u v : M.Vertex} (h : hNT.outerCycle.Chord u v) : Prop :=
  Disjoint
    (hNT.Side u v (M.dartFace (hNT.chordDart h)))
    (hNT.Side u v (M.dartFace (M.α (hNT.chordDart h))))

/-- All chord-split data for a near-triangulation `M` and a boundary chord `uv`.

This bundles the proven (unconditional) facts.  The single deferred planarity
input is carried as the field `sides_disjoint : hNT.SidesDisjoint h`, supplied by
the caller (file 6) once the side maps make it available; the partition lemma
below consumes it. -/
structure ChordSplitData (u v : M.Vertex) where
  /-- The chord. -/
  chord : hNT.outerCycle.Chord u v
  /-- The two boundary arcs determined by the chord endpoints. -/
  arc : BoundaryArcSplit M hNT.outerCycle.vertices hNT.outerCycle.edges u v
  /-- The first arc has an internal (strictly-between) boundary vertex. -/
  arc₁_internal : arc.path₁.HasInternalVertex
  /-- The second arc has an internal (strictly-between) boundary vertex. -/
  arc₂_internal : arc.path₂.HasInternalVertex

namespace ChordSplitData

variable {hNT} {u v : M.Vertex}

/-- The chord dart for the data bundle. -/
noncomputable def dart (data : hNT.ChordSplitData u v) : D :=
  hNT.chordDart data.chord

/-- The first chord-incident (non-outer, triangular) face. -/
noncomputable def face₁ (data : hNT.ChordSplitData u v) : M.Face :=
  M.dartFace data.dart

/-- The second chord-incident (non-outer, triangular) face. -/
noncomputable def face₂ (data : hNT.ChordSplitData u v) : M.Face :=
  M.dartFace (M.α data.dart)

/-- The face-set of the first side (reachability closure from `face₁`). -/
def side₁ (data : hNT.ChordSplitData u v) : Set M.Face :=
  hNT.Side u v data.face₁

/-- The face-set of the second side (reachability closure from `face₂`). -/
def side₂ (data : hNT.ChordSplitData u v) : Set M.Face :=
  hNT.Side u v data.face₂

/-- The dart-set of the first side. -/
def sideDarts₁ (data : hNT.ChordSplitData u v) : Set D :=
  hNT.sideFaceDarts u v data.face₁

/-- The dart-set of the second side. -/
def sideDarts₂ (data : hNT.ChordSplitData u v) : Set D :=
  hNT.sideFaceDarts u v data.face₂

/-- The two chord-incident faces are distinct. -/
lemma face_distinct (data : hNT.ChordSplitData u v) : data.face₁ ≠ data.face₂ :=
  hNT.chord_incident_faces_distinct data.chord

/-- The first chord-incident face is non-outer. -/
lemma face₁_not_outer (data : hNT.ChordSplitData u v) :
    data.face₁ ≠ hNT.outerFace :=
  hNT.chordDart_not_outer data.chord

/-- The second chord-incident face is non-outer. -/
lemma face₂_not_outer (data : hNT.ChordSplitData u v) :
    data.face₂ ≠ hNT.outerFace :=
  hNT.chordDart_alpha_not_outer data.chord

/-- The first chord-incident face is triangular. -/
lemma face₁_isFaceTriangle (data : hNT.ChordSplitData u v) :
    M.IsFaceTriangle data.dart (M.φ data.dart) (M.φ (M.φ data.dart)) :=
  hNT.chord_incident_face_isFaceTriangle data.chord

/-- The seed `face₁` belongs to side 1. -/
lemma face₁_mem_side₁ (data : hNT.ChordSplitData u v) :
    data.face₁ ∈ data.side₁ :=
  hNT.seed_mem_side _

/-- The seed `face₂` belongs to side 2. -/
lemma face₂_mem_side₂ (data : hNT.ChordSplitData u v) :
    data.face₂ ∈ data.side₂ :=
  hNT.seed_mem_side _

/-- Side 1 is closed under the chord-split adjacency relation. -/
lemma side₁_closed (data : hNT.ChordSplitData u v) {f g : M.Face}
    (hf : f ∈ data.side₁) (hfg : hNT.ChordSplitAdj u v f g) : g ∈ data.side₁ :=
  hNT.side_closed hf hfg

/-- Side 2 is closed under the chord-split adjacency relation. -/
lemma side₂_closed (data : hNT.ChordSplitData u v) {f g : M.Face}
    (hf : f ∈ data.side₂) (hfg : hNT.ChordSplitAdj u v f g) : g ∈ data.side₂ :=
  hNT.side_closed hf hfg

/-- Every face of side 1 is non-outer. -/
lemma side₁_subset_nonouter (data : hNT.ChordSplitData u v) {g : M.Face}
    (hg : g ∈ data.side₁) : g ≠ hNT.outerFace :=
  hNT.side_subset_nonouter data.face₁_not_outer hg

/-- Every face of side 2 is non-outer. -/
lemma side₂_subset_nonouter (data : hNT.ChordSplitData u v) {g : M.Face}
    (hg : g ∈ data.side₂) : g ≠ hNT.outerFace :=
  hNT.side_subset_nonouter data.face₂_not_outer hg

/-- The seam dart `d` (the chord dart) lands in side 1's dart-set: its face is the
seed `face₁`. -/
lemma dart_mem_sideDarts₁ (data : hNT.ChordSplitData u v) :
    data.dart ∈ data.sideDarts₁ :=
  data.face₁_mem_side₁

/-- The seam dart `α d` (the reverse chord dart) lands in side 2's dart-set: its
face is the seed `face₂`. -/
lemma alpha_dart_mem_sideDarts₂ (data : hNT.ChordSplitData u v) :
    M.α data.dart ∈ data.sideDarts₂ :=
  data.face₂_mem_side₂

/-! ### Disjointness-conditional partition (the planarity keystone) -/

/-- **`chordSplit_side_darts_partition`** (conditional on the deferred planarity
keystone `SidesDisjoint`).

Given the side disjointness input, the two side dart-sets are disjoint as
*face-dart* sets.  In the side-map construction the original chord `α`-pair
`{d, α d}` is the seam between the two sides: `d` belongs to side 1
(`dart_mem_sideDarts₁`), `α d` belongs to side 2 (`alpha_dart_mem_sideDarts₂`),
and they are duplicated by fresh chord darts in each side, so the *only*
original-dart overlap between the two sides is reconciled at this seam.  Here we
record the precise data-layer fact: the two face-dart sets do not share a single
dart. -/
lemma chordSplit_side_darts_partition (data : hNT.ChordSplitData u v)
    (hdisj : hNT.SidesDisjoint data.chord) :
    Disjoint data.sideDarts₁ data.sideDarts₂ := by
  rw [Set.disjoint_left]
  intro d hd1 hd2
  -- `d`'s face is in both sides, contradicting `SidesDisjoint`.
  have hmem : M.dartFace d ∈
      (hNT.Side u v data.face₁) ⊓ (hNT.Side u v data.face₂) := ⟨hd1, hd2⟩
  have : (hNT.Side u v data.face₁) ⊓ (hNT.Side u v data.face₂) ≤ ⊥ :=
    hdisj.le_bot
  exact (this hmem).elim

/-- The chord `α`-pair `{d, α d}` is exactly the seam: under the disjointness
keystone, `d` is in side 1 only and `α d` is in side 2 only. -/
lemma seam_darts_separated (data : hNT.ChordSplitData u v)
    (hdisj : hNT.SidesDisjoint data.chord) :
    data.dart ∈ data.sideDarts₁ ∧ data.dart ∉ data.sideDarts₂ ∧
      M.α data.dart ∈ data.sideDarts₂ ∧ M.α data.dart ∉ data.sideDarts₁ := by
  have hpart := data.chordSplit_side_darts_partition hdisj
  rw [Set.disjoint_left] at hpart
  refine ⟨data.dart_mem_sideDarts₁, ?_, data.alpha_dart_mem_sideDarts₂, ?_⟩
  · exact fun hd2 => hpart data.dart_mem_sideDarts₁ hd2
  · exact fun hd1 => hpart hd1 data.alpha_dart_mem_sideDarts₂

end ChordSplitData

/-! ## 5. Constructing the chord-split data from a chord -/

/-- Assemble the unconditional chord-split data from a boundary chord.  The two
arcs come from `BoundaryCycle.two_arcs`, and both are shown internally nonempty
via `two_arcs_internally_nonempty_of_chord` (the strict-decrease bookkeeping). -/
noncomputable def chordSplitData {u v : M.Vertex}
    (h : hNT.outerCycle.Chord u v) : hNT.ChordSplitData u v :=
  let S := hNT.outerCycle.two_arcs h.endpoints_ne h.left_boundary h.right_boundary
  { chord := h
    arc := S
    arc₁_internal := S.path₁_internal_of_chord h
    arc₂_internal := S.path₂_internal_of_chord h }

@[simp]
lemma chordSplitData_chord {u v : M.Vertex} (h : hNT.outerCycle.Chord u v) :
    (hNT.chordSplitData h).chord = h :=
  rfl

end NearTriangulation

end CombMap

end ProofsInTheBook.PlanarMap
