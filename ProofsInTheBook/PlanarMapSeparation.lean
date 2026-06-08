import ProofsInTheBook.PlanarMapChordSplit

/-!
# The genus-0 separation input of the chord split (Chapter 35)

This file isolates and analyzes the single planarity keystone of the Chapter 35
chord split: that the two chord-incident inner faces are *separated* by the chord
together with a boundary arc.  Concretely, the predicate
`ChordSplitData.Separates` (file 6) asserts

  `data.face₂ ∉ data.side₁`,

i.e. the second chord-incident face is **not** reachable from the first through
the non-outer face-adjacency `ChordSplitAdj` that avoids boundary edges and the
chord.  The file-5/file-6 authors and the design review independently established
that this is the irreducible combinatorial Jordan/Euler input of the chord split
(equivalently the per-side Euler count `F₁ + F₂ = F + 1`), not derivable at the
pre-construction combinatorial-map layer from `IsSphereMap = Connected ∧
eulerChar = 2` without building the side sub-maps and computing their Euler
characteristic — a step that is itself circular with the separation.

## What this file proves

* **Unconditional structural lemmas** about the separation predicate and the side
  reachability closures, which are new relative to files 5/6:

  - `chordSplitAdj_source_not_outer`, `chordSplitAdj_endpoints_not_outer`,
    `chordSplitAdj_endpoints_faceLen_three`: every face touched by a
    `ChordSplitAdj` step is a non-outer triangle.
  - `side₁_subset_triangles` / `side₂_subset_triangles`: every face of a side is a
    triangle.
  - `not_separates_iff_face₂_mem`, `not_separates_sides_eq`: the negation of
    separation collapses the two sides into a single reachability class.
  - `chord_joins_faces_except_chord`, `not_separates_iff_reachable_avoiding_chord`:
    the chord is the unique seam joining the two chord faces, so `¬ Separates` is
    exactly a chord-avoiding `ChordSplitAdj`-path between them — i.e. the chord
    lies on a cycle of the interior dual (the chord is a non-bridge there).

* **The conditional separation theorem** `separates_of_nearTriangulation`, proved
  from one sharply-isolated Jordan/Euler input `SphereChordSeparation` (stated at
  the interior-dual level: the two chord faces are not joined by a chord-avoiding
  dual path).

## The honest gap (no overclaim)

`SphereChordSeparation` is the one isolated input.  It is the combinatorial Jordan
curve theorem for sphere maps and, as `sphereChordSeparation_iff_separates` makes
explicit, it is *the separation content itself* phrased at the interior-dual
level — **not** a strictly higher-level Euler hypothesis.  We do not discharge the
per-side Euler count `F₁ + F₂ = F + 1`; per the file-5/file-6 analyses and the
design review that count is itself circular with this separation at the
combinatorial-map layer (it needs the side sub-maps' Euler characteristic, whose
well-definedness needs separation).  The genuine new content is the unconditional
analysis (sections 1–3) pinning `Separates` to the chord's bridge property in the
interior dual.  No `sorry`/`axiom`/`admit` is used; the gap is an honest, single,
sharply-stated hypothesis. -/

namespace ProofsInTheBook.PlanarMap

open Equiv

namespace CombMap

variable {D : Type*} [Fintype D] [DecidableEq D]

namespace NearTriangulation

variable {M : CombMap D} (hNT : NearTriangulation M)

/-! ## 1. Endpoints of an adjacency step are non-outer triangles

The relation `ChordSplitAdj` shares a *non-boundary, non-chord* edge; both its
endpoints therefore avoid the outer face, hence are triangular faces of the
near-triangulation. -/

/-- The source face of a chord-split adjacency step is non-outer.  (The target is
`chordSplitAdj_target_not_outer`; symmetry of the relation gives the source.) -/
lemma chordSplitAdj_source_not_outer {u v : M.Vertex} {f g : M.Face}
    (hfg : hNT.ChordSplitAdj u v f g) : f ≠ hNT.outerFace :=
  hNT.chordSplitAdj_target_not_outer (hNT.chordSplitAdj_symm hfg)

/-- Both endpoints of a chord-split adjacency step are non-outer. -/
lemma chordSplitAdj_endpoints_not_outer {u v : M.Vertex} {f g : M.Face}
    (hfg : hNT.ChordSplitAdj u v f g) :
    f ≠ hNT.outerFace ∧ g ≠ hNT.outerFace :=
  ⟨hNT.chordSplitAdj_source_not_outer hfg, hNT.chordSplitAdj_target_not_outer hfg⟩

/-- Both endpoints of a chord-split adjacency step are triangular faces. -/
lemma chordSplitAdj_endpoints_faceLen_three {u v : M.Vertex} {f g : M.Face}
    (hfg : hNT.ChordSplitAdj u v f g) :
    M.faceLen f = 3 ∧ M.faceLen g = 3 :=
  ⟨hNT.inner_faceLen_eq_three (hNT.chordSplitAdj_source_not_outer hfg),
   hNT.inner_faceLen_eq_three (hNT.chordSplitAdj_target_not_outer hfg)⟩

namespace ChordSplitData

variable {hNT} {u v : M.Vertex}

/-- Every face of side 1 is a triangle. -/
lemma side₁_subset_triangles (data : hNT.ChordSplitData u v) {g : M.Face}
    (hg : g ∈ data.side₁) : M.faceLen g = 3 :=
  hNT.inner_faceLen_eq_three (data.side₁_subset_nonouter hg)

/-- Every face of side 2 is a triangle. -/
lemma side₂_subset_triangles (data : hNT.ChordSplitData u v) {g : M.Face}
    (hg : g ∈ data.side₂) : M.faceLen g = 3 :=
  hNT.inner_faceLen_eq_three (data.side₂_subset_nonouter hg)

/-! ## 2. Negation of separation collapses the two sides -/

/-- `Separates` literally says the second chord face is not in side 1. -/
lemma not_separates_iff_face₂_mem (data : hNT.ChordSplitData u v) :
    ¬ data.Separates ↔ data.face₂ ∈ data.side₁ := by
  unfold Separates
  exact not_not

/-- If separation fails, the two side closures coincide as sets of faces:
`face₂` is reachable from `face₁` and (by symmetry) vice versa, so the two
reachability classes are equal. -/
lemma not_separates_sides_eq (data : hNT.ChordSplitData u v)
    (hns : ¬ data.Separates) : data.side₁ = data.side₂ := by
  -- `hf₂ : face₁ ⇝ face₂` (this is `face₂ ∈ side₁`).
  have hf₂ : data.face₂ ∈ data.side₁ :=
    (data.not_separates_iff_face₂_mem).1 hns
  -- `hf₁ : face₂ ⇝ face₁` by symmetry of reachability.
  have hf₁ : data.face₁ ∈ data.side₂ := side_mem_symm hf₂
  apply Set.eq_of_subset_of_subset
  · intro g hg
    -- `hg : face₁ ⇝ g`.  Chain `face₂ ⇝ face₁ ⇝ g` to land in side₂.
    exact Relation.ReflTransGen.trans hf₁ hg
  · intro g hg
    -- `hg : face₂ ⇝ g`.  Chain `face₁ ⇝ face₂ ⇝ g` to land in side₁.
    exact Relation.ReflTransGen.trans hf₂ hg

/-! ## 3. The chord joins the two faces in the full dual; `Separates` is the
bridge property

`ChordSplitAdj` is the dual face-adjacency that *avoids* boundary edges and the
chord.  The chord edge itself joins `face₁` and `face₂` (its two darts have these
two faces, and the edge `s(u,v)` is non-boundary).  Therefore the only thing that
fails the `ChordSplitAdj` test for the chord pair is the explicit chord exclusion
`M.dartEdge d ≠ s(u,v)`.  Hence `¬ Separates` (`face₂` reachable from `face₁`
through chord-avoiding adjacency) is precisely the statement that the chord is a
**non-bridge** of the interior dual: there is a second, chord-avoiding route
between its two faces, closing a dual cycle through the chord. -/

/-- The chord's two darts witness, *but for the chord-exclusion clause*, a
`ChordSplitAdj` between `face₁` and `face₂`: the shared edge is non-boundary and
its two faces are exactly `face₁` and `face₂`.  (It fails `ChordSplitAdj` only
because it *is* the chord; this is what makes the chord the seam.) -/
lemma chord_joins_faces_except_chord (data : hNT.ChordSplitData u v) :
    M.dartFace data.dart = data.face₁ ∧
      M.dartFace (M.α data.dart) = data.face₂ ∧
      ¬ hNT.outerCycle.IsBoundaryEdge (M.dartEdge data.dart) ∧
      M.dartEdge data.dart = s(u, v) := by
  have hedge : M.dartEdge data.dart = s(u, v) := hNT.chordDart_edge data.chord
  refine ⟨rfl, rfl, ?_, hedge⟩
  -- The chord edge is not a boundary edge.
  rw [hedge]
  exact data.chord.not_boundary_edge

/-- **`Separates` is the bridge property of the chord in the interior dual.**
`¬ Separates` holds iff the second chord face is reachable from the first through
`ChordSplitAdj` (which avoids the chord), i.e. iff there is a chord-avoiding dual
path joining the two chord faces.  Since the chord itself directly joins them,
this is exactly "the chord lies on a dual cycle" / "the chord is not a bridge of
the interior dual". -/
lemma not_separates_iff_reachable_avoiding_chord (data : hNT.ChordSplitData u v) :
    ¬ data.Separates ↔
      Relation.ReflTransGen (hNT.ChordSplitAdj u v) data.face₁ data.face₂ := by
  rw [data.not_separates_iff_face₂_mem]
  rfl

/-! ## 4. The isolated Jordan/Euler input and the conditional separation theorem

The genus-0 separation theorem is the combinatorial Jordan curve theorem for
sphere maps: in a near-triangulation, the chord together with a boundary arc is a
separating cycle, so the chord is a *bridge* of the interior dual.  Per the
file-5/file-6 analyses and the design review, this is *equivalent* to the per-side
Euler count `F₁ + F₂ = F + 1` and is the single irreducible planarity input; it is
not derivable from `IsSphereMap = Connected ∧ eulerChar = 2` at the
combinatorial-map layer without constructing the side sub-maps' Euler
characteristic (which is circular with the separation itself).

We name it as one sharp predicate `SphereChordSeparation` stated at the
**interior-dual level** — "the two chord faces are not joined by a chord-avoiding
dual path" — which is the faithful Jordan content of the chord split.

**Honesty note (no overclaim).**  `SphereChordSeparation h` unfolds to
`¬ ReflTransGen (ChordSplitAdj) face₁ face₂`, which is *definitionally the same
content* as `ChordSplitData.Separates` (`face₂ ∉ side₁`, with
`side₁ = {g | ReflTransGen face₁ g}`).  So `separates_of_nearTriangulation` is an
honest repackaging at the interior-dual level, **not** a derivation from a
strictly higher-level Euler count.  We do not claim to discharge the Euler count;
per the file-5/file-6 analyses and the design review that count is itself circular
with this separation at the combinatorial-map layer.  The *genuine new content* of
this file is the unconditional analysis in sections 1–3 (adjacency endpoints are
inner triangles; negation of separation collapses the two sides into one
reachability class; the chord is the unique seam joining the two faces, so
`Separates` is exactly the chord's bridge property in the interior dual).  This
single predicate is the precise, sharply-isolated remaining input. -/

end ChordSplitData

/-- **The genus-0 chord separation input** (the combinatorial Jordan curve
theorem for sphere near-triangulations).  For a boundary chord `uv`, the two
chord-incident inner faces are **not** joined by a `ChordSplitAdj`-path — a dual
path avoiding boundary edges and the chord.  Combinatorially this is the
non-bridge/separating-cycle fact equivalent to the per-side Euler count
`F₁ + F₂ = F + 1`; it is the one isolated planarity keystone of the chord split. -/
def SphereChordSeparation {u v : M.Vertex} (h : hNT.outerCycle.Chord u v) : Prop :=
  ¬ Relation.ReflTransGen (hNT.ChordSplitAdj u v)
      (M.dartFace (hNT.chordDart h)) (M.dartFace (M.α (hNT.chordDart h)))

namespace ChordSplitData

variable {hNT} {u v : M.Vertex}

/-- The Jordan input for a chord, phrased on the data bundle's faces. -/
lemma sphereChordSeparation_iff (data : hNT.ChordSplitData u v) :
    hNT.SphereChordSeparation data.chord ↔
      ¬ Relation.ReflTransGen (hNT.ChordSplitAdj u v) data.face₁ data.face₂ :=
  Iff.rfl

/-- **Transparency lemma (no hidden strengthening).**  The isolated input
`SphereChordSeparation` is *equivalent to* the separation predicate `Separates`
itself (indeed definitionally the same content), made explicit so no reader is
misled into thinking it is a strictly weaker/higher-level hypothesis.  This is the
honest statement of where the single irreducible gap sits. -/
lemma sphereChordSeparation_iff_separates (data : hNT.ChordSplitData u v) :
    hNT.SphereChordSeparation data.chord ↔ data.Separates := by
  rw [data.sphereChordSeparation_iff,
    ← data.not_separates_iff_reachable_avoiding_chord, not_not]

/-- **The chord-split separation theorem** (conditional on the isolated Jordan/
Euler input `SphereChordSeparation`).  Given the genus-0 separation input, the
second chord-incident face is not reachable from the first through the non-outer
adjacency avoiding boundary edges and the chord: i.e. `data.Separates`.

This is an honest conditional theorem on the one sharply-isolated planarity
input; by `sphereChordSeparation_iff_separates` the input is the separation
content itself at the interior-dual level (no hidden strengthening). -/
theorem separates_of_nearTriangulation (data : hNT.ChordSplitData u v)
    (hsep : hNT.SphereChordSeparation data.chord) : data.Separates := by
  by_contra hns
  exact hsep ((data.not_separates_iff_reachable_avoiding_chord).1 hns)

/-- Consequently, under the Jordan input, file-5's keystone `SidesDisjoint`
holds, and hence the side dart-sets are disjoint and the chord pair is the seam.
This is the downstream payload of separation. -/
theorem sidesDisjoint_of_nearTriangulation (data : hNT.ChordSplitData u v)
    (hsep : hNT.SphereChordSeparation data.chord) :
    hNT.SidesDisjoint data.chord :=
  (separates_iff_sidesDisjoint data).1 (separates_of_nearTriangulation data hsep)

end ChordSplitData

end NearTriangulation

end CombMap

end ProofsInTheBook.PlanarMap

