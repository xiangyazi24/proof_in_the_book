import ProofsInTheBook.PlanarMapChordSplitData

/-!
# The two side maps of a chord split (Chapter 35, file 6)

This file constructs, from a near-triangulation `M` together with chord-split
data `data : hNT.ChordSplitData u v` (file 5), the two side combinatorial maps
and packages the part of their near-triangulation structure that is available
unconditionally at the combinatorial-map level.

## What is in this file (by section)

0. `BoundaryPath` internal-vertex witnesses — a simple boundary path with an
   internal vertex has a listed vertex strictly between its endpoints.
1. `sideDel₁/₂`, the deleted finite dart-set of a side, and the kept subtype.
2. The **seam `α`-closure** lemmas (`alpha_mem_side₁/₂_of_interior`): across any
   *non-boundary, non-chord* edge the two faces lie in the same side.  These are
   the unconditional combinatorial substance of "chord + arc is the seam".
3. Symmetry of side membership and the **separation reduction**: the isolated
   keystone is `Separates data := face₂ ∉ side₁`, and
   `separates_iff_sidesDisjoint` proves it equivalent to file 5's `SidesDisjoint`.
   The partition lemma is then discharged from `Separates`.
4. `α`-closure in kept-set form.
5. Strict-decrease **witnesses** (`arc₁/₂_internal_witness_boundary`): each arc
   has a boundary vertex strictly between `u` and `v` — the vertex the opposite
   side omits.
6. The faithful side dart set `keptSet₁/₂ = (sideDarts ∪ outerArc) \ {chord}` and
   `alpha_keptSet₁/₂`: it is `α`-closed (conditional on `Separates`).
7. The side **edge involutions** `sideAlpha₁/₂` (fixed-point-free involutions,
   `sideAlpha_involutive`, `sideAlpha_no_fixed`) and the filtered rotations
   `sideSigma₁/₂` — conditional on `Separates`.
8. The assembled side maps `sideMap₁/₂ = freshMap …` on `keptSide ⊕ Fin 2`
   (task item 1), with their `α`/`σ` validity (task item 2), conditional on
   `Separates` and a choice of two distinct splice anchors.

## The honest status of the deep facts (per `c35review-reply.md` / `opus-f5-reply.md`)

The file-5 author established, after sustained effort, that the genuine
planarity content of the chord split — that the chord together with a boundary
arc *separates* the inner faces — is **not** derivable at the combinatorial-map
level without an external Jordan/Euler separation input.  It was isolated there
as `NearTriangulation.SidesDisjoint`.  The design review reaches the same
conclusion: the per-side Euler characteristic `chi = 2` is *equivalent* to the
side face-classification + the global count `F₁ + F₂ = F + 1`, which "needs BOTH
sides at once and the coverage/disjointness of sides — that is exactly how
`SidesDisjoint` gets discharged".  So discharging `SidesDisjoint` and the side
Euler characteristic are the *same* combinatorial Jordan-curve separation, which
this repository's CombMap API does not supply as a lemma.

This file therefore isolates that separation as the single sharp predicate
`Separates data := data.face₂ ∉ data.side₁` (the minimal single-non-reachability
form), and proves the reduction `separates_iff_sidesDisjoint`.  **Everything not
touching that one point is proved unconditionally** (sections 0–5: the seam
`α`-closure, the separation reduction, the boundary-edge/chord-edge dart facts,
the strict-decrease witnesses).  The faithful side construction (sections 6–8 —
the `α`-closed kept set, the side edge involutions, and the assembled side maps
with their `α`/`σ` validity) is proved **conditional on `Separates`**, which is
the genuine and only entanglement: the kept set's `α`-closure fails exactly at
the chord reverse `α dart` unless `face₂ ∉ side₁`.

### What is *not* in this file (honest gap)

The side maps' **connectivity, Euler characteristic `2`, the face
classification, and the discharge of `SidesDisjoint`** are not proved here.  They
all reduce to the same separation theorem (`Separates`), which is the irreducible
Jordan/Euler input; and the *correct* splice anchors (making the outer boundary
the arc-plus-fresh-chord) are part of that same classification layer.  Per the
task's explicit sanction ("If after genuine sustained effort ONE deep
classification lemma resists, isolate it as a named Prop with the exact
statement, keep everything else unconditional, and report honestly"), `Separates`
is that one isolated input, and the side maps above are constructed and shown
valid as `CombMap`s relative to it.  No `sorry`/`axiom`/`admit` is used; the
gap is an honest *hypothesis* (`Separates` + anchors), not a hidden assumption.
-/

namespace ProofsInTheBook.PlanarMap

open Equiv

namespace CombMap

variable {D : Type*} [Fintype D] [DecidableEq D]

/-! ## 0. Internal-vertex witness for boundary paths

A simple boundary path with an internal vertex has an internal vertex that is a
genuine listed vertex of the path and is distinct from both endpoints.  This is
the unconditional combinatorial substance behind the strict vertex decrease of a
chord split: each side omits the *interior* vertices of the opposite arc. -/

/-- Under `Nodup`, the last element of a list does not occur in its `dropLast`. -/
lemma getLast_notMem_dropLast {α : Type*} {l : List α} (hl : l ≠ [])
    (hnd : l.Nodup) : l.getLast hl ∉ l.dropLast := by
  have hsplit : l.dropLast ++ [l.getLast hl] = l := List.dropLast_append_getLast hl
  have hnd' : (l.dropLast ++ [l.getLast hl]).Nodup := by rw [hsplit]; exact hnd
  intro hmem
  exact (List.disjoint_of_nodup_append hnd') hmem (by simp)

/-- A generic list fact: if `l.head? = some a` and `l.Nodup`, then `a ∉ l.tail`. -/
lemma head?_notMem_tail {α : Type*} {a : α} {l : List α}
    (hh : l.head? = some a) (hnd : l.Nodup) : a ∉ l.tail := by
  cases l with
  | nil => simp at hh
  | cons b t =>
      simp only [List.head?_cons, Option.some.injEq] at hh
      subst hh
      simpa using (List.nodup_cons.mp hnd).1

/-- A generic list fact: if `l.getLast? = some a` and `l.tail ≠ []`, then `a` is
the last element of `l.tail`. -/
lemma getLast_tail_of_getLast? {α : Type*} {a : α} {l : List α}
    (hl : l.getLast? = some a) (ht : l.tail ≠ []) :
    l.tail.getLast ht = a := by
  cases l with
  | nil => exact absurd rfl ht
  | cons b s =>
      simp only [List.tail_cons] at ht ⊢
      have hs : (b :: s).getLast? = some a := hl
      rw [List.getLast?_eq_some_getLast (by simp)] at hs
      simp only [Option.some.injEq] at hs
      rw [← hs, List.getLast_cons ht]

namespace BoundaryPath

variable {M : CombMap D} {u v : M.Vertex}

/-- An internal vertex of a path is a listed vertex of the path. -/
lemma internalVertices_subset (P : BoundaryPath M u v) {w : M.Vertex}
    (hw : w ∈ P.internalVertices) : w ∈ P.vertices :=
  List.tail_subset _ (List.dropLast_subset _ hw)

/-- An internal vertex is distinct from the initial endpoint. -/
lemma internalVertex_ne_start (P : BoundaryPath M u v) {w : M.Vertex}
    (hw : w ∈ P.internalVertices) : w ≠ u := by
  -- `u` is the head, so `u ∉ tail ⊇ dropLast tail ∋ w`.
  have hutail : u ∉ P.vertices.tail :=
    head?_notMem_tail P.starts_at P.simple
  have hwtail : w ∈ P.vertices.tail := List.dropLast_subset _ hw
  intro hwu; subst hwu; exact hutail hwtail

/-- An internal vertex is distinct from the terminal endpoint. -/
lemma internalVertex_ne_end (P : BoundaryPath M u v) {w : M.Vertex}
    (hw : w ∈ P.internalVertices) : w ≠ v := by
  have hwtail_dropLast : w ∈ P.vertices.tail.dropLast := hw
  have htail_ne : P.vertices.tail ≠ [] := fun h => by rw [h] at hwtail_dropLast; simp at hwtail_dropLast
  have hnodup_tail : P.vertices.tail.Nodup := P.simple.sublist (List.tail_sublist _)
  -- `v` is the last of the tail, and the last is not in `dropLast` under nodup.
  have hlast_tail : P.vertices.tail.getLast htail_ne = v :=
    getLast_tail_of_getLast? P.ends_at htail_ne
  have hnotmem : P.vertices.tail.getLast htail_ne ∉ P.vertices.tail.dropLast :=
    getLast_notMem_dropLast htail_ne hnodup_tail
  intro hwv; subst hwv
  -- `w = v = getLast tail`, and `w ∈ dropLast tail`, contradiction.
  exact hnotmem (hlast_tail.symm ▸ hwtail_dropLast)

/-- **Internal-vertex witness.**  A path with an internal vertex has a listed
vertex strictly between its endpoints (distinct from both). -/
lemma exists_internal_vertex (P : BoundaryPath M u v) (h : P.HasInternalVertex) :
    ∃ w : M.Vertex, w ∈ P.vertices ∧ w ≠ u ∧ w ≠ v := by
  obtain ⟨w, hw⟩ := List.exists_mem_of_ne_nil _ h
  exact ⟨w, P.internalVertices_subset hw, P.internalVertex_ne_start hw,
    P.internalVertex_ne_end hw⟩

end BoundaryPath

namespace NearTriangulation

variable {M : CombMap D} (hNT : NearTriangulation M)

namespace ChordSplitData

variable {hNT} {u v : M.Vertex}

/-! ## 1. The side deleted-set and kept type -/

open scoped Classical in
/-- The **deleted** dart-set of side 1: the darts whose face is *not* in side 1.
The kept subtype `{d // d ∉ sideDel₁}` is then exactly the darts whose face lies
in side 1 (`mem_sideKept₁_iff`).  Classical decidability is used (the whole
construction is `noncomputable`, matching `chordDart`). -/
noncomputable def sideDel₁ (data : hNT.ChordSplitData u v) : Finset D :=
  Finset.univ.filter (fun d => M.dartFace d ∉ data.side₁)

open scoped Classical in
/-- The **deleted** dart-set of side 2 (darts whose face is not in side 2). -/
noncomputable def sideDel₂ (data : hNT.ChordSplitData u v) : Finset D :=
  Finset.univ.filter (fun d => M.dartFace d ∉ data.side₂)

/-- A dart is kept by side 1 iff its face lies in side 1. -/
lemma mem_sideKept₁_iff (data : hNT.ChordSplitData u v) (d : D) :
    d ∉ data.sideDel₁ ↔ M.dartFace d ∈ data.side₁ := by
  classical
  simp only [sideDel₁, Finset.mem_filter, Finset.mem_univ, true_and, not_not]

/-- A dart is kept by side 2 iff its face lies in side 2. -/
lemma mem_sideKept₂_iff (data : hNT.ChordSplitData u v) (d : D) :
    d ∉ data.sideDel₂ ↔ M.dartFace d ∈ data.side₂ := by
  classical
  simp only [sideDel₂, Finset.mem_filter, Finset.mem_univ, true_and, not_not]

/-- The kept type of side 1: darts whose face lies in side 1. -/
abbrev keptSide₁ (data : hNT.ChordSplitData u v) : Type _ :=
  {d : D // d ∉ data.sideDel₁}

/-- The kept type of side 2: darts whose face lies in side 2. -/
abbrev keptSide₂ (data : hNT.ChordSplitData u v) : Type _ :=
  {d : D // d ∉ data.sideDel₂}

/-! ## 2. The seam: where `α` leaves a side

The only way for the edge-reverse `α e` of a side-1 dart `e` to *leave* side 1 is
for the edge of `e` to be a boundary edge or the chord itself.  This is the
unconditional combinatorial content behind "the chord and the boundary arc are
the seam": across any *non-boundary, non-chord* edge, the two faces are in the
same side (immediate from `Side` being closed under `ChordSplitAdj`). -/

/-- **`α`-closure away from the seam (side 1).**  If a side-1 dart `e` (its face
lies in side 1) has an edge that is neither a boundary edge nor the chord, then
`α e` is again a side-1 dart.  In other words, the *only* edges along which side
1 can leak are boundary edges and the chord. -/
lemma alpha_mem_side₁_of_interior (data : hNT.ChordSplitData u v) {e : D}
    (he : M.dartFace e ∈ data.side₁)
    (hb : ¬ hNT.outerCycle.IsBoundaryEdge (M.dartEdge e))
    (hc : M.dartEdge e ≠ s(u, v)) :
    M.dartFace (M.α e) ∈ data.side₁ := by
  have hadj : hNT.ChordSplitAdj u v (M.dartFace e) (M.dartFace (M.α e)) :=
    ⟨e, rfl, rfl, hb, by
      -- rewrite the chord edge `s(u,v)` against `data.chord`'s endpoints
      simpa using hc⟩
  exact data.side₁_closed he hadj

/-- **`α`-closure away from the seam (side 2).** -/
lemma alpha_mem_side₂_of_interior (data : hNT.ChordSplitData u v) {e : D}
    (he : M.dartFace e ∈ data.side₂)
    (hb : ¬ hNT.outerCycle.IsBoundaryEdge (M.dartEdge e))
    (hc : M.dartEdge e ≠ s(u, v)) :
    M.dartFace (M.α e) ∈ data.side₂ := by
  have hadj : hNT.ChordSplitAdj u v (M.dartFace e) (M.dartFace (M.α e)) :=
    ⟨e, rfl, rfl, hb, by simpa using hc⟩
  exact data.side₂_closed he hadj

/-! ## 3. Symmetry of side membership and the separation keystone

`ChordSplitAdj` is symmetric, hence reachability `Side` is symmetric: a face `g`
is in the side seeded by `f` iff `f` is in the side seeded by `g`.  This is the
unconditional combinatorial fact that lets us reduce the file-5 planarity
keystone `SidesDisjoint` (full disjointness of the two side face-components) to a
**single** non-reachability statement: the second chord-incident face is not
reachable from the first.  That single non-reachability is the genuine
Jordan/Euler separation input (the chord plus a boundary arc separates the inner
faces); the reduction below is the honest combinatorial simplification we *can*
prove here, isolating the irreducible content to one sharp predicate. -/

/-- Side membership is symmetric: `g ∈ Side f ↔ f ∈ Side g`.  (Reflexive–
transitive closure of a symmetric relation is symmetric.) -/
lemma side_mem_symm {seed g : M.Face}
    (h : g ∈ hNT.Side u v seed) : seed ∈ hNT.Side u v g :=
  Relation.ReflTransGen.symmetric (fun _ _ => hNT.chordSplitAdj_symm) h

/-- **The chord-split separation predicate.**  `Separates data` says the second
chord-incident face is not reachable from the first through the non-outer
adjacency.  This is the sharp, single-non-reachability form of the file-5
planarity keystone `SidesDisjoint`; it is the genuine Jordan/Euler separation
input for the chord split and is *not* derivable at the combinatorial-map level
(see the module docstring).  It is the one isolated classification input. -/
def Separates (data : hNT.ChordSplitData u v) : Prop :=
  data.face₂ ∉ data.side₁

/-- **The separation predicate is equivalent to the file-5 keystone
`SidesDisjoint`.**  This is a genuine reduction: the full disjointness of the two
side face-components reduces, via symmetry of reachability, to the single
non-reachability `face₂ ∉ side₁`.  Thus a downstream separation theorem need
only establish `Separates` to discharge `SidesDisjoint` (and hence the partition
lemma `chordSplit_side_darts_partition`). -/
theorem separates_iff_sidesDisjoint (data : hNT.ChordSplitData u v) :
    data.Separates ↔ hNT.SidesDisjoint data.chord := by
  constructor
  · -- `face₂ ∉ side₁` ⇒ the two sides are disjoint.
    intro hsep
    rw [SidesDisjoint, Set.disjoint_left]
    intro f hf1 hf2
    -- `f ∈ side₁` and `f ∈ side₂`; show `face₂ ∈ side₁`, contradicting `hsep`.
    -- `f ∈ side₂` means `face₂ ∈ Side f` (symmetry), and `f ∈ side₁` chains.
    have hf2' : data.face₂ ∈ hNT.Side u v f := side_mem_symm hf2
    -- `Side` is transitive: `face₁ ⇝ f ⇝ face₂`, so `face₂ ∈ side₁`.
    have : data.face₂ ∈ data.side₁ :=
      Relation.ReflTransGen.trans hf1 hf2'
    exact hsep this
  · -- `SidesDisjoint` ⇒ `face₂ ∉ side₁`.
    intro hdisj hmem
    -- `face₂ ∈ side₁` and `face₂ ∈ side₂` (seed), contradicting disjointness.
    rw [SidesDisjoint, Set.disjoint_left] at hdisj
    exact hdisj hmem data.face₂_mem_side₂

/-- Under separation, the two side dart-sets are disjoint
(`chordSplit_side_darts_partition`). -/
theorem sideDarts_disjoint_of_separates (data : hNT.ChordSplitData u v)
    (hsep : data.Separates) :
    Disjoint data.sideDarts₁ data.sideDarts₂ :=
  data.chordSplit_side_darts_partition ((separates_iff_sidesDisjoint data).1 hsep)

/-- Under separation, the chord pair is exactly the seam: `d` lies only in side
1 and `α d` only in side 2 (`seam_darts_separated`). -/
theorem seam_separated_of_separates (data : hNT.ChordSplitData u v)
    (hsep : data.Separates) :
    data.dart ∈ data.sideDarts₁ ∧ data.dart ∉ data.sideDarts₂ ∧
      M.α data.dart ∈ data.sideDarts₂ ∧ M.α data.dart ∉ data.sideDarts₁ :=
  data.seam_darts_separated ((separates_iff_sidesDisjoint data).1 hsep)

/-! ## 4. The seam is α-stable on the deleted-set complement minus the chord

Combining §2 (seam α-closure) with §3, the deleted set obtained from
`sideDel₁` by additionally removing the two chord darts is `α`-stable on its
complement *except across the chord and the boundary arc*.  We record the precise
statement used to build the filtered edge involution of a side map: away from the
chord and the outer boundary, `α` maps kept side-1 darts to kept side-1 darts. -/

/-- The seam α-closure, in kept-set form (side 1): if `e` is kept by side 1
(its face is in side 1) and its edge is neither a boundary edge nor the chord,
then `α e` is again kept by side 1. -/
lemma alpha_kept₁_of_interior (data : hNT.ChordSplitData u v)
    {e : D} (he : e ∉ data.sideDel₁)
    (hb : ¬ hNT.outerCycle.IsBoundaryEdge (M.dartEdge e))
    (hc : M.dartEdge e ≠ s(u, v)) :
    M.α e ∉ data.sideDel₁ := by
  rw [data.mem_sideKept₁_iff] at he ⊢
  exact data.alpha_mem_side₁_of_interior he hb hc

/-- The seam α-closure, in kept-set form (side 2). -/
lemma alpha_kept₂_of_interior (data : hNT.ChordSplitData u v)
    {e : D} (he : e ∉ data.sideDel₂)
    (hb : ¬ hNT.outerCycle.IsBoundaryEdge (M.dartEdge e))
    (hc : M.dartEdge e ≠ s(u, v)) :
    M.α e ∉ data.sideDel₂ := by
  rw [data.mem_sideKept₂_iff] at he ⊢
  exact data.alpha_mem_side₂_of_interior he hb hc

/-! ## 5. Strict vertex decrease (the witnesses)

The strict decrease of each side's vertex count is driven, per the review
(`c35review-reply.md`, "Strictly smaller sides"), by both boundary arcs having an
internal vertex: side 1's vertices omit the interior vertices of arc 2, and vice
versa.  We expose the unconditional witnesses — each arc has a boundary vertex
strictly between the two chord endpoints.  Once a side map is constructed, these
witnesses are exactly the vertices it omits, giving the strict decrease
`@CombMap.V (sideMap) < M.V`. -/

/-- **Arc-1 internal-vertex witness.**  The first boundary arc of a chord split
has a boundary vertex distinct from both chord endpoints `u` and `v`.  This is the
vertex that the *second* side map omits, driving its strict decrease. -/
lemma arc₁_internal_witness (data : hNT.ChordSplitData u v) :
    ∃ w : M.Vertex, w ∈ data.arc.path₁.vertices ∧ w ≠ u ∧ w ≠ v :=
  data.arc.path₁.exists_internal_vertex data.arc₁_internal

/-- **Arc-2 internal-vertex witness.**  The second boundary arc has a boundary
vertex distinct from both chord endpoints (note `path₂ : BoundaryPath v u`, so its
endpoints are `v` and `u`).  This is the vertex that the *first* side map omits. -/
lemma arc₂_internal_witness (data : hNT.ChordSplitData u v) :
    ∃ w : M.Vertex, w ∈ data.arc.path₂.vertices ∧ w ≠ v ∧ w ≠ u :=
  data.arc.path₂.exists_internal_vertex data.arc₂_internal

/-- The two arcs' internal witnesses are genuine boundary vertices of `M`. -/
lemma arc₁_internal_witness_boundary (data : hNT.ChordSplitData u v) :
    ∃ w : M.Vertex, hNT.outerCycle.IsBoundaryVertex w ∧ w ≠ u ∧ w ≠ v := by
  obtain ⟨w, hw, hu, hv⟩ := data.arc₁_internal_witness
  exact ⟨w, data.arc.path₁_boundary_vertices hw, hu, hv⟩

/-- The arc-2 internal witness is a genuine boundary vertex of `M`. -/
lemma arc₂_internal_witness_boundary (data : hNT.ChordSplitData u v) :
    ∃ w : M.Vertex, hNT.outerCycle.IsBoundaryVertex w ∧ w ≠ u ∧ w ≠ v := by
  obtain ⟨w, hw, hv, hu⟩ := data.arc₂_internal_witness
  exact ⟨w, data.arc.path₂_boundary_vertices hw, hu, hv⟩

/-! ## 6. The side edge involution (conditional on `Separates`)

This is the genuine combinatorial heart of item 1/2 of the chord-split
construction: building the *faithful* dart set of a side map on which the
original edge involution `α` restricts to a fixed-point-free involution.

The correct side-1 dart set is **not** `sideDarts₁` (the inner darts), because a
boundary-arc dart's `α`-reverse lies on the outer face and would escape.  The
faithful kept set adds, for each boundary edge of the side, the *outer* dart
whose reverse is an inner side-1 dart:

`keptSet₁ = (sideDarts₁ ∪ outerArc₁) \ {chordDart}`,

where `outerArc₁ = {b | dartFace b = outerFace ∧ dartFace (α b) ∈ side₁}`.  The
single original chord dart is removed (it is re-added, duplicated, by the fresh
edge in file 4's `freshMap`).

`alpha_keptSet₁` shows `keptSet₁` is closed under `α`: away from the chord
(removed) and the boundary edges (whose outer dart is kept in `outerArc₁`), `α`
maps `keptSet₁` into itself.  **One step of this argument requires the separation
input `Separates`**: to know `keptSet₁` does *not* contain the chord *reverse*
`α dart` (whose face is `face₂`), we need `face₂ ∉ side₁` — precisely
`Separates`.  Without it, `α dart` could be in `keptSet₁` while `dart` is removed,
breaking closure.  So the side edge involution is constructed *conditionally on
the single isolated input* `Separates`; everything not touching that one point is
unconditional (the boundary-edge dart fact, the chord-edge two-dart fact, the
interior closure of §2). -/

/-- The outer-face darts whose `α`-reverse is an inner dart of side 1. -/
def outerArc₁ (data : hNT.ChordSplitData u v) : Set D :=
  {b | M.dartFace b = hNT.outerFace ∧ M.dartFace (M.α b) ∈ data.side₁}

/-- The outer-face darts whose `α`-reverse is an inner dart of side 2. -/
def outerArc₂ (data : hNT.ChordSplitData u v) : Set D :=
  {b | M.dartFace b = hNT.outerFace ∧ M.dartFace (M.α b) ∈ data.side₂}

/-- The faithful kept dart set of side 1: inner side-1 darts together with the
matching outer boundary darts, minus the original chord dart. -/
def keptSet₁ (data : hNT.ChordSplitData u v) : Set D :=
  (data.sideDarts₁ ∪ data.outerArc₁) \ {data.dart}

/-- The faithful kept dart set of side 2 (the chord *reverse* `α dart` is the
side-2 seam dart that is removed). -/
def keptSet₂ (data : hNT.ChordSplitData u v) : Set D :=
  (data.sideDarts₂ ∪ data.outerArc₂) \ {M.α data.dart}

/-- The chord edge has exactly the two darts `dart` and `α dart`: any dart whose
unoriented endpoints are `s(u, v)` is `α.SameCycle` with the chord dart, hence
equal to it or its reverse.  UNCONDITIONAL (uses only graph simplicity). -/
lemma chord_edge_darts (data : hNT.ChordSplitData u v) {e : D}
    (he : M.dartEdge e = s(u, v)) : e = data.dart ∨ e = M.α data.dart := by
  have hedge : M.dartEdge e = M.dartEdge data.dart := by
    rw [he]; exact (hNT.chordDart_edge data.chord).symm
  have hsc : M.α.SameCycle e data.dart :=
    M.alpha_sameCycle_of_dartEdge_eq hNT.simpleGraph hedge
  rcases (M.alpha_sameCycle_iff data.dart e).mp hsc.symm with h | h
  · exact Or.inl h
  · exact Or.inr h

/-- For a boundary edge, at least one of its two darts lies on the outer face.
UNCONDITIONAL.  (A boundary edge is the `dartEdge` of some outer-cycle dart; the
two darts of an edge are `b` and `α b` by simplicity.) -/
lemma boundaryEdge_dart_outer (_data : hNT.ChordSplitData u v) {e : D}
    (hbe : hNT.outerCycle.IsBoundaryEdge (M.dartEdge e)) :
    M.dartFace e = hNT.outerFace ∨ M.dartFace (M.α e) = hNT.outerFace := by
  -- `dartEdge e ∈ edges = darts.map dartEdge`, so some outer dart `b` has the
  -- same `dartEdge`; by simplicity `α.SameCycle e b`, i.e. `e = b` or `e = α b`.
  rw [BoundaryCycle.IsBoundaryEdge, hNT.outerCycle.edges_eq, List.mem_map] at hbe
  obtain ⟨b, hb, hbe⟩ := hbe
  have hbface : M.dartFace b = hNT.outerFace := (hNT.outerCycle.mem_darts_iff b).mp hb
  have hsc : M.α.SameCycle e b :=
    M.alpha_sameCycle_of_dartEdge_eq hNT.simpleGraph hbe.symm
  rcases (M.alpha_sameCycle_iff b e).mp hsc.symm with h | h
  · exact Or.inl (by rw [h]; exact hbface)
  · right; rw [h, M.alpha_alpha]; exact hbface

/-- Under `Separates`, the chord *reverse* `α dart` is not in the side-1 kept set
(its face `face₂` is outside side 1, and it is not an outer dart). -/
lemma alphaDart_notMem_keptSet₁ (data : hNT.ChordSplitData u v)
    (hsep : data.Separates) : M.α data.dart ∉ data.keptSet₁ := by
  rintro ⟨hU, _⟩
  rcases hU with h1 | h2
  · -- `α dart ∈ sideDarts₁` means `face₂ ∈ side₁`, contradicting `Separates`.
    exact hsep h1
  · -- `α dart ∈ outerArc₁` needs `dartFace (α dart) = outerFace`, but it is `face₂`.
    exact data.face₂_not_outer h2.1

/-- **The side-1 kept set is closed under `α`** (conditional on `Separates`).
Away from the chord (removed) and the boundary edges (outer dart kept in
`outerArc₁`), `α` maps `keptSet₁` into itself. -/
theorem alpha_keptSet₁ (data : hNT.ChordSplitData u v) (hsep : data.Separates)
    {e : D} (he : e ∈ data.keptSet₁) : M.α e ∈ data.keptSet₁ := by
  classical
  obtain ⟨heU, hene⟩ := he
  simp only [Set.mem_singleton_iff] at hene
  -- `α e ≠ dart`: else `e = α dart ∉ keptSet₁`, contradicting `e ∈ keptSet₁`.
  have hαe_ne : M.α e ≠ data.dart := by
    intro hcontra
    have he_eq : e = M.α data.dart := by
      have := congrArg M.α hcontra; rwa [M.alpha_alpha] at this
    exact data.alphaDart_notMem_keptSet₁ hsep (he_eq ▸ ⟨heU, by
      simp only [Set.mem_singleton_iff]; exact hene⟩)
  refine ⟨?_, by simp only [Set.mem_singleton_iff]; exact hαe_ne⟩
  rcases heU with hin | hout
  · have hface_e : M.dartFace e ∈ data.side₁ := hin
    have he_not_outer : M.dartFace e ≠ hNT.outerFace :=
      data.side₁_subset_nonouter hface_e
    by_cases hbe : hNT.outerCycle.IsBoundaryEdge (M.dartEdge e)
    · right
      have hαe_outer : M.dartFace (M.α e) = hNT.outerFace := by
        rcases data.boundaryEdge_dart_outer hbe with h | h
        · exact absurd h he_not_outer
        · exact h
      exact ⟨hαe_outer, by rw [M.alpha_alpha]; exact hface_e⟩
    · left
      have hch : M.dartEdge e ≠ s(u, v) := by
        intro hchord
        rcases data.chord_edge_darts hchord with h | h
        · exact hene h
        · -- `e = α dart`, so `dartFace e = face₂`; `hin` says `face₂ ∈ side₁`.
          apply hsep
          show M.dartFace (M.α data.dart) ∈ data.side₁
          rw [← h]; exact hin
      exact data.alpha_mem_side₁_of_interior hface_e hbe hch
  · left; exact hout.2

/-- `Separates` is symmetric across the two sides: it also gives `face₁ ∉ side₂`.
(Via symmetry of reachability: `face₁ ∈ side₂` would force `face₂ ∈ side₁`.) -/
lemma separates_symm (data : hNT.ChordSplitData u v) (hsep : data.Separates) :
    data.face₁ ∉ data.side₂ := by
  intro hmem
  -- `face₁ ∈ Side face₂` ⇒ `face₂ ∈ Side face₁ = side₁`, contradicting `Separates`.
  exact hsep (side_mem_symm hmem)

/-- Under `Separates`, the chord dart `dart` is not in the side-2 kept set. -/
lemma dart_notMem_keptSet₂ (data : hNT.ChordSplitData u v)
    (hsep : data.Separates) : data.dart ∉ data.keptSet₂ := by
  rintro ⟨hU, _⟩
  rcases hU with h1 | h2
  · -- `dart ∈ sideDarts₂` means `face₁ ∈ side₂`, contradicting `separates_symm`.
    exact data.separates_symm hsep h1
  · -- `dart ∈ outerArc₂` needs `dartFace dart = outerFace`, but it is `face₁`.
    exact data.face₁_not_outer h2.1

/-- **The side-2 kept set is closed under `α`** (conditional on `Separates`). -/
theorem alpha_keptSet₂ (data : hNT.ChordSplitData u v) (hsep : data.Separates)
    {e : D} (he : e ∈ data.keptSet₂) : M.α e ∈ data.keptSet₂ := by
  classical
  obtain ⟨heU, hene⟩ := he
  simp only [Set.mem_singleton_iff] at hene
  have hαe_ne : M.α e ≠ M.α data.dart := by
    intro hcontra
    have he_eq : e = data.dart := M.α.injective hcontra
    exact data.dart_notMem_keptSet₂ hsep (he_eq ▸ ⟨heU, by
      simp only [Set.mem_singleton_iff]; exact hene⟩)
  refine ⟨?_, by simp only [Set.mem_singleton_iff]; exact hαe_ne⟩
  rcases heU with hin | hout
  · have hface_e : M.dartFace e ∈ data.side₂ := hin
    have he_not_outer : M.dartFace e ≠ hNT.outerFace :=
      data.side₂_subset_nonouter hface_e
    by_cases hbe : hNT.outerCycle.IsBoundaryEdge (M.dartEdge e)
    · right
      have hαe_outer : M.dartFace (M.α e) = hNT.outerFace := by
        rcases data.boundaryEdge_dart_outer hbe with h | h
        · exact absurd h he_not_outer
        · exact h
      exact ⟨hαe_outer, by rw [M.alpha_alpha]; exact hface_e⟩
    · left
      have hch : M.dartEdge e ≠ s(u, v) := by
        intro hchord
        rcases data.chord_edge_darts hchord with h | h
        · -- `e = dart`, so `dartFace e = face₁`; `hin` says `face₁ ∈ side₂`.
          apply data.separates_symm hsep
          show M.dartFace data.dart ∈ data.side₂
          rw [← h]; exact hin
        · exact hene h
      exact data.alpha_mem_side₂_of_interior hface_e hbe hch
  · left; exact hout.2

/-! ## 7. The side edge-involution permutations (conditional on `Separates`)

The kept sets being `α`-closed, `α` restricts to a fixed-point-free involution
on each side's kept subtype.  These are the side maps' edge involutions before
the fresh chord is spliced; combined with `FilteredRotation.freshAlpha` (file 4)
they give the side maps' `α`, fixed-point-free and involutive, which is exactly
the alpha obligation of task item 2. -/

open scoped Classical in
/-- The deleted dart-set of side 1, as a `Finset` (complement of `keptSet₁`). -/
noncomputable def keptDel₁ (data : hNT.ChordSplitData u v) : Finset D :=
  Finset.univ.filter (fun d => d ∉ data.keptSet₁)

open scoped Classical in
/-- The deleted dart-set of side 2, as a `Finset` (complement of `keptSet₂`). -/
noncomputable def keptDel₂ (data : hNT.ChordSplitData u v) : Finset D :=
  Finset.univ.filter (fun d => d ∉ data.keptSet₂)

lemma mem_keptDel₁_iff (data : hNT.ChordSplitData u v) (d : D) :
    d ∉ data.keptDel₁ ↔ d ∈ data.keptSet₁ := by
  classical
  simp only [keptDel₁, Finset.mem_filter, Finset.mem_univ, true_and, not_not]

lemma mem_keptDel₂_iff (data : hNT.ChordSplitData u v) (d : D) :
    d ∉ data.keptDel₂ ↔ d ∈ data.keptSet₂ := by
  classical
  simp only [keptDel₂, Finset.mem_filter, Finset.mem_univ, true_and, not_not]

/-- Membership in the side-1 kept set is `α`-invariant (under `Separates`). -/
lemma mem_keptSet₁_alpha_iff (data : hNT.ChordSplitData u v) (hsep : data.Separates)
    (d : D) : M.α d ∈ data.keptSet₁ ↔ d ∈ data.keptSet₁ := by
  constructor
  · intro hd
    have := data.alpha_keptSet₁ hsep hd
    rwa [M.alpha_alpha] at this
  · intro hd; exact data.alpha_keptSet₁ hsep hd

/-- Membership in the side-2 kept set is `α`-invariant (under `Separates`). -/
lemma mem_keptSet₂_alpha_iff (data : hNT.ChordSplitData u v) (hsep : data.Separates)
    (d : D) : M.α d ∈ data.keptSet₂ ↔ d ∈ data.keptSet₂ := by
  constructor
  · intro hd
    have := data.alpha_keptSet₂ hsep hd
    rwa [M.alpha_alpha] at this
  · intro hd; exact data.alpha_keptSet₂ hsep hd

/-- **The side-1 edge involution.**  `α` restricted to the kept subtype of side 1.
A genuine permutation because `keptSet₁` is `α`-closed (under `Separates`). -/
noncomputable def sideAlpha₁ (data : hNT.ChordSplitData u v) (hsep : data.Separates) :
    Equiv.Perm {d : D // d ∉ data.keptDel₁} :=
  M.α.subtypePerm (fun d => by
    rw [data.mem_keptDel₁_iff, data.mem_keptDel₁_iff]
    constructor
    · intro hd; exact (data.mem_keptSet₁_alpha_iff hsep d).1 hd
    · intro hd; exact (data.mem_keptSet₁_alpha_iff hsep d).2 hd)

/-- **The side-2 edge involution.** -/
noncomputable def sideAlpha₂ (data : hNT.ChordSplitData u v) (hsep : data.Separates) :
    Equiv.Perm {d : D // d ∉ data.keptDel₂} :=
  M.α.subtypePerm (fun d => by
    rw [data.mem_keptDel₂_iff, data.mem_keptDel₂_iff]
    constructor
    · intro hd; exact (data.mem_keptSet₂_alpha_iff hsep d).1 hd
    · intro hd; exact (data.mem_keptSet₂_alpha_iff hsep d).2 hd)

@[simp]
lemma sideAlpha₁_apply_coe (data : hNT.ChordSplitData u v) (hsep : data.Separates)
    (d : {d : D // d ∉ data.keptDel₁}) :
    (data.sideAlpha₁ hsep d : D) = M.α d.1 := by
  simp [sideAlpha₁]

@[simp]
lemma sideAlpha₂_apply_coe (data : hNT.ChordSplitData u v) (hsep : data.Separates)
    (d : {d : D // d ∉ data.keptDel₂}) :
    (data.sideAlpha₂ hsep d : D) = M.α d.1 := by
  simp [sideAlpha₂]

/-- **Side-1 edge involution is an involution.** -/
lemma sideAlpha₁_involutive (data : hNT.ChordSplitData u v) (hsep : data.Separates) :
    data.sideAlpha₁ hsep * data.sideAlpha₁ hsep = 1 := by
  ext d
  simp only [Equiv.Perm.coe_mul, Function.comp_apply, sideAlpha₁_apply_coe,
    Equiv.Perm.coe_one, id_eq]
  exact M.alpha_alpha d.1

/-- **Side-2 edge involution is an involution.** -/
lemma sideAlpha₂_involutive (data : hNT.ChordSplitData u v) (hsep : data.Separates) :
    data.sideAlpha₂ hsep * data.sideAlpha₂ hsep = 1 := by
  ext d
  simp only [Equiv.Perm.coe_mul, Function.comp_apply, sideAlpha₂_apply_coe,
    Equiv.Perm.coe_one, id_eq]
  exact M.alpha_alpha d.1

/-- **Side-1 edge involution is fixed-point free.** -/
lemma sideAlpha₁_no_fixed (data : hNT.ChordSplitData u v) (hsep : data.Separates) :
    ∀ d, data.sideAlpha₁ hsep d ≠ d := by
  intro d hd
  apply M.α_no_fixed d.1
  have := congrArg Subtype.val hd
  rwa [sideAlpha₁_apply_coe] at this

/-- **Side-2 edge involution is fixed-point free.** -/
lemma sideAlpha₂_no_fixed (data : hNT.ChordSplitData u v) (hsep : data.Separates) :
    ∀ d, data.sideAlpha₂ hsep d ≠ d := by
  intro d hd
  apply M.α_no_fixed d.1
  have := congrArg Subtype.val hd
  rwa [sideAlpha₂_apply_coe] at this

/-- **The side-1 filtered rotation** (the kept σ before the fresh chord splice),
from file 4's generic `filteredRotation`.  A genuine permutation by construction. -/
noncomputable def sideSigma₁ (data : hNT.ChordSplitData u v) :
    Equiv.Perm {d : D // d ∉ data.keptDel₁} :=
  FilteredRotation.filteredRotation M.σ data.keptDel₁

/-- **The side-2 filtered rotation.** -/
noncomputable def sideSigma₂ (data : hNT.ChordSplitData u v) :
    Equiv.Perm {d : D // d ∉ data.keptDel₂} :=
  FilteredRotation.filteredRotation M.σ data.keptDel₂

/-! ## 8. The assembled side maps (conditional on `Separates` + splice anchors)

With the side edge involution (`sideAlpha`) and the filtered rotation
(`sideSigma`) in hand, the side map is the fresh-dart adjunction of file 4:
`freshMap` adds a duplicated chord edge (`Fin 2`) spliced at two anchor darts
`a₀, a₁` (the kept darts at `u` and `v` whose rotations receive the fresh chord
darts).  This delivers item 1 (the side dart type `keptSide ⊕ Fin 2`) and item 2
(the side map's `α` is a fixed-point-free involution and its `σ` is a
permutation), both inherited directly and *unconditionally* from `freshMap`'s
construction, once `Separates` (for `sideAlpha`) and the anchors are supplied.

The anchors `a₀, a₁` (with `a₀ ≠ a₁`) are the remaining construction input: they
are determined by the cyclic position of the deleted chord dart in the `u`- and
`v`-rotations, whose contiguity is the `ContiguousInterval` obligation of file 4.
We take them as parameters here (the side map is well defined for *any* distinct
anchors; the *correct* anchors are what make the outer boundary the arc-plus-fresh
chord, which is part of the separation/classification layer). -/

/-- **The side-1 map.**  The fresh-dart adjunction over the side-1 kept type, with
edge involution `sideAlpha₁`, rotation `sideSigma₁`, and a duplicated chord edge
spliced at the two anchor darts `a₀, a₁`.  Its `α` is a fixed-point-free
involution and its `σ` is a permutation, both from `freshMap`. -/
noncomputable def sideMap₁ (data : hNT.ChordSplitData u v) (hsep : data.Separates)
    (a₀ a₁ : {d : D // d ∉ data.keptDel₁}) (hne : a₀ ≠ a₁) :
    CombMap ({d : D // d ∉ data.keptDel₁} ⊕ Fin 2) :=
  FilteredRotation.freshMap (data.sideAlpha₁ hsep) data.sideSigma₁
    (data.sideAlpha₁_involutive hsep) (data.sideAlpha₁_no_fixed hsep) a₀ a₁ hne

/-- **The side-2 map.** -/
noncomputable def sideMap₂ (data : hNT.ChordSplitData u v) (hsep : data.Separates)
    (a₀ a₁ : {d : D // d ∉ data.keptDel₂}) (hne : a₀ ≠ a₁) :
    CombMap ({d : D // d ∉ data.keptDel₂} ⊕ Fin 2) :=
  FilteredRotation.freshMap (data.sideAlpha₂ hsep) data.sideSigma₂
    (data.sideAlpha₂_involutive hsep) (data.sideAlpha₂_no_fixed hsep) a₀ a₁ hne

/-- **Side-1 map: `α` is an involution** (task item 2, alpha obligation). -/
lemma sideMap₁_alpha_involutive (data : hNT.ChordSplitData u v) (hsep : data.Separates)
    (a₀ a₁ : {d : D // d ∉ data.keptDel₁}) (hne : a₀ ≠ a₁) :
    (data.sideMap₁ hsep a₀ a₁ hne).α * (data.sideMap₁ hsep a₀ a₁ hne).α = 1 :=
  (data.sideMap₁ hsep a₀ a₁ hne).α_invol

/-- **Side-1 map: `α` is fixed-point free** (task item 2, alpha obligation). -/
lemma sideMap₁_alpha_no_fixed (data : hNT.ChordSplitData u v) (hsep : data.Separates)
    (a₀ a₁ : {d : D // d ∉ data.keptDel₁}) (hne : a₀ ≠ a₁) :
    ∀ x, (data.sideMap₁ hsep a₀ a₁ hne).α x ≠ x :=
  (data.sideMap₁ hsep a₀ a₁ hne).α_no_fixed

/-- **Side-2 map: `α` is an involution.** -/
lemma sideMap₂_alpha_involutive (data : hNT.ChordSplitData u v) (hsep : data.Separates)
    (a₀ a₁ : {d : D // d ∉ data.keptDel₂}) (hne : a₀ ≠ a₁) :
    (data.sideMap₂ hsep a₀ a₁ hne).α * (data.sideMap₂ hsep a₀ a₁ hne).α = 1 :=
  (data.sideMap₂ hsep a₀ a₁ hne).α_invol

/-- **Side-2 map: `α` is fixed-point free.** -/
lemma sideMap₂_alpha_no_fixed (data : hNT.ChordSplitData u v) (hsep : data.Separates)
    (a₀ a₁ : {d : D // d ∉ data.keptDel₂}) (hne : a₀ ≠ a₁) :
    ∀ x, (data.sideMap₂ hsep a₀ a₁ hne).α x ≠ x :=
  (data.sideMap₂ hsep a₀ a₁ hne).α_no_fixed

/-- **Side-1 map: `σ` is the spliced fresh rotation** (a genuine permutation by
construction, since `CombMap.σ` is a `Equiv.Perm`).  This records the σ
obligation of task item 2: the side rotation is `freshSigma` of the filtered
rotation, hence a permutation. -/
lemma sideMap₁_sigma_eq (data : hNT.ChordSplitData u v) (hsep : data.Separates)
    (a₀ a₁ : {d : D // d ∉ data.keptDel₁}) (hne : a₀ ≠ a₁) :
    (data.sideMap₁ hsep a₀ a₁ hne).σ =
      FilteredRotation.freshSigma data.sideSigma₁ a₀ a₁ hne :=
  rfl

/-- **Side-2 map: `σ` is the spliced fresh rotation.** -/
lemma sideMap₂_sigma_eq (data : hNT.ChordSplitData u v) (hsep : data.Separates)
    (a₀ a₁ : {d : D // d ∉ data.keptDel₂}) (hne : a₀ ≠ a₁) :
    (data.sideMap₂ hsep a₀ a₁ hne).σ =
      FilteredRotation.freshSigma data.sideSigma₂ a₀ a₁ hne :=
  rfl

end ChordSplitData

end NearTriangulation

end CombMap

end ProofsInTheBook.PlanarMap
