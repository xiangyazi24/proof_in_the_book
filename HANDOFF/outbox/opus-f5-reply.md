# File 5 reply: `ProofsInTheBook/PlanarMapChordSplitData.lean`

Status: **complete, verified clean** on uisai1
(`lake env lean ProofsInTheBook/PlanarMapChordSplitData.lean` → 0 errors).
0 `sorry` / `axiom` / `admit` / `native_decide`. `#print axioms` on the headline
declarations reports only `[propext, Classical.choice, Quot.sound]`.

Imports only `ProofsInTheBook.PlanarMapFilteredRotation` (transitively
NearTriangulation). Owns nothing else.

This is the **data** layer for the chord split, per `c35review-reply.md` §"Chord
split: break points and corrected invariant". The two side `CombMap`s are file 6,
not here. The construction follows the review's correction exactly: sides are the
reachability closures of the adjacency relation **on non-outer faces only**,
adjacency across non-boundary non-chord edges, seeded by the two chord-incident
inner faces. The old outer face is never assigned to a side (it is excluded
automatically — see `side_subset_nonouter`).

## Namespace

`ProofsInTheBook.PlanarMap.CombMap.NearTriangulation` (most defs are
`hNT`-methods); the bundle lives in nested `ChordSplitData`.

## 1. Chord darts and incident faces (all UNCONDITIONAL)

```lean
noncomputable def chordDart (h : C.Chord u v) : D            -- a dart with dartEdge = s(u,v)
lemma chordDart_edge        : M.dartEdge (hNT.chordDart h) = s(u, v)
lemma chordDart_alpha_edge  : M.dartEdge (M.α (hNT.chordDart h)) = s(u, v)
lemma chordDart_not_outer       : M.dartFace (hNT.chordDart h) ≠ hNT.outerFace
lemma chordDart_alpha_not_outer : M.dartFace (M.α (hNT.chordDart h)) ≠ hNT.outerFace
lemma chord_incident_faces_distinct :          -- THE review item (2)
    M.dartFace (hNT.chordDart h) ≠ M.dartFace (M.α (hNT.chordDart h))
lemma chord_incident_face_isFaceTriangle :      -- both faces are triangles
    M.IsFaceTriangle (hNT.chordDart h) (M.φ ..) (M.φ (M.φ ..))
```
`chord_incident_faces_distinct` is proved via
`NearTriangulation.edge_faces_distinct_or_boundary_edge` (no-bridge lemma) +
`Chord.not_boundary_edge`; non-outerness via the boundary-edge characterization
(`mem_darts_iff` + `edges_eq`).

## 2. Non-outer-face adjacency (UNCONDITIONAL)

```lean
def ChordSplitAdj (u v) (f g : M.Face) : Prop :=
  ∃ d, M.dartFace d = f ∧ M.dartFace (M.α d) = g ∧
       ¬ C.IsBoundaryEdge (M.dartEdge d) ∧ M.dartEdge d ≠ s(u, v)
lemma chordSplitAdj_symm
lemma chordSplitAdj_target_not_outer : ChordSplitAdj .. f g → g ≠ outerFace
```
The key structural fact (`target_not_outer`): adjacency across a non-boundary
edge can never reach the outer face — this is what makes "components among
non-outer faces" automatic and is exactly the review's fix (the old outer face
does NOT reconnect the sides because it is never reachable).

## 3. The two sides as reachability closures (UNCONDITIONAL)

```lean
def Side (u v) (seed : M.Face) : Set M.Face := {g | ReflTransGen (ChordSplitAdj u v) seed g}
lemma seed_mem_side        : seed ∈ Side u v seed
lemma side_closed          : f ∈ Side u v seed → ChordSplitAdj u v f g → g ∈ Side u v seed
lemma side_subset_nonouter : seed ≠ outerFace → g ∈ Side u v seed → g ≠ outerFace
def sideFaceDarts (u v) (seed) : Set D := {d | M.dartFace d ∈ Side u v seed}
```

## 4. The data structure + the planarity keystone

```lean
def SidesDisjoint (h : C.Chord u v) : Prop :=
  Disjoint (Side u v (M.dartFace (chordDart h))) (Side u v (M.dartFace (M.α (chordDart h))))

structure ChordSplitData (u v : M.Vertex) where
  chord         : C.Chord u v
  arc           : BoundaryArcSplit M C.vertices C.edges u v
  arc₁_internal : arc.path₁.HasInternalVertex
  arc₂_internal : arc.path₂.HasInternalVertex
```
`ChordSplitData` carries only the UNCONDITIONALLY-proven data. The deferred
planarity input is the standalone predicate `SidesDisjoint`, passed as a
hypothesis to the partition lemma (NOT a structure field, so the bundle is
constructible unconditionally — see `chordSplitData` below).

Accessors / facts (all UNCONDITIONAL): `dart`, `face₁`, `face₂`, `side₁`,
`side₂`, `sideDarts₁`, `sideDarts₂`, `face_distinct`, `face₁_not_outer`,
`face₂_not_outer`, `face₁_isFaceTriangle`, `face₁_mem_side₁`, `face₂_mem_side₂`,
`side₁_closed`, `side₂_closed`, `side₁_subset_nonouter`, `side₂_subset_nonouter`,
`dart_mem_sideDarts₁`, `alpha_dart_mem_sideDarts₂`.

## 5. The partition (CONDITIONAL on `SidesDisjoint`)

```lean
lemma chordSplit_side_darts_partition (data) (hdisj : SidesDisjoint data.chord) :
    Disjoint data.sideDarts₁ data.sideDarts₂
lemma seam_darts_separated (data) (hdisj : SidesDisjoint data.chord) :
    data.dart ∈ sideDarts₁ ∧ data.dart ∉ sideDarts₂ ∧
    M.α data.dart ∈ sideDarts₂ ∧ M.α data.dart ∉ sideDarts₁
```

## Constructor (UNCONDITIONAL)

```lean
noncomputable def chordSplitData (h : C.Chord u v) : ChordSplitData u v
@[simp] lemma chordSplitData_chord : (chordSplitData h).chord = h
```
Arcs from `BoundaryCycle.two_arcs`; both arcs shown internally nonempty via
`two_arcs_internally_nonempty_of_chord` (review item 5 / strict-decrease
bookkeeping).

## HONEST status of disjointness/coverage (review item 3)

I tried to prove full dual-component disjointness here and concluded it is **not
derivable at this pre-construction layer** — it is the genuine Jordan/Euler
separation fact (chord + arc separates inner faces; combinatorially equivalent to
the side face classification + `F₁ + F₂ = F + 1` that the side maps make
available). Per the review's explicit sanction, it is isolated as the single
named `def SidesDisjoint`. Everything that does NOT need it is proved
unconditionally (faces distinct/non-outer/triangular, closure, seed membership,
non-outerness of whole sides, seam darts landing in their own sides, both arcs
internally nonempty). Only `chordSplit_side_darts_partition` and
`seam_darts_separated` consume `SidesDisjoint`.

**For file 6:** discharge `SidesDisjoint (chord)` from the side face
classification, then feed it to `chordSplit_side_darts_partition`. Use
`chord_incident_face_isFaceTriangle`, `sideDarts₁/₂`, `face₁/₂`, and the
`arc₁/₂_internal` fields. Wire `filteredRotation` / `freshMap` from file 4 with
`a₀ = chordDart`, `a₁` from the matching side darts.
