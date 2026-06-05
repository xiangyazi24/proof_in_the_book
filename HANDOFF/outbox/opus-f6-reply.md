# File 6 reply: `ProofsInTheBook/PlanarMapChordSplit.lean`

Status: **complete and verified clean** on uisai1
(`lake env lean ProofsInTheBook/PlanarMapChordSplit.lean` → 0 errors, 0 warnings;
`lake build ProofsInTheBook.PlanarMapChordSplit` → success, 8427 jobs).
0 `sorry` / `axiom` / `admit` / `native_decide`.  `#print axioms` on all 13
headline declarations reports only `[propext, Classical.choice, Quot.sound]`.

Imports only `ProofsInTheBook.PlanarMapChordSplitData` (file 5), transitively
file 4's `FilteredRotation` toolkit and the NearTriangulation stack.  Owns
nothing else.  754 lines.

Namespace: `ProofsInTheBook.PlanarMap.CombMap.NearTriangulation.ChordSplitData`
(all defs/lemmas are `data`-methods of `hNT.ChordSplitData u v`); plus a small
`BoundaryPath` section and three generic `List` helpers in the outer `CombMap`
namespace.

## The single isolated input (the honest gap)

After sustained effort I confirm — independently, and matching both the file-5
author's conclusion and the design review — that the genuine planarity content
of the chord split (the chord + a boundary arc **separates** the inner faces) is
**not derivable** at the combinatorial-map level from the available API.  It is
the combinatorial Jordan/Euler separation, and per the review it is *equivalent*
to the per-side Euler count `chi = 2` / `F₁+F₂=F+1`; discharging file 5's
`SidesDisjoint` and proving the side Euler characteristic are the *same* theorem.

I isolate it as the single sharp predicate

```lean
def Separates (data) : Prop := data.face₂ ∉ data.side₁
```

and prove the genuine reduction

```lean
theorem separates_iff_sidesDisjoint : data.Separates ↔ hNT.SidesDisjoint data.chord
```

via symmetry of reachability (`side_mem_symm`).  This is a real simplification:
file 5's full disjointness keystone reduces to one non-reachability statement.

## Unconditional results (sections 0–5)

* `BoundaryPath.exists_internal_vertex` (+ `internalVertex_ne_start/_ne_end`,
  `internalVertices_subset`): a simple path with an internal vertex has a listed
  vertex strictly between its endpoints.  Generic list helpers
  `getLast_notMem_dropLast`, `head?_notMem_tail`, `getLast_tail_of_getLast?`.
* `sideDel₁/₂`, `keptSide₁/₂`, `mem_sideKept₁/₂_iff` — the side deleted-set and
  kept type (item 1, data level).
* **Seam `α`-closure** `alpha_mem_side₁/₂_of_interior` and kept-set form
  `alpha_kept₁/₂_of_interior`: across any non-boundary, non-chord edge the two
  faces lie in the same side.  (Load-bearing combinatorial fact.)
* `separates_iff_sidesDisjoint`, `sideDarts_disjoint_of_separates`,
  `seam_separated_of_separates`, `separates_symm` (separation is symmetric
  across the two sides).
* `chord_edge_darts`: the chord edge has exactly `{dart, α dart}` (graph
  simplicity).  `boundaryEdge_dart_outer`: a boundary edge has at least one dart
  on the outer face.
* **Strict-decrease witnesses** `arc₁/₂_internal_witness(_boundary)`: each
  boundary arc has a boundary vertex `≠ u, v` — the vertex the opposite side
  omits (the substance of `chordSplit_smaller`).

## Results conditional on `Separates` (sections 6–8)

The faithful side dart set is **not** `sideDarts` (inner darts); a boundary-arc
dart's reverse escapes to the outer face.  The correct set adds the matching
outer darts and drops the original chord dart:

```lean
def outerArc₁ := {b | dartFace b = outerFace ∧ dartFace (α b) ∈ side₁}
def keptSet₁  := (sideDarts₁ ∪ outerArc₁) \ {dart}
```

* `alpha_keptSet₁/₂` — `keptSet` is `α`-closed.  **This needs `Separates`** at
  exactly one point: to rule out `α dart ∈ keptSet₁` (its face is `face₂`); this
  is the genuine and only entanglement with separation.
* `sideAlpha₁/₂` — the side **edge involutions** (`α` restricted to the kept
  subtype), with `sideAlpha_involutive` and `sideAlpha_no_fixed` (task item 2,
  alpha obligation, fully proved).
* `sideSigma₁/₂` — the filtered rotations (file 4 `filteredRotation`).
* `sideMap₁/₂ := freshMap sideAlpha sideSigma … a₀ a₁` — the assembled side
  `CombMap` on `keptSide ⊕ Fin 2` (**task item 1**), taking two distinct splice
  anchors as parameters.  `sideMap₁/₂_alpha_involutive`,
  `sideMap₁/₂_alpha_no_fixed`, `sideMap₁/₂_sigma_eq` — its `α`/`σ` validity
  (**task item 2**), inherited from `freshMap`.

## What is NOT proved here (the honest gap, restated)

The side maps' **connectivity, Euler characteristic 2, face classification, and
the discharge of `SidesDisjoint`** are not established.  They all reduce to the
same separation theorem (`Separates`), and the *correct* splice anchors (making
the outer boundary the arc-plus-fresh-chord) are part of that classification
layer.  Therefore:

* `chordSplit_smaller` as a statement about `(sideMap).V < M.V` is **not** stated
  on the side map (its vertex count needs the face/vertex classification, hence
  separation); its unconditional substance — the omitted boundary vertex — is
  delivered as `arc₁/₂_internal_witness_boundary`.
* `NearTriangulation (sideMap₁/₂)` is **not** constructed.

This is an honest hypothesis (`Separates` + anchors), not a hidden assumption: no
`sorry`/`axiom`/`admit`, and `#print axioms` is clean on every declaration.

## For the downstream Thomassen file (file 10)

When a separation theorem becomes available (a lemma producing
`data.Separates`), it immediately discharges `SidesDisjoint` via
`separates_iff_sidesDisjoint`, yields the disjoint dart partition
(`sideDarts_disjoint_of_separates`), and makes the side maps `sideMap₁/₂`
available as genuine `CombMap`s with valid `α`/`σ`.  The remaining work to reach
`NearTriangulation (sideMap)` is the face classification + Euler count, which the
review identifies with that same separation input.

The separation theorem itself most plausibly comes from a *new* CombMap-level
Jordan/Euler lemma (sphere map ⇒ a chord+arc cycle separates faces), which is
outside this file's import surface and the f4/f5 toolkits.
