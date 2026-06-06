# Ch36 Layer A3 — Convex Vertex / Ear / Diagonal — Reply (opus-convexvertex)

**Status: DELIVERED + VERIFIED.** `ProofsInTheBook/PolygonConvexVertex.lean`
(imports `ProofsInTheBook.PolygonParity`) compiles clean on **uisai2**
(uisai1 down). 0 sorry / 0 axiom / 0 admit / 0 native_decide.

## Verification

```
rsync -az ProofsInTheBook/PolygonConvexVertex.lean uisai2:~/repos/proof_in_the_book/ProofsInTheBook/
ssh uisai2 'cd ~/repos/proof_in_the_book && lake env lean ProofsInTheBook/PolygonConvexVertex.lean'   # EXIT 0
ssh uisai2 'cd ~/repos/proof_in_the_book && lake build ProofsInTheBook.PolygonConvexVertex'           # ✔ 8422/8422
```

`#print axioms` on all five headline results →
`[propext, Classical.choice, Quot.sound]` only (no `sorryAx`, no custom axiom):
`exists_convex_vertex`, `convex_vertex_empty_triangle_gives_ear`,
`slide_last_vertex_gives_diagonal`, `exists_diagonal`,
`a3GeometryFacts_of_residues`.
`grep sorry|admit|native_decide|axiom` → nothing.

## What is proven (the four A3 headlines + assembly)

1. **`exists_convex_vertex`** — `∃ i, IsConvexVertex P ρ i`. The combinatorial
   existence of the extreme/lexicographic vertex enters through
   `ExtremeConvexResidue` (which records the extreme vertex *together with* its
   region-containment convexity — the one genuinely region-level fact whose
   proof needs the parity machinery applied to the extreme vertex, exposed as
   the design-sanctioned residue per §3 / Layer A3).

2. **`convex_vertex_empty_triangle_gives_ear`** (`4 ≤ n`) — convex `i` + empty
   adjacent triangle ⇒ `IsDiagonal P ρ (cyclicPrev i) (cyclicNext i)`. Built via
   `PolygonParity.isDiagonal_of_certificate`.

3. **`slide_last_vertex_gives_diagonal`** — convex `i` + slide-height-maximal
   enclosed `z ∈ verticesInAdjacentTriangle P i` ⇒ `IsDiagonal P ρ i z`. Same
   certificate route. (The finite maximum itself is
   `PolygonDiagonal.slide_last_vertex_exists`.)

4. **`exists_diagonal`** (`4 ≤ n`) — case split on
   `verticesInAdjacentTriangle P i = ∅`: empty ⇒ ear branch, nonempty ⇒ slide
   branch on the height-maximal vertex. Combines 1–3.

5. **`a3GeometryFacts_of_residues`** — packages all four into the
   `PolygonDiagonal.A3GeometryFacts` interface the cutting/triangulation layer
   consumes, from a single global `A3Residues` package.

## Proved unconditionally (not assumed)

- All convex-geometry plumbing: triangle-vertex membership
  (`mem_closedTri_left/mid/right`), `seg_subset_closedTri`,
  `openSegment_subset_closedTri`, and the engine
  `seg_subset_region_of_convex_aux` (a segment between two vertices of a convex
  vertex's adjacent triangle lies in the region, by convexity + `IsConvexVertex`).
- **The interior region witness is DERIVED, not assumed**: in both diagonal
  lemmas the midpoint of the relevant segment lies in the convex adjacent
  triangle (ear: base endpoints `q(prev), q(next)` are triangle corners; slide:
  `q i` is a corner and `q z` is in the triangle by membership), hence in the
  region. This is what makes the conditional structures **non-vacuous**.
- All `Fin n` non-adjacency bookkeeping for `4 ≤ n`:
  `cyclicPrev_ne_cyclicNext`, `not_cyclicAdjacent_prev_next`,
  `not_cyclicAdjacent_slide` (value-level `cyclicNext/cyclicPrev` analysis +
  `omega`), `vertexInTriangle_ne`.

## Sanctioned residues (explicit hypotheses, per the file-header discipline)

Mirroring `PolygonParity`'s §4 residue isolation, the genuinely *topological*
transversality content is taken as documented, non-vacuous hypotheses, each a
field of a residue structure whose type is the true geometric statement:

- `EarTransversality` / `SlideTransversality`: open-segment local constancy
  (`OpenSegmentRegionLocallyConstant`), open-segment boundary-freeness, and the
  boundary-only-at-endpoints clause — exactly the three clauses
  `isDiagonal_of_certificate` consumes. (Boundary-freeness from maximality in
  the slide case is the design's "where the pain lives" residue.)
- `ExtremeConvexResidue`: the extreme vertex + its convexity.
- `DiagonalTransversality` / `A3Residues`: branch-aware / global dispatchers that
  hand the right residue to whichever branch fires.

Non-vacuity is structural: every residue field is the genuine geometric
statement (true for a real strict simple polygon with a non-parallel ray), and
the derived interior witness / non-adjacency facts are proved, so none of the
conditional theorems collapse.

## Notes

- Stayed on branch `main`; no commits; no codex/OpenAI tooling; verified
  exclusively on uisai2 (never ran lake locally). I own only the new file.
- One small Mathlib-API point: `midpoint_mem_openSegment x y` is total (no
  `x ≠ y` needed) because Mathlib's `openSegment ℝ x x = {x}` is nonempty; the
  derived witness is genuinely in a nonempty open segment.
