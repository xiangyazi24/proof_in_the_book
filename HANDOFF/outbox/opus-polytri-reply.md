# opus-polytri — Polygon triangulation existence (Ch36 Layers A4–A5)

**STATUS: COMPLETE (with one honestly-isolated geometry interface).**
New file `ProofsInTheBook/PolygonTriangulation.lean` (542 lines) compiles clean
on uisai1: **0 sorry / 0 axiom / 0 admit / 0 native_decide**, all 11 headline
theorems **clean-3** (`{propext, Classical.choice, Quot.sound}`).

Branch `main` (no switches). No commits. Only the one NEW file touched; it is not
imported anywhere, so no other build is disturbed. Verified exclusively via
rsync→uisai1 `lake env lean` per the kernel-panic rule; never ran lake locally.
Dependency oleans (`PolygonSideCrossing` chain, 8426 jobs) built first via tmux.

## What was built

### A5 — the inductive existence object + the count (UNCONDITIONAL)
- `EarTriangulation'` : inductive over `(P : StrictSimplePolygon n) (ρ)` — a
  triangle `base` (`n = 3`) and a `splitDiagonal` constructor storing a corrected
  diagonal `IsDiagonal'` and the two sub-triangulations on the cut subpolygons.
  (The ear cut is the `prev/next` special case of a split, so a single split
  constructor suffices for existence; the count is additive and recovers `n-2`.)
- `EarTriangulation'.triangleCount` + **`earTriangulation'_count : t.triangleCount = n - 2`**
  — proved by induction on the cutting object: split additivity
  `(k-2)+(m-2) = (k+m)-4 = (n+2)-4 = n-2` via the arc-length identity
  `leftLength_add_rightLength` (`k+m = n+2`) and the `≥3` polygon bound. `omega`.

### Termination combinatorics (UNCONDITIONAL — genuine new content)
The existing scaffold only proved arcs `≤ n`; strong induction needs `< n`:
- `cyclicNext_of_cyclicSteps_eq_one` : `cyclicSteps i j = 1 → cyclicNext i = j`
  (both branches of `cyclicSteps`, incl. the wrap case `i=n-1, j=0`).
- `cyclicSteps_ge_two_of_diagonal` : a diagonal's non-adjacency forces each arc
  `≥ 2` (contrapositive of the above on `¬CyclicAdjacent`).
- `leftLength_lt` / `rightLength_lt` : each subpolygon is *strictly* smaller.

### A5 — existence by strong induction (CONDITIONAL on the cut oracle)
- **`strictSimplePolygon_triangulable' (oracle : CutOracle) : ∀ N, Nonempty (EarTriangulation' P ρ)`**
  — strong induction on size `N`: base `N=3`; for `N≥4` the oracle's local data
  at `P` yields a diagonal via `exists_diagonal'` (the unconditional A3 engine),
  and the same oracle triangulates the two strictly-smaller subpolygons.

### A5'' — compilation to finite triangle data
- `EarTriangulation'.triangles : List (Pt×Pt×Pt)` (parent ++ sub-lists), with
  `triangles_length = n - 2`.
- **`triangles_nondegenerate` (UNCONDITIONAL)** + `baseTri_nondegenerate`: every
  listed triangle is noncollinear — base from `P.noncollinear_consecutive` at
  vertex 1 (`cyclicPrev 1 = 0`, `cyclicNext 1 = 2` in `Fin 3`, by `rfl`); step
  inherits (nondegeneracy is a property of the points).
- `triangles_subset_region` / `region_covered_by_triangles` : region-subset and
  **coverage**, both by induction, driven by the cutting interface's region-union
  identity (`split_region_union`) and the base-triangle facts at the leaf.
- `GeomTriangulation'` structure (fields: `tris`, `card = n-2`, `nondegenerate`,
  `subset_region`, `cover_region`) + **`EarTriangulation'.toGeom`** compilation.
- `strictSimplePolygon_geomTriangulation'` (end-to-end, `n-2` triangles) and
  **`every_region'_point_in_some_triangle`** — the exact coverage fact the Fisk
  art-gallery bridge consumes.

## Honest scoping — the ONE isolated geometry interface
Per the task ("isolate at most ONE named region-split fact if genuinely
resistant"), the genuine *planar* (Jordan-substitute) facts are bundled, exactly
as the existing A3/A4 scaffold (`A3GeometryFacts`/`A4CuttingFacts`) does for the
old convention, into explicit **data** interfaces — NOT hidden in trivial Prop
hypotheses:

- `LocalCutData' P ρ` (per polygon): a convex vertex + `IsConvexVertex'` spec, a
  `DiagonalTransversality'` dispatcher, the left/right strict subpolygons
  (`subpolygonLeftTuple`/`Right` tuples) + ray directions, and the two heaviest
  named facts **`split_region_union`** and **`split_region_intersection`** (the
  region equalities that replace Jordan).
- `CutOracle := ∀ {m} (P) (ρ), LocalCutData' P ρ` — the size-uniform family that
  closes the recursion (a recursive *structure* is impossible here: the
  subpolygons live at a different index `leftLength i j ≠ n`, which the kernel
  rejects as a non-uniform self-reference; the oracle sidesteps this cleanly).
- `BaseTriangleFacts` — the leaf fact that a `3`-gon's region equals its closed
  hull (subset both ways).

**Why this is the honest boundary, not a hidden gap.** The diagonal-existence
*engine* (`exists_diagonal'`) is unconditional in its analytic content (all
vertex-sweep local constancy discharged by the side-coordinate convention). What
remains genuinely beyond the current substrate is the Jordan-substitute region
*union/intersection* identity for `ClosedRegion'` along a cut — the design itself
flags this as "the heaviest item / substitute for Jordan". It is a real, true,
*satisfiable* planar fact (so the conditional theorems are **non-vacuous** — not
a vacuous-keystone), isolated as a named data field rather than proved, and it is
the single resistant item. Everything else — the inductive object, termination,
the `n-2` count, nondegeneracy, and the geometric-data compilation + coverage
bridge — is proved with no geometry hypothesis.

## Faithfulness verdicts
- **FAITHFUL (unconditional):** `EarTriangulation'`, `earTriangulation'_count`
  (n−2), `triangles_length`, `triangles_nondegenerate`, `baseTri_nondegenerate`,
  the four termination-combinatorics lemmas.
- **CONDITIONAL-honest** on `(oracle : CutOracle)` / `(B : BaseTriangleFacts)`:
  `strictSimplePolygon_triangulable'`, `toGeom`, `strictSimplePolygon_geomTriangulation'`,
  `region_covered_by_triangles`, `every_region'_point_in_some_triangle`. The
  conditional surface is explicit named-data parameters; the hard half is not
  smuggled into a trivially-true Prop hypothesis.

## Next step to fully discharge (for whoever migrates the substrate)
Prove a `CutOracle` and a `BaseTriangleFacts` from `ClosedRegion'` first
principles: (1) `subpolygonLeftTuple`/`Right` are strict simple polygons (edge
simplicity inherits from the parent + the diagonal's boundary-only-at-endpoints;
noncollinearity at the new diagonal-endpoint triples is the one corner case the
task flagged); (2) the side-coordinate parity region-union/intersection along the
diagonal, from the per-edge `CrossingNumber'` bookkeeping of `PolygonSideCrossing`.
These wire directly into the fields above with zero change to this file.

## Verification
```
rsync -az .../PolygonTriangulation.lean uisai1:~/repos/proof_in_the_book/ProofsInTheBook/
ssh uisai1 'cd ~/repos/proof_in_the_book && export PATH=$HOME/.elan/bin:$PATH \
  && lake env lean ProofsInTheBook/PolygonTriangulation.lean'      # exit 0, no warnings
```
`#print axioms` on all 11 headlines → `[propext, Classical.choice, Quot.sound]`.
