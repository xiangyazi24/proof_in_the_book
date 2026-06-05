# opus-fanexist reply — Chapter 35 boundary-vertex fan EXISTENCE

## Status: CLOSED to the isolated orientation/Jordan residue. New file
`ProofsInTheBook/PlanarMapFanExistence.lean` (456 lines, 0 sorry / 0 axiom /
clean-3). Verified exclusively on uisai1:
`lake build ProofsInTheBook.PlanarMapFanExistence` → 8434 jobs OK;
`lake env lean` on the file → no errors/warnings/sorry.

Imports `ProofsInTheBook.PlanarMapOuterArc` (top of the chain, so it transitively
sees the whole fan layer + the deletion assembly). **NOT yet wired into
`ProofsInTheBook.lean`** (one-writer rule): add
`import ProofsInTheBook.PlanarMapFanExistence` to the import graph + `Audit.lean`.

## What is proved (all clean-3: [propext, Classical.choice, Quot.sound])

The keystone: **construct the boundary-vertex fan from the bare near-triangulation
plus the single isolated orientation/Jordan datum**.

1. **`vertexDartList` + its orbit calculus** — the explicit `σ`-rotation list at a
   vertex (`M.σ.toList v`), mirror of the existing `faceDartList` for `φ`. Proved:
   `_length_pos`, `_getElem`, `_head`, `_nodup`, `mem_vertexDartList_iff`,
   `_toFinset` (= `vertexDarts`), `_tail`, `_pow_length`, and the crux
   **`vertexDartList_consecutive_sigma`** (the cyclic-next dart is the `σ`-image —
   exact mirror of `faceDartList_consecutive_phi`).

2. **`neighborRotationOrderOfVertexDartList`** — the ENTIRE `NeighborRotationOrder`
   certificate (`darts_nodup`, `darts_nonempty`, `tails_eq`, `heads_eq`,
   `consecutive_sigma`) built constructively from the `σ`-rotation list. This is the
   real new orbit-algebra content; `rotation_order` is no longer assumed anywhere.

3. **`fanTriangleOfSpoke`** — a `FanTriangle hNT v0 (head d) (head (φ d))` from any
   inner spoke `d` at `v0`, via `inner_face_isFaceTriangle`.

4. **`head_injOn_sameCycle` + `vertexDartList_heads_nodup`** — the fan path is simple
   from graph **simplicity alone** (two distinct spokes at `v0` sharing a head would
   be parallel edges / a loop). This discharges the `path_nodup_of_chordless` fan
   field *unconditionally* (no chordless hypothesis needed).

5. **`FanIncidenceData`** — the single isolated planar residue (see below).

6. **`boundaryVertexFan_of_incidenceData` / `boundaryVertexFan_exists`** — the fan is
   assembled field-by-field and `Nonempty (BoundaryVertexFan hNT v0)` is produced.

7. **`fan_first_spoke_head`** — construction byproduct: the first fan endpoint
   `x = M.head d0`, i.e. the rooting spoke `d0` is the extreme fan spoke landing on
   the first outer neighbour — the dart-level extreme-spoke/outer-cycle tie that the
   `MergedOuterArcData` seam reconnection consumes.

8. **`deleteBoundaryVertex_nearTriangulation_of_incidenceData`**,
   `deleteBoundaryVertex_smaller_of_incidenceData`,
   `deleteBoundaryVertex_inductiveStep_of_incidenceData` — the fan (now
   *constructed*, not assumed) fed into the already-proven
   `deleteBoundaryVertex_nearTriangulation_of_outerArc`, giving the deleted
   near-triangulation, the strict vertex decrease, and the `1 ≤ t` inductive step.
   The only remaining inputs are the two residues the chain *already* isolates:
   `MergedOuterArcData` (the seam tie) and `DeletedOuterBoundary` (the merged
   boundary cycle).

## The single isolated field — and the orientation wall (honest)

The fields fed by `FanIncidenceData` are: the path decomposition (`x, interior, w`)
with `heads_eq` tying it to the `σ`-rotation head list, the three boundary-vertex
facts, `incident_faces_exact`, and the two genuinely chordless/Jordan facts
(`interior_not_boundary_of_chordless`, `empty_iff_base_triangle_of_chordless`).

**Why `incident_faces_exact` is genuinely isolated (the orientation wall).** I
fixed conventions by computing the tetrahedron explicitly (trace in the module
docstring). The handedness-independent orbit identity is
`face(spoke d) = (v0, head d, head (σ⁻¹ d))` in `φ`-order; so the face between two
`σ`-consecutive spokes `(s_i, s_{i+1})` is `face(s_{i+1}) = (v0, head s_{i+1},
head s_i)`. But `consecutive_sigma` forces the rotation darts `σ`-forward and
`heads_eq` forces the path `= darts.map head` (forward), so a forward path pair is
`(head s_i, head s_{i+1})` while the genuine triangle is the **reverse** labelling
`FanTriangle v0 (head s_{i+1}) (head s_i)`. The `φ`-forward `FanTriangle` cannot be
re-oriented (a triangular face has one `φ`-orientation), and the rotation list
cannot be reversed without breaking `consecutive_sigma`. Reconciling all three is
exactly the planar (Jordan) orientation fact — which side of `v0`'s rotation the
deleted boundary lies on, depending on embedding handedness relative to the chosen
boundary face — and is **not** an orbit-algebraic consequence of `σ, α, φ`. I
isolate precisely this as `incident_faces_exact` inside `FanIncidenceData`,
following the chain's established discipline (`hNT.outerCycle`, `MergedOuterArcData`,
`DeletedOuterBoundary` are all isolated Jordan data the same way).

## Faithfulness self-audit (Group C)

- **Not the goal in disguise / not vacuous.** `FanIncidenceData` is satisfiable on
  any genuine chordless boundary-vertex deletion — the tetrahedron `t = 1` (module
  docstring trace) gives a concrete witness. It is strictly the *orientation +
  Jordan* residue: the entire `NeighborRotationOrder` and the path-simplicity field
  are **derived** (items 1, 2, 4), not assumed.
- **No banking.** `rotation_order` and `path_nodup` carry real new orbit-algebra /
  simplicity proofs (~200 lines); they are not re-wrappers.
- **`#print axioms`** on `boundaryVertexFan_exists`, `boundaryVertexFan_of_incidenceData`,
  `fan_first_spoke_head`, `neighborRotationOrderOfVertexDartList`, and the three
  deletion theorems → all `[propext, Classical.choice, Quot.sound]`.
- Verdict on the headline `boundaryVertexFan_exists`: **CONDITIONAL-honest** — the
  fan is constructed unconditionally except for the isolated planar
  `incident_faces_exact` (+ the two chordless/Jordan fan facts), which are bundled
  in `FanIncidenceData` exactly as the rest of the chain isolates its Jordan data.

## What remains to make the chain fully unconditional

Discharging `incident_faces_exact` (the orientation bijection) and the two
chordless fields from a stronger `NearTriangulation`/embedding invariant that pins
the boundary face on a definite side of every boundary vertex's rotation. That is
the same planar-orientation input the whole boundary layer treats as data; this
file reduces the fan's consumption of it to the minimal `FanIncidenceData` and
discharges all the surrounding orbit algebra.

## Verification commands run (uisai1 only)
```
lake build ProofsInTheBook.PlanarMapFanExistence     # 8434 jobs, OK
lake env lean ProofsInTheBook/PlanarMapFanExistence.lean   # no errors/warnings/sorry
#print axioms (7 theorems above)                     # all clean-3
```
