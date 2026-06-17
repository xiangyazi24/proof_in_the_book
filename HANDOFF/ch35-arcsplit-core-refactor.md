# Ch35 #0 — arcSplit core refactor (CONVERGED design, R1 pbook-Pro + pbook2-xhigh)

**Goal:** make `boundaryCycleOfFace` (and the side/deleted-map assemblers) DERIVE `arcSplit`
from `VertexNodup` instead of taking it as a parameter, so we can inhabit `Ch35RecursionResiduals`
and remove `arcSplit` from the residual surface. Unblocks ContiguousInterval / DeletedOuterBoundary.

**Both engines converged (R1) on Option C, staged "core + cached field". A and B rejected:**
- **A (move arcSplit stack up)** — DEAD: real import cycle `PlanarMapDeletedBoundary → PlanarMapFanFaces
  → … → PlanarMapBoundary`, and `ArcSplitUniversal → ZinanCh35BoundaryAssembler → PlanarMapDeletedBoundary`.
  Verified against files.
- **B (raw re-prove in one constructor)** — wrong abstraction, not reusable for side/deleted maps.

**Lean idiom (the unlock):** no self-field idiom exists; a self-referential `arcSplit` field is
genuinely recursive to Lean (fails termination; `partial` needs `Inhabited`). Correct idiom:
build the non-recursive **core** first, prove `arcSplit` from the core, then promote:
`let core := {…}; { toBoundaryCycleData := core, arcSplit := fun … => core.arcSplit_of_nodup hC … }`.

## Refactor steps (blast radius: 1 new file + ~5 edits, NOT repo-wide)

1. **`PlanarMapBoundary.lean`**: add `structure BoundaryCycleData M f` = all `BoundaryCycle` fields
   EXCEPT `arcSplit`. Make `BoundaryCycle extends BoundaryCycleData` (arcSplit the only own field).
   Add `BoundaryCycleData.{IsBoundaryVertex,IsBoundaryEdge,VertexNodup,length,darts_length_pos}`.
2. **New `PlanarMapBoundaryArcSplit.lean`** (imports ONLY `PlanarMapBoundary`): a **core-only**
   `DataDartArc` (mirror of `DartArc` over `BoundaryCycleData` — do NOT reuse `DartArc.lean`, it imports
   `SeamIncidence` and has 8 downstream users) + `mod_cover` (move up; pure ℕ) + core `cyclicDataDartArc`
   + `bpOfDataDartArc` + core `nonEdgeRuns` + `BoundaryCycleData.arcSplit_of_nodup`
   + `BoundaryCycleData.exists_pos_of_isBoundaryVertex`. Then
   `BoundaryCycleData.toBoundaryCycle (hC : VertexNodup) : BoundaryCycle` (promotion).
3. **`PlanarMapDeletedBoundary.lean`**: `boundaryCycleOfFace` takes `hnodup` (not `arcSplit`): build
   `boundaryCycleDataOfFace` core, then `.toBoundaryCycle (by simpa … using hnodup)`.
   `DeletedOuterBoundary.ofMergedFace` drops `arcSplit` param, passes `outer_simple`.
4. **`ZinanCh35BoundaryAssembler.lean`**: `nearTriangulation_of_explicit_boundary_classification`
   drops `arcSplit` param, passes `houter_simple`.
5. **`ZinanCh35ArcSplitUniversal.lean`**: `arcSplit_of_nodup C hC … := BoundaryCycleData.arcSplit_of_nodup C.toBoundaryCycleData hC …` (thin wrapper; keeps the public name).
6. **Call sites** of the two assemblers: delete the `arcSplit` argument. `two_arcs`/`chordSplitData`
   UNCHANGED (keep `arcSplit` as a cached field projection in first pass).

**Caveat (both engines):** this discharges ONLY `arcSplit`. The remaining Ch35 residuals
(side/deleted boundary `outer_simple`+`inner_tri`, pullback Thomassen lists, precolored placement,
deleted lists, reserved colours) still need construction — those are the #1–#6 parallel work.
