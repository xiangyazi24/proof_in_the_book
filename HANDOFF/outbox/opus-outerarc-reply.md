# opus-outerarc reply — Chapter 35 φ-level outer-arc reconnection

## Status: CLOSED to the isolated Jordan residue. New file
`ProofsInTheBook/PlanarMapOuterArc.lean` (233 lines, 0 sorry / 0 axiom / clean-3).
Verified exclusively on uisai1 (`lake build ProofsInTheBook.PlanarMapOuterArc`
→ 8433 jobs OK; `lake env lean` on the file → no errors/warnings/sorry).

Imports `ProofsInTheBook.PlanarMapFanMergedOrbit` +
`ProofsInTheBook.PlanarMapDeletedBoundary`. **NOT yet wired into
`ProofsInTheBook.lean`** (one writer; the import-graph edit — adding
`import ProofsInTheBook.PlanarMapOuterArc` after line 55 — is left to you).

## What is proved

The seam analysis confirmed the residue is genuinely the planar (Jordan) tie that
the `BoundaryVertexFan` certificate does not expose. I isolated **exactly** that
tie as the data structure `MergedOuterArcData M d0 r outerFace` and proved
everything downstream of it with the already-existing `φ'` calculus — no new core
mathematics, no axiom.

The decisive simplification over the handoff's two-bridge picture: only **one**
seam jump is needed. The triangle backbone theorem already links every `d1_i` to
the reference `r = d1_0` independently, so to attach the *entire* surviving outer
arc it suffices that the arc's single exit survivor `o_pre` reconnects to `r`.
Hence `MergedOuterArcData` carries just:

* `exit` (= `o_pre`, the last survivor of the contiguous outer arc) with
  `exit_face : dartFace exit = outerFace`;
* `exit_next_deleted : M.φ exit ∈ deleteVertexSet d0` (its successor `bin`, head
  `v0`, is deleted);
* `exit_jump : M.σ (M.φ exit) = r` (the Case-B closed-form successor lands on the
  head-triangle edge dart — the spoke identification `M.φ(M.α bin) = T_head.d1`);
* `arc_run` : every outer survivor reaches `exit` along a contiguous forward
  `M.φ`-run of survivors (the surviving outer arc is one `M.φ`-block).

Results (all clean-3):

1. `MergedOuterArcData.mergedOuterArcReconnects` — **unconditionally from the
   data**: walk the arc forward with `deleteVertex_phi_survRun_iterate`, then the
   single Case-B jump (`deleteVertex_phi_apply_of_next_deleted`) to `r`. This is
   exactly the isolated `MergedOuterArcReconnects` Prop.
2. `deleteVertexMergedFaceSingleOrbit_of_fan_of_outerArc` — feeds (1) into the
   fan-discharged `deleteVertexMergedFaceSingleOrbit_of_fan`, giving
   `DeleteVertexMergedFaceSingleOrbit M d0` conditional only on `MergedOuterArcData`
   for the head-triangle reference dart.
3. `DeletedMergedBoundaryCertificate.ofOuterArc` — assembles the full
   `DeletedMergedBoundaryCertificate` from the fan + outer-arc data + the
   normalized merged-boundary cycle `DeletedOuterBoundary`.
4. `deleteBoundaryVertex_nearTriangulation_of_outerArc` (+
   `deleteBoundaryVertex_smaller_of_outerArc`) — the fully-assembled inductive
   step: `NearTriangulation (M.deleteVertex d0)` and the strict vertex decrease,
   conditional on `MergedOuterArcData` and `DeletedOuterBoundary`.

## Faithfulness self-audit (Group C)

`MergedOuterArcData` is **not the goal in disguise**: it asserts no `SameCycle` /
single-orbit fact. It supplies (i) the surviving-outer-arc geometry (`arc_run`, a
statement about `M.φ`-runs + survival in the *original* map) and (ii) one spoke
equation (`exit_jump`). The single-orbit conclusion is *derived* by the proved
`φ'`-iterate calculus, not assumed.

It is **satisfiable / non-vacuous**: holds for any genuine chordless
boundary-vertex deletion (tetrahedron `t = 1`: the surviving outer arc is a single
dart, `exit` is that dart, `arc_run` reflexive with `k = 0`, `exit_jump` is the one
boundary-edge tie). It is **strictly weaker** than the merged-orbit goal — the
entire `t + 1`-triangle backbone is discharged unconditionally upstream; this data
constrains only the outer-face survivors via one reference dart.

It is the φ-level analogue of how `hNT.outerCycle` is data in `NearTriangulation`
and of the proved `DeleteVertexNeighborsConnected` residue: a Jordan-curve fact
about the position of `v0` on the outer boundary cycle, which the current
`BoundaryVertexFan` certificate exposes only as boundary *vertices* `x, w`, not as
the spoke *darts* tied to `hNT.outerCycle`.

## What remains to make the chain fully unconditional

`MergedOuterArcData` could be discharged from the fan if `BoundaryVertexFan` (or
`NearTriangulation`) gained a field tying the two extreme spoke darts
(`T_head.d0`, `T_t.d2`) to the two boundary darts of `v0` on `hNT.outerCycle`
(plus the contiguity of the surviving arc, immediate from `outer_simple` once the
two deleted darts are pinned as consecutive). That is the same single planar input
the handoff diagnosed; this file reduces its *consumption* to the minimal form
(`MergedOuterArcData`) and discharges all the orbit algebra around it. The other
chain residue, the normalized merged-boundary cycle `DeletedOuterBoundary` (its
`arcSplit` Jordan pairing), is unchanged and still an input — exactly as
`PlanarMapDeletedBoundary` already treats it.

## Verification commands run (uisai1 only)

```
lake build ProofsInTheBook.PlanarMapOuterArc          # 8433 jobs, OK
lake env lean ProofsInTheBook/PlanarMapOuterArc.lean   # no errors/warnings/sorry
#print axioms MergedOuterArcData.mergedOuterArcReconnects
#print axioms deleteVertexMergedFaceSingleOrbit_of_fan_of_outerArc
#print axioms deleteBoundaryVertex_nearTriangulation_of_outerArc
   # all → [propext, Classical.choice, Quot.sound]
```
