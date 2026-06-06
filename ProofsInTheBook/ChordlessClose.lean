import ProofsInTheBook.PlanarMapFanFaces
import ProofsInTheBook.ThomassenInduction

/-!
# The chordless branch: structural fan fields discharged, residue isolated to the
  same genus-dependent boundary classification (Chapter 35)

The chordless branch of Thomassen's induction (`ThomassenInduction.thomassen_aux`,
chordless case) deletes the boundary neighbour `v0` of `p`, recurses on the strictly
smaller deleted map, and extends.  The deletion's planar (Jordan/Schoenflies) output is
the structure `FanSurgeryReconstruction hNT d0` (`PlanarMapFanSurgery.lean`), packaged
into the `ChordlessOracle.recon` field.  To make the headline
`nearTriangulation_five_colorable` **unconditional** the chordless branch must produce a
`FanSurgeryReconstruction` (and a `ChordlessOracle`) unconditionally for a chordless
boundary.

This file records, parallel to the chord side (`ChordContiguous.lean`), exactly how far
the proven fan/deletion machinery reaches and isolates the single residual field.

## What the fan machinery genuinely discharges (PROVED upstream, re-exported here)

For a boundary vertex fan `fan : BoundaryVertexFan hNT v0` at a chordless boundary, with
`d0` representing `v0` (`M.tail d0 = v0`), the **three dart-rotation surgery fields** of
`FanSurgeryReconstruction` are proved unconditionally from the fan and the
near-triangulation invariant:

* **`vertexQuotient`** — `deleteVertex_vertexQuotientEquiv fan htail0`
  (`PlanarMapFanFaces`): the surviving vertex `σ`-orbits are the old ones minus `⟦d0⟧`;
* **`connected`** — `deleteVertex_connected_of_fan fan htail0`
  (`PlanarMapFanConnectivity`): the deleted map stays connected (the fan path
  `x, z₁, …, z_t, w` keeps the neighbours joined);
* **`facesMerge`** — `deleteVertex_facesMerge_of_fan fan htail0 hmerge`
  (`PlanarMapFanFaces`): the faces incident with `v0` merge into one new outer face,
  *modulo* the single `φ`-seam-walk fact `DeleteVertexMergedFaceSingleOrbit`.

These are the chordless analogues of the chord side's proved disk core (genus-0
`IsSphereMap`, connectivity) — discharged, not assumed.  `fanSurgery_structural_fields`
below bundles them.

## What the fan machinery does NOT discharge (the single isolated residue)

`FanSurgeryReconstruction`'s remaining content is exactly `DeletedOuterBoundary hNT d0`
(`PlanarMapFanFaces`): the merged outer face, its boundary cycle, simplicity, length
bound, and — the lone genus-dependent field — **`inner_tri`** (every non-outer face of
the deleted map has `faceLen = 3`), together with the merged-orbit fact
`DeleteVertexMergedFaceSingleOrbit`.

The `inner_tri` field is the **same** discrete Jordan–Schoenflies content the chord side
isolates as `ChordContiguous.SideInnerTriangulation`: it asks that the surviving faces of
the deleted map are intact old inner triangles, which is the face-survival correspondence
the repository's `CutFaceLabel.lean` campaign **refuted inside the Lean kernel** (the
deletion's `φ`-orbits merge and split old faces; no genus-uniform orbit label of the
right cardinality exists — `CutFaceLabel.lean` lines 28–67).  `outerCycle`/`outer_simple`/
`outer_len_ge_three` are the boundary-cycle normalization of the merged face — the
chordless analogue of the chord side's side-map outer-cycle datum.

## The exact pinning (PROVED here)

`fanSurgeryReconstruction fan htail0 hmerge bdry` (`PlanarMapFanFaces`) assembles the full
`FanSurgeryReconstruction` from the fan, the merged-orbit fact `hmerge`, and the boundary
datum `bdry : DeletedOuterBoundary hNT d0`.  We re-export it as `chordlessRecon_of_bdry`
and confirm:

* **`fanSurgery_structural_fields`** — the three structural fields ARE unconditional from
  the fan (their producers, bundled);
* **`chordlessResidue_pins_recon`** — the assembled reconstruction's `inner_tri` IS the
  boundary datum's `inner_tri` (the residue field is genuinely used, not bypassed);
* **non-vacuity** — `DeletedOuterBoundary` is satisfiable from a deleted near-triangulation.

So the chordless residue is **exactly** `DeleteVertexMergedFaceSingleOrbit` (the `φ`-seam
walk) plus `DeletedOuterBoundary` (whose lone genus-dependent field is `inner_tri`) — the
same content as the chord side, isolated honestly and not fabricated (§3.3: no fake
deleted-map boundary cycle, no fake face-survival correspondence).

No `sorry` / `axiom` / `admit` / `native_decide`.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace ProofsInTheBook.ChordlessClose

open ProofsInTheBook.PlanarMap
open ProofsInTheBook.PlanarMap.CombMap
open ProofsInTheBook.PlanarMap.CombMap.NearTriangulation

universe u

variable {D : Type u} [Fintype D] [DecidableEq D] {M : CombMap D}
  {hNT : NearTriangulation M} {v0 : M.Vertex}

/-! ## Section 1.  The structural fan surgery fields (PROVED unconditionally from a fan)

The three dart-rotation fields of `FanSurgeryReconstruction` — `vertexQuotient`,
`connected`, `facesMerge` — are discharged from the boundary fan.  `facesMerge` needs the
single isolated `φ`-seam-walk fact `DeleteVertexMergedFaceSingleOrbit`; the other two are
fully unconditional.  We re-export the producers and bundle them. -/

/-- **The surviving vertex `σ`-orbit equivalence, unconditional from the fan.**  The
deleted map's vertex orbits are the old ones minus `⟦d0⟧` (`deleteVertex_vertexQuotientEquiv`). -/
noncomputable def chordless_vertexQuotient (fan : BoundaryVertexFan hNT v0) {d0 : D}
    (htail0 : M.tail d0 = v0) :
    Quotient (cycleSetoid (M.deleteVertex d0).σ) ≃
      {Q : Quotient (cycleSetoid M.σ) // Q ≠ Quotient.mk (cycleSetoid M.σ) d0} :=
  deleteVertex_vertexQuotientEquiv fan htail0

/-- **The deleted map is connected, unconditional from the fan.**
(`deleteVertex_connected_of_fan`.) -/
theorem chordless_connected (fan : BoundaryVertexFan hNT v0) {d0 : D}
    (htail0 : M.tail d0 = v0) :
    (M.deleteVertex d0).Connected :=
  deleteVertex_connected_of_fan fan htail0

/-- **The faces incident with `v0` merge into one outer face**, given the single isolated
`φ`-seam-walk fact `DeleteVertexMergedFaceSingleOrbit` (`deleteVertex_facesMerge_of_fan`). -/
theorem chordless_facesMerge (fan : BoundaryVertexFan hNT v0) {d0 : D}
    (htail0 : M.tail d0 = v0) (hmerge : DeleteVertexMergedFaceSingleOrbit M d0) :
    M.DeleteVertexFacesMerge d0 :=
  deleteVertex_facesMerge_of_fan fan htail0 hmerge

/-- **The two structural Prop-valued surgery fields, bundled.**  Given the fan and the
single `φ`-seam-walk fact, connectivity and face-merge of the deleted map both hold — the
chordless analogue of the chord side's proved disk core (genus-0 `IsSphereMap` +
connectivity).  (The vertex-quotient equivalence is data, exported separately as
`chordless_vertexQuotient`.)  These are NOT in the residue. -/
theorem fanSurgery_structural_fields (fan : BoundaryVertexFan hNT v0) {d0 : D}
    (htail0 : M.tail d0 = v0) (hmerge : DeleteVertexMergedFaceSingleOrbit M d0) :
    (M.deleteVertex d0).Connected ∧ M.DeleteVertexFacesMerge d0 :=
  ⟨chordless_connected fan htail0, chordless_facesMerge fan htail0 hmerge⟩

/-! ## Section 2.  The reconstruction assembled, residue pinned to `DeletedOuterBoundary`

`fanSurgeryReconstruction fan htail0 hmerge bdry` (`PlanarMapFanFaces`) assembles the full
`FanSurgeryReconstruction` from the fan + the merged-orbit fact + the boundary datum
`bdry : DeletedOuterBoundary`.  We re-export it and pin the residue: every field beyond
`bdry`'s comes from the fan (Section 1); `bdry` supplies exactly the merged outer face,
its boundary cycle (simple, length `≥ 3`), and the lone genus-dependent `inner_tri`. -/

/-- **The chordless reconstruction, assembled from the fan + the residue datum.**  This is
`fanSurgeryReconstruction`: the three structural fields come from the fan, the boundary
data (`bdry`) supplies the merged outer face, its boundary cycle, and `inner_tri`. -/
noncomputable def chordlessRecon_of_bdry (fan : BoundaryVertexFan hNT v0) {d0 : D}
    (htail0 : M.tail d0 = v0) (hmerge : DeleteVertexMergedFaceSingleOrbit M d0)
    (bdry : DeletedOuterBoundary hNT d0) :
    FanSurgeryReconstruction hNT d0 :=
  fanSurgeryReconstruction fan htail0 hmerge bdry

/-- **The residue genuinely supplies `inner_tri`** (no-bypass check).  The assembled
reconstruction's `inner_tri` field IS the boundary datum's `inner_tri` — so the lone
genus-dependent field is taken from the residue `bdry`, not synthesized.  This pins the
chordless residue to exactly `DeletedOuterBoundary` (and the merged-orbit fact). -/
theorem chordlessResidue_pins_recon (fan : BoundaryVertexFan hNT v0) {d0 : D}
    (htail0 : M.tail d0 = v0) (hmerge : DeleteVertexMergedFaceSingleOrbit M d0)
    (bdry : DeletedOuterBoundary hNT d0) :
    (chordlessRecon_of_bdry fan htail0 hmerge bdry).inner_tri = bdry.inner_tri :=
  rfl

/-- **The assembled reconstruction's outer cycle IS the residue's** (no-bypass check). -/
theorem chordlessRecon_outerCycle_eq (fan : BoundaryVertexFan hNT v0) {d0 : D}
    (htail0 : M.tail d0 = v0) (hmerge : DeleteVertexMergedFaceSingleOrbit M d0)
    (bdry : DeletedOuterBoundary hNT d0) :
    (chordlessRecon_of_bdry fan htail0 hmerge bdry).outerCycle = bdry.outerCycle :=
  rfl

/-! ## Section 3.  Non-vacuity of the chordless residue (the §3.3 satisfiability obligation)

`DeletedOuterBoundary` is not an unsatisfiable premise: any genuine near-triangulation
structure on the deleted map supplies it (its outer face, outer cycle, and `inner_tri`).
So the residue is inhabited exactly when the deletion is a near-triangulation — the lone
content separating the proved structural fan fields from the full reconstruction, not a
vacuous conditional / hidden `False`. -/

/-- **`DeletedOuterBoundary` is satisfiable from a deleted near-triangulation** (non-vacuity).
A `NearTriangulation (M.deleteVertex d0)` projects onto a `DeletedOuterBoundary` (its
boundary fields), so the chordless residue is inhabited whenever the deletion is a genuine
near-triangulation. -/
def deletedOuterBoundary_of_nearTriangulation {d0 : D}
    (N : NearTriangulation (M.deleteVertex d0)) :
    DeletedOuterBoundary hNT d0 where
  outerFace := N.outerFace
  outerCycle := N.outerCycle
  outer_simple := N.outer_simple
  outer_len_ge_three := N.outer_len
  inner_tri := N.inner_tri

end ProofsInTheBook.ChordlessClose

/-! ## Axiom audit -/

#print axioms ProofsInTheBook.ChordlessClose.chordless_vertexQuotient
#print axioms ProofsInTheBook.ChordlessClose.chordless_connected
#print axioms ProofsInTheBook.ChordlessClose.chordless_facesMerge
#print axioms ProofsInTheBook.ChordlessClose.fanSurgery_structural_fields
#print axioms ProofsInTheBook.ChordlessClose.chordlessRecon_of_bdry
#print axioms ProofsInTheBook.ChordlessClose.chordlessResidue_pins_recon
#print axioms ProofsInTheBook.ChordlessClose.chordlessRecon_outerCycle_eq
#print axioms ProofsInTheBook.ChordlessClose.deletedOuterBoundary_of_nearTriangulation
