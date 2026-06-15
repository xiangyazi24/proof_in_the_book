import ProofsInTheBook.PlanarMapFanMergedOrbit
import ProofsInTheBook.PlanarMapDeletedBoundary

/-!
# The outer-arc reconnection of the Chapter 35 deletion chain (φ-level)

This file closes the last residue of the boundary-vertex deletion merged-orbit
fact: the predicate `MergedOuterArcReconnects` isolated in
`PlanarMapFanMergedOrbit`, which asserts that every surviving dart on the **old
outer face** is `φ'`-`SameCycle` to a fixed fan-triangle edge dart `r`.

## The geometry of the seam

The old outer face is the boundary cycle `hNT.outerCycle`; the deleted vertex
`v0 = M.tail d0` is one of its boundary vertices.  In the cyclic `M.φ`-orbit of
the outer face the vertex `v0` is touched by exactly two **consecutive** darts:
`bin` (head `v0`) and `bout = M.φ bin` (tail `v0`).  Both are deleted (they touch
`v0`); every other outer dart survives.  Removing the two consecutive deleted
darts leaves a **single contiguous surviving `M.φ`-arc**: the run

```
o_post = M.φ bout ,  M.φ o_post ,  … ,  o_pre   (with M.φ o_pre = bin)
```

Walking this arc with the survival-run iterate of `PlanarMapFanMergedOrbit`
(`deleteVertex_phi_survRun_iterate`), the deleted map's `φ'` agrees step-for-step
with `M.φ` (Case A) all along the arc; the only seam jump is from the last
survivor `o_pre`, whose `M.φ`-successor `bin` is deleted, so the closed-form
Case-B successor fires:

```
φ'(o_pre) = M.σ (M.φ o_pre) = M.σ bin = M.φ (M.α bin).
```

Because `M.head bin = v0`, the reverse dart `M.α bin` is a spoke at `v0`, and the
genuinely planar (Jordan) fact is that this spoke is the head triangle's `d0`, so
`M.φ (M.α bin) = T_head.d1 = r`.  This single seam reconnection — that the exit of
the surviving outer arc lands on the fan-triangle chain — together with the
contiguity of the surviving arc, is the irreducible planar residue that the
orbit-algebra of the fan layer does not expose.  We isolate it as the data
structure `MergedOuterArcData` (the `φ`-level analogue of how `hNT.outerCycle`
itself is data: a Jordan-curve fact, not an orbit-algebraic consequence), and
prove `MergedOuterArcReconnects` from it using only the already-proved `φ'`
calculus.

## What is proved here, and what is isolated

* `MergedOuterArcData.mergedOuterArcReconnects` — *unconditionally from the data*:
  the survival-run walk plus the one Case-B seam jump give
  `MergedOuterArcReconnects` (no further planar input).
* `deleteVertexMergedFaceSingleOrbit_of_fan_of_outerArc` — the merged-orbit fact
  `DeleteVertexMergedFaceSingleOrbit M d0`, conditional only on a
  `MergedOuterArcData` for the head-triangle reference dart (the
  `t + 1`-triangle backbone is discharged unconditionally upstream).
* `DeletedMergedBoundaryCertificate.ofOuterArc` and
  `deleteBoundaryVertex_nearTriangulation_of_outerArc` — the assembly into the
  full `FanSurgeryReconstruction` / deleted near-triangulation, conditional on the
  `MergedOuterArcData` and the normalized merged-boundary-cycle data
  (`DeletedOuterBoundary`).

`MergedOuterArcData` is faithful: it is not the goal in disguise (it supplies the
arc geometry and one spoke identification, from which the *single-orbit* statement
is derived by the proved `φ'`-iterate calculus, not asserted), and it is
satisfiable on any genuine chordless boundary-vertex deletion (e.g. the
tetrahedron `t = 1`, where the surviving outer arc is a single dart).
-/

namespace ProofsInTheBook.PlanarMap

open Equiv

namespace CombMap

variable {D : Type*} [Fintype D] [DecidableEq D]

namespace NearTriangulation

variable {M : CombMap D} {hNT : NearTriangulation M} {v0 : M.Vertex}

/-! ## The outer-arc data: the isolated Jordan residue along the merge seam

`MergedOuterArcData M d0 r outerFace` packages exactly the planar facts about the
old outer face that the orbit-algebra of the fan layer does not produce:

* `exit` — the *last* surviving dart of the contiguous surviving outer arc (the
  survivor `o_pre` whose `M.φ`-successor is the deleted in-boundary dart `bin`);
* `exit_face` — `exit` lies on the old outer face;
* `exit_next_deleted` — its `M.φ`-successor (`bin`) is deleted (touches `v0`);
* `exit_jump` — the Case-B closed-form successor `M.σ (M.φ exit)` is the
  reference fan-triangle edge dart `r` (the seam reconnection into the chain);
* `arc_run` — every surviving outer dart reaches `exit` along a contiguous forward
  `M.φ`-run of survivors (the surviving arc is one `M.φ`-block).

The last field is the contiguity of the surviving arc; the third and fourth are
the boundary-edge / spoke-identification facts.  All are Jordan-curve facts about
the position of `v0` on the outer boundary cycle, none is the merged-orbit goal,
and the whole bundle is satisfiable on the tetrahedron. -/
structure MergedOuterArcData (M : CombMap D) (d0 : D)
    (r : {d : D // d ∉ M.deleteVertexSet d0}) (outerFace : M.Face) where
  /-- The exit survivor `o_pre`: the last surviving dart of the outer arc. -/
  exit : {d : D // d ∉ M.deleteVertexSet d0}
  /-- The exit dart lies on the old outer face. -/
  exit_face : M.dartFace exit.1 = outerFace
  /-- Its immediate `M.φ`-successor (the in-boundary dart `bin`) is deleted. -/
  exit_next_deleted : M.φ exit.1 ∈ M.deleteVertexSet d0
  /-- The Case-B closed-form successor of `exit` is the reference triangle dart
  `r`: the seam reconnection from the outer arc into the fan-triangle chain. -/
  exit_jump : M.σ (M.φ exit.1) = r.1
  /-- Every surviving outer dart reaches `exit` along a contiguous forward
  `M.φ`-run of survivors (the surviving outer arc is one `M.φ`-block). -/
  arc_run : ∀ x : {d : D // d ∉ M.deleteVertexSet d0}, M.dartFace x.1 = outerFace →
    ∃ k : ℕ, (∀ j ≤ k, (M.φ ^ j) x.1 ∉ M.deleteVertexSet d0) ∧
      (M.φ ^ k) x.1 = exit.1

namespace MergedOuterArcData

variable {d0 : D} {r : {d : D // d ∉ M.deleteVertexSet d0}} {outerFace : M.Face}

/-- The `φ'`-successor of the exit survivor is the reference dart `r`: the single
Case-B seam jump from the surviving outer arc into the fan-triangle chain. -/
lemma phi'_exit (data : MergedOuterArcData M d0 r outerFace) :
    ((M.deleteVertex d0).φ data.exit : D) = r.1 := by
  have hsurv : M.σ (M.φ data.exit.1) ∉ M.deleteVertexSet d0 := by
    rw [data.exit_jump]; exact r.2
  rw [deleteVertex_phi_apply_of_next_deleted M d0 data.exit
      data.exit_next_deleted hsurv, data.exit_jump]

/-- The exit survivor is in the `φ'`-cycle of the reference dart `r`. -/
lemma sameCycle_exit (data : MergedOuterArcData M d0 r outerFace) :
    (M.deleteVertex d0).φ.SameCycle r data.exit := by
  have hexit_r : (M.deleteVertex d0).φ.SameCycle data.exit r := by
    refine ⟨1, ?_⟩
    apply Subtype.ext
    rw [zpow_one]
    exact data.phi'_exit
  exact hexit_r.symm

/-- **The outer-arc reconnection from the data.**  Every surviving dart on the old
outer face is `φ'`-`SameCycle` to the reference dart `r`: walk the contiguous
surviving arc forward with `deleteVertex_phi_survRun_iterate` to the exit
survivor, then take the single Case-B seam jump to `r`.  No further planar input
is consumed — all `φ'` machinery is the already-proved
`PlanarMapFanMergedOrbit` calculus. -/
theorem mergedOuterArcReconnects (data : MergedOuterArcData M d0 r outerFace) :
    MergedOuterArcReconnects M d0 r outerFace := by
  intro x hx
  obtain ⟨k, hrun, hk⟩ := data.arc_run x hx
  -- x reaches data.exit along the surviving arc.
  have hxexit : (M.deleteVertex d0).φ.SameCycle x data.exit :=
    deleteVertex_phi_sameCycle_of_survRun M d0 x data.exit k hrun hk
  -- r ~ exit (seam jump) and x ~ exit (arc run); compose to r ~ x.
  exact data.sameCycle_exit.trans hxexit.symm

end MergedOuterArcData

/-! ## The merged-face single-orbit fact from the outer-arc data

Plugging the outer-arc reconnection into the fan-discharged backbone theorem
`deleteVertexMergedFaceSingleOrbit_of_fan` closes
`DeleteVertexMergedFaceSingleOrbit M d0`, conditional only on a
`MergedOuterArcData` for the head-triangle reference dart. -/

/-- **The merged-face single-orbit fact, conditional on the outer-arc data.**
Given the boundary fan at `v0` and, for the head-triangle reference dart, the
outer-arc data, all surviving `v0`-incident darts lie in one `φ'`-cycle. -/
theorem deleteVertexMergedFaceSingleOrbit_of_fan_of_outerArc
    (fan : BoundaryVertexFan hNT v0) (hchord : BoundaryChordless hNT.outerCycle)
    {d0 : D} (htail0 : M.tail d0 = v0)
    (hdata : ∀ (r : {d : D // d ∉ M.deleteVertexSet d0}),
      (∃ (a b : M.Vertex) (T : FanTriangle hNT v0 b a)
        (_hp : (a, b) ∈ consecutivePairs fan.path), r.1 = T.d1) →
      MergedOuterArcData M d0 r hNT.outerFace) :
    DeleteVertexMergedFaceSingleOrbit M d0 :=
  deleteVertexMergedFaceSingleOrbit_of_fan fan hchord htail0
    (fun r hr => (hdata r hr).mergedOuterArcReconnects)

/-! ## Assembly into the full reconstruction

With the merged-orbit fact discharged from the outer-arc data, the only remaining
input of `DeletedMergedBoundaryCertificate` is the normalized merged-boundary
cycle `DeletedOuterBoundary`.  We assemble the certificate and the deleted
near-triangulation conditional on both. -/

/-- **Assemble the merged-boundary certificate from the fan, the outer-arc data,
and the merged-boundary cycle.** -/
noncomputable def DeletedMergedBoundaryCertificate.ofOuterArc
    (fan : BoundaryVertexFan hNT v0) (hchord : BoundaryChordless hNT.outerCycle)
    {d0 : D} (htail0 : M.tail d0 = v0)
    (hdata : ∀ (r : {d : D // d ∉ M.deleteVertexSet d0}),
      (∃ (a b : M.Vertex) (T : FanTriangle hNT v0 b a)
        (_hp : (a, b) ∈ consecutivePairs fan.path), r.1 = T.d1) →
      MergedOuterArcData M d0 r hNT.outerFace)
    (boundary : DeletedOuterBoundary hNT d0) :
    DeletedMergedBoundaryCertificate hNT d0 where
  mergedOrbit :=
    deleteVertexMergedFaceSingleOrbit_of_fan_of_outerArc fan hchord htail0 hdata
  boundary := boundary

/-- **The deleted map is a near-triangulation, conditional on the outer-arc data
and the merged-boundary cycle.**  This is the fully-assembled inductive step of
the Chapter 35 boundary-vertex deletion, with the merged-orbit residue discharged
to the isolated `MergedOuterArcData` and the only remaining input being the
normalized merged-outer-boundary cycle `DeletedOuterBoundary`. -/
noncomputable def deleteBoundaryVertex_nearTriangulation_of_outerArc
    (fan : BoundaryVertexFan hNT v0) (hchord : BoundaryChordless hNT.outerCycle)
    {d0 : D} (htail0 : M.tail d0 = v0)
    (hdata : ∀ (r : {d : D // d ∉ M.deleteVertexSet d0}),
      (∃ (a b : M.Vertex) (T : FanTriangle hNT v0 b a)
        (_hp : (a, b) ∈ consecutivePairs fan.path), r.1 = T.d1) →
      MergedOuterArcData M d0 r hNT.outerFace)
    (boundary : DeletedOuterBoundary hNT d0) :
    NearTriangulation (M.deleteVertex d0) :=
  (DeletedMergedBoundaryCertificate.ofOuterArc fan hchord htail0 hdata
    boundary).nearTriangulation fan htail0

/-- **Strict vertex decrease for the outer-arc-conditional deletion.** -/
theorem deleteBoundaryVertex_smaller_of_outerArc
    (fan : BoundaryVertexFan hNT v0) (hchord : BoundaryChordless hNT.outerCycle)
    {d0 : D} (htail0 : M.tail d0 = v0)
    (hdata : ∀ (r : {d : D // d ∉ M.deleteVertexSet d0}),
      (∃ (a b : M.Vertex) (T : FanTriangle hNT v0 b a)
        (_hp : (a, b) ∈ consecutivePairs fan.path), r.1 = T.d1) →
      MergedOuterArcData M d0 r hNT.outerFace)
    (boundary : DeletedOuterBoundary hNT d0) :
    (M.deleteVertex d0).V = M.V - 1 :=
  (DeletedMergedBoundaryCertificate.ofOuterArc fan hchord htail0 hdata
    boundary).smaller fan htail0

end NearTriangulation

end CombMap

end ProofsInTheBook.PlanarMap
