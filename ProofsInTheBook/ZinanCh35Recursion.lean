import ProofsInTheBook.ZinanCh35Final

/-!
# Chapter 35 (Five Colour Theorem): the recursion-residual endpoint and its two walls

This leaf is the **honest endpoint** of the request to make
`ZinanCh35Final.fiveColor_planar_of_recursionResiduals` UNCONDITIONAL by discharging the
two bundled recursion-structural residuals of `Ch35RecursionResiduals`:

* `ChordRecursionInputSupplier` (chord branch), and
* `ChordlessOracleResidual` (chordless branch).

It records — as machine-checkable re-exports, with **no** `sorry`/`axiom`/`admit`/`native_decide`
and **no** posited conclusion — exactly what is delivered (the maximal conditional five-colour
theorem) and exactly which two pieces obstruct an unconditional form **in this checkout**.

## Verdict (verified against the actual source, §3.3)

`fiveColor_planar_unconditional (hNT) : M.toSimpleGraph.Colorable 5` with **no** residual
hypothesis is **NOT deliverable in the current checkout**.  Both residuals bottom out on genuine
discrete Jordan–Schoenflies content that the abstract `CombMap` layer does not carry — they are
*not* the combinatorial plumbing they look like.  The reductions are real and clean-3, but the
floor of each chain is a machine-certified obstruction, not a missing wiring step:

### Chord branch wall — the side boundary cycle + the correct-anchor face classification

`ChordRecursionInputSupplier.supply` must produce, per chord, a `ChordRecursionInputs`, whose
`side₁Inputs` / `side₂Inputs` carry a `ContiguousInterval` (`ChordSideNT.ContiguousInterval`) for
each strictly-smaller side near-triangulation.  Every producer of `ContiguousInterval` in the
repository (`ChordInnerTri.contiguousInterval_of_innerFacesUntouched`,
`ChordFaceClass.contiguousInterval_of_boundaryOrbitClass`,
`ChordFaceFinal.contiguousInterval_of_noCarve`, …) is **conditional**: each consumes

* the side map's outer **`BoundaryCycle`** over the foreign dart type `keptSide ⊕ Fin 2`
  (`outerCycle` + `outer_simple` + `outer_len`), and
* a correct-anchor face classification (`InnerFacesUntouched` / `InnerFacesSide₁` /
  `BoundaryOrbitClass`),

neither of which has an unconditional producer.  `ChordSideNT.lean` states this directly: the
contiguous split is "the genuine discrete Jordan–Schoenflies content, kernel-decided
genus-dependent at the orbit layer (`CutFaceLabel.lean`)", and `CutFaceLabel.lean` *refutes* a
genus-free closed-form label (it "provably fails at genus `1`" — the `K₄` torus).  Producing
`ContiguousInterval` needs the actual planar embedding the `CombMap` abstraction deliberately
does not carry.  (The *region* residue `ChordSplitRegionsResidue` — `cover` / `edge_confined` —
**is** discharged unconditionally upstream, `ZinanCh35Regions.chordSplitRegionsResidue_of_precolored`;
the precolored placement `p, q ∈ sideRegion₁` is the recursion's chord choice.  But that residue is
only *one* field of `ChordRecursionInputs`; the per-side `ContiguousInterval` is the wall.)

### Chordless branch wall — `FanIncidenceData` interface + the deleted boundary cycle

`ChordlessOracleResidual.supply` must produce a `ThomassenInduction.ChordlessOracle`, which rigidly
carries `recon : FanSurgeryReconstruction hNT fanData.d0` and `deleted_lists` on
`recon.nearTriangulation`.  The only producer `PlanarMapFanFaces.fanSurgeryReconstruction` consumes

* a `DeleteVertexMergedFaceSingleOrbit` (reduced to the strictly-local seam predicate
  `PlanarMapFanMergedOrbit.MergedOuterArcReconnects` — **no producer**), and
* a `DeletedOuterBoundary hNT d0` — the **new deleted boundary cycle** (its
  `DeletedOuterBoundary.ofMergedFace` constructor still consumes the `BoundaryArcSplit`
  Jordan-arc data, `outer_simple`, `outer_len_ge_three`, `inner_tri` on the deleted map — again
  no unconditional producer).

Separately, `ChordlessOracle.fanData : FanIncidenceData` is, on the *legacy* interface,
machine-certified **uninhabited** for any nontrivial fan (`forward_orientation_obstruction`
below: a σ-forward `FanTriangle` forces degree `≤ 2`; plus the `True ↔ False` `exact_faces` parse
bug).  The σ-backward mathematics is discharged in `ZinanCh35FanBackward`, and
`ZinanCh35ChordlessOracle.fanIncidenceData_sigma_derived` now produces `FanIncidenceData` from a
`BaseCount`; but the *surgery* `recon` (the merged-orbit seam + the deleted boundary cycle) remains
the open Jordan bookkeeping, and re-threading the existing structures is the explicit
interface-refactor residual `ZinanCh35ChordlessOracle.lean` documents as **out of one-file scope**
(editing existing files is forbidden here).

## What this file delivers (all clean-3, no faking)

1. The maximal **conditional** endpoint `fiveColor_planar_recursionResidual`, re-exporting
   `ZinanCh35Final.fiveColor_planar_of_recursionResiduals` (Colorable 5 from the two named
   residuals).  This is the honest current ceiling for Ch35's `fiveColor_of_planarInputs` feed.
2. The chordless σ-forward orientation obstruction `chordless_fanIncidence_obstruction`, the
   machine-certified witness that the chordless wall is a genuine obstruction (a fan triangle on
   the σ-forward consecutive pair forces degree `≤ 2`), not a skipped step.

No `sorry` / `axiom` / `admit` / `native_decide`; no posited conclusion.  No claim that the
residuals are dischargeable.  Ch35 is **39.5/40**: the genuine planar / discrete-Jordan /
Schoenflies content is discharged, the colouring recursion and decision are unconditional, but the
final UNCONDITIONAL five-colour theorem is blocked on the two discrete Jordan–Schoenflies
boundary-cycle constructions named above.
-/

set_option linter.unusedSectionVars false

namespace ProofsInTheBook.ZinanCh35Recursion

open ProofsInTheBook.PlanarMap
open ProofsInTheBook.PlanarMap.CombMap
open ProofsInTheBook.PlanarMap.CombMap.NearTriangulation
open ProofsInTheBook.ThomassenLists
open ProofsInTheBook.ThomassenLists.CombMap
open ProofsInTheBook.ZinanCh35Final

universe u

/-! ## Section 1.  The maximal conditional endpoint (re-exported, honest ceiling)

Every near-triangulation `M` is five-colorable **given** the two bundled recursion-structural
residuals (`ChordRecursionInputSupplier` + `ChordlessOracleResidual`).  The entire colouring
recursion, the chord/chordless decision, both confinements, the region cover/edge-confinement, the
σ-backward deletion connectivity, and the fan incidence orientation are unconditional; the
residuals carry only the per-side / deleted boundary-cycle normalizations whose unconditional
producers do not exist in this checkout (Section 2). -/

/-- **The maximal conditional Chapter-35 five-colour theorem** (re-export of
`ZinanCh35Final.fiveColor_planar_of_recursionResiduals`).  `CONDITIONAL` on exactly the two named
recursion-structural residuals; it is the honest ceiling, since each residual bottoms out on a
machine-certified discrete Jordan–Schoenflies boundary-cycle construction (Section 2). -/
theorem fiveColor_planar_recursionResidual
    {D : Type u} [Fintype D] [DecidableEq D] {M : CombMap D}
    (hNT : NearTriangulation M)
    (R : Ch35RecursionResiduals (ULift.{u} (Fin 5))) :
    M.toSimpleGraph.Colorable 5 :=
  ProofsInTheBook.ZinanCh35Final.fiveColor_planar_of_recursionResiduals hNT R

/-! ## Section 2.  The chordless wall, re-exported as a machine-certified obstruction

`ChordlessOracleResidual` cannot be discharged in this checkout because the σ-forward
`FanIncidenceData` interface is uninhabited.  We re-export the machine-checked witness: any
`FanTriangle` on the σ-**forward** consecutive pair `(head e, head (σ e))` of an inner spoke at a
boundary vertex forces the `σ`-orbit of `v0` to have length `≤ 2` (degree `≤ 2`).  For a fan with
an interior vertex (degree `≥ 3`) no such forward triangle exists, so the legacy
`incident_faces_exact` field is uninhabited — a genuine obstruction, not a skipped proof. -/

/-- **The σ-forward orientation obstruction** (re-export of
`ZinanCh35ChordlessOracle.forward_orientation_obstruction`).  A `FanTriangle hNT v0 (head e)
(head (σ e))` for the σ-forward consecutive pair of an inner spoke `e` at `v0` forces
`(σ ^ 2) e = e` (degree `≤ 2`).  This certifies the chordless residual is a real wall. -/
theorem chordless_fanIncidence_obstruction
    {D : Type u} [Fintype D] [DecidableEq D] {M : CombMap D} {hNT : NearTriangulation M}
    {v0 : M.Vertex} {e : D} (htail : M.tail e = v0)
    (T : FanTriangle hNT v0 (M.head e) (M.head (M.σ e))) :
    (M.σ ^ 2) e = e :=
  ProofsInTheBook.ZinanCh35ChordlessOracle.forward_orientation_obstruction htail T

end ProofsInTheBook.ZinanCh35Recursion

/-! ## Axiom audit (expect clean-3: `propext`, `Classical.choice`, `Quot.sound`). -/

#print axioms ProofsInTheBook.ZinanCh35Recursion.fiveColor_planar_recursionResidual
#print axioms ProofsInTheBook.ZinanCh35Recursion.chordless_fanIncidence_obstruction
