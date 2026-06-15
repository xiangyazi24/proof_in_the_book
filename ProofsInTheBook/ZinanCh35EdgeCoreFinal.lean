import ProofsInTheBook.ZinanCh35BankCount
import ProofsInTheBook.ZinanCh35StarConn
import ProofsInTheBook.ZinanCh35Schoenflies2

/-!
# `ZinanCh35EdgeCoreFinal` — the coverage-atom cascade (Chapter 35, Five Color Theorem).

With the coverage atom `numComp (OuterDualStep hNT) = 2` discharged unconditionally
(`ZinanCh35BankCount.outerDualNumCompTwo_holds`, route-B swap-peeling) and the vertex Schoenflies
bridge `SideRegionInterChordEnds` discharged unconditionally (`ZinanCh35StarConn.sideRegionInterChordEnds_holds`,
σ-star connectivity), the two `edge_core` bridges are now BOTH proven.  This file assembles them:
`BoundedFacePartition` and `OuterDartArc₁` become UNCONDITIONAL (modulo the separately-dischargeable
`data.Separates`).
-/

namespace ProofsInTheBook.ZinanCh35EdgeCoreFinal

open ProofsInTheBook.PlanarMap
open ProofsInTheBook.PlanarMap.CombMap
open ProofsInTheBook.PlanarMap.CombMap.NearTriangulation
open ProofsInTheBook.ChordReconClose
open ProofsInTheBook.ZinanCh35EdgeCore
open ProofsInTheBook.ZinanCh35OuterCount
open ProofsInTheBook.ZinanCh35BankCount
open ProofsInTheBook.ZinanCh35StarConn
open ProofsInTheBook.ZinanCh35Schoenflies
open ProofsInTheBook.ZinanCh35Schoenflies2

universe u

variable {D : Type u} [Fintype D] [DecidableEq D] {M : CombMap D}
  {hNT : NearTriangulation M} {u v : M.Vertex}

/-- **`BoundedFacePartition` is UNCONDITIONAL** — the coverage atom is discharged
(`outerDualNumCompTwo_holds`). -/
theorem boundedFacePartition_uncond (data : hNT.ChordSplitData u v) :
    BoundedFacePartition data :=
  boundedFacePartition_via_numComp data (outerDualNumCompTwo_holds hNT)

/-- **`OuterDartArc₁` is UNCONDITIONAL** (given the chord split + `Separates`): both its bridges
(`BoundedFacePartition` from the coverage atom, `SideRegionInterChordEnds` from σ-star) are proven. -/
theorem outerDartArc₁_uncond (data : hNT.ChordSplitData u v) (hsep : data.Separates) :
    OuterDartArc₁ data :=
  outerDartArc₁_holds data hsep (boundedFacePartition_uncond data)
    (sideRegionInterChordEnds_holds data hsep)

/-- **The corrected bounded `edge_core` is UNCONDITIONAL** (given the chord split + `Separates`):
both bridges are now proven, so the formerly-residual `edge_core` field of `Side₁StarConfinement`
is dischargeable.  Stated via the landed `edge_core_holds` shape. -/
theorem edge_core_uncond (data : hNT.ChordSplitData u v) (hsep : data.Separates)
    {e : D} (hchord : M.dartEdge e ≠ s(u, v)) (houter : M.dartFace e ≠ hNT.outerFace)
    (htail : M.tail e ∈ sideRegion₁ data) (hhead : M.head e ∈ sideRegion₁ data) :
    M.dartFace e ∈ data.side₁ :=
  edge_core_holds data hsep (boundedFacePartition_uncond data)
    (sideRegionInterChordEnds_holds data hsep) hchord houter htail hhead

end ProofsInTheBook.ZinanCh35EdgeCoreFinal
