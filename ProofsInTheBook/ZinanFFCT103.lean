import ProofsInTheBook.ZinanFFCT97
import ProofsInTheBook.ZinanFFCT100
import ProofsInTheBook.ZinanFFCT101

/-!
# Ch13 wiring: proper-no-collision from the planar full-closure lemma + the opened-arm span

`planar_properRepeat_is_fullClosure` (FFCT101, UNCONDITIONAL): a planar chain with a
`PlanarLiftedTurnSpan` and global weak support whose vertex repeats at `r+2 ≤ s` must have
`r = 0 ∧ s = N-1` (full closure only).  The opened WBS arm's gnomonic image carries exactly that
data: the lifted turn span (`GnomonicSingleWind`, FFCT97, modulo the span-existence residue
`OpenedWBSPlanarLiftedTurnSpanExists`) and the global weak support
(`gnomonic_edge_support_nonneg` on the weakly-convex opened arm).  A *proper* cross-piece collision
(`0 < r ∨ s < n`) would force `r = 0 ∧ s = n` — impossible.  Hence
`ProperCrossPieceNoCollisionAtSup`, and through FFCT100, `SphericalArmMonotone`.

Chapter 13 is thereby reduced to the single residue `OpenedWBSPlanarLiftedTurnSpanExists`.
-/

open scoped RealInnerProductSpace NNReal
open ProofsInTheBook.SphericalKernel ProofsInTheBook.SphericalArm
open ProofsInTheBook.SphericalRotation
open ProofsInTheBook.SphericalSZInduction
open ProofsInTheBook.SphericalSZFinal
open ProofsInTheBook.SphericalGnomonic
open ProofsInTheBook.SphericalOpeningOutcome
open ProofsInTheBook.ZinanFFCT8
open ProofsInTheBook.ZinanFFCT45
open ProofsInTheBook.ZinanFFCT46
open ProofsInTheBook.ZinanFFCT47
open ProofsInTheBook.ZinanFFCT49
open ProofsInTheBook.ZinanFFCT78
open ProofsInTheBook.ZinanFFCT95
open ProofsInTheBook.ZinanFFCT97
open ProofsInTheBook.ZinanFFCT100
open ProofsInTheBook.ZinanFFCT101

namespace ProofsInTheBook.ZinanFFCT103

/-- **Proper cross-piece no-collision, modulo the opened-arm span residue.**  The opened WBS arm's
gnomonic image has a `PlanarLiftedTurnSpan` (FFCT97, via `hres`) and global weak support
(`gnomonic_edge_support_nonneg`); FFCT101 then forces any repeat to be the full closure `r=0 ∧ s=n`,
contradicting properness. -/
theorem properNoCollision_of_spanResidue
    (hres : OpenedWBSPlanarLiftedTurnSpanExists) :
    ProperCrossPieceNoCollisionAtSup := by
  intro n A B hA hB hside hangle k hkdef hstuck r s hr hs hrs hrK hKs hprop hcoll
  -- The gnomonic single-wind certificate for the opened arm.
  have cert : GnomonicSingleWind (openedWBS A B k) :=
    openedWBS_gnomonicSingleWind hres A B hA hB hside hangle k hkdef hstuck
  -- The opened arm is weakly convex (so its gnomonic edges have nonnegative support).
  obtain ⟨hka, hkt⟩ := SphericalOpeningOutcome.shortArcs_of_strict hA k
  have hwrap :
      ShortArc (openTail A (openingAxis k) (-(monitoredSupWBS A B k)) (Fin.last n))
        (openTail A (openingAxis k) (-(monitoredSupWBS A B k)) 0) :=
    ZinanFFCT47.openedWrapShortArc_at_supWBS hA hB hka hkt hkdef
  have hPweak : WeakConvexSphArm (openedWBS A B k) := by
    unfold openedWBS
    exact ZinanFFCT46.supportStuckWBS_weakConvex hA hB hka hkt hkdef hwrap
  -- Global weak support of the gnomonic image, with the certificate's hemisphere normal.
  have hsupp : ∀ i j : Fin (n + 1),
      0 ≤ det3 (gproj cert.h (openedWBS A B k i))
        (gproj cert.h (openedWBS A B k (i + 1))) (gproj cert.h (openedWBS A B k j)) :=
    fun i j => gnomonic_edge_support_nonneg hPweak.closed_convex cert.hpos i j
  -- The collision transports to the gnomonic image.
  have hQcoll :
      gproj cert.h (openedWBS A B k ⟨r, hr⟩) = gproj cert.h (openedWBS A B k ⟨s, hs⟩) := by
    rw [hcoll]
  -- FFCT101: the only repeat is the full closure r = 0 ∧ s = (n+1) - 1 = n.
  have hfull := planar_properRepeat_is_fullClosure cert.lifted hsupp hr hs hrs hQcoll
  obtain ⟨hr0, hsn⟩ := hfull
  -- Contradicts properness.
  rcases hprop with hrpos | hslt
  · omega
  · omega

/-- **Chapter 13 reduced to the opened-arm span residue.**  Composing with FFCT100, the spherical
arm-monotonicity follows from `OpenedWBSPlanarLiftedTurnSpanExists` alone. -/
theorem spherical_arm_mono_ch13_of_spanResidue
    (hres : OpenedWBSPlanarLiftedTurnSpanExists) :
    SphericalArmMonotone :=
  spherical_arm_mono_ch13_of_properNoCollision (properNoCollision_of_spanResidue hres)

end ProofsInTheBook.ZinanFFCT103

#print axioms ProofsInTheBook.ZinanFFCT103.properNoCollision_of_spanResidue
#print axioms ProofsInTheBook.ZinanFFCT103.spherical_arm_mono_ch13_of_spanResidue
