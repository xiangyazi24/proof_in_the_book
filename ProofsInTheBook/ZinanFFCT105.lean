import ProofsInTheBook.ZinanFFCT103
import ProofsInTheBook.ZinanFFCT104

/-!
# Ch13 reduced to the single satisfiable residue `OpenedArmTurningLtTwoPi`

FFCT104 replaced the over-quantified, unsatisfiable residue `OpenedWBSPlanarLiftedTurnSpanExists`
(which quantifies over all orthonormal frames, including the wrong-handed one that breaks
`turn_pos`) by the genuine analytic core `OpenedArmTurningLtTwoPi`: the *weak*-support open-arm
turning bound (`< 2π`).  `openedWBS_gnomonicSingleWind_of_bound` produces the opened arm's
`GnomonicSingleWind` certificate from that bound alone, supplying the oriented frame internally.

This file re-runs the FFCT103 wiring with that certificate, so Chapter 13's strict-arm
monotonicity follows from the single, non-vacuous, numerically-true planar bound
`OpenedArmTurningLtTwoPi`.
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
open ProofsInTheBook.ZinanFFCT100
open ProofsInTheBook.ZinanFFCT101
open ProofsInTheBook.ZinanFFCT104

namespace ProofsInTheBook.ZinanFFCT105

/-- **Proper cross-piece no-collision from the turning bound (unconditional in the over-quantified
residue).**  Uses `openedWBS_gnomonicSingleWind_of_bound` for the lifted span (oriented frame
internal) + `gnomonic_edge_support_nonneg` for the global support; FFCT101 forces any repeat to the
full closure `r = 0 ∧ s = n`, contradicting properness. -/
theorem properNoCollision_of_turningBound
    (hbound : OpenedArmTurningLtTwoPi) :
    ProperCrossPieceNoCollisionAtSup := by
  intro n A B hA hB hside hangle k hkdef hstuck r s hr hs hrs hrK hKs hprop hcoll
  obtain ⟨cert⟩ :=
    openedWBS_gnomonicSingleWind_of_bound hbound A B hA hB hside hangle k hkdef hstuck
  obtain ⟨hka, hkt⟩ := SphericalOpeningOutcome.shortArcs_of_strict hA k
  have hwrap :
      ShortArc (openTail A (openingAxis k) (-(monitoredSupWBS A B k)) (Fin.last n))
        (openTail A (openingAxis k) (-(monitoredSupWBS A B k)) 0) :=
    ZinanFFCT47.openedWrapShortArc_at_supWBS hA hB hka hkt hkdef
  have hPweak : WeakConvexSphArm (openedWBS A B k) := by
    unfold openedWBS
    exact ZinanFFCT46.supportStuckWBS_weakConvex hA hB hka hkt hkdef hwrap
  have hsupp : ∀ i j : Fin (n + 1),
      0 ≤ det3 (gproj cert.h (openedWBS A B k i))
        (gproj cert.h (openedWBS A B k (i + 1))) (gproj cert.h (openedWBS A B k j)) :=
    fun i j => gnomonic_edge_support_nonneg hPweak.closed_convex cert.hpos i j
  have hQcoll :
      gproj cert.h (openedWBS A B k ⟨r, hr⟩) = gproj cert.h (openedWBS A B k ⟨s, hs⟩) := by
    rw [hcoll]
  have hfull := planar_properRepeat_is_fullClosure cert.lifted hsupp hr hs hrs hQcoll
  obtain ⟨hr0, hsn⟩ := hfull
  rcases hprop with hrpos | hslt
  · omega
  · omega

/-- **Chapter 13 strict-arm monotonicity, reduced to `OpenedArmTurningLtTwoPi`.**  The single
remaining residue is the weak-support open-arm turning bound — non-vacuous (FFCT104
`premises_satisfiable`) and numerically true (max turning `≈ 6.25 < 2π`). -/
theorem spherical_arm_mono_ch13_of_turningBound
    (hbound : OpenedArmTurningLtTwoPi) :
    SphericalArmMonotone :=
  spherical_arm_mono_ch13_of_properNoCollision (properNoCollision_of_turningBound hbound)

end ProofsInTheBook.ZinanFFCT105

#print axioms ProofsInTheBook.ZinanFFCT105.properNoCollision_of_turningBound
#print axioms ProofsInTheBook.ZinanFFCT105.spherical_arm_mono_ch13_of_turningBound
