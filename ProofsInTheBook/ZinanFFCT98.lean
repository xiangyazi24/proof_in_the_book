import ProofsInTheBook.ZinanFFCT86

/-!
# Ch13 final assembly: the no-collision residue discharges the headline (vacuously)

The whole Ch13 strict-arm monotonicity residue has been reduced (FFCT86) to the
collision-endpoint predicate `CrossPieceCollisionEndpointAtSup`: *if* a cross-piece
collision `openedWBS r = openedWBS s` (`r ≤ K < s`, `r + 2 ≤ s`) occurs at the WBS
support-stuck supremum, *then* the opened endpoint is bounded by `endpt B`.

The single-wind programme (FFCT94/95/96/97) instead targets the sharper
`CrossPieceNoCollisionAtSup` (FFCT68): such a collision **never** occurs.  This file
records the trivial logical bridge: no-collision implies the collision-endpoint
predicate *vacuously* (the collision hypothesis is never satisfiable, so its conclusion
holds by absurdity), hence `SphericalArmMonotone` follows from the no-collision residue.

Once a channel discharges `CrossPieceNoCollisionAtSup` unconditionally, plugging it into
`spherical_arm_mono_ch13_of_noCollision` yields the unconditional Ch13 headline.
-/

open scoped RealInnerProductSpace NNReal
open ProofsInTheBook.SphericalKernel ProofsInTheBook.SphericalArm
open ProofsInTheBook.SphericalRotation
open ProofsInTheBook.SphericalSZInduction
open ProofsInTheBook.SphericalSZFinal
open ProofsInTheBook.ZinanFFCT68
open ProofsInTheBook.ZinanFFCT78
open ProofsInTheBook.ZinanFFCT86

namespace ProofsInTheBook.ZinanFFCT98

/-- **No-collision implies the collision-endpoint predicate, vacuously.**  If the
cross-piece collision `openedWBS r = openedWBS s` never occurs, then the
collision-endpoint conclusion holds by absurdity for every (impossible) collision
branch. -/
theorem collisionEndpoint_of_noCollision
    (hnc : CrossPieceNoCollisionAtSup) :
    CrossPieceCollisionEndpointAtSup := by
  intro n A B hA hB hside hangle k hkdef hstuck r s hr hs hrs hrK hKs heq
  exact absurd heq (hnc A B hA hB hside hangle k hkdef hstuck r s hr hs hrs hrK hKs)

/-- **Ch13 strict-arm monotonicity from the no-collision residue.**  This is the
unconditional Ch13 headline modulo `CrossPieceNoCollisionAtSup` — the single-wind
target of FFCT94/95/96/97.  Discharging `CrossPieceNoCollisionAtSup` closes Ch13. -/
theorem spherical_arm_mono_ch13_of_noCollision
    (hnc : CrossPieceNoCollisionAtSup) :
    SphericalArmMonotone :=
  spherical_arm_mono_final_ch13_v11 (collisionEndpoint_of_noCollision hnc)

end ProofsInTheBook.ZinanFFCT98

#print axioms ProofsInTheBook.ZinanFFCT98.collisionEndpoint_of_noCollision
#print axioms ProofsInTheBook.ZinanFFCT98.spherical_arm_mono_ch13_of_noCollision
