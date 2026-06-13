import ProofsInTheBook.ZinanFFCT86
import ProofsInTheBook.ZinanFFCT97

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
open ProofsInTheBook.ZinanFFCT23
open ProofsInTheBook.ZinanFFCT64
open ProofsInTheBook.ZinanFFCT68
open ProofsInTheBook.ZinanFFCT78
open ProofsInTheBook.ZinanFFCT86
open ProofsInTheBook.ZinanFFCT97

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

/-- **The natural single-wind output discharges the no-collision residue.**  The
single-wind programme proves `NoNonadjacentRepeat (openedWBS A B k)` directly (gnomonic
image + planar single-wind no-repeat), packaged as `OpenedWBSNoNonadjacentRepeatSupply`
(FFCT64).  The cross-piece no-collision predicate is the `r ≤ K < s` subcase of that
full no-repeat (`r + 2 ≤ s` ⟹ nonadjacent), so it follows by specialization. -/
theorem crossPieceNoCollision_of_openedWBSNoRepeat
    (hsupply : OpenedWBSNoNonadjacentRepeatSupply) :
    CrossPieceNoCollisionAtSup := by
  intro n A B hA hB hside hangle k hkdef hstuck r s hr hs hrs _hrK _hKs
  exact hsupply A B hA hB hside hangle k hkdef hstuck r s hr hs hrs

/-- **Ch13 strict-arm monotonicity from the opened-arm no-repeat supply.**  This is the
cleanest unconditional headline modulo the single-wind output: once the single-wind
machinery (FFCT94/95/96/97) supplies `NoNonadjacentRepeat (openedWBS A B k)`, Ch13 closes. -/
theorem spherical_arm_mono_ch13_of_openedWBSNoRepeat
    (hsupply : OpenedWBSNoNonadjacentRepeatSupply) :
    SphericalArmMonotone :=
  spherical_arm_mono_ch13_of_noCollision (crossPieceNoCollision_of_openedWBSNoRepeat hsupply)

/-- **Ch13 strict-arm monotonicity, reduced to the TWO planar residues.**  Combining
the opened-arm gnomonic single-wind layer (FFCT97) with the vacuous no-collision bridge,
Chapter 13 closes once the two genuine planar-analytic residues are discharged:
* `OpenedWBSPlanarLiftedTurnSpanExists` — from a weak-support, distinct-edge,
  strict-turn planar chain with an orthonormal frame, build the lifted-turn span
  (its `one_wind : θ N − θ 0 < 2π` is the single-wind total-turning bound), and
* `PlanarOneWindNoRepeat` — a planar lifted-turn span (single-wind) has no
  nonadjacent vertex repeat (the full `< 2π` generalization of FFCT94's `< π` case).
Both are non-vacuous (realised by strictly convex planar chains, e.g. FFCT94's
`witChain`) and are the only remaining unformalized analytic content of Ch13. -/
theorem spherical_arm_mono_ch13_of_planar_residues
    (hres : OpenedWBSPlanarLiftedTurnSpanExists)
    (hplanar : PlanarOneWindNoRepeat) :
    SphericalArmMonotone :=
  spherical_arm_mono_ch13_of_noCollision
    (crossPieceNoCollisionAtSup_of_openedWBS_gnomonicSingleWind hres hplanar)

end ProofsInTheBook.ZinanFFCT98

#print axioms ProofsInTheBook.ZinanFFCT98.spherical_arm_mono_ch13_of_planar_residues
#print axioms ProofsInTheBook.ZinanFFCT98.collisionEndpoint_of_noCollision
#print axioms ProofsInTheBook.ZinanFFCT98.spherical_arm_mono_ch13_of_noCollision
#print axioms ProofsInTheBook.ZinanFFCT98.crossPieceNoCollision_of_openedWBSNoRepeat
#print axioms ProofsInTheBook.ZinanFFCT98.spherical_arm_mono_ch13_of_openedWBSNoRepeat
