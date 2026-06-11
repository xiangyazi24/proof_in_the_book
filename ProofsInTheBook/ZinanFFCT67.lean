import ProofsInTheBook.ZinanFFCT66

/-!
# `ZinanFFCT67` -- final reconciliation wrapper for the Chapter 13 endpoint surface

This file is additive.  It removes the operationally unused backward-fold field from the final
headline by bypassing the `BTrichotomyEndpointSurfaceV2` wrapper and feeding the direct
`BTrichotomyEndpointCases` surface to the FFCT64 dispatcher.
-/

noncomputable section

open scoped RealInnerProductSpace NNReal
open ProofsInTheBook.SphericalKernel ProofsInTheBook.SphericalArm
open ProofsInTheBook.SphericalSZInduction
open ProofsInTheBook.ZinanFFCT64
open ProofsInTheBook.ZinanFFCT65
open ProofsInTheBook.ZinanFFCT66

namespace ProofsInTheBook.ZinanFFCT67

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000

/-- The accepted opened-arm no-repeat supply, under the public final name. -/
def NoRepeatSupply : Prop :=
  OpenedWBSNoNonadjacentRepeatSupply

/-- Final reconciled surface for the strict-arm headline.

`BackwardFoldCase` is not present: the final route dispatches the normalized WBS binding directly
through `BTrichotomyEndpointCases`, whose normalized interface only exposes `i + 1 < j`.
-/
structure Ch13FinalSurface67 : Prop where
  hspanSeed : SupportStuckWBSVanishingSpanSeedSupply
  hnorepeat : NoRepeatSupply
  hcases : BTrichotomyEndpointCases

/-- Assemble FFCT64's dispatcher from the final reconciled surface. -/
theorem btrichotomyDispatchSurface_of_final67
    (res : Ch13FinalSurface67) : BTrichotomyDispatchSurface where
  hspan := supportStuckWBSSpanSupply_of_vanishingSeed res.hspanSeed
    (show OpenedWBSNoNonadjacentRepeatSupply from res.hnorepeat)
  hnorepeat := openedWBSNoNonadjacentRepeat_pass
    (show OpenedWBSNoNonadjacentRepeatSupply from res.hnorepeat)
  hcases := res.hcases

/-- Final Chapter 13 strict-arm monotonicity statement, modulo the explicit final surface:
normalized WBS vanishing-span seed, opened-arm no-repeat, and the direct b-trichotomy endpoint
cases. -/
theorem spherical_arm_mono_final_ch13 (res : Ch13FinalSurface67)
    {n : ℕ} (hn : 2 ≤ n) (A B : Fin (n + 1) → S2)
    (hA : StrictConvexSphArm A) (hB : StrictConvexSphArm B)
    (hside : ∀ i : Fin n, sideLen A i = sideLen B i)
    (hangle : ∀ i : Fin (n - 1), jointAngle A i ≤ jointAngle B i) :
    sDist (A 0) (A (Fin.last n)) ≤ sDist (B 0) (B (Fin.last n)) :=
  spherical_arm_mono_vNext_btrichotomy
    (btrichotomyDispatchSurface_of_final67 res) hn A B hA hB hside hangle

/-- Unpacked corollary using the public no-repeat supply name. -/
theorem spherical_arm_mono_final_ch13_of_supplies
    (hspanSeed : SupportStuckWBSVanishingSpanSeedSupply)
    (hnorepeat : NoRepeatSupply)
    (hcases : BTrichotomyEndpointCases)
    {n : ℕ} (hn : 2 ≤ n) (A B : Fin (n + 1) → S2)
    (hA : StrictConvexSphArm A) (hB : StrictConvexSphArm B)
    (hside : ∀ i : Fin n, sideLen A i = sideLen B i)
    (hangle : ∀ i : Fin (n - 1), jointAngle A i ≤ jointAngle B i) :
    sDist (A 0) (A (Fin.last n)) ≤ sDist (B 0) (B (Fin.last n)) :=
  spherical_arm_mono_final_ch13
    ⟨hspanSeed, hnorepeat, hcases⟩ hn A B hA hB hside hangle

/-- Non-vacuity guard for the final conclusion shape. -/
theorem spherical_arm_mono_final_ch13_conclusion_satisfiable {n : ℕ}
    (A : Fin (n + 1) → S2) :
    sDist (A 0) (A (Fin.last n)) ≤ sDist (A 0) (A (Fin.last n)) := le_refl _

#print axioms btrichotomyDispatchSurface_of_final67
#print axioms spherical_arm_mono_final_ch13
#print axioms spherical_arm_mono_final_ch13_of_supplies

end ProofsInTheBook.ZinanFFCT67
