import ProofsInTheBook.ZinanFFCT78

/-!
# `ZinanFFCT79` -- v10 boundary-propagation audit layer

This file records the sharp checked wrapper available after `ZinanFFCT78`.
The requested hcross-only v10 headline is not asserted here: the arbitrary
wrap-probe propagation and the signed tail-corner endpoint closure are still
the missing proof content.

No proof placeholders or unsafe declarations.
-/

noncomputable section

open scoped RealInnerProductSpace NNReal
open ProofsInTheBook.SphericalKernel ProofsInTheBook.SphericalArm
open ProofsInTheBook.SphericalSZInduction
open ProofsInTheBook.SphericalSZStepClose
open ProofsInTheBook.SphericalSZFinal
open ProofsInTheBook.SphericalSZClose
open ProofsInTheBook.SphericalArmAssembly
open ProofsInTheBook.SphericalMonitoredSup
open ProofsInTheBook.SphericalOpeningOutcome
open ProofsInTheBook.SphericalReachStuck
open ProofsInTheBook.SphericalStuckGeneral
open ProofsInTheBook.SphericalCutTransport
open ProofsInTheBook.ZinanFFCT18
open ProofsInTheBook.ZinanFFCT23
open ProofsInTheBook.ZinanFFCT68
open ProofsInTheBook.ZinanFFCT76
open ProofsInTheBook.ZinanFFCT77
open ProofsInTheBook.ZinanFFCT78

namespace ProofsInTheBook.ZinanFFCT79

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000

/-! ## Exact missing v10 boundary theorem shape. -/

/-- The general wrap-probe propagation statement requested by the v10 handoff.
It is kept as a proposition, not assumed. -/
def WrapPlanePropagationGeneral : Prop :=
  ∀ {n : ℕ} {A B : Fin (n + 1) → S2},
    2 ≤ n →
    WeakConvexSphArm A →
    PositiveJoints A →
    StrictConvexSphArm B →
    SameSides A B →
    JointLe A B →
    NoNonadjacentRepeat A →
    (∃ h : E3, ‖h‖ = 1 ∧
      ∀ r : Fin (n + 1), 0 < (⟪h, (A r : E3)⟫ : ℝ)) →
    ∀ {j : Fin (n + 1)},
      j ≠ Fin.last n →
      j ≠ 0 →
      sOrient (A (Fin.last n)) (A 0) (A j) = 0 →
        BoundaryZeroProgress A B

/-- The three v9 residues that still have to be supplied in addition to
`CrossPieceNoCollisionAtSup` for the checked `ZinanFFCT77` assembly. -/
structure V10BoundaryResidues : Prop where
  hweakWrapSeed : WeakVanishingWrapSeedResidueV9
  hwrapSeed : SupportStuckWBSWrapSeedResidueV9
  hbpos_aneg_tail : BPosANegTailCornerResidueV9

/-- Assemble the checked v9 final surface from the single cross-piece field and
the still-missing boundary residues. -/
def surface77_of_hcross_and_boundaryResidues
    (hcross : CrossPieceNoCollisionAtSup)
    (res : V10BoundaryResidues) : Ch13FinalSurface77 where
  hweakWrapSeed := res.hweakWrapSeed
  hwrapSeed := res.hwrapSeed
  hcross := hcross
  hbpos_aneg_tail := res.hbpos_aneg_tail

/-- The sharp checked wrapper currently available at the v10 interface: once the
three boundary residues are closed, the final surface is exactly hcross-only. -/
theorem spherical_arm_mono_final_ch13_v10_of_hcross_and_boundaryResidues
    (hcross : CrossPieceNoCollisionAtSup)
    (res : V10BoundaryResidues) :
    SphericalArmMonotone := by
  intro n hn A B hA hB hside hangle
  exact spherical_arm_mono_final_ch13_v9
    (surface77_of_hcross_and_boundaryResidues hcross res)
    hn A B hA hB hside hangle

/-- Backward-compatible spelling: the already checked `Ch13FinalSurface77`
implies the v10 headline predicate. -/
theorem spherical_arm_mono_final_ch13_v10_from_surface77
    (res : Ch13FinalSurface77) :
    SphericalArmMonotone := by
  intro n hn A B hA hB hside hangle
  exact spherical_arm_mono_final_ch13_v9 res hn A B hA hB hside hangle

/-! ## Guards. -/

theorem wrapPlanePropagationGeneral_probe_one_satisfies_shape :
    ∀ {n : ℕ} {A B : Fin (n + 1) → S2},
      2 ≤ n →
      WeakConvexSphArm A →
      PositiveJoints A →
      StrictConvexSphArm B →
      SameSides A B →
      JointLe A B →
      NoNonadjacentRepeat A →
      (∃ h : E3, ‖h‖ = 1 ∧
        ∀ r : Fin (n + 1), 0 < (⟪h, (A r : E3)⟫ : ℝ)) →
      ∀ {j : Fin (n + 1)},
        j.val = 1 →
        sOrient (A (Fin.last n)) (A 0) (A j) = 0 →
          BoundaryZeroProgress A B := by
  intro n A B hn hA hpos hB hside hangle hnr hhem j hj hzero
  exact wrapPlanePropagation_probe_one hn hA hpos hB hside hangle hnr hhem hj hzero

#print axioms spherical_arm_mono_final_ch13_v10_of_hcross_and_boundaryResidues
#print axioms spherical_arm_mono_final_ch13_v10_from_surface77
#print axioms wrapPlanePropagationGeneral_probe_one_satisfies_shape

end ProofsInTheBook.ZinanFFCT79
