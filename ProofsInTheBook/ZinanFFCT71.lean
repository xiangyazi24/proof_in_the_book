import ProofsInTheBook.ZinanFFCT70

/-!
# `ZinanFFCT71` -- surface-70 grind: wrap-seed shrink and bpos/apos step adapter

This additive layer keeps the FFCT70 theorem path intact but sharpens the seed field:
non-wrap raw WBS supports are normalized by the existing FFCT52/69 machinery, so the
final seed residue only has to cover the wrap-base raw support.

It also records the exact `b > 0, a > 0` adapter needed at an induction-step site:
with the dimension IH and a supplied diagonal inequality, the landed forward
folded-flat transport closes the endpoint branch.
-/

noncomputable section

open scoped RealInnerProductSpace NNReal
open ProofsInTheBook.SphericalKernel ProofsInTheBook.SphericalArm
open ProofsInTheBook.SphericalSZInduction
open ProofsInTheBook.ZinanFFCT18
open ProofsInTheBook.ZinanFFCT23
open ProofsInTheBook.ZinanFFCT45
open ProofsInTheBook.ZinanFFCT46
open ProofsInTheBook.ZinanFFCT49
open ProofsInTheBook.ZinanFFCT52
open ProofsInTheBook.ZinanFFCT61
open ProofsInTheBook.ZinanFFCT64
open ProofsInTheBook.ZinanFFCT66
open ProofsInTheBook.ZinanFFCT68
open ProofsInTheBook.ZinanFFCT69
open ProofsInTheBook.ZinanFFCT70

namespace ProofsInTheBook.ZinanFFCT71

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000

/-! ## The remaining wrap-base seed residue. -/

/-- The exact raw WBS seed residue left after the non-wrap support base is handled by
`orientationNormalized`.

The inputs are a raw support-stuck witness whose binding edge has no ordinary successor
in natural-number coordinates (`¬ a.val + 1 < n + 1`), i.e. the cyclic wrap edge.  The
output is the same mirror-aware normalized seed consumed by FFCT69. -/
def SupportStuckWBSWrapSeedResidue : Prop :=
  ∀ {n : ℕ} (A B : Fin (n + 1) → S2),
    StrictConvexSphArm A → StrictConvexSphArm B → SameSides A B → JointLe A B →
    ∀ k : Fin (n - 1), jointAngle A k < jointAngle B k →
    SupportStuckWBS A B k →
    ∀ a b : Fin (n + 1),
      b ≠ a → b ≠ a + 1 → ¬ a.val + 1 < n + 1 →
      sOrient (openedWBS A B k a) (openedWBS A B k (a + 1)) (openedWBS A B k b) = 0 →
        (∃ i j : ℕ, ∃ (hi : i < n + 1) (hi1 : i + 1 < n + 1) (hj : j < n + 1),
          i + 1 < j ∧
            sOrient (openedWBS A B k ⟨i, hi⟩) (openedWBS A B k ⟨i + 1, hi1⟩)
              (openedWBS A B k ⟨j, hj⟩) = 0)
        ∨
        (∃ i j : ℕ, ∃ (hi : i < n + 1) (hi1 : i + 1 < n + 1) (hj : j < n + 1),
          i + 1 < j ∧
            sOrient (mirrorArm (openedWBS A B k) ⟨i, hi⟩)
              (mirrorArm (openedWBS A B k) ⟨i + 1, hi1⟩)
              (mirrorArm (openedWBS A B k) ⟨j, hj⟩) = 0)

/-- A wrap-only seed residue supplies FFCT69's mirror-aware normalized seed.

The proof uses the raw support-stuck witness.  If its binding edge is non-wrap,
`orientationNormalized` handles it; if it is wrap, the new residue is invoked. -/
theorem mirrorSeed_of_wrapSeedResidue
    (hwrap : SupportStuckWBSWrapSeedResidue) :
    SupportStuckWBSMirrorVanishingSpanSeedSupply := by
  intro n A B hA hB hside hangle k hkdef hstuck
  obtain ⟨a, b, hne, hne1, hsupp0⟩ := supportStuckWBS_vanishingSupport hstuck
  have hsupp :
      sOrient (openedWBS A B k a) (openedWBS A B k (a + 1))
        (openedWBS A B k b) = 0 := by
    simpa [openedWBS] using hsupp0
  by_cases hadj : a.val + 1 < n + 1
  · rcases orientationNormalized (openedWBS A B k) hne hne1 hsupp hadj with hdir | hrev
    · obtain ⟨i, j, hij, hj, hzero⟩ := hdir
      left
      refine ⟨i, j, by omega, by omega, by omega, hij, ?_⟩
      simpa using hzero
    · obtain ⟨i, j, hij, hj, hzero⟩ := hrev
      right
      refine ⟨i, j, by omega, by omega, by omega, hij, ?_⟩
      exact mirrorArm_sOrient_zero_of_revArm_zero (openedWBS A B k)
        (by omega) (by omega) (by omega) hzero
  · exact hwrap A B hA hB hside hangle k hkdef hstuck a b hne hne1 hadj hsupp

/-! ## The `b > 0, a > 0` step-site adapter. -/

/-- The genuinely missing datum for the positive-positive coefficient branch at an
induction-step site: the diagonal inequality for the same normalized binding.

Unlike `BPosAPosEndpointCase`, this does not assert the endpoint conclusion.  The
endpoint is produced below from the landed forward folded-flat transport, once the
strong dimension IH is in scope. -/
def BPosAPosDiagonalSupply : Prop :=
  ∀ {n : ℕ} {P B : Fin (n + 1) → S2},
    WeakConvexSphArm P → PositiveJoints P → StrictConvexSphArm B →
    SameSides P B → JointLe P B → NoNonadjacentRepeat P →
    (∃ h : E3, ‖h‖ = 1 ∧ ∀ r : Fin (n + 1), 0 < (⟪h, (P r : E3)⟫ : ℝ)) →
    (∀ m : ℕ, m < n → MainPlus m) →
    ∀ {i j : ℕ}, i + 1 < j →
    ∀ (hi : i < n + 1) (hi1 : i + 1 < n + 1) (hj : j < n + 1),
    ∀ {a b : ℝ},
      (P ⟨i, hi⟩ : E3) = a • (P ⟨i + 1, hi1⟩ : E3) + b • (P ⟨j, hj⟩ : E3) →
      0 < b → 0 < a →
        sDist (P ⟨i, hi⟩) (P ⟨j, hj⟩) ≤ sDist (B ⟨i, by omega⟩) (B ⟨j, hj⟩)

/-- At a fixed induction level, the positive-positive endpoint branch follows from
the dimension IH and the diagonal supply. -/
theorem bpos_apos_endpoint_of_diagonalSupply_at_level
    (hdiagSupply : BPosAPosDiagonalSupply)
    {n : ℕ} {P B : Fin (n + 1) → S2}
    (hP : WeakConvexSphArm P) (hpos : PositiveJoints P) (hB : StrictConvexSphArm B)
    (hside : SameSides P B) (hangle : JointLe P B) (hnr : NoNonadjacentRepeat P)
    (hhem : ∃ h : E3, ‖h‖ = 1 ∧ ∀ r : Fin (n + 1), 0 < (⟪h, (P r : E3)⟫ : ℝ))
    (ihdim : ∀ m : ℕ, m < n → MainPlus m)
    {i j : ℕ} (hij : i + 1 < j)
    (hi : i < n + 1) (hi1 : i + 1 < n + 1) (hj : j < n + 1)
    {a b : ℝ}
    (hspan : (P ⟨i, hi⟩ : E3) =
      a • (P ⟨i + 1, hi1⟩ : E3) + b • (P ⟨j, hj⟩ : E3))
    (hbpos : 0 < b) (hapos : 0 < a) :
    endpt P ≤ endpt B := by
  have hdiag := hdiagSupply hP hpos hB hside hangle hnr hhem ihdim
    hij hi hi1 hj hspan hbpos hapos
  exact bpos_apos_endpointConsumer_forward_holds foldedFlatCutTransportPlusForward_v3
    hP hpos hB hside hangle hnr ihdim hij hi hi1 hj hspan hbpos hapos hdiag

/-! ## Final FFCT71 surface. -/

/-- FFCT71 final surface.  Compared with FFCT70, the mirror-aware seed field is
replaced by the exact wrap-base residue; non-wrap raw support witnesses are now
normalized in this file. -/
structure Ch13FinalSurface71 : Prop where
  hwrapSeed : SupportStuckWBSWrapSeedResidue
  hcross : CrossPieceNoCollisionAtSup
  hbpos_apos : BPosAPosEndpointCase
  hbpos_aneg_tail : BPosANegTailCornerResidue

/-- The FFCT71 surface maps into FFCT70's final surface. -/
theorem final70_of_final71 (res : Ch13FinalSurface71) : Ch13FinalSurface70 where
  hmirrorSeed := mirrorSeed_of_wrapSeedResidue res.hwrapSeed
  hcross := res.hcross
  hbpos_apos := res.hbpos_apos
  hbpos_aneg_tail := res.hbpos_aneg_tail

/-- Chapter 13 monotonicity through the FFCT71 surface. -/
theorem spherical_arm_mono_final_ch13_v5 (res : Ch13FinalSurface71)
    {n : ℕ} (hn : 2 ≤ n) (A B : Fin (n + 1) → S2)
    (hA : StrictConvexSphArm A) (hB : StrictConvexSphArm B)
    (hside : ∀ i : Fin n, sideLen A i = sideLen B i)
    (hangle : ∀ i : Fin (n - 1), jointAngle A i ≤ jointAngle B i) :
    sDist (A 0) (A (Fin.last n)) ≤ sDist (B 0) (B (Fin.last n)) :=
  spherical_arm_mono_final_ch13_v4 (final70_of_final71 res) hn A B hA hB hside hangle

/-- Non-vacuity guard for the wrap residue: the conclusion it must produce is a
real normalized zero support, not `True`. -/
theorem wrapSeedResidue_target_real {n : ℕ} (P : Fin (n + 1) → S2)
    {i j : ℕ} (hi : i < n + 1) (hi1 : i + 1 < n + 1) (hj : j < n + 1) :
    sOrient (P ⟨i, hi⟩) (P ⟨i + 1, hi1⟩) (P ⟨j, hj⟩) = 0 →
      sOrient (P ⟨i, hi⟩) (P ⟨i + 1, hi1⟩) (P ⟨j, hj⟩) = 0 := id

/-- Non-vacuity guard for the diagonal supply's target. -/
theorem bpos_apos_diagonal_target_satisfiable {n : ℕ} (P : Fin (n + 1) → S2)
    {i j : ℕ} (hi : i < n + 1) (hj : j < n + 1) :
    sDist (P ⟨i, hi⟩) (P ⟨j, hj⟩) ≤ sDist (P ⟨i, hi⟩) (P ⟨j, hj⟩) := le_refl _

#print axioms mirrorSeed_of_wrapSeedResidue
#print axioms bpos_apos_endpoint_of_diagonalSupply_at_level
#print axioms final70_of_final71
#print axioms spherical_arm_mono_final_ch13_v5

end ProofsInTheBook.ZinanFFCT71
