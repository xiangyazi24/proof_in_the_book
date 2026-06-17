import ProofsInTheBook.ZinanFFCT68

/-!
# `ZinanFFCT69` -- mirror-aware WBS seed dispatch

This additive layer removes the old forward-only `SupportStuckWBSVanishingSpanSeedSupply`
from the final dispatch path by allowing the normalized vanishing support seed to live either
on the opened WBS arm itself or on its mirror-reversed arm.
-/

noncomputable section

open scoped RealInnerProductSpace NNReal
open ProofsInTheBook.SphericalKernel ProofsInTheBook.SphericalArm
open ProofsInTheBook.SphericalRotation
open ProofsInTheBook.SphericalSZInduction
open ProofsInTheBook.SphericalSZFinal
open ProofsInTheBook.SphericalSZClose
open ProofsInTheBook.SphericalMonitoredSup
open ProofsInTheBook.SphericalOpeningOutcome
open ProofsInTheBook.SphericalReachStuck
open ProofsInTheBook.ZinanFFCT12
open ProofsInTheBook.ZinanFFCT18
open ProofsInTheBook.ZinanFFCT23
open ProofsInTheBook.ZinanFFCT25
open ProofsInTheBook.ZinanFFCT45
open ProofsInTheBook.ZinanFFCT46
open ProofsInTheBook.ZinanFFCT47
open ProofsInTheBook.ZinanFFCT49
open ProofsInTheBook.ZinanFFCT52
open ProofsInTheBook.ZinanFFCT61
open ProofsInTheBook.ZinanFFCT62
open ProofsInTheBook.ZinanFFCT64
open ProofsInTheBook.ZinanFFCT65
open ProofsInTheBook.ZinanFFCT67
open ProofsInTheBook.ZinanFFCT68

namespace ProofsInTheBook.ZinanFFCT69

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000

/-! ## Mirror-aware seed surface. -/

/-- A normalized WBS vanishing seed, allowing the reversed-orientation branch to be consumed on
`mirrorArm (openedWBS A B k)`. -/
def SupportStuckWBSMirrorVanishingSpanSeedSupply : Prop :=
  ∀ {n : ℕ} (A B : Fin (n + 1) → S2),
    StrictConvexSphArm A → StrictConvexSphArm B → SameSides A B → JointLe A B →
    ∀ k : Fin (n - 1), jointAngle A k < jointAngle B k →
    SupportStuckWBS A B k →
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

/-- The old forward-only seed is a special case of the mirror-aware seed surface. -/
theorem mirrorSeed_of_forwardSeed
    (hseed : SupportStuckWBSVanishingSpanSeedSupply) :
    SupportStuckWBSMirrorVanishingSpanSeedSupply := by
  intro n A B hA hB hside hangle k hkdef hstuck
  exact Or.inl (hseed A B hA hB hside hangle k hkdef hstuck)

/-- A raw non-wrap support-stuck witness.  This is the exact hypothesis needed to run
`orientationNormalized`; the wrap-base case `a.val = n` is intentionally not hidden. -/
def SupportStuckWBSNonWrapVanishingSupportSupply : Prop :=
  ∀ {n : ℕ} (A B : Fin (n + 1) → S2),
    StrictConvexSphArm A → StrictConvexSphArm B → SameSides A B → JointLe A B →
    ∀ k : Fin (n - 1), jointAngle A k < jointAngle B k →
    SupportStuckWBS A B k →
      ∃ a b : Fin (n + 1), b ≠ a ∧ b ≠ a + 1 ∧ a.val + 1 < n + 1 ∧
        sOrient (openedWBS A B k a) (openedWBS A B k (a + 1)) (openedWBS A B k b) = 0

/-- Reflection converts a reversed-arm zero support into a mirror-arm zero support. -/
theorem mirrorArm_sOrient_zero_of_revArm_zero {n : ℕ} (P : Fin (n + 1) → S2)
    {i j : ℕ} (hi : i < n + 1) (hi1 : i + 1 < n + 1) (hj : j < n + 1)
    (hzero :
      sOrient (revArm P ⟨i, hi⟩) (revArm P ⟨i + 1, hi1⟩)
        (revArm P ⟨j, hj⟩) = 0) :
    sOrient (mirrorArm P ⟨i, hi⟩) (mirrorArm P ⟨i + 1, hi1⟩)
      (mirrorArm P ⟨j, hj⟩) = 0 := by
  rw [mirrorArm_apply, mirrorArm_apply, mirrorArm_apply, sOrient_mirrorS2, hzero, neg_zero]

/-- A non-wrap raw WBS support witness gives the mirror-aware normalized seed. -/
theorem mirrorSeed_of_nonWrapVanishingSupport
    (hsupply : SupportStuckWBSNonWrapVanishingSupportSupply) :
    SupportStuckWBSMirrorVanishingSpanSeedSupply := by
  intro n A B hA hB hside hangle k hkdef hstuck
  obtain ⟨a, b, hne, hne1, hadj, hsupp⟩ :=
    hsupply A B hA hB hside hangle k hkdef hstuck
  rcases orientationNormalized (openedWBS A B k) hne hne1 hsupp hadj with hdir | hrev
  · rcases hdir with ⟨i, j, hij, hj, hzero⟩
    left
    refine ⟨i, j, by omega, by omega, by omega, hij, ?_⟩
    simpa using hzero
  · rcases hrev with ⟨i, j, hij, hj, hzero⟩
    right
    refine ⟨i, j, by omega, by omega, by omega, hij, ?_⟩
    exact mirrorArm_sOrient_zero_of_revArm_zero (openedWBS A B k)
      (by omega) (by omega) (by omega) (by simpa using hzero)

/-! ## Endpoint dispatch from a normalized seed. -/

/-- A normalized vanishing support on any weak convex arm produces the endpoint comparison through
the b-trichotomy endpoint-case surface. -/
theorem endpoint_of_normalized_vanishing_support
    (cases : BTrichotomyEndpointCases)
    {n : ℕ} {P B : Fin (n + 1) → S2}
    (hP : WeakConvexSphArm P) (hpos : PositiveJoints P) (hB : StrictConvexSphArm B)
    (hside : SameSides P B) (hangle : JointLe P B) (hnr : NoNonadjacentRepeat P)
    (hhem : ∃ h : E3, ‖h‖ = 1 ∧ ∀ r : Fin (n + 1), 0 < (⟪h, (P r : E3)⟫ : ℝ))
    {i j : ℕ} (hij : i + 1 < j)
    (hi : i < n + 1) (hi1 : i + 1 < n + 1) (hj : j < n + 1)
    (hzero : sOrient (P ⟨i, hi⟩) (P ⟨i + 1, hi1⟩) (P ⟨j, hj⟩) = 0) :
    endpt P ≤ endpt B := by
  obtain ⟨h, hnorm, hhemPos⟩ := hhem
  have hdist : P ⟨i + 1, hi1⟩ ≠ P ⟨j, hj⟩ := by
    have hdist0 : P ⟨i + 1, by omega⟩ ≠ P ⟨j, by omega⟩ :=
      distinctNormalized_of_noRepeat hP hnr hij (by omega)
    simpa using hdist0
  have hanti : (P ⟨i + 1, hi1⟩ : E3) ≠ -(P ⟨j, hj⟩ : E3) :=
    hemisphere_nonAntipodal hhemPos ⟨i + 1, hi1⟩ ⟨j, hj⟩
  have hdet : det3 (P ⟨i + 1, hi1⟩ : E3) (P ⟨j, hj⟩ : E3)
      (P ⟨i, hi⟩ : E3) = 0 := by
    rw [sOrient] at hzero
    rwa [det3_cyclic (P ⟨i, hi⟩ : E3) (P ⟨i + 1, hi1⟩ : E3)
      (P ⟨j, hj⟩ : E3)] at hzero
  obtain ⟨a, b, hspan⟩ :=
    lin_indep_span_of_det3_zero (P ⟨i + 1, hi1⟩).2 (P ⟨j, hj⟩).2
      (fun h => hdist (S2.ext h)) hanti hdet
  exact endpoint_of_btrichotomy_cases cases hP hpos hB hside hangle hnr
    ⟨h, hnorm, hhemPos⟩
    hij hi hi1 hj hspan

/-- The mirror-aware seed surface gives the WBS support-stuck endpoint dispatch. -/
theorem supportStuckWBS_endpoint_dispatch_mirrorSeed
    (hseed : SupportStuckWBSMirrorVanishingSpanSeedSupply)
    (hcross : CrossPieceNoCollisionAtSup)
    (cases : BTrichotomyEndpointCases) :
    SupportStuckWBSEndpointDispatch := by
  intro n A B hA hB hside hangle k hkdef hstuck
  obtain ⟨hka, hkt⟩ := shortArcs_of_strict hA k
  have hwrap :
      ShortArc (openTail A (openingAxis k) (-(monitoredSupWBS A B k)) (Fin.last n))
        (openTail A (openingAxis k) (-(monitoredSupWBS A B k)) 0) :=
    openedWrapShortArc_at_supWBS hA hB hka hkt hkdef
  have hPweak : WeakConvexSphArm (openedWBS A B k) := by
    unfold openedWBS
    exact supportStuckWBS_weakConvex hA hB hka hkt hkdef hwrap
  have hPpos : PositiveJoints (openedWBS A B k) := by
    intro r
    unfold openedWBS
    exact (openedJoints_in_Ioo_at_supWBS hA hB hka hkt hkdef r).1
  have hedge := openedEdges_short_at_supWBS_of_wrap (A := A) (B := B) hA hwrap
  have hjopen := openedJoints_in_Ioo_at_supWBS hA hB hka hkt hkdef
  have hhem0 := openHemisphere_at_WBS_sup hA hka hkt hkdef hedge hjopen
  have hhem : ∃ h : E3, ‖h‖ = 1 ∧
      ∀ r : Fin (n + 1), 0 < (⟪h, (openedWBS A B k r : E3)⟫ : ℝ) := by
    simpa [openedWBS] using hhem0
  have hside' : SameSides (openedWBS A B k) B := by
    intro r
    unfold openedWBS
    rw [openTail_preserves_sides A (openingAxis k) (-(monitoredSupWBS A B k)) r]
    exact hside r
  have hjointk : jointAngle (openedWBS A B k) k =
      openedInteriorJointAngle A k (-(monitoredSupWBS A B k)) := by
    unfold openedWBS
    exact jointAngle_openTail_eq_openedInterior A k (-(monitoredSupWBS A B k))
  have hslack : openedInteriorJointAngle A k (-(monitoredSupWBS A B k)) ≤ jointAngle B k :=
    openedInteriorJoint_le_at_supWBS hA hka hkt hkdef
  have hangle' : JointLe (openedWBS A B k) B := by
    intro r
    by_cases hrk : r = k
    · rw [hrk, hjointk]
      exact hslack
    · unfold openedWBS
      rw [jointAngle_openTail_eq_of_ne A k (-(monitoredSupWBS A B k)) hrk]
      exact hangle r
  have hnr : NoNonadjacentRepeat (openedWBS A B k) :=
    openedWBS_noNonadjacentRepeat_of_crossPiece hcross A B hA hB hside hangle k hkdef hstuck
  rcases hseed A B hA hB hside hangle k hkdef hstuck with hdir | hmir
  · obtain ⟨i, j, hi, hi1, hj, hij, hzero⟩ := hdir
    exact endpoint_of_normalized_vanishing_support cases hPweak hPpos hB hside' hangle' hnr hhem
      hij hi hi1 hj hzero
  · obtain ⟨i, j, hi, hi1, hj, hij, hzero⟩ := hmir
    have hmirror : endpt (mirrorArm (openedWBS A B k)) ≤ endpt (mirrorArm B) :=
      endpoint_of_normalized_vanishing_support cases
        (weakConvex_mirrorArm hPweak) (positiveJoints_mirrorArm hPpos)
        (strictConvex_mirrorArm hB) (sameSides_mirrorArm hside') (jointLe_mirrorArm hangle')
        (noNonadjacentRepeat_mirrorArm hnr)
        (weakConvex_mirrorArm hPweak).closed_convex.open_hemisphere hij hi hi1 hj hzero
    simpa [endpt_mirrorArm] using hmirror

/-! ## Final wrapper with the forward-only seed removed. -/

/-- FFCT69 final surface: the seed may be on the opened arm or on the mirror-reversed opened arm.
The endpoint-case surface is unchanged from FFCT64. -/
structure Ch13FinalSurface69 : Prop where
  hmirrorSeed : SupportStuckWBSMirrorVanishingSpanSeedSupply
  hcross : CrossPieceNoCollisionAtSup
  hcases : BTrichotomyEndpointCases

/-- FFCT68's surface maps into FFCT69's mirror-aware surface. -/
theorem final69_of_final68 (res : Ch13FinalSurface68) : Ch13FinalSurface69 where
  hmirrorSeed := mirrorSeed_of_forwardSeed res.hspanSeed
  hcross := res.hcross
  hcases := res.hcases

/-- Chapter 13 strict-arm monotonicity with the forward-only seed replaced by the mirror-aware seed. -/
theorem spherical_arm_mono_final_ch13_v3 (res : Ch13FinalSurface69)
    {n : ℕ} (hn : 2 ≤ n) (A B : Fin (n + 1) → S2)
    (hA : StrictConvexSphArm A) (hB : StrictConvexSphArm B)
    (hside : ∀ i : Fin n, sideLen A i = sideLen B i)
    (hangle : ∀ i : Fin (n - 1), jointAngle A i ≤ jointAngle B i) :
    sDist (A 0) (A (Fin.last n)) ≤ sDist (B 0) (B (Fin.last n)) :=
  spherical_arm_mono_of_supportStuckEndpointDispatch
    (supportStuckWBS_endpoint_dispatch_mirrorSeed res.hmirrorSeed res.hcross res.hcases)
    hn A B hA hB hside hangle

/-- Unpacked FFCT69 corollary. -/
theorem spherical_arm_mono_final_ch13_v3_of_supplies
    (hmirrorSeed : SupportStuckWBSMirrorVanishingSpanSeedSupply)
    (hcross : CrossPieceNoCollisionAtSup)
    (hcases : BTrichotomyEndpointCases)
    {n : ℕ} (hn : 2 ≤ n) (A B : Fin (n + 1) → S2)
    (hA : StrictConvexSphArm A) (hB : StrictConvexSphArm B)
    (hside : ∀ i : Fin n, sideLen A i = sideLen B i)
    (hangle : ∀ i : Fin (n - 1), jointAngle A i ≤ jointAngle B i) :
    sDist (A 0) (A (Fin.last n)) ≤ sDist (B 0) (B (Fin.last n)) :=
  spherical_arm_mono_final_ch13_v3
    ⟨hmirrorSeed, hcross, hcases⟩ hn A B hA hB hside hangle

/-- Non-vacuity guard for the FFCT69 conclusion shape. -/
theorem spherical_arm_mono_final_ch13_v3_conclusion_satisfiable {n : ℕ}
    (A : Fin (n + 1) → S2) :
    sDist (A 0) (A (Fin.last n)) ≤ sDist (A 0) (A (Fin.last n)) := le_refl _

#print axioms mirrorSeed_of_nonWrapVanishingSupport
#print axioms endpoint_of_normalized_vanishing_support
#print axioms supportStuckWBS_endpoint_dispatch_mirrorSeed
#print axioms spherical_arm_mono_final_ch13_v3

end ProofsInTheBook.ZinanFFCT69
