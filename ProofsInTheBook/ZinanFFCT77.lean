import ProofsInTheBook.ZinanFFCT76

/-!
# `ZinanFFCT77` -- endpoint-aware wrap interface

This layer performs the interface surgery forced by `BoundaryZeroProgress`: the
two wrap seed residues no longer have to discard an endpoint branch.  Instead,
the NR consumer chain consumes the endpoint-aware payload directly.  The signed
tail corner remains the old endpoint residue; replacing it by
`BoundaryZeroProgress` would require the still-missing cyclic propagation
theorem to avoid a circular normalized-zero dispatch.

No proof placeholders or unsafe declarations.
-/

noncomputable section

open scoped RealInnerProductSpace NNReal
open ProofsInTheBook.SphericalKernel ProofsInTheBook.SphericalArm
open ProofsInTheBook.SphericalRotation
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
open ProofsInTheBook.ZinanFFCT19
open ProofsInTheBook.ZinanFFCT23
open ProofsInTheBook.ZinanFFCT25
open ProofsInTheBook.ZinanFFCT45
open ProofsInTheBook.ZinanFFCT46
open ProofsInTheBook.ZinanFFCT47
open ProofsInTheBook.ZinanFFCT48
open ProofsInTheBook.ZinanFFCT49
open ProofsInTheBook.ZinanFFCT52
open ProofsInTheBook.ZinanFFCT56
open ProofsInTheBook.ZinanFFCT57
open ProofsInTheBook.ZinanFFCT58
open ProofsInTheBook.ZinanFFCT61
open ProofsInTheBook.ZinanFFCT64
open ProofsInTheBook.ZinanFFCT65
open ProofsInTheBook.ZinanFFCT66
open ProofsInTheBook.ZinanFFCT68
open ProofsInTheBook.ZinanFFCT69
open ProofsInTheBook.ZinanFFCT70
open ProofsInTheBook.ZinanFFCT71
open ProofsInTheBook.ZinanFFCT74
open ProofsInTheBook.ZinanFFCT76

namespace ProofsInTheBook.ZinanFFCT77

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000

/-! ## Endpoint-aware residue shapes. -/

/-- Boundary progress, allowing the normalized seed to appear on either the arm
or its mirror. -/
def MirrorBoundaryZeroProgress {n : ℕ} (P B : Fin (n + 1) → S2) : Prop :=
  BoundaryZeroProgress P B ∨ BoundaryZeroProgress (mirrorArm P) (mirrorArm B)

/-- The v9 weak-entry wrap seed: the cyclic wrap zero may already close the
endpoint, or may normalize on either orientation. -/
def WeakVanishingWrapSeedResidueV9 : Prop :=
  ∀ {n : ℕ} (P B : Fin (n + 1) → S2),
    WeakConvexSphArm P → PositiveJoints P → NoNonadjacentRepeat P →
    StrictConvexSphArm B → SameSides P B → JointLe P B →
    ∀ a b : Fin (n + 1),
      b ≠ a → b ≠ a + 1 → ¬ a.val + 1 < n + 1 →
      sOrient (P a) (P (a + 1)) (P b) = 0 →
        MirrorBoundaryZeroProgress P B

/-- The v9 WBS wrap seed: the opened cyclic wrap zero may already close the
opened endpoint, or may normalize on either orientation. -/
def SupportStuckWBSWrapSeedResidueV9 : Prop :=
  ∀ {n : ℕ} (A B : Fin (n + 1) → S2),
    StrictConvexSphArm A → StrictConvexSphArm B → SameSides A B → JointLe A B →
    ∀ k : Fin (n - 1), jointAngle A k < jointAngle B k →
    SupportStuckWBS A B k →
    ∀ a b : Fin (n + 1),
      b ≠ a → b ≠ a + 1 → ¬ a.val + 1 < n + 1 →
      sOrient (openedWBS A B k a) (openedWBS A B k (a + 1)) (openedWBS A B k b) = 0 →
        MirrorBoundaryZeroProgress (openedWBS A B k) B

/-- The v9 signed tail residue: unlike the v8 global tail endpoint field, this
version is consumed at the live NR induction level and therefore carries the
dimension IH needed by the normalized-zero endpoint dispatch. -/
def BPosANegTailCornerResidueV9 : Prop :=
  ∀ {n : ℕ} {P B : Fin (n + 1) → S2},
    WeakConvexSphArm P → PositiveJoints P → StrictConvexSphArm B →
    SameSides P B → JointLe P B → NoNonadjacentRepeat P →
    (∃ h : E3, ‖h‖ = 1 ∧ ∀ r : Fin (n + 1), 0 < (⟪h, (P r : E3)⟫ : ℝ)) →
    (∀ m : ℕ, m < n → MainPlusNR m) →
    ∀ {i : ℕ}, i + 1 < n →
    ∀ (hi : i < n + 1) (hi1 : i + 1 < n + 1) (hn : n < n + 1),
    ∀ {a b : ℝ},
      (P ⟨i, hi⟩ : E3) = a • (P ⟨i + 1, hi1⟩ : E3) + b • (P ⟨n, hn⟩ : E3) →
      0 < b → a < 0 → endpt P ≤ endpt B

/-! ## Bridges from v9 progress into the NR endpoint consumers. -/

/-- Coefficient dispatch at a fixed NR induction level, using the v9 live tail
residue for the `b > 0, a < 0, j = n` branch. -/
theorem endpoint_of_span_at_level_nr_v9
    (htail : BPosANegTailCornerResidueV9)
    {n : ℕ} {P B : Fin (n + 1) → S2}
    (hP : WeakConvexSphArm P) (hpos : PositiveJoints P) (hnr : NoNonadjacentRepeat P)
    (hB : StrictConvexSphArm B)
    (hside : SameSides P B) (hangle : JointLe P B)
    (hhem : ∃ h : E3, ‖h‖ = 1 ∧ ∀ r : Fin (n + 1), 0 < (⟪h, (P r : E3)⟫ : ℝ))
    (ihdim : ∀ m : ℕ, m < n → MainPlusNR m)
    {i j : ℕ} (hij : i + 1 < j)
    (hi : i < n + 1) (hi1 : i + 1 < n + 1) (hj : j < n + 1)
    {a b : ℝ}
    (hspan : (P ⟨i, hi⟩ : E3) =
      a • (P ⟨i + 1, hi1⟩ : E3) + b • (P ⟨j, hj⟩ : E3)) :
    endpt P ≤ endpt B := by
  rcases lt_trichotomy b 0 with hbneg | hb0 | hbpos
  · by_cases hi2 : i + 2 < n + 1
    · exact False.elim (midFold_bneg_false hP hpos hB hangle hi hi1 hi2 hj hhem hspan hbneg)
    · exact bneg_tail_closed_by_normalization hP hpos hB hside hangle hnr hhem
        hij hi hi1 hj hspan hbneg hi2
  · exact False.elim (span_bzero_false_of_weak hP hi hi1 hj hspan hb0)
  · rcases lt_trichotomy a 0 with haneg | ha0 | hapos
    · by_cases hj1 : j + 1 < n + 1
      · exact False.elim
          (bpos_aneg_false_of_successor hP hpos hB hangle hnr hhem
            hij hi hi1 hj hj1 hspan hbpos haneg)
      · have hjn : j = n := by omega
        subst hjn
        exact htail hP hpos hB hside hangle hnr hhem ihdim
          hij hi hi1 hj hspan hbpos haneg
    · have hij2 : i + 2 ≤ j := by omega
      exact False.elim (span_azero_bpos_false_of_noRepeat hnr hi hi1 hj hij2 hspan hbpos ha0)
    · exact bpos_apos_endpoint_at_level_nr hP hpos hnr hB hside hangle ihdim
        hij hi hi1 hj hspan hbpos hapos

/-- A normalized zero support on a weak-positive NR arm closes at a fixed NR
level through the v9 tail residue. -/
theorem endpoint_of_normalized_vanishing_support_at_level_nr_v9
    (htail : BPosANegTailCornerResidueV9)
    {n : ℕ} {P B : Fin (n + 1) → S2}
    (hP : WeakConvexSphArm P) (hpos : PositiveJoints P) (hnr : NoNonadjacentRepeat P)
    (hB : StrictConvexSphArm B)
    (hside : SameSides P B) (hangle : JointLe P B)
    (hhem : ∃ h : E3, ‖h‖ = 1 ∧ ∀ r : Fin (n + 1), 0 < (⟪h, (P r : E3)⟫ : ℝ))
    (ihdim : ∀ m : ℕ, m < n → MainPlusNR m)
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
    rwa [ProofsInTheBook.ZinanFFCT12.det3_cyclic (P ⟨i, hi⟩ : E3)
      (P ⟨i + 1, hi1⟩ : E3) (P ⟨j, hj⟩ : E3)] at hzero
  obtain ⟨a, b, hspan⟩ :=
    lin_indep_span_of_det3_zero (P ⟨i + 1, hi1⟩).2 (P ⟨j, hj⟩).2
      (fun h => hdist (S2.ext h)) hanti hdet
  exact endpoint_of_span_at_level_nr_v9 htail hP hpos hnr hB hside hangle
    ⟨h, hnorm, hhemPos⟩ ihdim hij hi hi1 hj hspan

/-- Consume a `BoundaryZeroProgress` payload at a live NR level. -/
theorem endpoint_of_boundaryZeroProgress_at_level_nr
    (htail : BPosANegTailCornerResidueV9)
    {n : ℕ} {P B : Fin (n + 1) → S2}
    (hP : WeakConvexSphArm P) (hpos : PositiveJoints P) (hnr : NoNonadjacentRepeat P)
    (hB : StrictConvexSphArm B)
    (hside : SameSides P B) (hangle : JointLe P B)
    (hhem : ∃ h : E3, ‖h‖ = 1 ∧ ∀ r : Fin (n + 1), 0 < (⟪h, (P r : E3)⟫ : ℝ))
    (ihdim : ∀ m : ℕ, m < n → MainPlusNR m)
    (hprog : BoundaryZeroProgress P B) :
    endpt P ≤ endpt B := by
  rcases hprog with hnorm | hend
  · obtain ⟨i, j, hi, hi1, hj, hij, hzero⟩ := hnorm
    exact endpoint_of_normalized_vanishing_support_at_level_nr_v9 htail hP hpos hnr hB
      hside hangle hhem ihdim hij hi hi1 hj hzero
  · exact hend

/-- Consume mirror-aware boundary progress at a live NR level. -/
theorem endpoint_of_mirrorBoundaryZeroProgress_at_level_nr
    (htail : BPosANegTailCornerResidueV9)
    {n : ℕ} {P B : Fin (n + 1) → S2}
    (hP : WeakConvexSphArm P) (hpos : PositiveJoints P) (hnr : NoNonadjacentRepeat P)
    (hB : StrictConvexSphArm B)
    (hside : SameSides P B) (hangle : JointLe P B)
    (hhem : ∃ h : E3, ‖h‖ = 1 ∧ ∀ r : Fin (n + 1), 0 < (⟪h, (P r : E3)⟫ : ℝ))
    (ihdim : ∀ m : ℕ, m < n → MainPlusNR m)
    (hprog : MirrorBoundaryZeroProgress P B) :
    endpt P ≤ endpt B := by
  rcases hprog with hdir | hmir
  · exact endpoint_of_boundaryZeroProgress_at_level_nr htail hP hpos hnr hB
      hside hangle hhem ihdim hdir
  · have hmirror : endpt (mirrorArm P) ≤ endpt (mirrorArm B) :=
      endpoint_of_boundaryZeroProgress_at_level_nr htail
        (weakConvex_mirrorArm hP) (positiveJoints_mirrorArm hpos)
        (noNonadjacentRepeat_mirrorArm hnr)
        (strictConvex_mirrorArm hB) (sameSides_mirrorArm hside) (jointLe_mirrorArm hangle)
        (weakConvex_mirrorArm hP).closed_convex.open_hemisphere ihdim hmir
    simpa [endpt_mirrorArm] using hmirror

/-! ## Weak-entry wrap branch. -/

/-- Raw weak-entry vanishing support normalized or endpoint-closed, modulo only
the v9 wrap-edge residue. -/
theorem weakBoundaryProgress_of_wrapSeedResidueV9
    (hwrap : WeakVanishingWrapSeedResidueV9)
    {n : ℕ} {P B : Fin (n + 1) → S2}
    (hP : WeakConvexSphArm P) (hpos : PositiveJoints P) (hnr : NoNonadjacentRepeat P)
    (hB : StrictConvexSphArm B) (hside : SameSides P B) (hangle : JointLe P B)
    (hvanish : ∃ a b : Fin (n + 1), b ≠ a ∧ b ≠ a + 1 ∧
      sOrient (P a) (P (a + 1)) (P b) = 0) :
    MirrorBoundaryZeroProgress P B := by
  obtain ⟨a, b, hne, hne1, hsupp⟩ := hvanish
  by_cases hadj : a.val + 1 < n + 1
  · rcases orientationNormalized P hne hne1 hsupp hadj with hdir | hrev
    · obtain ⟨i, j, hij, hj, hzero⟩ := hdir
      left
      left
      refine ⟨i, j, by omega, by omega, by omega, hij, ?_⟩
      simpa using hzero
    · obtain ⟨i, j, hij, hj, hzero⟩ := hrev
      right
      left
      refine ⟨i, j, by omega, by omega, by omega, hij, ?_⟩
      exact mirrorArm_sOrient_zero_of_revArm_zero P (by omega) (by omega) (by omega) hzero
  · exact hwrap P B hP hpos hnr hB hside hangle a b hne hne1 hadj hsupp

/-- Static weak-entry endpoint closure under NR, consuming v9 boundary progress
directly. -/
def WeakPositiveCutReadyNRV9 : Prop :=
  WeakVanishingWrapSeedResidueV9 → BPosANegTailCornerResidueV9 →
    ∀ {n : ℕ} {P B : Fin (n + 1) → S2},
      WeakConvexSphArm P → PositiveJoints P → NoNonadjacentRepeat P →
      StrictConvexSphArm B → SameSides P B → JointLe P B →
      (∀ m : ℕ, m < n → MainPlusNR m) →
      (∃ a b : Fin (n + 1), b ≠ a ∧ b ≠ a + 1 ∧
        sOrient (P a) (P (a + 1)) (P b) = 0) →
      endpt P ≤ endpt B

theorem weakPositiveCutReadyNR_v9_holds : WeakPositiveCutReadyNRV9 := by
  intro hwrap htail n P B hP hpos hnr hB hside hangle ihdim hvanish
  have hprog := weakBoundaryProgress_of_wrapSeedResidueV9 hwrap
    hP hpos hnr hB hside hangle hvanish
  exact endpoint_of_mirrorBoundaryZeroProgress_at_level_nr htail
    hP hpos hnr hB hside hangle hP.closed_convex.open_hemisphere ihdim hprog

/-! ## WBS support-stuck wrap branch. -/

/-- Raw support-stuck WBS vanishing support normalized or endpoint-closed, modulo
only the v9 WBS wrap residue. -/
theorem supportStuckWBS_boundaryProgress_of_wrapSeedResidueV9
    (hwrap : SupportStuckWBSWrapSeedResidueV9) :
    ∀ {n : ℕ} (A B : Fin (n + 1) → S2),
      StrictConvexSphArm A → StrictConvexSphArm B → SameSides A B → JointLe A B →
      ∀ k : Fin (n - 1), jointAngle A k < jointAngle B k →
      SupportStuckWBS A B k →
        MirrorBoundaryZeroProgress (openedWBS A B k) B := by
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
      left
      refine ⟨i, j, by omega, by omega, by omega, hij, ?_⟩
      simpa using hzero
    · obtain ⟨i, j, hij, hj, hzero⟩ := hrev
      right
      left
      refine ⟨i, j, by omega, by omega, by omega, hij, ?_⟩
      exact mirrorArm_sOrient_zero_of_revArm_zero (openedWBS A B k)
        (by omega) (by omega) (by omega) hzero
  · exact hwrap A B hA hB hside hangle k hkdef hstuck a b hne hne1 hadj hsupp

structure Ch13FinalSurface77 : Prop where
  hweakWrapSeed : WeakVanishingWrapSeedResidueV9
  hwrapSeed : SupportStuckWBSWrapSeedResidueV9
  hcross : CrossPieceNoCollisionAtSup
  hbpos_aneg_tail : BPosANegTailCornerResidueV9

theorem supportStuckWBS_endpoint_dispatch_at_level_nr_v9
    (res : Ch13FinalSurface77)
    {n : ℕ} (ihdim : ∀ m : ℕ, m < n → MainPlusNR m)
    (A B : Fin (n + 1) → S2)
    (hA : StrictConvexSphArm A) (hB : StrictConvexSphArm B)
    (hside : SameSides A B) (hangle : JointLe A B)
    (k : Fin (n - 1)) (hkdef : jointAngle A k < jointAngle B k)
    (hstuck : SupportStuckWBS A B k) :
    endpt (openedWBS A B k) ≤ endpt B := by
  obtain ⟨hka, hkt⟩ := shortArcs_of_strict hA k
  have hwrapArc :
      ShortArc (openTail A (openingAxis k) (-(monitoredSupWBS A B k)) (Fin.last n))
        (openTail A (openingAxis k) (-(monitoredSupWBS A B k)) 0) :=
    openedWrapShortArc_at_supWBS hA hB hka hkt hkdef
  have hPweak : WeakConvexSphArm (openedWBS A B k) := by
    unfold openedWBS
    exact supportStuckWBS_weakConvex hA hB hka hkt hkdef hwrapArc
  have hPpos : PositiveJoints (openedWBS A B k) := by
    intro r
    unfold openedWBS
    exact (openedJoints_in_Ioo_at_supWBS hA hB hka hkt hkdef r).1
  have hedge := openedEdges_short_at_supWBS_of_wrap (A := A) (B := B) hA hwrapArc
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
    openedWBS_noNonadjacentRepeat_of_crossPiece res.hcross A B hA hB hside hangle k hkdef hstuck
  have hprog :=
    supportStuckWBS_boundaryProgress_of_wrapSeedResidueV9 res.hwrapSeed
      A B hA hB hside hangle k hkdef hstuck
  exact endpoint_of_mirrorBoundaryZeroProgress_at_level_nr res.hbpos_aneg_tail
    hPweak hPpos hnr hB hside' hangle' hhem ihdim hprog

theorem open_step_wbs_nr_v9 (res : Ch13FinalSurface77)
    {n : ℕ} (_hn : 2 ≤ n) (ihdim : ∀ m : ℕ, m < n → MainPlusNR m)
    {A B : Fin (n + 1) → S2}
    (hA : StrictConvexSphArm A) (hB : StrictConvexSphArm B)
    (hside : SameSides A B) (hangle : JointLe A B)
    (ihdef : ∀ A' B' : Fin (n + 1) → S2,
      WeakConvexSphArm A' → PositiveJoints A' → NoNonadjacentRepeat A' →
      StrictConvexSphArm B' → SameSides A' B' → JointLe A' B' →
      deficitCount A' B' < deficitCount A B → endpt A' ≤ endpt B')
    (k : Fin (n - 1)) (hkdef : jointAngle A k < jointAngle B k) :
    endpt A ≤ endpt B := by
  set K : Fin (n + 1) := openingAxis k with hK
  set δ : ℝ := monitoredSupWBS A B k with hδ
  set A' : Fin (n + 1) → S2 := openTail A K (-δ) with hA'
  obtain ⟨hka, hkt⟩ := shortArcs_of_strict hA k
  have hjointk : jointAngle A' k = openedInteriorJointAngle A k (-δ) := by
    rw [hA']; exact jointAngle_openTail_eq_openedInterior A k (-δ)
  have hslack : openedInteriorJointAngle A k (-δ) ≤ jointAngle B k :=
    openedInteriorJoint_le_at_supWBS hA hka hkt hkdef
  have hside' : SameSides A' B := by
    intro i; rw [hA', openTail_preserves_sides A K (-δ) i]; exact hside i
  have hangle' : JointLe A' B := by
    intro r
    by_cases hrk : r = k
    · rw [hrk, hjointk]; exact hslack
    · rw [hA', jointAngle_openTail_eq_of_ne A k (-δ) hrk]; exact hangle r
  have hmono : endpt A ≤ endpt A' := glueWBS_clause_i hA hka hkt hkdef
  by_cases hstuck : SupportStuckWBS A B k
  · have hAB0 : endpt (openedWBS A B k) ≤ endpt B :=
      supportStuckWBS_endpoint_dispatch_at_level_nr_v9 res ihdim
        A B hA hB hside hangle k hkdef hstuck
    have hAB : endpt A' ≤ endpt B := by
      rw [hA']
      exact hAB0
    exact le_trans hmono hAB
  · have hreach : ReachWBS A B k := by
      rcases glueWBS_clause_ii hA hB hka hkt hkdef hstuck with hr | hbase
      · exact hr
      · rcases BaseStuckProgressWBS_holds n A B hA hB k hkdef hbase with hr | hvan
        · exact hr
        · exfalso
          obtain ⟨i, j, hji, hji1, heq⟩ := hvan
          exact hstuck ⟨⟨(i, j), ⟨hji, hji1⟩⟩, by rw [supportConstraint_apply]; exact heq⟩
    have hstrict : StrictConvexSphArm A' := by
      rw [hA']; exact reachWBS_strictConvex hA hB hka hkt hkdef hstuck
    have hreach_k : jointAngle A' k = jointAngle B k := by rw [hjointk]; exact hreach
    have hdrop : deficitCount A' B < deficitCount A B := by
      rw [hA']; exact deficitCount_openTail_reach_lt A B k (-δ) hkdef hreach_k
    have hAB : endpt A' ≤ endpt B :=
      ihdef A' B (strictConvexSphArm_toWeak hstrict)
        (strictConvexSphArm_positiveJoints hstrict) (strictConvex_noNonadjacentRepeat hstrict)
        hB hside' hangle' hdrop
    exact le_trans hmono hAB

/-! ## NR opening step and chapter headline. -/

theorem szOpeningStepPlusNR_v9 (res : Ch13FinalSurface77) : SZOpeningStepPlusNR := by
  intro n hn ihdim A B hA hposA hnrA hB hside hangle ihdef
  rcases strict_or_vanishing hA with hvanish | hAstrict
  · exact weakPositiveCutReadyNR_v9_holds res.hweakWrapSeed res.hbpos_aneg_tail
      hA hposA hnrA hB hside hangle ihdim hvanish
  · by_cases hnd : deficitCount A B = 0
    · exact congruence_step hAstrict hB hside hangle hnd
    · have hpos : 0 < deficitCount A B := Nat.pos_of_ne_zero hnd
      obtain ⟨k, hkdef⟩ := exists_deficit_of_pos hpos
      exact open_step_wbs_nr_v9 res hn ihdim hAstrict hB hside hangle ihdef k hkdef

theorem mainPlusNR_at_level_v9 (res : Ch13FinalSurface77) {n : ℕ} (hn : 2 ≤ n)
    (ihdim : ∀ m : ℕ, m < n → MainPlusNR m) : MainPlusNR n := by
  intro A B hA hposA hnrA hB hside hangle
  let hstep := szOpeningStepPlusNR_v9 res
  have hrec :
      ∀ d : ℕ, ∀ A B : Fin (n + 1) → S2,
        WeakConvexSphArm A → PositiveJoints A → NoNonadjacentRepeat A →
        StrictConvexSphArm B → SameSides A B → JointLe A B →
        deficitCount A B = d → endpt A ≤ endpt B := by
    intro d
    induction d using Nat.strong_induction_on with
    | _ d IH =>
      intro A B hA hposA hnrA hB hside hangle hdef
      refine hstep n hn ihdim A B hA hposA hnrA hB hside hangle ?_
      intro A' B' hA' hposA' hnrA' hB' hside' hangle' hlt
      exact IH (deficitCount A' B') (hdef ▸ hlt) A' B' hA' hposA' hnrA'
        hB' hside' hangle' rfl
  exact hrec (deficitCount A B) A B hA hposA hnrA hB hside hangle rfl

theorem mainPlusNR_all_v9 (res : Ch13FinalSurface77) :
    ∀ n : ℕ, 2 ≤ n → MainPlusNR n := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n IH =>
    intro hn A B hA hposA hnrA hB hside hangle
    have ihdim : ∀ m : ℕ, m < n → MainPlusNR m := by
      intro m hm
      rcases Nat.lt_or_ge m 2 with h2 | h2
      · exact mainPlusNR_of_lt_two h2
      · exact IH m hm h2
    exact mainPlusNR_at_level_v9 res hn ihdim A B hA hposA hnrA hB hside hangle

/-- Complete honest Chapter 13 arm monotonicity statement for the endpoint-aware
v9 interface: the two wrap residues may return `BoundaryZeroProgress`
endpoint branches directly; the remaining explicit non-cross inputs are
`CrossPieceNoCollisionAtSup` and the live-IH signed tail endpoint residue. -/
theorem spherical_arm_mono_final_ch13_v9 (res : Ch13FinalSurface77)
    {n : ℕ} (hn : 2 ≤ n) (A B : Fin (n + 1) → S2)
    (hA : StrictConvexSphArm A) (hB : StrictConvexSphArm B)
    (hside : ∀ i : Fin n, sideLen A i = sideLen B i)
    (hangle : ∀ i : Fin (n - 1), jointAngle A i ≤ jointAngle B i) :
    sDist (A 0) (A (Fin.last n)) ≤
      sDist (B 0) (B (Fin.last n)) :=
  (mainPlusNR_all_v9 res n hn) A B (strictConvexSphArm_toWeak hA)
    (strictConvexSphArm_positiveJoints hA) (strictConvex_noNonadjacentRepeat hA)
    hB hside hangle

/-! ## Guards. -/

theorem boundaryZeroProgress_endpoint_target_satisfiable {n : ℕ}
    (A : Fin (n + 1) → S2) :
    BoundaryZeroProgress A A := Or.inr (le_refl _)

theorem spherical_arm_mono_final_ch13_v9_conclusion_satisfiable {n : ℕ}
    (A : Fin (n + 1) → S2) :
    sDist (A 0) (A (Fin.last n)) ≤ sDist (A 0) (A (Fin.last n)) := le_refl _

#print axioms endpoint_of_boundaryZeroProgress_at_level_nr
#print axioms endpoint_of_mirrorBoundaryZeroProgress_at_level_nr
#print axioms endpoint_of_normalized_vanishing_support_at_level_nr_v9
#print axioms weakBoundaryProgress_of_wrapSeedResidueV9
#print axioms weakPositiveCutReadyNR_v9_holds
#print axioms supportStuckWBS_boundaryProgress_of_wrapSeedResidueV9
#print axioms supportStuckWBS_endpoint_dispatch_at_level_nr_v9
#print axioms szOpeningStepPlusNR_v9
#print axioms mainPlusNR_all_v9
#print axioms spherical_arm_mono_final_ch13_v9

end ProofsInTheBook.ZinanFFCT77
