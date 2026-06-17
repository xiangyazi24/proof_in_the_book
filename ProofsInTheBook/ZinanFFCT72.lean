import ProofsInTheBook.ZinanFFCT71

/-!
# `ZinanFFCT72` -- step-level assembly with the `b > 0, a > 0` endpoint field removed

This file moves the final assembly back to the `SZOpeningStepPlus` level so the
support-stuck endpoint dispatch can consume the live dimension IH.  The `hbpos_apos`
endpoint case is no longer a surface field.

The full `MainPlus` recursion still has the already-isolated weak-entry CUT inputs:
`WeakPositiveCutReady` and `FoldedFlatCutTransportPlus`.  Without them the weak
`PositiveJoints` entry branch of `SZOpeningStepPlus` cannot be typed honestly.
-/

noncomputable section

open scoped RealInnerProductSpace NNReal
open ProofsInTheBook.SphericalKernel ProofsInTheBook.SphericalArm
open ProofsInTheBook.SphericalRotation
open ProofsInTheBook.SphericalSZInduction
open ProofsInTheBook.SphericalSZFinal
open ProofsInTheBook.SphericalSZClose
open ProofsInTheBook.SphericalArmAssembly
open ProofsInTheBook.SphericalMonitoredSup
open ProofsInTheBook.SphericalOpeningOutcome
open ProofsInTheBook.SphericalReachStuck
open ProofsInTheBook.SphericalStuckGeneral
open ProofsInTheBook.ZinanFFCT18
open ProofsInTheBook.ZinanFFCT19
open ProofsInTheBook.ZinanFFCT23
open ProofsInTheBook.ZinanFFCT24
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

namespace ProofsInTheBook.ZinanFFCT72

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000

/-! ## The positive-positive branch at a live induction level. -/

/-- A span relation across `(p, mid, q)` forces the oriented support to vanish. -/
theorem sOrient_zero_of_span_coeff {p mid q : S2} {a b : ℝ}
    (hspan : (p : E3) = a • (mid : E3) + b • (q : E3)) :
    sOrient p mid q = 0 := by
  rw [sOrient, hspan, det3_add_fst, det3_smul_fst, det3_smul_fst]
  rw [ProofsInTheBook.SphericalDiagCut.det3_self_left,
    ProofsInTheBook.SphericalDiagCut.det3_self_right]
  ring

/-- The normalized positive-positive branch supplies a weak-entry cut-ready datum via
`WeakPositiveCutReady`, then closes with the live dimension IH. -/
theorem bpos_apos_endpoint_of_weakCut_at_level
    (hwpc : WeakPositiveCutReady) (hffct : FoldedFlatCutTransportPlus)
    {n : ℕ} {P B : Fin (n + 1) → S2}
    (hP : WeakConvexSphArm P) (hpos : PositiveJoints P) (hB : StrictConvexSphArm B)
    (hside : SameSides P B) (hangle : JointLe P B)
    (_hnr : NoNonadjacentRepeat P)
    (_hhem : ∃ h : E3, ‖h‖ = 1 ∧ ∀ r : Fin (n + 1), 0 < (⟪h, (P r : E3)⟫ : ℝ))
    (ihdim : ∀ m : ℕ, m < n → MainPlus m)
    {i j : ℕ} (hij : i + 1 < j)
    (hi : i < n + 1) (hi1 : i + 1 < n + 1) (hj : j < n + 1)
    {a b : ℝ}
    (hspan : (P ⟨i, hi⟩ : E3) =
      a • (P ⟨i + 1, hi1⟩ : E3) + b • (P ⟨j, hj⟩ : E3))
    (_hbpos : 0 < b) (_hapos : 0 < a) :
    endpt P ≤ endpt B := by
  have hsucc : ((⟨i, hi⟩ : Fin (n + 1)) + 1) = (⟨i + 1, hi1⟩ : Fin (n + 1)) := by
    apply Fin.ext
    have hone : ((1 : Fin (n + 1)) : ℕ) = 1 := by
      rw [Fin.val_one']; exact Nat.mod_eq_of_lt (by omega)
    rw [Fin.val_add, Fin.val_mk, hone, Nat.mod_eq_of_lt (show i + 1 < n + 1 by omega)]
  have hsupp :
      sOrient (P ⟨i, hi⟩) (P ((⟨i, hi⟩ : Fin (n + 1)) + 1)) (P ⟨j, hj⟩) = 0 := by
    rw [hsucc]
    exact sOrient_zero_of_span_coeff hspan
  have hvanish :
      ∃ u v : Fin (n + 1), v ≠ u ∧ v ≠ u + 1 ∧
        sOrient (P u) (P (u + 1)) (P v) = 0 := by
    refine ⟨⟨i, hi⟩, ⟨j, hj⟩, ?_, ?_, hsupp⟩
    · intro h
      have : j = i := by simpa using congrArg Fin.val h
      omega
    · intro h
      rw [hsucc] at h
      have : j = i + 1 := by simpa using congrArg Fin.val h
      omega
  have hcr : CutReadyPlus P B := hwpc P B hP hpos hB hside hangle hvanish
  exact cut_step_from_stuckAtK_plus hffct hP.two_le ihdim hP hpos hB hside hangle hcr

/-- Coefficient dispatch at a fixed induction level.  The `b > 0, a > 0`
case uses `ihdim` through the modern cut-ready route instead of a headline
`BPosAPosEndpointCase` field. -/
theorem endpoint_of_span_at_level
    (hwpc : WeakPositiveCutReady) (hffct : FoldedFlatCutTransportPlus)
    (htail : BPosANegTailCornerResidue)
    {n : ℕ} {P B : Fin (n + 1) → S2}
    (hP : WeakConvexSphArm P) (hpos : PositiveJoints P) (hB : StrictConvexSphArm B)
    (hside : SameSides P B) (hangle : JointLe P B) (hnr : NoNonadjacentRepeat P)
    (hhem : ∃ h : E3, ‖h‖ = 1 ∧ ∀ r : Fin (n + 1), 0 < (⟪h, (P r : E3)⟫ : ℝ))
    (ihdim : ∀ m : ℕ, m < n → MainPlus m)
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
    · exact bpos_aneg_endpointConsumer_of_tail htail hP hpos hB hside hangle hnr hhem
        hij hi hi1 hj hspan hbpos haneg
    · have hij2 : i + 2 ≤ j := by omega
      exact False.elim (span_azero_bpos_false_of_noRepeat hnr hi hi1 hj hij2 hspan hbpos ha0)
    · exact bpos_apos_endpoint_of_weakCut_at_level hwpc hffct hP hpos hB hside hangle hnr hhem
        ihdim hij hi hi1 hj hspan hbpos hapos

/-- A normalized vanishing support on a weak-positive arm closes at a fixed
induction level. -/
theorem endpoint_of_normalized_vanishing_support_at_level
    (hwpc : WeakPositiveCutReady) (hffct : FoldedFlatCutTransportPlus)
    (htail : BPosANegTailCornerResidue)
    {n : ℕ} {P B : Fin (n + 1) → S2}
    (hP : WeakConvexSphArm P) (hpos : PositiveJoints P) (hB : StrictConvexSphArm B)
    (hside : SameSides P B) (hangle : JointLe P B) (hnr : NoNonadjacentRepeat P)
    (hhem : ∃ h : E3, ‖h‖ = 1 ∧ ∀ r : Fin (n + 1), 0 < (⟪h, (P r : E3)⟫ : ℝ))
    (ihdim : ∀ m : ℕ, m < n → MainPlus m)
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
    rwa [ProofsInTheBook.ZinanFFCT12.det3_cyclic (P ⟨i, hi⟩ : E3) (P ⟨i + 1, hi1⟩ : E3)
      (P ⟨j, hj⟩ : E3)] at hzero
  obtain ⟨a, b, hspan⟩ :=
    lin_indep_span_of_det3_zero (P ⟨i + 1, hi1⟩).2 (P ⟨j, hj⟩).2
      (fun h => hdist (S2.ext h)) hanti hdet
  exact endpoint_of_span_at_level hwpc hffct htail hP hpos hB hside hangle hnr
    ⟨h, hnorm, hhemPos⟩ ihdim hij hi hi1 hj hspan

/-! ## WBS support-stuck endpoint dispatch with the live dimension IH. -/

theorem supportStuckWBS_endpoint_dispatch_at_level
    (hwrap : SupportStuckWBSWrapSeedResidue)
    (hcross : CrossPieceNoCollisionAtSup)
    (hwpc : WeakPositiveCutReady) (hffct : FoldedFlatCutTransportPlus)
    (htail : BPosANegTailCornerResidue)
    {n : ℕ} (ihdim : ∀ m : ℕ, m < n → MainPlus m)
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
    openedWBS_noNonadjacentRepeat_of_crossPiece hcross A B hA hB hside hangle k hkdef hstuck
  rcases (mirrorSeed_of_wrapSeedResidue hwrap) A B hA hB hside hangle k hkdef hstuck with hdir | hmir
  · obtain ⟨i, j, hi, hi1, hj, hij, hzero⟩ := hdir
    exact endpoint_of_normalized_vanishing_support_at_level hwpc hffct htail
      hPweak hPpos hB hside' hangle' hnr hhem ihdim hij hi hi1 hj hzero
  · obtain ⟨i, j, hi, hi1, hj, hij, hzero⟩ := hmir
    have hmirror : endpt (mirrorArm (openedWBS A B k)) ≤ endpt (mirrorArm B) :=
      endpoint_of_normalized_vanishing_support_at_level hwpc hffct htail
        (weakConvex_mirrorArm hPweak) (positiveJoints_mirrorArm hPpos)
        (strictConvex_mirrorArm hB) (sameSides_mirrorArm hside') (jointLe_mirrorArm hangle')
        (noNonadjacentRepeat_mirrorArm hnr)
        (weakConvex_mirrorArm hPweak).closed_convex.open_hemisphere ihdim
        hij hi hi1 hj hzero
    simpa [endpt_mirrorArm] using hmirror

/-! ## Step-level assembly. -/

structure Ch13FinalSurface72 : Prop where
  /-- Weak-entry vanishing support to modern cut-ready data. -/
  hwpc : WeakPositiveCutReady
  /-- Folded-flat transport used by the weak-entry modern cut. -/
  hffct : FoldedFlatCutTransportPlus
  /-- Raw WBS wrap seed residue; non-wrap seeds are normalized by FFCT71. -/
  hwrapSeed : SupportStuckWBSWrapSeedResidue
  /-- Cross-piece no-collision, used to get opened-arm no-repeat. -/
  hcross : CrossPieceNoCollisionAtSup
  /-- The remaining `b > 0, a < 0` tail endpoint. -/
  hbpos_aneg_tail : BPosANegTailCornerResidue

theorem open_step_wbs_v6 (res : Ch13FinalSurface72)
    {n : ℕ} (_hn : 2 ≤ n) (ihdim : ∀ m : ℕ, m < n → MainPlus m)
    {A B : Fin (n + 1) → S2}
    (hA : StrictConvexSphArm A) (hB : StrictConvexSphArm B)
    (hside : SameSides A B) (hangle : JointLe A B)
    (ihdef : ∀ A' B' : Fin (n + 1) → S2,
      WeakConvexSphArm A' → PositiveJoints A' →
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
      supportStuckWBS_endpoint_dispatch_at_level res.hwrapSeed res.hcross res.hwpc res.hffct
        res.hbpos_aneg_tail ihdim A B hA hB hside hangle k hkdef hstuck
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
        (strictConvexSphArm_positiveJoints hstrict) hB hside' hangle' hdrop
    exact le_trans hmono hAB

/-- The step-level `SZOpeningStepPlus` assembly.  The support-stuck branch no
longer asks for a global `BPosAPosEndpointCase`; the positive-positive subcase
uses the local `ihdim`. -/
theorem szOpeningStepPlus_v6 (res : Ch13FinalSurface72) : SZOpeningStepPlus := by
  intro n hn ihdim A B hA hposA hB hside hangle ihdefRaw
  have ihdef : ∀ A' B' : Fin (n + 1) → S2,
      WeakConvexSphArm A' → PositiveJoints A' →
      StrictConvexSphArm B' → SameSides A' B' → JointLe A' B' →
      deficitCount A' B' < deficitCount A B → endpt A' ≤ endpt B' := by
    intro A' B' hA' hposA' hB' hside' hangle' hlt
    exact ihdefRaw A' B' hA' hposA' hB' hside' hangle' hlt
  rcases strict_or_vanishing hA with hvanish | hAstrict
  · have hcr : CutReadyPlus A B := res.hwpc A B hA hposA hB hside hangle hvanish
    exact cut_step_from_stuckAtK_plus res.hffct hn ihdim hA hposA hB hside hangle hcr
  · by_cases hnd : deficitCount A B = 0
    · exact congruence_step hAstrict hB hside hangle hnd
    · have hpos : 0 < deficitCount A B := Nat.pos_of_ne_zero hnd
      obtain ⟨k, hkdef⟩ := exists_deficit_of_pos hpos
      exact open_step_wbs_v6 res hn ihdim hAstrict hB hside hangle ihdef k hkdef

/-- Fixed-level `MainPlus` step for the v6 surface. -/
theorem mainPlus_at_level_v6 (res : Ch13FinalSurface72) {n : ℕ} (hn : 2 ≤ n)
    (ihdim : ∀ m : ℕ, m < n → MainPlus m) : MainPlus n := by
  intro A B hA hposA hB hside hangle
  exact mainPlus_at_level (szOpeningStepPlus_v6 res) hn ihdim
    (deficitCount A B) A B hA hposA hB hside hangle rfl

/-- Strong induction on the level, mirroring FFCT19's banked recursion. -/
theorem mainPlus_all_v6 (res : Ch13FinalSurface72) : ∀ n : ℕ, 2 ≤ n → MainPlus n :=
  mainPlus_all (szOpeningStepPlus_v6 res)

/-- Chapter 13 strict-arm monotonicity through the v6 step-level surface. -/
theorem spherical_arm_mono_final_ch13_v6 (res : Ch13FinalSurface72)
    {n : ℕ} (hn : 2 ≤ n) (A B : Fin (n + 1) → S2)
    (hA : StrictConvexSphArm A) (hB : StrictConvexSphArm B)
    (hside : ∀ i : Fin n, sideLen A i = sideLen B i)
    (hangle : ∀ i : Fin (n - 1), jointAngle A i ≤ jointAngle B i) :
    sDist (A 0) (A (Fin.last n)) ≤ sDist (B 0) (B (Fin.last n)) :=
  spherical_arm_mono_of_stepPlus (szOpeningStepPlus_v6 res) hn A B hA hB hside hangle

/-- Guard: the v6 headline conclusion is a real endpoint inequality. -/
theorem spherical_arm_mono_final_ch13_v6_conclusion_satisfiable {n : ℕ}
    (A : Fin (n + 1) → S2) :
    sDist (A 0) (A (Fin.last n)) ≤ sDist (A 0) (A (Fin.last n)) := le_refl _

#print axioms sOrient_zero_of_span_coeff
#print axioms bpos_apos_endpoint_of_weakCut_at_level
#print axioms endpoint_of_normalized_vanishing_support_at_level
#print axioms supportStuckWBS_endpoint_dispatch_at_level
#print axioms szOpeningStepPlus_v6
#print axioms mainPlus_at_level_v6
#print axioms mainPlus_all_v6
#print axioms spherical_arm_mono_final_ch13_v6

end ProofsInTheBook.ZinanFFCT72
