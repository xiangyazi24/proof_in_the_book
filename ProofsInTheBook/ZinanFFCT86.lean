import ProofsInTheBook.ZinanFFCT85

/-!
# `ZinanFFCT86` -- localizing the cross-piece input

This layer removes `CrossPieceNoCollisionAtSup` from the v10 headline by
splitting the WBS support-stuck endpoint dispatch locally.  If the opened WBS
arm has no fixed/tail collision, the old no-repeat consumer runs.  If such a
collision exists, the branch is routed to the exact endpoint payload needed at
that stuck supremum.

The remaining residue is therefore strictly weaker than global no-collision:
`CrossPieceCollisionEndpointAtSup` asks only that an actual collision branch
already close the opened endpoint.

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
open ProofsInTheBook.ZinanFFCT12
open ProofsInTheBook.ZinanFFCT18
open ProofsInTheBook.ZinanFFCT22
open ProofsInTheBook.ZinanFFCT23
open ProofsInTheBook.ZinanFFCT24
open ProofsInTheBook.ZinanFFCT25
open ProofsInTheBook.ZinanFFCT45
open ProofsInTheBook.ZinanFFCT46
open ProofsInTheBook.ZinanFFCT47
open ProofsInTheBook.ZinanFFCT49
open ProofsInTheBook.ZinanFFCT52
open ProofsInTheBook.ZinanFFCT56
open ProofsInTheBook.ZinanFFCT61
open ProofsInTheBook.ZinanFFCT64
open ProofsInTheBook.ZinanFFCT65
open ProofsInTheBook.ZinanFFCT68
open ProofsInTheBook.ZinanFFCT69
open ProofsInTheBook.ZinanFFCT70
open ProofsInTheBook.ZinanFFCT71
open ProofsInTheBook.ZinanFFCT74
open ProofsInTheBook.ZinanFFCT75
open ProofsInTheBook.ZinanFFCT76
open ProofsInTheBook.ZinanFFCT77
open ProofsInTheBook.ZinanFFCT78
open ProofsInTheBook.ZinanFFCT79
open ProofsInTheBook.ZinanFFCT80
open ProofsInTheBook.ZinanFFCT81
open ProofsInTheBook.ZinanFFCT82
open ProofsInTheBook.ZinanFFCT83
open ProofsInTheBook.ZinanFFCT84
open ProofsInTheBook.ZinanFFCT85

namespace ProofsInTheBook.ZinanFFCT86

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1800000

/-! ## The smaller cross-piece endpoint residue. -/

/-- The only cross-piece information still needed by the localized dispatch:
if an actual fixed/tail collision occurs at the WBS support-stuck supremum, the
opened endpoint comparison already follows. -/
def CrossPieceCollisionEndpointAtSup : Prop :=
  ∀ {n : ℕ} (A B : Fin (n + 1) → S2),
    StrictConvexSphArm A → StrictConvexSphArm B → SameSides A B → JointLe A B →
    ∀ k : Fin (n - 1), jointAngle A k < jointAngle B k →
    SupportStuckWBS A B k →
      ∀ (r s : ℕ) (hr : r < n + 1) (hs : s < n + 1),
        r + 2 ≤ s →
        r ≤ (openingAxis k).val → (openingAxis k).val < s →
        openedWBS A B k ⟨r, hr⟩ = openedWBS A B k ⟨s, hs⟩ →
          endpt (openedWBS A B k) ≤ endpt B

/-- Global no-collision implies the new endpoint-on-collision residue
vacuously.  This records that the v11 surface is weaker than the v10 input. -/
theorem crossPieceCollisionEndpointAtSup_of_noCollision
    (hcross : CrossPieceNoCollisionAtSup) :
    CrossPieceCollisionEndpointAtSup := by
  intro n A B hA hB hside hangle k hkdef hstuck r s hr hs hrs hrK hKs heq
  exact False.elim
    ((hcross A B hA hB hside hangle k hkdef hstuck r s hr hs hrs hrK hKs) heq)

/-! ## Local no-cross supplies opened no-repeat. -/

/-- The opened WBS arm has no nonadjacent repeats from a local fixed/tail
no-collision statement for this support-stuck branch. -/
theorem openedWBS_noNonadjacentRepeat_of_localNoCross
    {n : ℕ} (A B : Fin (n + 1) → S2)
    (hA : StrictConvexSphArm A) (_hB : StrictConvexSphArm B)
    (_hside : SameSides A B) (_hangle : JointLe A B)
    (k : Fin (n - 1)) (_hkdef : jointAngle A k < jointAngle B k)
    (_hstuck : SupportStuckWBS A B k)
    (hnocross :
      ∀ (r s : ℕ) (hr : r < n + 1) (hs : s < n + 1),
        r + 2 ≤ s →
        r ≤ (openingAxis k).val → (openingAxis k).val < s →
          openedWBS A B k ⟨r, hr⟩ ≠ openedWBS A B k ⟨s, hs⟩) :
    NoNonadjacentRepeat (openedWBS A B k) := by
  intro r s hr hs hrs heq
  have hbase : NoNonadjacentRepeat A := strictConvex_noNonadjacentRepeat hA
  by_cases hsK : s ≤ (openingAxis k).val
  · have hrK : r ≤ (openingAxis k).val := by omega
    have hrw : openedWBS A B k ⟨r, hr⟩ = A ⟨r, hr⟩ := by
      unfold openedWBS
      exact openTail_fixed A (openingAxis k) (-(monitoredSupWBS A B k)) hrK
    have hsw : openedWBS A B k ⟨s, hs⟩ = A ⟨s, hs⟩ := by
      unfold openedWBS
      exact openTail_fixed A (openingAxis k) (-(monitoredSupWBS A B k)) hsK
    apply hbase r s hr hs hrs
    rwa [hrw, hsw] at heq
  · have hKs : (openingAxis k).val < s := by omega
    by_cases hrK : r ≤ (openingAxis k).val
    · exact (hnocross r s hr hs hrs hrK hKs) heq
    · have hKr : (openingAxis k).val < r := by omega
      have hrw :
          openedWBS A B k ⟨r, hr⟩ =
            rotS2 (A (openingAxis k)) (-(monitoredSupWBS A B k)) (A ⟨r, hr⟩) := by
        unfold openedWBS
        exact openTail_rot A (openingAxis k) (-(monitoredSupWBS A B k)) hKr
      have hsw :
          openedWBS A B k ⟨s, hs⟩ =
            rotS2 (A (openingAxis k)) (-(monitoredSupWBS A B k)) (A ⟨s, hs⟩) := by
        unfold openedWBS
        exact openTail_rot A (openingAxis k) (-(monitoredSupWBS A B k)) hKs
      apply hbase r s hr hs hrs
      apply rotS2_injective (A (openingAxis k)) (-(monitoredSupWBS A B k))
      rwa [← hrw, ← hsw]

/-! ## Local support-stuck dispatch. -/

/-- With a local opened-arm no-repeat proof, the raw WBS support-stuck witness
produces the v9 mirror-aware boundary progress.  The wrap edge is handled by
the FFCT85 first-step theorem. -/
theorem supportStuckWBS_boundaryProgress_of_noRepeat_firstStep
    {n : ℕ} (A B : Fin (n + 1) → S2)
    (_hA : StrictConvexSphArm A) (_hB : StrictConvexSphArm B)
    (_hside : SameSides A B) (_hangle : JointLe A B)
    (k : Fin (n - 1)) (_hkdef : jointAngle A k < jointAngle B k)
    (hstuck : SupportStuckWBS A B k)
    (hPweak : WeakConvexSphArm (openedWBS A B k))
    (hnr : NoNonadjacentRepeat (openedWBS A B k))
    (hhem : ∃ h : E3, ‖h‖ = 1 ∧
      ∀ r : Fin (n + 1), 0 < (⟪h, (openedWBS A B k r : E3)⟫ : ℝ)) :
    MirrorBoundaryZeroProgress (openedWBS A B k) B := by
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
  · have ha_val : a.val = n := weak_wrap_base_is_last hadj
    have ha : a = Fin.last n := Fin.ext (by simpa using ha_val)
    have hsucc : a + 1 = (0 : Fin (n + 1)) :=
      weak_wrap_successor_is_zero hadj
    have hb_ne_last : b ≠ Fin.last n := by
      intro hb
      exact hne (hb.trans ha.symm)
    have hb_ne_zero : b ≠ 0 := by
      intro hb
      exact hne1 (hb.trans hsucc.symm)
    have hzero :
        sOrient (openedWBS A B k (Fin.last n)) (openedWBS A B k 0)
          (openedWBS A B k b) = 0 := by
      simpa [ha, hsucc] using hsupp
    exact mirrorBoundaryProgress_of_wrap_firstStep hPweak.two_le hPweak hnr hhem
      hb_ne_last hb_ne_zero hzero

/-- WBS support-stuck endpoint dispatch with `CrossPieceNoCollisionAtSup`
localized away.  Collision-free branches reconstruct opened no-repeat locally;
collision branches are exactly the new endpoint payload. -/
theorem supportStuckWBS_endpoint_dispatch_at_level_nr_v11
    (hcollision : CrossPieceCollisionEndpointAtSup)
    {n : ℕ} (ihdim : ∀ m : ℕ, m < n → MainPlusNR m)
    (A B : Fin (n + 1) → S2)
    (hA : StrictConvexSphArm A) (hB : StrictConvexSphArm B)
    (hside : SameSides A B) (hangle : JointLe A B)
    (k : Fin (n - 1)) (hkdef : jointAngle A k < jointAngle B k)
    (hstuck : SupportStuckWBS A B k) :
    endpt (openedWBS A B k) ≤ endpt B := by
  by_cases hnocross :
      ∀ (r s : ℕ) (hr : r < n + 1) (hs : s < n + 1),
        r + 2 ≤ s →
        r ≤ (openingAxis k).val → (openingAxis k).val < s →
          openedWBS A B k ⟨r, hr⟩ ≠ openedWBS A B k ⟨s, hs⟩
  · obtain ⟨hka, hkt⟩ := shortArcs_of_strict hA k
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
      openedWBS_noNonadjacentRepeat_of_localNoCross A B hA hB hside hangle
        k hkdef hstuck hnocross
    have hprog : MirrorBoundaryZeroProgress (openedWBS A B k) B :=
      supportStuckWBS_boundaryProgress_of_noRepeat_firstStep A B hA hB hside hangle
        k hkdef hstuck hPweak hnr hhem
    exact endpoint_of_mirrorBoundaryZeroProgress_at_level_nr
      bpos_aneg_tailCornerResidueV9_of_firstStepInteriorZero
      hPweak hPpos hnr hB hside' hangle' hhem ihdim hprog
  · push Not at hnocross
    obtain ⟨r, s, hr, hs, hrs, hrK, hKs, heq⟩ := hnocross
    exact hcollision A B hA hB hside hangle k hkdef hstuck
      r s hr hs hrs hrK hKs heq

/-! ## v11 recursion and headline. -/

theorem open_step_wbs_nr_v11
    (hcollision : CrossPieceCollisionEndpointAtSup)
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
      supportStuckWBS_endpoint_dispatch_at_level_nr_v11 hcollision ihdim
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

theorem szOpeningStepPlusNR_v11
    (hcollision : CrossPieceCollisionEndpointAtSup) :
    SZOpeningStepPlusNR := by
  intro n hn ihdim A B hA hposA hnrA hB hside hangle ihdef
  rcases strict_or_vanishing hA with hvanish | hAstrict
  · exact weakPositiveCutReadyNR_v9_holds weakWrapSeed_v9_of_firstStep
      bpos_aneg_tailCornerResidueV9_of_firstStepInteriorZero
      hA hposA hnrA hB hside hangle ihdim hvanish
  · by_cases hnd : deficitCount A B = 0
    · exact congruence_step hAstrict hB hside hangle hnd
    · have hpos : 0 < deficitCount A B := Nat.pos_of_ne_zero hnd
      obtain ⟨k, hkdef⟩ := exists_deficit_of_pos hpos
      exact open_step_wbs_nr_v11 hcollision hn ihdim hAstrict hB hside hangle ihdef k hkdef

theorem mainPlusNR_at_level_v11
    (hcollision : CrossPieceCollisionEndpointAtSup)
    {n : ℕ} (hn : 2 ≤ n)
    (ihdim : ∀ m : ℕ, m < n → MainPlusNR m) : MainPlusNR n := by
  intro A B hA hposA hnrA hB hside hangle
  let hstep := szOpeningStepPlusNR_v11 hcollision
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

theorem mainPlusNR_all_v11
    (hcollision : CrossPieceCollisionEndpointAtSup) :
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
    exact mainPlusNR_at_level_v11 hcollision hn ihdim
      A B hA hposA hnrA hB hside hangle

/-- Chapter 13 strict-arm monotonicity with the global no-collision input
replaced by the sharper collision-endpoint residue. -/
theorem spherical_arm_mono_final_ch13_v11
    (hcollision : CrossPieceCollisionEndpointAtSup) :
    SphericalArmMonotone := by
  intro n hn A B hA hB hside hangle
  exact (mainPlusNR_all_v11 hcollision n hn) A B
    (strictConvexSphArm_toWeak hA) (strictConvexSphArm_positiveJoints hA)
    (strictConvex_noNonadjacentRepeat hA) hB hside hangle

/-- Compatibility with the v10 surface: global no-collision still suffices, but
only through the weaker endpoint-on-collision residue. -/
theorem spherical_arm_mono_final_ch13_v11_of_hcross
    (hcross : CrossPieceNoCollisionAtSup) :
    SphericalArmMonotone :=
  spherical_arm_mono_final_ch13_v11
    (crossPieceCollisionEndpointAtSup_of_noCollision hcross)

/-! ## Guards. -/

#print axioms crossPieceCollisionEndpointAtSup_of_noCollision
#print axioms openedWBS_noNonadjacentRepeat_of_localNoCross
#print axioms supportStuckWBS_boundaryProgress_of_noRepeat_firstStep
#print axioms supportStuckWBS_endpoint_dispatch_at_level_nr_v11
#print axioms spherical_arm_mono_final_ch13_v11
#print axioms spherical_arm_mono_final_ch13_v11_of_hcross

end ProofsInTheBook.ZinanFFCT86
