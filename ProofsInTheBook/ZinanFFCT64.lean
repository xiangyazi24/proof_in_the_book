import ProofsInTheBook.ZinanFFCT62

/-!
# `ZinanFFCT64` — b-trichotomy endpoint dispatch surface

This file performs the coefficient dispatch requested by the b-trichotomy handoff without importing
the parallel `ZinanFFCT63` worker.

The raw `SupportStuckWBS` predicate still does not carry a real-span witness.  Therefore the final
endpoint theorem is stated over the honest span-supply surface, plus the three remaining endpoint
case consumers.  The local branches that are already available are closed here:

* `b = 0` is impossible from the opened edge's `ShortArc`;
* `b < 0` is impossible when the apex has a successor edge, by `midFold_bneg_false`;
* `b > 0, a = 0` is impossible from `NoNonadjacentRepeat`.
-/

noncomputable section

open scoped RealInnerProductSpace NNReal
open ProofsInTheBook.SphericalKernel ProofsInTheBook.SphericalArm
open ProofsInTheBook.SphericalRotation
open ProofsInTheBook.SphericalSZInduction
open ProofsInTheBook.SphericalSZFinal
open ProofsInTheBook.SphericalSZClose
open ProofsInTheBook.SphericalMonitoredSup
open ProofsInTheBook.SphericalCore ProofsInTheBook.SphericalFinish
open ProofsInTheBook.SphericalArmAssembly
open ProofsInTheBook.SphericalOpeningOutcome
open ProofsInTheBook.SphericalReachStuck
open ProofsInTheBook.ZinanFFCT18
open ProofsInTheBook.ZinanFFCT23
open ProofsInTheBook.ZinanFFCT45
open ProofsInTheBook.ZinanFFCT46
open ProofsInTheBook.ZinanFFCT47
open ProofsInTheBook.ZinanFFCT49
open ProofsInTheBook.ZinanFFCT52
open ProofsInTheBook.ZinanFFCT53
open ProofsInTheBook.ZinanFFCT56
open ProofsInTheBook.ZinanFFCT57
open ProofsInTheBook.ZinanFFCT61
open ProofsInTheBook.ZinanFFCT62

namespace ProofsInTheBook.ZinanFFCT64

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000

/-! ## §1. Local coefficient kills. -/

/-- If the far coefficient is zero, a span relation across a short edge is impossible. -/
theorem span_bzero_false_of_weak {n : ℕ} {P : Fin (n + 1) → S2}
    (hP : WeakConvexSphArm P) {i j : ℕ}
    (hi : i < n + 1) (hi1 : i + 1 < n + 1) (hj : j < n + 1)
    {a b : ℝ}
    (hspan : (P ⟨i, hi⟩ : E3) = a • (P ⟨i + 1, hi1⟩ : E3) + b • (P ⟨j, hj⟩ : E3))
    (hb0 : b = 0) :
    False := by
  have hedge : ShortArc (P ⟨i, hi⟩) (P ⟨i + 1, hi1⟩) := by
    have h := hP.closed_convex.edge_short ⟨i, hi⟩
    have hsucc : ((⟨i, hi⟩ : Fin (n + 1)) + 1) = (⟨i + 1, hi1⟩ : Fin (n + 1)) := by
      apply Fin.ext
      have hone : ((1 : Fin (n + 1)) : ℕ) = 1 := by
        rw [Fin.val_one']; exact Nat.mod_eq_of_lt (by omega)
      rw [Fin.val_add, Fin.val_mk, hone, Nat.mod_eq_of_lt (show i + 1 < n + 1 by omega)]
    rwa [hsucc] at h
  exact bcoef_ne_zero_of_short_edge hedge hspan hb0

/-- If `b > 0` and `a = 0`, the span relation forces a forbidden nonadjacent repeat. -/
theorem span_azero_bpos_false_of_noRepeat {n : ℕ} {P : Fin (n + 1) → S2}
    (hnr : NoNonadjacentRepeat P) {i j : ℕ}
    (hi : i < n + 1) (hi1 : i + 1 < n + 1) (hj : j < n + 1)
    (hij : i + 2 ≤ j) {a b : ℝ}
    (hspan : (P ⟨i, hi⟩ : E3) = a • (P ⟨i + 1, hi1⟩ : E3) + b • (P ⟨j, hj⟩ : E3))
    (hbpos : 0 < b) (ha0 : a = 0) :
    False := by
  have hpj : (P ⟨i, hi⟩ : E3) = b • (P ⟨j, hj⟩ : E3) := by
    rw [hspan, ha0, zero_smul, zero_add]
  have hbabs : |b| = 1 := by
    have hnorm := congrArg (fun x : E3 => ‖x‖) hpj
    simp only [norm_smul, Real.norm_eq_abs] at hnorm
    rw [(P ⟨i, hi⟩).2, (P ⟨j, hj⟩).2, mul_one] at hnorm
    linarith
  have hb1 : b = 1 := by
    rcases (abs_eq (by norm_num : (0 : ℝ) ≤ 1)).1 hbabs with hb | hb
    · exact hb
    · linarith
  have hpeq : P ⟨i, hi⟩ = P ⟨j, hj⟩ := by
    apply S2.ext
    rw [hpj, hb1, one_smul]
  exact (hnr i j hi hj hij) hpeq

/-! ## §2. The b-trichotomy endpoint case surface. -/

/-- The remaining endpoint consumers after the local coefficient kills. -/
structure BTrichotomyEndpointCases : Prop where
  /-- The `b < 0` tail endpoint branch, after the successor-edge branch has been killed locally. -/
  bneg_tail :
    ∀ {n : ℕ} {P B : Fin (n + 1) → S2},
      WeakConvexSphArm P → PositiveJoints P → StrictConvexSphArm B →
      SameSides P B → JointLe P B → NoNonadjacentRepeat P →
      (∃ h : E3, ‖h‖ = 1 ∧ ∀ r : Fin (n + 1), 0 < (⟪h, (P r : E3)⟫ : ℝ)) →
      ∀ {i j : ℕ}, i + 1 < j →
      ∀ (hi : i < n + 1) (hi1 : i + 1 < n + 1) (hj : j < n + 1),
      ∀ {a b : ℝ},
        (P ⟨i, hi⟩ : E3) = a • (P ⟨i + 1, hi1⟩ : E3) + b • (P ⟨j, hj⟩ : E3) →
        b < 0 → ¬ i + 2 < n + 1 → endpt P ≤ endpt B
  /-- The `b > 0, a > 0` boundary-fold endpoint branch. -/
  bpos_apos :
    ∀ {n : ℕ} {P B : Fin (n + 1) → S2},
      WeakConvexSphArm P → PositiveJoints P → StrictConvexSphArm B →
      SameSides P B → JointLe P B → NoNonadjacentRepeat P →
      (∃ h : E3, ‖h‖ = 1 ∧ ∀ r : Fin (n + 1), 0 < (⟪h, (P r : E3)⟫ : ℝ)) →
      ∀ {i j : ℕ}, i + 1 < j →
      ∀ (hi : i < n + 1) (hi1 : i + 1 < n + 1) (hj : j < n + 1),
      ∀ {a b : ℝ},
        (P ⟨i, hi⟩ : E3) = a • (P ⟨i + 1, hi1⟩ : E3) + b • (P ⟨j, hj⟩ : E3) →
        0 < b → 0 < a → endpt P ≤ endpt B
  /-- The `b > 0, a < 0` opposite-mid-fold endpoint branch. -/
  bpos_aneg :
    ∀ {n : ℕ} {P B : Fin (n + 1) → S2},
      WeakConvexSphArm P → PositiveJoints P → StrictConvexSphArm B →
      SameSides P B → JointLe P B → NoNonadjacentRepeat P →
      (∃ h : E3, ‖h‖ = 1 ∧ ∀ r : Fin (n + 1), 0 < (⟪h, (P r : E3)⟫ : ℝ)) →
      ∀ {i j : ℕ}, i + 1 < j →
      ∀ (hi : i < n + 1) (hi1 : i + 1 < n + 1) (hj : j < n + 1),
      ∀ {a b : ℝ},
        (P ⟨i, hi⟩ : E3) = a • (P ⟨i + 1, hi1⟩ : E3) + b • (P ⟨j, hj⟩ : E3) →
        0 < b → a < 0 → endpt P ≤ endpt B

/-- The coefficient trichotomy converts a raw normalized span datum into the endpoint comparison. -/
theorem endpoint_of_btrichotomy_cases (cases : BTrichotomyEndpointCases)
    {n : ℕ} {P B : Fin (n + 1) → S2}
    (hP : WeakConvexSphArm P) (hpos : PositiveJoints P) (hB : StrictConvexSphArm B)
    (hside : SameSides P B) (hangle : JointLe P B) (hnr : NoNonadjacentRepeat P)
    (hhem : ∃ h : E3, ‖h‖ = 1 ∧ ∀ r : Fin (n + 1), 0 < (⟪h, (P r : E3)⟫ : ℝ))
    {i j : ℕ} (hij : i + 1 < j)
    (hi : i < n + 1) (hi1 : i + 1 < n + 1) (hj : j < n + 1)
    {a b : ℝ}
    (hspan : (P ⟨i, hi⟩ : E3) = a • (P ⟨i + 1, hi1⟩ : E3) + b • (P ⟨j, hj⟩ : E3)) :
    endpt P ≤ endpt B := by
  rcases lt_trichotomy b 0 with hbneg | hb0 | hbpos
  · by_cases hi2 : i + 2 < n + 1
    · exact False.elim (midFold_bneg_false hP hpos hB hangle hi hi1 hi2 hj hhem hspan hbneg)
    · exact cases.bneg_tail hP hpos hB hside hangle hnr hhem hij hi hi1 hj hspan hbneg hi2
  · exact False.elim (span_bzero_false_of_weak hP hi hi1 hj hspan hb0)
  · rcases lt_trichotomy a 0 with haneg | ha0 | hapos
    · exact cases.bpos_aneg hP hpos hB hside hangle hnr hhem hij hi hi1 hj hspan hbpos haneg
    · have hij2 : i + 2 ≤ j := by omega
      exact False.elim (span_azero_bpos_false_of_noRepeat hnr hi hi1 hj hij2 hspan hbpos ha0)
    · exact cases.bpos_apos hP hpos hB hside hangle hnr hhem hij hi hi1 hj hspan hbpos hapos

/-! ## §3. WBS endpoint dispatch from span supply. -/

/-- Normalized real-span witnesses for every WBS support-stuck branch. -/
def SupportStuckWBSSpanSupply : Prop :=
  ∀ {n : ℕ} (A B : Fin (n + 1) → S2),
    StrictConvexSphArm A → StrictConvexSphArm B → SameSides A B → JointLe A B →
    ∀ k : Fin (n - 1), jointAngle A k < jointAngle B k →
    SupportStuckWBS A B k →
      ∃ i j : ℕ, ∃ (hi : i < n + 1) (hi1 : i + 1 < n + 1) (hj : j < n + 1),
        i + 1 < j ∧
          ∃ a b : ℝ,
            (openedWBS A B k ⟨i, hi⟩ : E3)
              = a • (openedWBS A B k ⟨i + 1, hi1⟩ : E3)
                + b • (openedWBS A B k ⟨j, hj⟩ : E3)

/-- The accepted opened-arm no-repeat surface, scoped to WBS support-stuck branches. -/
def OpenedWBSNoNonadjacentRepeatSupply : Prop :=
  ∀ {n : ℕ} (A B : Fin (n + 1) → S2),
    StrictConvexSphArm A → StrictConvexSphArm B → SameSides A B → JointLe A B →
    ∀ k : Fin (n - 1), jointAngle A k < jointAngle B k →
    SupportStuckWBS A B k →
      NoNonadjacentRepeat (openedWBS A B k)

/-- The exact b-trichotomy surface needed to produce FFCT62's endpoint dispatch. -/
structure BTrichotomyDispatchSurface : Prop where
  hspan : SupportStuckWBSSpanSupply
  hnorepeat : OpenedWBSNoNonadjacentRepeatSupply
  hcases : BTrichotomyEndpointCases

/-- The requested WBS endpoint dispatch, modulo the exact remaining b-trichotomy surface. -/
theorem supportStuckWBS_endpoint_dispatch_final
    (res : BTrichotomyDispatchSurface) : SupportStuckWBSEndpointDispatch := by
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
    res.hnorepeat A B hA hB hside hangle k hkdef hstuck
  obtain ⟨i, j, hi, hi1, hj, hij, a, b, hspan⟩ :=
    res.hspan A B hA hB hside hangle k hkdef hstuck
  exact endpoint_of_btrichotomy_cases res.hcases hPweak hPpos hB hside' hangle' hnr hhem
    hij hi hi1 hj hspan

/-- FFCT62's `spherical_arm_mono_vNext` with the b-trichotomy dispatch plugged in. -/
theorem spherical_arm_mono_vNext_btrichotomy (res : BTrichotomyDispatchSurface)
    {n : ℕ} (hn : 2 ≤ n) (A B : Fin (n + 1) → S2)
    (hA : StrictConvexSphArm A) (hB : StrictConvexSphArm B)
    (hside : ∀ i : Fin n, sideLen A i = sideLen B i)
    (hangle : ∀ i : Fin (n - 1), jointAngle A i ≤ jointAngle B i) :
    sDist (A 0) (A (Fin.last n)) ≤ sDist (B 0) (B (Fin.last n)) :=
  spherical_arm_mono_vNext
    ⟨supportStuckWBS_endpoint_dispatch_final res⟩ hn A B hA hB hside hangle

/-! ## §4. Small guards for the exposed surface. -/

theorem btrichotomy_sign_cases (b : ℝ) : b < 0 ∨ b = 0 ∨ 0 < b :=
  lt_trichotomy b 0

theorem btrichotomy_headline_conclusion_satisfiable {n : ℕ} (A : Fin (n + 1) → S2) :
    sDist (A 0) (A (Fin.last n)) ≤ sDist (A 0) (A (Fin.last n)) :=
  le_refl _

#print axioms span_bzero_false_of_weak
#print axioms span_azero_bpos_false_of_noRepeat
#print axioms endpoint_of_btrichotomy_cases
#print axioms supportStuckWBS_endpoint_dispatch_final
#print axioms spherical_arm_mono_vNext_btrichotomy

end ProofsInTheBook.ZinanFFCT64
