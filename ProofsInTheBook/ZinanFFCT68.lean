import ProofsInTheBook.ZinanFFCT67
import ProofsInTheBook.ZinanFFCT26

/-!
# `ZinanFFCT68` -- cross-piece no-collision shrink and endpoint data adapter

This additive layer records the pieces from the final handoff that can be closed from the
currently landed library without changing earlier files.
-/

noncomputable section

open scoped RealInnerProductSpace NNReal
open ProofsInTheBook.SphericalKernel ProofsInTheBook.SphericalArm
open ProofsInTheBook.SphericalRotation
open ProofsInTheBook.SphericalSZInduction
open ProofsInTheBook.SphericalSZFinal
open ProofsInTheBook.ZinanFFCT18
open ProofsInTheBook.ZinanFFCT19
open ProofsInTheBook.ZinanFFCT23
open ProofsInTheBook.ZinanFFCT25
open ProofsInTheBook.ZinanFFCT26
open ProofsInTheBook.ZinanFFCT45
open ProofsInTheBook.ZinanFFCT46
open ProofsInTheBook.ZinanFFCT49
open ProofsInTheBook.ZinanFFCT53
open ProofsInTheBook.ZinanFFCT54
open ProofsInTheBook.ZinanFFCT64
open ProofsInTheBook.ZinanFFCT65
open ProofsInTheBook.ZinanFFCT66
open ProofsInTheBook.ZinanFFCT67

namespace ProofsInTheBook.ZinanFFCT68

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000

/-! ## Same-piece no-repeat and the cross-piece residue. -/

/-- A strict arm has no repeated vertices at nonadjacent positions. -/
theorem strictConvex_noNonadjacentRepeat {n : ℕ} {A : Fin (n + 1) → S2}
    (hA : StrictConvexSphArm A) : NoNonadjacentRepeat A := by
  intro r s hr hs hrs heq
  have hr1 : r + 1 < n + 1 := by omega
  have hsucc : ((⟨r, hr⟩ : Fin (n + 1)) + 1) = (⟨r + 1, hr1⟩ : Fin (n + 1)) := by
    apply Fin.ext
    have hone : ((1 : Fin (n + 1)) : ℕ) = 1 := by
      rw [Fin.val_one']
      exact Nat.mod_eq_of_lt (by omega)
    rw [Fin.val_add, Fin.val_mk, hone, Nat.mod_eq_of_lt (show r + 1 < n + 1 by omega)]
  have hnon :
      0 < sOrient (A ⟨r, hr⟩) (A ⟨r + 1, hr1⟩) (A ⟨s, hs⟩) := by
    have hbase := hA.closed_convex.strict_nonincident
      (⟨r, hr⟩ : Fin (n + 1)) (⟨s, hs⟩ : Fin (n + 1))
      (by
        intro h
        have hv : s = r := by simpa using congrArg Fin.val h
        omega)
      (by
        rw [hsucc]
        intro h
        have hv : s = r + 1 := by simpa using congrArg Fin.val h
        omega)
    rwa [hsucc] at hbase
  have hzero : sOrient (A ⟨r, hr⟩) (A ⟨r + 1, hr1⟩) (A ⟨s, hs⟩) = 0 := by
    rw [← heq, sOrient]
    exact ProofsInTheBook.SphericalDiagCut.det3_self_right _ _
  linarith

/-- The induced rotation on `S²` is injective. -/
theorem rotS2_injective (k : S2) (θ : ℝ) : Function.Injective (rotS2 k θ) := by
  intro p q hpq
  apply S2.ext
  apply rot_injective k.2 θ
  exact congrArg (fun x : S2 => (x : E3)) hpq

/-- The only no-repeat content not forced from the original strict arm: a fixed-side vertex and a
rotated-side vertex do not collide at the WBS support-stuck supremum. -/
def CrossPieceNoCollisionAtSup : Prop :=
  ∀ {n : ℕ} (A B : Fin (n + 1) → S2),
    StrictConvexSphArm A → StrictConvexSphArm B → SameSides A B → JointLe A B →
    ∀ k : Fin (n - 1), jointAngle A k < jointAngle B k →
    SupportStuckWBS A B k →
      ∀ (r s : ℕ) (hr : r < n + 1) (hs : s < n + 1),
        r + 2 ≤ s →
        r ≤ (openingAxis k).val → (openingAxis k).val < s →
          openedWBS A B k ⟨r, hr⟩ ≠ openedWBS A B k ⟨s, hs⟩

/-- The opened WBS arm has no nonadjacent repeats once the cross-piece collisions are excluded. -/
theorem openedWBS_noNonadjacentRepeat_of_crossPiece
    (hcross : CrossPieceNoCollisionAtSup)
    {n : ℕ} (A B : Fin (n + 1) → S2)
    (hA : StrictConvexSphArm A) (hB : StrictConvexSphArm B)
    (hside : SameSides A B) (hangle : JointLe A B)
    (k : Fin (n - 1)) (hkdef : jointAngle A k < jointAngle B k)
    (hstuck : SupportStuckWBS A B k) :
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
    · exact (hcross A B hA hB hside hangle k hkdef hstuck r s hr hs hrs hrK hKs) heq
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

/-- The public WBS no-repeat supply follows from the sharper cross-piece no-collision residue. -/
theorem openedWBSNoNonadjacentRepeatSupply_of_crossPiece
    (hcross : CrossPieceNoCollisionAtSup) :
    OpenedWBSNoNonadjacentRepeatSupply := by
  intro n A B hA hB hside hangle k hkdef hstuck
  exact openedWBS_noNonadjacentRepeat_of_crossPiece hcross A B hA hB hside hangle k hkdef hstuck

/-! ## The `b > 0, a > 0` endpoint adapter with its missing data explicit. -/

/-- The repaired endpoint consumer for the `b > 0, a > 0` branch: the dimension IH and the diagonal
inequality are explicit arguments, which is the data `FoldedFlatCutTransportPlusNR` actually needs. -/
def BPosAPosFFCTPlusV3EndpointConsumer : Prop :=
  FoldedFlatCutTransportPlusNR →
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
        sDist (P ⟨i, hi⟩) (P ⟨j, hj⟩) ≤ sDist (B ⟨i, by omega⟩) (B ⟨j, hj⟩) →
          endpt P ≤ endpt B

/-- `FoldedFlatCutTransportPlusNR` closes the `b > 0, a > 0` endpoint branch once the real missing
inputs, `ihdim` and the diagonal inequality, are present. -/
theorem bpos_apos_endpointConsumer_v3_holds :
    BPosAPosFFCTPlusV3EndpointConsumer := by
  intro hffct n P B hP hpos hB hside hangle hnr _hhem ih i j hij hi hi1 hj a b hspan hbpos hapos hdiag
  have hcol : (P ⟨i, hi⟩ : E3) ∈
      Submodule.span NNReal
        ({(P ⟨i + 1, hi1⟩ : E3), (P ⟨j, hj⟩ : E3)} : Set E3) := by
    rw [Submodule.mem_span_pair]
    refine ⟨⟨a, le_of_lt hapos⟩, ⟨b, le_of_lt hbpos⟩, ?_⟩
    rw [NNReal.smul_def, NNReal.smul_def]
    exact hspan.symm
  exact hffct n hP.two_le ih P B hP hpos hnr hB hside hangle i j
    (by omega) (by omega) hi1 hj hcol hdiag

/-- Forward-only version of the `b > 0, a > 0` endpoint consumer.  This is the shape the normalized
branch needs; it does not mention the backward-fold case. -/
def BPosAPosFFCTPlusForwardEndpointConsumer : Prop :=
  FoldedFlatCutTransportPlusForward →
    ∀ {n : ℕ} {P B : Fin (n + 1) → S2},
      WeakConvexSphArm P → PositiveJoints P → StrictConvexSphArm B →
      SameSides P B → JointLe P B → NoNonadjacentRepeat P →
      (∀ m : ℕ, m < n → MainPlus m) →
      ∀ {i j : ℕ}, i + 1 < j →
      ∀ (hi : i < n + 1) (hi1 : i + 1 < n + 1) (hj : j < n + 1),
      ∀ {a b : ℝ},
        (P ⟨i, hi⟩ : E3) = a • (P ⟨i + 1, hi1⟩ : E3) + b • (P ⟨j, hj⟩ : E3) →
        0 < b → 0 < a →
        sDist (P ⟨i, hi⟩) (P ⟨j, hj⟩) ≤ sDist (B ⟨i, by omega⟩) (B ⟨j, hj⟩) →
          endpt P ≤ endpt B

/-- The landed forward transport closes the normalized `b > 0, a > 0` endpoint branch once the
dimension IH and diagonal inequality are supplied. -/
theorem bpos_apos_endpointConsumer_forward_holds :
    BPosAPosFFCTPlusForwardEndpointConsumer := by
  intro hfwd n P B hP hpos hB hside hangle hnr ih i j hij hi hi1 hj a b hspan hbpos hapos hdiag
  have hcol : (P ⟨i, hi⟩ : E3) ∈
      Submodule.span NNReal
        ({(P ⟨i + 1, hi1⟩ : E3), (P ⟨j, hj⟩ : E3)} : Set E3) := by
    rw [Submodule.mem_span_pair]
    refine ⟨⟨a, le_of_lt hapos⟩, ⟨b, le_of_lt hbpos⟩, ?_⟩
    rw [NNReal.smul_def, NNReal.smul_def]
    exact hspan.symm
  exact hfwd n hP.two_le ih P B hP hpos hnr hB hside hangle i j
    hij hi1 hj hcol hdiag

/-! ## Final wrapper with the no-repeat field replaced. -/

/-- Final surface after replacing the opened-arm no-repeat supply by cross-piece no-collision. -/
structure Ch13FinalSurface68 : Prop where
  hspanSeed : SupportStuckWBSVanishingSpanSeedSupply
  hcross : CrossPieceNoCollisionAtSup
  hcases : BTrichotomyEndpointCases

/-- Assemble the FFCT67 final surface from the sharper FFCT68 fields. -/
theorem final67_of_final68 (res : Ch13FinalSurface68) : Ch13FinalSurface67 where
  hspanSeed := res.hspanSeed
  hnorepeat := openedWBSNoNonadjacentRepeatSupply_of_crossPiece res.hcross
  hcases := res.hcases

/-- Chapter 13 strict-arm monotonicity with no-repeat replaced by cross-piece no-collision. -/
theorem spherical_arm_mono_final_ch13_v2 (res : Ch13FinalSurface68)
    {n : ℕ} (hn : 2 ≤ n) (A B : Fin (n + 1) → S2)
    (hA : StrictConvexSphArm A) (hB : StrictConvexSphArm B)
    (hside : ∀ i : Fin n, sideLen A i = sideLen B i)
    (hangle : ∀ i : Fin (n - 1), jointAngle A i ≤ jointAngle B i) :
    sDist (A 0) (A (Fin.last n)) ≤ sDist (B 0) (B (Fin.last n)) :=
  spherical_arm_mono_final_ch13 (final67_of_final68 res) hn A B hA hB hside hangle

/-- Unpacked FFCT68 corollary. -/
theorem spherical_arm_mono_final_ch13_v2_of_supplies
    (hspanSeed : SupportStuckWBSVanishingSpanSeedSupply)
    (hcross : CrossPieceNoCollisionAtSup)
    (hcases : BTrichotomyEndpointCases)
    {n : ℕ} (hn : 2 ≤ n) (A B : Fin (n + 1) → S2)
    (hA : StrictConvexSphArm A) (hB : StrictConvexSphArm B)
    (hside : ∀ i : Fin n, sideLen A i = sideLen B i)
    (hangle : ∀ i : Fin (n - 1), jointAngle A i ≤ jointAngle B i) :
    sDist (A 0) (A (Fin.last n)) ≤ sDist (B 0) (B (Fin.last n)) :=
  spherical_arm_mono_final_ch13_v2
    ⟨hspanSeed, hcross, hcases⟩ hn A B hA hB hside hangle

/-- Non-vacuity guard for the FFCT68 conclusion shape. -/
theorem spherical_arm_mono_final_ch13_v2_conclusion_satisfiable {n : ℕ}
    (A : Fin (n + 1) → S2) :
    sDist (A 0) (A (Fin.last n)) ≤ sDist (A 0) (A (Fin.last n)) := le_refl _

#print axioms strictConvex_noNonadjacentRepeat
#print axioms openedWBSNoNonadjacentRepeatSupply_of_crossPiece
#print axioms bpos_apos_endpointConsumer_v3_holds
#print axioms bpos_apos_endpointConsumer_forward_holds
#print axioms spherical_arm_mono_final_ch13_v2

end ProofsInTheBook.ZinanFFCT68
