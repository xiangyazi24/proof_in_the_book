import ProofsInTheBook.ZinanFFCT69
import ProofsInTheBook.ZinanFFCT32

/-!
# `ZinanFFCT70` -- endpoint successor collapse and honest final surface

This additive layer closes the successor-edge part of FFCT64's
`b > 0, a < 0` endpoint case.  The tail corner and the other public remnants
are kept explicit rather than hidden behind a stronger headline.
-/

noncomputable section

open scoped RealInnerProductSpace NNReal
open ProofsInTheBook.SphericalKernel ProofsInTheBook.SphericalArm
open ProofsInTheBook.SphericalSZInduction
open ProofsInTheBook.ZinanFFCT3
open ProofsInTheBook.ZinanFFCT18
open ProofsInTheBook.ZinanFFCT23
open ProofsInTheBook.ZinanFFCT25
open ProofsInTheBook.ZinanFFCT31
open ProofsInTheBook.ZinanFFCT32
open ProofsInTheBook.ZinanFFCT49
open ProofsInTheBook.ZinanFFCT52
open ProofsInTheBook.ZinanFFCT64
open ProofsInTheBook.ZinanFFCT65
open ProofsInTheBook.ZinanFFCT68
open ProofsInTheBook.ZinanFFCT69

namespace ProofsInTheBook.ZinanFFCT70

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000

/-! ## Endpoint surfaces. -/

/-- The `b > 0, a > 0` endpoint field of `BTrichotomyEndpointCases`, named so it can
be used without carrying the whole three-case structure. -/
def BPosAPosEndpointCase : Prop :=
  ∀ {n : ℕ} {P B : Fin (n + 1) → S2},
    WeakConvexSphArm P → PositiveJoints P → StrictConvexSphArm B →
    SameSides P B → JointLe P B → NoNonadjacentRepeat P →
    (∃ h : E3, ‖h‖ = 1 ∧ ∀ r : Fin (n + 1), 0 < (⟪h, (P r : E3)⟫ : ℝ)) →
    ∀ {i j : ℕ}, i + 1 < j →
    ∀ (hi : i < n + 1) (hi1 : i + 1 < n + 1) (hj : j < n + 1),
    ∀ {a b : ℝ},
      (P ⟨i, hi⟩ : E3) = a • (P ⟨i + 1, hi1⟩ : E3) + b • (P ⟨j, hj⟩ : E3) →
      0 < b → 0 < a → endpt P ≤ endpt B

/-- The only `b > 0, a < 0` endpoint corner not reached by the real successor edge
`(j, j+1)`: the far vertex is the last vertex. -/
def BPosANegTailCornerResidue : Prop :=
  ∀ {n : ℕ} {P B : Fin (n + 1) → S2},
    WeakConvexSphArm P → PositiveJoints P → StrictConvexSphArm B →
    SameSides P B → JointLe P B → NoNonadjacentRepeat P →
    (∃ h : E3, ‖h‖ = 1 ∧ ∀ r : Fin (n + 1), 0 < (⟪h, (P r : E3)⟫ : ℝ)) →
    ∀ {i : ℕ}, i + 1 < n →
    ∀ (hi : i < n + 1) (hi1 : i + 1 < n + 1) (hn : n < n + 1),
    ∀ {a b : ℝ},
      (P ⟨i, hi⟩ : E3) = a • (P ⟨i + 1, hi1⟩ : E3) + b • (P ⟨n, hn⟩ : E3) →
      0 < b → a < 0 → endpt P ≤ endpt B

/-! ## The `b > 0, a < 0` successor-edge collapse. -/

/-- In the normalized `b > 0, a < 0` branch, a real successor edge at the far
vertex forces both adjacent witness determinants at `j` to vanish.  The
FFCT32 two-witness flat-joint core then contradicts positive, non-flat joints. -/
theorem bpos_aneg_false_of_successor {n : ℕ} {P B : Fin (n + 1) → S2}
    (hP : WeakConvexSphArm P) (hpos : PositiveJoints P)
    (hB : StrictConvexSphArm B) (hangle : JointLe P B) (hnr : NoNonadjacentRepeat P)
    (hhem : ∃ h : E3, ‖h‖ = 1 ∧ ∀ r : Fin (n + 1), 0 < (⟪h, (P r : E3)⟫ : ℝ))
    {i j : ℕ} (hij : i + 1 < j)
    (hi : i < n + 1) (hi1 : i + 1 < n + 1) (hj : j < n + 1)
    (hj1 : j + 1 < n + 1)
    {a b : ℝ}
    (hspan : (P ⟨i, hi⟩ : E3) =
        a • (P ⟨i + 1, hi1⟩ : E3) + b • (P ⟨j, hj⟩ : E3))
    (_hb : 0 < b) (ha : a < 0) :
    False := by
  have hij2 : i + 2 ≤ j := by omega
  have hjle : j ≤ n := by omega
  have hdist0 : P ⟨i + 1, by omega⟩ ≠ P ⟨j, by omega⟩ :=
    distinctNormalized_of_noRepeat hP hnr hij hjle
  have hdist : P ⟨i + 1, hi1⟩ ≠ P ⟨j, hj⟩ := by
    simpa using hdist0
  obtain ⟨h, _hnorm, hhemPos⟩ := hhem
  have hanti : (P ⟨i + 1, hi1⟩ : E3) ≠ -(P ⟨j, hj⟩ : E3) :=
    hemisphere_nonAntipodal hhemPos ⟨i + 1, hi1⟩ ⟨j, hj⟩
  have hbaseShort : ShortArc (P ⟨i + 1, hi1⟩) (P ⟨j, hj⟩) :=
    ⟨hdist, hanti⟩
  have hjm1 : j - 1 < n + 1 := by omega
  have hspan' : (P ⟨i, by omega⟩ : E3) =
      a • (P ⟨i + 1, hi1⟩ : E3) + b • (P ⟨j, hj⟩ : E3) := by
    simpa using hspan
  have hpredSucc : ((⟨j - 1, hjm1⟩ : Fin (n + 1)) + 1) =
      (⟨j, hj⟩ : Fin (n + 1)) := by
    apply Fin.ext
    have hone : ((1 : Fin (n + 1)) : ℕ) = 1 := by
      rw [Fin.val_one']; exact Nat.mod_eq_of_lt (by omega)
    rw [Fin.val_add, Fin.val_mk, hone,
      Nat.mod_eq_of_lt (show (j - 1) + 1 < n + 1 by omega)]
    change (j - 1) + 1 = j
    omega
  have hsucc : ((⟨j, hj⟩ : Fin (n + 1)) + 1) =
      (⟨j + 1, hj1⟩ : Fin (n + 1)) := by
    apply Fin.ext
    have hone : ((1 : Fin (n + 1)) : ℕ) = 1 := by
      rw [Fin.val_one']; exact Nat.mod_eq_of_lt (by omega)
    rw [Fin.val_add, Fin.val_mk, hone,
      Nat.mod_eq_of_lt (show j + 1 < n + 1 by omega)]
  have hpredShort : ShortArc (P ⟨j, hj⟩) (P ⟨j - 1, hjm1⟩) := by
    have h := hP.closed_convex.edge_short ⟨j - 1, hjm1⟩
    rw [hpredSucc] at h
    exact h.symm
  have hsuccShort : ShortArc (P ⟨j, hj⟩) (P ⟨j + 1, hj1⟩) := by
    have h := hP.closed_convex.edge_short ⟨j, hj⟩
    rwa [hsucc] at h
  have hEpred_mid : 0 ≤ det3 (P ⟨j - 1, hjm1⟩ : E3) (P ⟨j, hj⟩ : E3)
      (P ⟨i + 1, hi1⟩ : E3) := by
    have h := hP.closed_convex.edge_support ⟨j - 1, hjm1⟩ ⟨i + 1, hi1⟩
    rw [hpredSucc] at h
    exact h
  have hEpred_i : 0 ≤ det3 (P ⟨j - 1, hjm1⟩ : E3) (P ⟨j, hj⟩ : E3)
      (P ⟨i, by omega⟩ : E3) := by
    have h := hP.closed_convex.edge_support ⟨j - 1, hjm1⟩ ⟨i, by omega⟩
    rw [hpredSucc] at h
    exact h
  have hEpred_read :
      0 ≤ a * det3 (P ⟨j - 1, hjm1⟩ : E3) (P ⟨j, hj⟩ : E3)
        (P ⟨i + 1, hi1⟩ : E3) :=
    nearSide_a_readout hi1 hj hjm1 hspan' hEpred_i
  have hEpred0 : det3 (P ⟨j - 1, hjm1⟩ : E3) (P ⟨j, hj⟩ : E3)
      (P ⟨i + 1, hi1⟩ : E3) = 0 := by
    nlinarith [hEpred_read, hEpred_mid, ha]
  have hEsucc_mid : 0 ≤ det3 (P ⟨j, hj⟩ : E3) (P ⟨j + 1, hj1⟩ : E3)
      (P ⟨i + 1, hi1⟩ : E3) := by
    have h := hP.closed_convex.edge_support ⟨j, hj⟩ ⟨i + 1, hi1⟩
    rw [hsucc] at h
    exact h
  have hEsucc_i : 0 ≤ det3 (P ⟨j, hj⟩ : E3) (P ⟨j + 1, hj1⟩ : E3)
      (P ⟨i, by omega⟩ : E3) := by
    have h := hP.closed_convex.edge_support ⟨j, hj⟩ ⟨i, by omega⟩
    rw [hsucc] at h
    exact h
  have hEsucc_read :
      0 ≤ a * det3 (P ⟨j, hj⟩ : E3) (P ⟨j + 1, hj1⟩ : E3)
        (P ⟨i + 1, hi1⟩ : E3) :=
    nearSide_a_readout_succ hi1 hj hj1 hspan' hEsucc_i
  have hEsucc0 : det3 (P ⟨j, hj⟩ : E3) (P ⟨j + 1, hj1⟩ : E3)
      (P ⟨i + 1, hi1⟩ : E3) = 0 := by
    nlinarith [hEsucc_read, hEsucc_mid, ha]
  exact not_both_witness_zero (B := B) hpos hB hangle hi1 hj hjm1 hj1 hij2
    hbaseShort hpredShort hsuccShort hEpred0 hEsucc0

/-- The FFCT64 `b > 0, a < 0` endpoint consumer, modulo only the last-vertex
tail corner. -/
theorem bpos_aneg_endpointConsumer_of_tail
    (res : BPosANegTailCornerResidue) : BPosANegEndpointConsumer := by
  intro n P B hP hpos hB hside hangle hnr hhem i j hij hi hi1 hj a b hspan hb ha
  by_cases hj1 : j + 1 < n + 1
  · exact False.elim
      (bpos_aneg_false_of_successor hP hpos hB hangle hnr hhem hij hi hi1 hj hj1 hspan hb ha)
  · have hjn : j = n := by omega
    subst hjn
    exact res hP hpos hB hside hangle hnr hhem hij hi hi1 hj hspan hb ha

/-! ## Final wrapper. -/

/-- FFCT70 final surface.  The successor-edge part of `bpos_aneg` is closed, but
the final theorem is still honest about the remaining non-cross inputs. -/
structure Ch13FinalSurface70 : Prop where
  hmirrorSeed : SupportStuckWBSMirrorVanishingSpanSeedSupply
  hcross : CrossPieceNoCollisionAtSup
  hbpos_apos : BPosAPosEndpointCase
  hbpos_aneg_tail : BPosANegTailCornerResidue

/-- Assemble FFCT64's three endpoint cases from the FFCT70 surface. -/
theorem btrichotomyEndpointCases_of_surface70
    (res : Ch13FinalSurface70) : BTrichotomyEndpointCases where
  bneg_tail := by
    intro n P B hP hpos hB hside hangle hnr hhem i j hij hi hi1 hj a b hspan hb hnot
    exact bneg_tail_closed_by_normalization hP hpos hB hside hangle hnr hhem hij hi hi1 hj hspan hb hnot
  bpos_apos := by
    exact res.hbpos_apos
  bpos_aneg := by
    exact bpos_aneg_endpointConsumer_of_tail res.hbpos_aneg_tail

/-- Chapter 13 monotonicity through the FFCT70 surface. -/
theorem spherical_arm_mono_final_ch13_v4 (res : Ch13FinalSurface70)
    {n : ℕ} (hn : 2 ≤ n) (A B : Fin (n + 1) → S2)
    (hA : StrictConvexSphArm A) (hB : StrictConvexSphArm B)
    (hside : ∀ i : Fin n, sideLen A i = sideLen B i)
    (hangle : ∀ i : Fin (n - 1), jointAngle A i ≤ jointAngle B i) :
    sDist (A 0) (A (Fin.last n)) ≤ sDist (B 0) (B (Fin.last n)) :=
  spherical_arm_mono_final_ch13_v3
    ⟨res.hmirrorSeed, res.hcross, btrichotomyEndpointCases_of_surface70 res⟩
    hn A B hA hB hside hangle

/-- Non-vacuity guard for the new successor collapse's determinant constraints. -/
theorem bpos_aneg_successor_surface_nonvacuous :
    (0 : ℝ) < det3 (!₂[(1:ℝ),0,0] : E3) (!₂[(0:ℝ),1,0] : E3)
      (!₂[(0:ℝ),0,1] : E3) :=
  F_axes_pos

#print axioms bpos_aneg_false_of_successor
#print axioms bpos_aneg_endpointConsumer_of_tail
#print axioms btrichotomyEndpointCases_of_surface70
#print axioms spherical_arm_mono_final_ch13_v4

end ProofsInTheBook.ZinanFFCT70
