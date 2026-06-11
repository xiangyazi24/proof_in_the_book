import ProofsInTheBook.ZinanFFCT80

/-!
# `ZinanFFCT81` -- stratified no-tail endpoint consumers

This layer separates the normalized-zero endpoint consumer that never calls the
live signed-tail residue.  The separation is deliberately stated on a stronger
progress payload: the normalized support zero must have a far probe with an
ordinary successor.  Under that payload the `b > 0, a < 0` coefficient branch is
closed by `bpos_aneg_false_of_successor`, so the signed-tail field is not
re-entered.

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
open ProofsInTheBook.ZinanFFCT12
open ProofsInTheBook.ZinanFFCT18
open ProofsInTheBook.ZinanFFCT23
open ProofsInTheBook.ZinanFFCT25
open ProofsInTheBook.ZinanFFCT45
open ProofsInTheBook.ZinanFFCT49
open ProofsInTheBook.ZinanFFCT52
open ProofsInTheBook.ZinanFFCT56
open ProofsInTheBook.ZinanFFCT64
open ProofsInTheBook.ZinanFFCT65
open ProofsInTheBook.ZinanFFCT68
open ProofsInTheBook.ZinanFFCT70
open ProofsInTheBook.ZinanFFCT74
open ProofsInTheBook.ZinanFFCT76
open ProofsInTheBook.ZinanFFCT77
open ProofsInTheBook.ZinanFFCT78
open ProofsInTheBook.ZinanFFCT79
open ProofsInTheBook.ZinanFFCT80

namespace ProofsInTheBook.ZinanFFCT81

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000

/-! ## Stronger progress payload. -/

/-- A normalized ordinary support zero whose far probe still has an ordinary
successor.  This is the exact side condition that makes the signed tail branch
of the coefficient dispatch vacuous. -/
def NormalizedStrictInteriorSupportZero {n : ℕ} (A : Fin (n + 1) → S2) : Prop :=
  ∃ i j : ℕ, ∃ (hi : i < n + 1) (hi1 : i + 1 < n + 1) (hj : j < n + 1),
    i + 1 < j ∧ j + 1 < n + 1 ∧
      sOrient (A ⟨i, hi⟩) (A ⟨i + 1, hi1⟩) (A ⟨j, hj⟩) = 0

/-- Boundary progress with a no-tail normalized branch. -/
def BoundaryZeroProgressNoTail {n : ℕ} (A B : Fin (n + 1) → S2) : Prop :=
  NormalizedStrictInteriorSupportZero A ∨ endpt A ≤ endpt B

/-- Forget the no-tail side condition and recover the old v9 progress payload. -/
theorem boundaryZeroProgress_of_noTail
    {n : ℕ} {A B : Fin (n + 1) → S2}
    (hprog : BoundaryZeroProgressNoTail A B) :
    BoundaryZeroProgress A B := by
  rcases hprog with hnorm | hend
  · left
    obtain ⟨i, j, hi, hi1, hj, hij, _hj1, hzero⟩ := hnorm
    exact ⟨i, j, hi, hi1, hj, hij, hzero⟩
  · exact Or.inr hend

/-! ## Endpoint consumers that do not carry the signed-tail residue. -/

/-- Coefficient dispatch for a normalized zero whose far probe has a successor.
The only `b > 0, a < 0` branch is closed by the successor-edge contradiction,
so this consumer has no `BPosANegTailCornerResidueV9` argument. -/
theorem endpoint_of_span_at_level_nr_noTail
    {n : ℕ} {P B : Fin (n + 1) → S2}
    (hP : WeakConvexSphArm P) (hpos : PositiveJoints P) (hnr : NoNonadjacentRepeat P)
    (hB : StrictConvexSphArm B)
    (hside : SameSides P B) (hangle : JointLe P B)
    (hhem : ∃ h : E3, ‖h‖ = 1 ∧ ∀ r : Fin (n + 1), 0 < (⟪h, (P r : E3)⟫ : ℝ))
    (ihdim : ∀ m : ℕ, m < n → MainPlusNR m)
    {i j : ℕ} (hij : i + 1 < j)
    (hi : i < n + 1) (hi1 : i + 1 < n + 1) (hj : j < n + 1)
    (hj1 : j + 1 < n + 1)
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
    · exact False.elim
        (bpos_aneg_false_of_successor hP hpos hB hangle hnr hhem
          hij hi hi1 hj hj1 hspan hbpos haneg)
    · have hij2 : i + 2 ≤ j := by omega
      exact False.elim (span_azero_bpos_false_of_noRepeat hnr hi hi1 hj hij2 hspan hbpos ha0)
    · exact bpos_apos_endpoint_at_level_nr hP hpos hnr hB hside hangle ihdim
        hij hi hi1 hj hspan hbpos hapos

/-- A normalized zero with a successor on the far probe closes at a live NR
level without invoking the signed-tail residue. -/
theorem endpoint_of_normalized_vanishing_support_at_level_nr_noTail
    {n : ℕ} {P B : Fin (n + 1) → S2}
    (hP : WeakConvexSphArm P) (hpos : PositiveJoints P) (hnr : NoNonadjacentRepeat P)
    (hB : StrictConvexSphArm B)
    (hside : SameSides P B) (hangle : JointLe P B)
    (hhem : ∃ h : E3, ‖h‖ = 1 ∧ ∀ r : Fin (n + 1), 0 < (⟪h, (P r : E3)⟫ : ℝ))
    (ihdim : ∀ m : ℕ, m < n → MainPlusNR m)
    {i j : ℕ} (hij : i + 1 < j)
    (hi : i < n + 1) (hi1 : i + 1 < n + 1) (hj : j < n + 1)
    (hj1 : j + 1 < n + 1)
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
  exact endpoint_of_span_at_level_nr_noTail hP hpos hnr hB hside hangle
    ⟨h, hnorm, hhemPos⟩ ihdim hij hi hi1 hj hj1 hspan

/-- Consume an already-normalized no-tail support zero. -/
theorem endpoint_of_normalizedInteriorZero_noTail
    {n : ℕ} {P B : Fin (n + 1) → S2}
    (hP : WeakConvexSphArm P) (hpos : PositiveJoints P) (hnr : NoNonadjacentRepeat P)
    (hB : StrictConvexSphArm B)
    (hside : SameSides P B) (hangle : JointLe P B)
    (hhem : ∃ h : E3, ‖h‖ = 1 ∧ ∀ r : Fin (n + 1), 0 < (⟪h, (P r : E3)⟫ : ℝ))
    (ihdim : ∀ m : ℕ, m < n → MainPlusNR m)
    (hnorm : NormalizedStrictInteriorSupportZero P) :
    endpt P ≤ endpt B := by
  obtain ⟨i, j, hi, hi1, hj, hij, hj1, hzero⟩ := hnorm
  exact endpoint_of_normalized_vanishing_support_at_level_nr_noTail hP hpos hnr hB
    hside hangle hhem ihdim hij hi hi1 hj hj1 hzero

/-- Consume the stronger no-tail boundary progress payload at a live NR level. -/
theorem endpoint_of_boundaryZeroProgress_noTail_at_level_nr
    {n : ℕ} {P B : Fin (n + 1) → S2}
    (hP : WeakConvexSphArm P) (hpos : PositiveJoints P) (hnr : NoNonadjacentRepeat P)
    (hB : StrictConvexSphArm B)
    (hside : SameSides P B) (hangle : JointLe P B)
    (hhem : ∃ h : E3, ‖h‖ = 1 ∧ ∀ r : Fin (n + 1), 0 < (⟪h, (P r : E3)⟫ : ℝ))
    (ihdim : ∀ m : ℕ, m < n → MainPlusNR m)
    (hprog : BoundaryZeroProgressNoTail P B) :
    endpt P ≤ endpt B := by
  rcases hprog with hnorm | hend
  · exact endpoint_of_normalizedInteriorZero_noTail hP hpos hnr hB hside hangle
      hhem ihdim hnorm
  · exact hend

/-! ## Tail closure from a stronger wrap-propagation theorem. -/

/-- The strengthened wrap propagation shape needed by the stratified consumer:
the normalized branch must preserve the no-tail successor side condition. -/
def WrapPlanePropagationNoTail : Prop :=
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
        BoundaryZeroProgressNoTail A B

/-- The no-tail propagation theorem implies the old v10 propagation shape by
forgetting the extra successor side condition. -/
theorem wrapPlanePropagationGeneral_of_noTail
    (hwrap : WrapPlanePropagationNoTail) :
    WrapPlanePropagationGeneral := by
  intro n A B hn hA hpos hB hside hangle hnr hhem j hj_ne_last hj_ne_zero hzero
  exact boundaryZeroProgress_of_noTail
    (hwrap hn hA hpos hB hside hangle hnr hhem hj_ne_last hj_ne_zero hzero)

/-- The signed tail corner closes non-circularly once wrap propagation returns
the stronger no-tail progress payload. -/
theorem bpos_aneg_tailCornerResidueV9_of_wrapPlanePropagationNoTail
    (hwrap : WrapPlanePropagationNoTail) :
    BPosANegTailCornerResidueV9 := by
  intro n P B hP hpos hB hside hangle hnr hhem ihdim i hitail hi hi1 hn a b hspan _hbpos haneg
  have hzero :=
    bpos_aneg_tail_span_forces_wrap_zero hP hi hi1 hn hspan haneg
  have hlast : (⟨n, hn⟩ : Fin (n + 1)) = Fin.last n := Fin.ext (by simp)
  have hj_ne_last : (⟨i + 1, hi1⟩ : Fin (n + 1)) ≠ Fin.last n := by
    intro h
    have hv : i + 1 = n := by
      simpa using congrArg Fin.val h
    omega
  have hj_ne_zero : (⟨i + 1, hi1⟩ : Fin (n + 1)) ≠ 0 := by
    intro h
    have hv : i + 1 = 0 := by
      simpa using congrArg Fin.val h
    omega
  have hzero' :
      sOrient (P (Fin.last n)) (P 0) (P ⟨i + 1, hi1⟩) = 0 := by
    simpa [hlast] using hzero
  have hprog :
      BoundaryZeroProgressNoTail P B :=
    hwrap hP.two_le hP hpos hB hside hangle hnr hhem
      hj_ne_last hj_ne_zero hzero'
  exact endpoint_of_boundaryZeroProgress_noTail_at_level_nr hP hpos hnr hB
    hside hangle hhem ihdim hprog

/-- Conditional v10 assembly after stratifying the boundary consumer.  The
remaining non-cross input is now the strengthened wrap propagation theorem. -/
theorem spherical_arm_mono_final_ch13_v10_of_hcross_wrapNoTail
    (hcross : CrossPieceNoCollisionAtSup)
    (hwrap : WrapPlanePropagationNoTail) :
    SphericalArmMonotone :=
  spherical_arm_mono_final_ch13_v10_of_hcross_wrap_and_tail hcross
    (wrapPlanePropagationGeneral_of_noTail hwrap)
    (bpos_aneg_tailCornerResidueV9_of_wrapPlanePropagationNoTail hwrap)

/-! ## Guards. -/

theorem boundaryZeroProgressNoTail_endpoint_target_satisfiable {n : ℕ}
    (A : Fin (n + 1) → S2) :
    BoundaryZeroProgressNoTail A A := Or.inr (le_refl _)

#print axioms boundaryZeroProgress_of_noTail
#print axioms endpoint_of_span_at_level_nr_noTail
#print axioms endpoint_of_normalized_vanishing_support_at_level_nr_noTail
#print axioms endpoint_of_normalizedInteriorZero_noTail
#print axioms endpoint_of_boundaryZeroProgress_noTail_at_level_nr
#print axioms wrapPlanePropagationGeneral_of_noTail
#print axioms bpos_aneg_tailCornerResidueV9_of_wrapPlanePropagationNoTail
#print axioms spherical_arm_mono_final_ch13_v10_of_hcross_wrapNoTail

end ProofsInTheBook.ZinanFFCT81
