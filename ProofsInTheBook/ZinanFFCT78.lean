import ProofsInTheBook.ZinanFFCT77

/-!
# `ZinanFFCT78` -- propagation wrappers and v10 surface

This additive layer is reserved for the final boundary-propagation wrappers on
top of the endpoint-aware v9 interface.

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
open ProofsInTheBook.ZinanFFCT45
open ProofsInTheBook.ZinanFFCT46
open ProofsInTheBook.ZinanFFCT47
open ProofsInTheBook.ZinanFFCT49
open ProofsInTheBook.ZinanFFCT52
open ProofsInTheBook.ZinanFFCT56
open ProofsInTheBook.ZinanFFCT61
open ProofsInTheBook.ZinanFFCT64
open ProofsInTheBook.ZinanFFCT68
open ProofsInTheBook.ZinanFFCT70
open ProofsInTheBook.ZinanFFCT71
open ProofsInTheBook.ZinanFFCT74
open ProofsInTheBook.ZinanFFCT75
open ProofsInTheBook.ZinanFFCT76
open ProofsInTheBook.ZinanFFCT77

namespace ProofsInTheBook.ZinanFFCT78

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000

/-- The Chapter 13 strict spherical-arm monotonicity headline. -/
def SphericalArmMonotone : Prop :=
  ∀ {n : ℕ}, 2 ≤ n → ∀ A B : Fin (n + 1) → S2,
    StrictConvexSphArm A → StrictConvexSphArm B →
    (∀ i : Fin n, sideLen A i = sideLen B i) →
    (∀ i : Fin (n - 1), jointAngle A i ≤ jointAngle B i) →
      sDist (A 0) (A (Fin.last n)) ≤
        sDist (B 0) (B (Fin.last n))

/-! ## Boundary-zero wrappers. -/

/-- The probe-`1` wrap zero is the only wrap boundary case that normalizes
without a propagation induction. -/
theorem wrapPlanePropagation_probe_one
    {n : ℕ} {A B : Fin (n + 1) → S2}
    (hn : 2 ≤ n)
    (_hA : WeakConvexSphArm A)
    (_hpos : PositiveJoints A)
    (_hB : StrictConvexSphArm B)
    (_hside : SameSides A B)
    (_hangle : JointLe A B)
    (_hnr : NoNonadjacentRepeat A)
    (_hhem :
      ∃ h : E3, ‖h‖ = 1 ∧
        ∀ r : Fin (n + 1), 0 < (⟪h, (A r : E3)⟫ : ℝ))
    {j : Fin (n + 1)}
    (hjval : j.val = 1)
    (hzero : sOrient (A (Fin.last n)) (A 0) (A j) = 0) :
    BoundaryZeroProgress A B := by
  left
  have hj : j = (⟨1, by omega⟩ : Fin (n + 1)) := Fin.ext hjval
  have hzero' :
      sOrient (A (Fin.last n)) (A 0) (A ⟨1, by omega⟩) = 0 := by
    simpa [hj] using hzero
  exact normalized_zero_of_wrap_probe_one hn hzero'

/-- The apex-`n` boundary zero is already a normalized ordinary support zero
when the probed apex is separated from the edge endpoint. -/
theorem apexNBoundaryZeroPropagation
    {n : ℕ} {A B : Fin (n + 1) → S2}
    (_hn : 2 ≤ n)
    (_hA : WeakConvexSphArm A)
    (_hpos : PositiveJoints A)
    (_hB : StrictConvexSphArm B)
    (_hside : SameSides A B)
    (_hangle : JointLe A B)
    (_hnr : NoNonadjacentRepeat A)
    (_hhem :
      ∃ h : E3, ‖h‖ = 1 ∧
        ∀ r : Fin (n + 1), 0 < (⟪h, (A r : E3)⟫ : ℝ))
    {i : ℕ}
    (hi : i < n + 1)
    (hi1 : i + 1 < n + 1)
    (hfar : i + 1 < n)
    (hzero :
      sOrient (A ⟨i, hi⟩)
        (A ⟨i + 1, hi1⟩)
        (A ⟨n, by omega⟩) = 0) :
    BoundaryZeroProgress A B := by
  left
  refine ⟨i, n, hi, hi1, by omega, hfar, ?_⟩
  simpa using hzero

/-- Backward-compatible alias for the already normalized apex payload. -/
theorem apexNBoundaryZeroProgress
    {n : ℕ} {A B : Fin (n + 1) → S2}
    (hn : 2 ≤ n)
    (hA : WeakConvexSphArm A)
    (hpos : PositiveJoints A)
    (hB : StrictConvexSphArm B)
    (hside : SameSides A B)
    (hangle : JointLe A B)
    (hnr : NoNonadjacentRepeat A)
    (hhem :
      ∃ h : E3, ‖h‖ = 1 ∧
        ∀ r : Fin (n + 1), 0 < (⟪h, (A r : E3)⟫ : ℝ))
    {i : ℕ}
    (hi : i < n + 1)
    (hi1 : i + 1 < n + 1)
    (hfar : i + 1 < n)
    (hzero :
      sOrient (A ⟨i, hi⟩)
        (A ⟨i + 1, hi1⟩)
        (A ⟨n, by omega⟩) = 0) :
    BoundaryZeroProgress A B :=
  apexNBoundaryZeroPropagation hn hA hpos hB hside hangle hnr hhem hi hi1 hfar hzero

#print axioms wrapPlanePropagation_probe_one
#print axioms apexNBoundaryZeroPropagation
#print axioms apexNBoundaryZeroProgress

end ProofsInTheBook.ZinanFFCT78
