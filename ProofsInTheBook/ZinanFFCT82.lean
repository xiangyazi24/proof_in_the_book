import ProofsInTheBook.ZinanFFCT81

/-!
# `ZinanFFCT82` -- final-composition interface audit

This layer records the precise kernel-checked interface facts needed for the
last v10 composition attempt.  The probe-`1` wrap zero and the apex-`n` boundary
zero both produce the old `BoundaryZeroProgress` normalized witness with far
probe `n`.  The stratified FFCT81 consumer deliberately requires the far probe
to have an ordinary successor, hence every no-tail normalized witness has
`j < n`.

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
open ProofsInTheBook.ZinanFFCT81

namespace ProofsInTheBook.ZinanFFCT82

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000

/-! ## Apex/probe-one payloads. -/

/-- The apex-`n` boundary zero has exactly the old normalized payload shape. -/
theorem normalizedInteriorSupportZero_of_apexNBoundaryZero
    {n : ℕ} {A : Fin (n + 1) → S2}
    {i : ℕ}
    (hi : i < n + 1)
    (hi1 : i + 1 < n + 1)
    (hfar : i + 1 < n)
    (hzero :
      sOrient (A ⟨i, hi⟩)
        (A ⟨i + 1, hi1⟩)
        (A ⟨n, by omega⟩) = 0) :
    NormalizedInteriorSupportZero A := by
  refine ⟨i, n, hi, hi1, by omega, hfar, ?_⟩
  simpa using hzero

/-- The same apex zero, packaged as the old endpoint-aware progress payload. -/
theorem boundaryZeroProgress_of_apexNBoundaryZero
    {n : ℕ} {A B : Fin (n + 1) → S2}
    {i : ℕ}
    (hi : i < n + 1)
    (hi1 : i + 1 < n + 1)
    (hfar : i + 1 < n)
    (hzero :
      sOrient (A ⟨i, hi⟩)
        (A ⟨i + 1, hi1⟩)
        (A ⟨n, by omega⟩) = 0) :
    BoundaryZeroProgress A B :=
  Or.inl (normalizedInteriorSupportZero_of_apexNBoundaryZero hi hi1 hfar hzero)

/-- The probe-`1` wrap zero normalizes to the apex witness `(0,n)` in the old
payload, matching `wrapPlanePropagation_probe_one`. -/
theorem normalizedInteriorSupportZero_of_wrap_probe_one
    {n : ℕ} {A : Fin (n + 1) → S2}
    (hn : 2 ≤ n)
    {j : Fin (n + 1)}
    (hjval : j.val = 1)
    (hzero : sOrient (A (Fin.last n)) (A 0) (A j) = 0) :
    NormalizedInteriorSupportZero A := by
  have hj : j = (⟨1, by omega⟩ : Fin (n + 1)) := Fin.ext hjval
  have hzero' :
      sOrient (A (Fin.last n)) (A 0) (A ⟨1, by omega⟩) = 0 := by
    simpa [hj] using hzero
  exact normalized_zero_of_wrap_probe_one hn hzero'

/-- Probe-`1` gives old `BoundaryZeroProgress`; this is not the FFCT81 no-tail
payload. -/
theorem boundaryZeroProgress_of_wrap_probe_one
    {n : ℕ} {A B : Fin (n + 1) → S2}
    (hn : 2 ≤ n)
    {j : Fin (n + 1)}
    (hjval : j.val = 1)
    (hzero : sOrient (A (Fin.last n)) (A 0) (A j) = 0) :
    BoundaryZeroProgress A B :=
  Or.inl (normalizedInteriorSupportZero_of_wrap_probe_one hn hjval hzero)

/-! ## The FFCT81 no-tail payload excludes the apex far probe. -/

/-- A no-tail normalized witness always has far index strictly below `n`. -/
theorem normalizedStrictInteriorSupportZero_probe_lt_n
    {n : ℕ} {A : Fin (n + 1) → S2}
    (hnorm : NormalizedStrictInteriorSupportZero A) :
    ∃ i j : ℕ, ∃ (hi : i < n + 1) (hi1 : i + 1 < n + 1) (hj : j < n + 1),
      i + 1 < j ∧ j < n ∧
        sOrient (A ⟨i, hi⟩) (A ⟨i + 1, hi1⟩) (A ⟨j, hj⟩) = 0 := by
  obtain ⟨i, j, hi, hi1, hj, hij, hj1, hzero⟩ := hnorm
  exact ⟨i, j, hi, hi1, hj, hij, by omega, hzero⟩

/-- In particular, the concrete apex far probe `j = n` can never be the
normalized branch expected by the no-tail consumer. -/
theorem apex_far_probe_not_noTail_witness
    {n : ℕ} {A : Fin (n + 1) → S2}
    {i : ℕ}
    (hi : i < n + 1)
    (hi1 : i + 1 < n + 1)
    (hj : n < n + 1)
    (_hij : i + 1 < n)
    (hj1 : n + 1 < n + 1)
    (_hzero :
      sOrient (A ⟨i, hi⟩) (A ⟨i + 1, hi1⟩) (A ⟨n, hj⟩) = 0) :
    False := by
  omega

/-- Case analysis on the no-tail progress payload exposes the same strict
`j < n` fact on its normalized branch. -/
theorem boundaryZeroProgressNoTail_cases_probe_lt_n
    {n : ℕ} {A B : Fin (n + 1) → S2}
    (hprog : BoundaryZeroProgressNoTail A B) :
    (∃ i j : ℕ, ∃ (hi : i < n + 1) (hi1 : i + 1 < n + 1) (hj : j < n + 1),
      i + 1 < j ∧ j < n ∧
        sOrient (A ⟨i, hi⟩) (A ⟨i + 1, hi1⟩) (A ⟨j, hj⟩) = 0)
      ∨ endpt A ≤ endpt B := by
  rcases hprog with hnorm | hend
  · exact Or.inl (normalizedStrictInteriorSupportZero_probe_lt_n hnorm)
  · exact Or.inr hend

/-! ## Conditional final wrapper re-export. -/

/-- FFCT81's checked conditional final assembly, re-exported at the FFCT82
boundary.  The missing input is still the strengthened no-tail wrap propagation
theorem. -/
theorem spherical_arm_mono_final_ch13_v10_of_hcross_wrapNoTail_ffct82
    (hcross : CrossPieceNoCollisionAtSup)
    (hwrap : WrapPlanePropagationNoTail) :
    SphericalArmMonotone :=
  spherical_arm_mono_final_ch13_v10_of_hcross_wrapNoTail hcross hwrap

/-! ## Guards. -/

#print axioms normalizedInteriorSupportZero_of_apexNBoundaryZero
#print axioms boundaryZeroProgress_of_apexNBoundaryZero
#print axioms normalizedInteriorSupportZero_of_wrap_probe_one
#print axioms boundaryZeroProgress_of_wrap_probe_one
#print axioms normalizedStrictInteriorSupportZero_probe_lt_n
#print axioms apex_far_probe_not_noTail_witness
#print axioms boundaryZeroProgressNoTail_cases_probe_lt_n
#print axioms spherical_arm_mono_final_ch13_v10_of_hcross_wrapNoTail_ffct82

end ProofsInTheBook.ZinanFFCT82
