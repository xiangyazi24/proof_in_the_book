import ProofsInTheBook.ZinanFFCT75
import ProofsInTheBook.ZinanFFCT44

/-!
# `ZinanFFCT76` -- boundary-zero progress layer

This file starts the final wrap-boundary layer on top of FFCT75.  The public
payload is deliberately endpoint-aware: a cyclic boundary zero either produces a
normalized ordinary support zero, or it is consumed directly as an endpoint
comparison.

No proof placeholders or unsafe declarations.
-/

noncomputable section

open scoped RealInnerProductSpace NNReal
open ProofsInTheBook.SphericalKernel ProofsInTheBook.SphericalArm
open ProofsInTheBook.SphericalSZInduction
open ProofsInTheBook.ZinanFFCT3
open ProofsInTheBook.ZinanFFCT18
open ProofsInTheBook.ZinanFFCT21
open ProofsInTheBook.ZinanFFCT23
open ProofsInTheBook.ZinanFFCT24
open ProofsInTheBook.ZinanFFCT44
open ProofsInTheBook.ZinanFFCT49
open ProofsInTheBook.ZinanFFCT52
open ProofsInTheBook.ZinanFFCT56
open ProofsInTheBook.ZinanFFCT64
open ProofsInTheBook.ZinanFFCT70
open ProofsInTheBook.ZinanFFCT71
open ProofsInTheBook.ZinanFFCT74
open ProofsInTheBook.ZinanFFCT75

namespace ProofsInTheBook.ZinanFFCT76

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000

/-! ## Shared output predicates. -/

/-- A normalized ordinary nonincident support zero, suitable for the landed
cut/seed machinery. -/
def NormalizedInteriorSupportZero {n : ℕ} (A : Fin (n + 1) → S2) : Prop :=
  ∃ i j : ℕ, ∃ (hi : i < n + 1) (hi1 : i + 1 < n + 1) (hj : j < n + 1),
    i + 1 < j ∧
      sOrient (A ⟨i, hi⟩) (A ⟨i + 1, hi1⟩) (A ⟨j, hj⟩) = 0

/-- The progress payload produced by a boundary zero. -/
def BoundaryZeroProgress {n : ℕ} (A B : Fin (n + 1) → S2) : Prop :=
  NormalizedInteriorSupportZero A ∨ endpt A ≤ endpt B

/-! ## Worker bricks. -/

/-- A public wrapper around the flat-interior-joint contradiction used by the
wrap-boundary propagation layer. -/
theorem flat_interior_joint_absurd_public
    {n : ℕ} {A B : Fin (n + 1) → S2}
    (hA : WeakConvexSphArm A)
    (hpos : PositiveJoints A)
    (hB : StrictConvexSphArm B)
    (hangle : JointLe A B)
    {r : ℕ}
    (hr : r + 2 < n + 1)
    (hdet :
      det3 (A ⟨r, by omega⟩ : E3)
           (A ⟨r + 1, by omega⟩ : E3)
           (A ⟨r + 2, by omega⟩ : E3) = 0) :
    False := by
  have hshort_prev : ShortArc (A ⟨r + 1, by omega⟩) (A ⟨r, by omega⟩) := by
    have h := hA.closed_convex.edge_short ⟨r, by omega⟩
    have hsucc :
        ((⟨r, by omega⟩ : Fin (n + 1)) + 1) =
          (⟨r + 1, by omega⟩ : Fin (n + 1)) := by
      apply Fin.ext
      have hone : ((1 : Fin (n + 1)) : ℕ) = 1 := by
        rw [Fin.val_one']; exact Nat.mod_eq_of_lt (by omega)
      rw [Fin.val_add, Fin.val_mk, hone,
        Nat.mod_eq_of_lt (show r + 1 < n + 1 by omega)]
    rw [hsucc] at h
    exact h.symm
  have hshort_next : ShortArc (A ⟨r + 1, by omega⟩) (A ⟨r + 2, by omega⟩) := by
    have h := hA.closed_convex.edge_short ⟨r + 1, by omega⟩
    have hsucc :
        ((⟨r + 1, by omega⟩ : Fin (n + 1)) + 1) =
          (⟨r + 2, by omega⟩ : Fin (n + 1)) := by
      apply Fin.ext
      have hone : ((1 : Fin (n + 1)) : ℕ) = 1 := by
        rw [Fin.val_one']; exact Nat.mod_eq_of_lt (by omega)
      rw [Fin.val_add, Fin.val_mk, hone,
        Nat.mod_eq_of_lt (show r + 2 < n + 1 by omega)]
    rwa [hsucc] at h
  have hbridge := sphAngle_eq_zero_or_pi_of_det3_zero
    (u := A ⟨r, by omega⟩)
    (v := A ⟨r + 1, by omega⟩)
    (w := A ⟨r + 2, by omega⟩)
    hshort_prev hshort_next hdet
  let k : Fin (n - 1) := ⟨r, by omega⟩
  have hposk : 0 < jointAngle A k := hpos k
  have hltk : jointAngle A k < Real.pi := jointAngle_lt_pi hB hangle k
  have hjoint_eq :
      jointAngle A k =
        sphAngle (A ⟨r, by omega⟩) (A ⟨r + 1, by omega⟩)
          (A ⟨r + 2, by omega⟩) := rfl
  rcases hbridge with hzero | hpi
  · rw [hjoint_eq, hzero] at hposk
    exact lt_irrefl 0 hposk
  · rw [hjoint_eq, hpi] at hltk
    exact lt_irrefl Real.pi hltk

/-- Same-sign propagation across one ordinary edge. -/
theorem boundaryPlane_step_sameSign
    {n : ℕ} {A : Fin (n + 1) → S2}
    {U V : S2} {k : ℕ}
    (hk : k + 1 < n + 1)
    {c d : ℝ}
    (hrep :
      (A ⟨k, by omega⟩ : E3) =
        c • (U : E3) + d • (V : E3))
    (_hc : c ≠ 0) (_hd : d ≠ 0)
    (hsame : 0 < c * d)
    (hU :
      0 ≤ sOrient (A ⟨k, by omega⟩)
        (A ⟨k + 1, by omega⟩) U)
    (hV :
      0 ≤ sOrient (A ⟨k, by omega⟩)
        (A ⟨k + 1, by omega⟩) V) :
    sOrient U V (A ⟨k + 1, by omega⟩) = 0 := by
  set W : E3 := (A ⟨k + 1, by omega⟩ : E3)
  set UE : E3 := (U : E3)
  set VE : E3 := (V : E3)
  set D : ℝ := det3 UE VE W
  have hU' : 0 ≤ d * D := by
    have hraw : 0 ≤ det3 (c • UE + d • VE) W UE := by
      simpa [sOrient, hrep, UE, VE, W] using hU
    have hid : det3 (c • UE + d • VE) W UE = d * D := by
      simp only [D, det3, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
      ring_nf
    simpa [hid] using hraw
  have hV' : 0 ≤ -c * D := by
    have hraw : 0 ≤ det3 (c • UE + d • VE) W VE := by
      simpa [sOrient, hrep, UE, VE, W] using hV
    have hid : det3 (c • UE + d • VE) W VE = -c * D := by
      simp only [D, det3, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
      ring_nf
    simpa [hid] using hraw
  have hD : D = 0 := by
    rcases (mul_pos_iff.mp hsame) with ⟨hcpos, hdpos⟩ | ⟨hcneg, hdneg⟩
    · have hD_nonneg : 0 ≤ D := by nlinarith [hU', hdpos]
      have hD_nonpos : D ≤ 0 := by nlinarith [hV', hcpos]
      linarith
    · have hD_nonpos : D ≤ 0 := by nlinarith [hU', hdneg]
      have hD_nonneg : 0 ≤ D := by nlinarith [hV', hcneg]
      linarith
  simpa [sOrient, D, UE, VE, W] using hD

/-! ## Small boundary normalizations. -/

/-- If the wrap zero probes vertex `1`, it is already an ordinary normalized
zero on the first edge, with the last vertex as the probe. -/
theorem normalized_zero_of_wrap_probe_one
    {n : ℕ} {A : Fin (n + 1) → S2}
    (hn : 2 ≤ n)
    (hzero : sOrient (A (Fin.last n)) (A 0) (A ⟨1, by omega⟩) = 0) :
    NormalizedInteriorSupportZero A := by
  refine ⟨0, n, by omega, by omega, by omega, by omega, ?_⟩
  rw [sOrient] at hzero ⊢
  have hlast : (⟨n, by omega⟩ : Fin (n + 1)) = Fin.last n := Fin.ext (by simp)
  rw [hlast]
  have hcyc := ProofsInTheBook.ZinanFFCT12.det3_cyclic
    (A (Fin.last n) : E3) (A 0 : E3) (A ⟨1, by omega⟩ : E3)
  rw [hcyc] at hzero
  simpa using hzero

#print axioms flat_interior_joint_absurd_public
#print axioms boundaryPlane_step_sameSign
#print axioms normalized_zero_of_wrap_probe_one

end ProofsInTheBook.ZinanFFCT76
