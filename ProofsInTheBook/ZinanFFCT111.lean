import ProofsInTheBook.ZinanFFCT100

/-!
# `ZinanFFCT111` -- DIRECT subarm-induction route for cross-piece no-collision

This file discharges the cross-piece collision residue by a DIRECT subarm argument
(the induction-hypothesis route), replacing the failed planar turning-bound route.

The target is `ProperCrossPieceNoCollisionAtSup` (FFCT100): for a *proper* cross pair
`r ≤ K < s` (`K = openingAxis k`, `r + 2 ≤ s`, not the full closure `r = 0 ∧ s = n`),
the opened WBS vertices do not coincide: `openedWBS A B k ⟨r⟩ ≠ openedWBS A B k ⟨s⟩`.

Composing with FFCT100's `spherical_arm_mono_ch13_of_properNoCollision` yields the
Chapter-13 headline `SphericalArmMonotone` with the `hcollision` residue removed.

## Route (numerically verified TRUE; two false routes killed — see HANDOFF notes)
By contradiction, assume the collision `heq`.  Let `δ = monitoredSupWBS A B k`.

* **`δ = 0`**: `openedWBS = A`, so `heq` is a nonadjacent repeat of `A`, refuted by
  `strictConvex_noNonadjacentRepeat`.
* **`r = K` (`δ > 0`)**: the opened tail is a rigid rotation about `A K`; the isometry
  `sDist_rotS2` plus `rotS2_axis_fixed` turns `heq` into `A K = A s`, again a nonadjacent
  repeat — contradiction.  (No induction hypothesis needed.)
* **`r < K` (`δ > 0`)**: the genuine subarm-induction case.  The opened subarm
  `O = openTail A^{r,s} (K-r) (-δ)` restricts `openedWBS`; `heq ⟹ endpt O = 0`; but
  `A^{r,s}` is strictly convex so `endpt A^{r,s} > 0`, and the (weak-target) spherical-arm
  monotonicity on the smaller arm forces `endpt A^{r,s} ≤ endpt O = 0` — contradiction.
  This last case is isolated as `ProperCrossHardResidue` and discharged separately.

No proof placeholders or unsafe declarations.
-/

noncomputable section

open scoped RealInnerProductSpace NNReal
open ProofsInTheBook.SphericalKernel ProofsInTheBook.SphericalArm
open ProofsInTheBook.SphericalRotation
open ProofsInTheBook.SphericalSZInduction
open ProofsInTheBook.SphericalSZStepClose
open ProofsInTheBook.SphericalSZFinal
open ProofsInTheBook.SphericalArmAssembly
open ProofsInTheBook.SphericalMonitoredSup
open ProofsInTheBook.SphericalOpeningOutcome
open ProofsInTheBook.ZinanFFCT23
open ProofsInTheBook.ZinanFFCT45
open ProofsInTheBook.ZinanFFCT49
open ProofsInTheBook.ZinanFFCT52
open ProofsInTheBook.ZinanFFCT68
open ProofsInTheBook.ZinanFFCT74
open ProofsInTheBook.ZinanFFCT78
open ProofsInTheBook.ZinanFFCT86
open ProofsInTheBook.ZinanFFCT100

namespace ProofsInTheBook.ZinanFFCT111

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1800000

/-! ## The isolated hard case: proper cross collision with `r < K` and `δ > 0`. -/

/-- The genuine subarm-induction residue: a proper cross collision with the opening axis
strictly interior to the pair (`r < K < s`) and a positive opening (`0 < δ*`) is impossible.
This is the case discharged by the smaller-arm induction hypothesis. -/
def ProperCrossHardResidue : Prop :=
  ∀ {n : ℕ} (A B : Fin (n + 1) → S2),
    StrictConvexSphArm A → StrictConvexSphArm B → SameSides A B → JointLe A B →
    ∀ k : Fin (n - 1), jointAngle A k < jointAngle B k → SupportStuckWBS A B k →
      ∀ (r s : ℕ) (hr : r < n + 1) (hs : s < n + 1),
        r + 2 ≤ s →
        r < (openingAxis k).val → (openingAxis k).val < s →
        (0 < r ∨ s < n) →
        0 < monitoredSupWBS A B k →
        openedWBS A B k ⟨r, hr⟩ = openedWBS A B k ⟨s, hs⟩ → False

/-! ## Reduction of `ProperCrossPieceNoCollisionAtSup` to the hard residue. -/

/-- Proper cross-piece no-collision from the hard residue: the `δ = 0` and `r = K` cases
are discharged directly, leaving the `r < K`, `δ > 0` case to the residue. -/
theorem properCrossPieceNoCollision_of_hard
    (hHard : ProperCrossHardResidue) :
    ProperCrossPieceNoCollisionAtSup := by
  intro n A B hA hB hside hangle k hkdef hstuck r s hr hs hrs hrK hKs hproper heq
  -- `heq : openedWBS A B k ⟨r⟩ = openedWBS A B k ⟨s⟩`; goal is `False`.
  have hbase : NoNonadjacentRepeat A := strictConvex_noNonadjacentRepeat hA
  set δ : ℝ := monitoredSupWBS A B k with hδdef
  by_cases hδ0 : δ = 0
  · -- `openedWBS = openTail A K (-0) = A`.
    have hO : openedWBS A B k = A := by
      simp only [openedWBS, ← hδdef, hδ0, neg_zero]
      exact openTail_zero_angle A (openingAxis k)
    rw [hO] at heq
    exact hbase r s hr hs hrs heq
  · have hδpos : 0 < δ := lt_of_le_of_ne (hδdef ▸ (monitoredSupWBS_mem_Icc hA
      (shortArcs_of_strict hA k).1 (shortArcs_of_strict hA k).2 hkdef).1)
      (Ne.symm hδ0)
    by_cases hrKeq : r = (openingAxis k).val
    · -- `r = K`: rigid rotation about `A K`.  `heq` becomes `A K = A s`.
      exfalso
      -- `openedWBS ⟨r⟩ = A (openingAxis k)` (fixed, since `r = K`).
      have hrleK : r ≤ (openingAxis k).val := le_of_eq hrKeq
      have hrw_r : openedWBS A B k ⟨r, hr⟩ = A (openingAxis k) := by
        have h1 : openedWBS A B k ⟨r, hr⟩ = A ⟨r, hr⟩ := by
          simp only [openedWBS, ← hδdef]
          exact openTail_fixed A (openingAxis k) (-δ) hrleK
        rw [h1]
        congr 1
        exact Fin.ext (by simp [hrKeq])
      -- `openedWBS ⟨s⟩ = rotS2 (A K) (-δ) (A s)` (rotated, since `s > K`).
      have hrw_s : openedWBS A B k ⟨s, hs⟩ = rotS2 (A (openingAxis k)) (-δ) (A ⟨s, hs⟩) := by
        simp only [openedWBS, ← hδdef]
        exact openTail_rot A (openingAxis k) (-δ) hKs
      -- `heq : A K = rotS2 (A K) (-δ) (A s)`.
      rw [hrw_r, hrw_s] at heq
      -- isometry: sDist (A K) (A s) = sDist (rot (A K)) (rot (A s)) = sDist (A K) (A K) = 0.
      have hzero : sDist (A (openingAxis k)) (A ⟨s, hs⟩) = 0 := by
        have hiso : sDist (A (openingAxis k)) (A ⟨s, hs⟩)
            = sDist (rotS2 (A (openingAxis k)) (-δ) (A (openingAxis k)))
                (rotS2 (A (openingAxis k)) (-δ) (A ⟨s, hs⟩)) :=
          (sDist_rotS2 (A (openingAxis k)) (-δ) (A (openingAxis k)) (A ⟨s, hs⟩)).symm
        rw [hiso, rotS2_axis_fixed, ← heq, sDist_eq_zero_iff]
      have hKs2 : A (openingAxis k) = A ⟨s, hs⟩ := sDist_eq_zero_iff.mp hzero
      -- `A K = A s` with `K + 2 ≤ s`: a nonadjacent repeat.
      have hKlt : (openingAxis k).val + 2 ≤ s := by omega
      refine hbase (openingAxis k).val s (openingAxis k).isLt hs hKlt ?_
      rw [← hKs2]
    · -- `r < K`: the genuine subarm-induction residue.
      have hrK_lt : r < (openingAxis k).val := lt_of_le_of_ne hrK hrKeq
      exact hHard A B hA hB hside hangle k hkdef hstuck r s hr hs hrs hrK_lt hKs hproper hδpos heq

/-! ## v12 headline (conditional on the hard residue). -/

/-- Chapter-13 strict-arm monotonicity, with the cross-piece collision residue replaced by
the genuine subarm-induction residue `ProperCrossHardResidue`. -/
theorem spherical_arm_mono_final_ch13_v12
    (hHard : ProperCrossHardResidue) :
    SphericalArmMonotone :=
  spherical_arm_mono_ch13_of_properNoCollision
    (properCrossPieceNoCollision_of_hard hHard)

/-! ## Guards. -/

#print axioms properCrossPieceNoCollision_of_hard
#print axioms spherical_arm_mono_final_ch13_v12

end ProofsInTheBook.ZinanFFCT111
