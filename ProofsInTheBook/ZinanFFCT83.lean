import ProofsInTheBook.ZinanFFCT82

/-!
# `ZinanFFCT83` -- tail-corner backward-sweep audit bricks

This additive layer records the checked algebraic part of the proposed
backward sweep for the remaining `b > 0, a < 0, j = n` corner.  The current
library supports the tail-cone rearrangement, the edge-anchor determinant step,
and the adjacent-tail contradiction.  The full descending sweep still requires
the semantic re-extraction step from a coplanar short edge back into the open
cone; this file keeps that missing content explicit as a proposition.
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
open ProofsInTheBook.ZinanFFCT22
open ProofsInTheBook.ZinanFFCT23
open ProofsInTheBook.ZinanFFCT24
open ProofsInTheBook.ZinanFFCT25
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
open ProofsInTheBook.ZinanFFCT82

namespace ProofsInTheBook.ZinanFFCT83

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000

/-! ## The open cone carried by the backward sweep. -/

/-- `z` lies in the strict positive real cone spanned by `p` and `q`. -/
def OpenCone (p q z : S2) : Prop :=
  ∃ c d : ℝ, 0 < c ∧ 0 < d ∧
    (z : E3) = c • (p : E3) + d • (q : E3)

/-- A point in `OpenCone p q` is coplanar with the two cone anchors. -/
theorem OpenCone.sOrient_zero {p q z : S2} (h : OpenCone p q z) :
    sOrient p q z = 0 := by
  rcases h with ⟨c, d, _hc, _hd, hrep⟩
  rw [sOrient, hrep]
  simp only [det3, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
  ring

/-! ## Brick A: the signed tail span is a positive tail cone. -/

/-- The `a < 0, b > 0, j = n` span rearranges to
`P n ∈ OpenCone (P i) (P (i+1))`. -/
theorem openCone_tail_of_aneg_bpos
    {n : ℕ} {P : Fin (n + 1) → S2}
    {i : ℕ}
    (hi : i < n + 1) (hi1 : i + 1 < n + 1) (hn : n < n + 1)
    {a b : ℝ}
    (hspan :
      (P ⟨i, hi⟩ : E3) =
        a • (P ⟨i + 1, hi1⟩ : E3) + b • (P ⟨n, hn⟩ : E3))
    (hb : 0 < b) (ha : a < 0) :
    OpenCone (P ⟨i, hi⟩) (P ⟨i + 1, hi1⟩) (P ⟨n, hn⟩) := by
  refine ⟨1 / b, (-a) / b, div_pos zero_lt_one hb, div_pos (neg_pos.mpr ha) hb, ?_⟩
  have hbne : b ≠ 0 := ne_of_gt hb
  have hbvec :
      b • (P ⟨n, hn⟩ : E3) =
        (P ⟨i, hi⟩ : E3) - a • (P ⟨i + 1, hi1⟩ : E3) := by
    rw [hspan]
    module
  calc
    (P ⟨n, hn⟩ : E3)
        = (1 / b) • (b • (P ⟨n, hn⟩ : E3)) := by
            rw [smul_smul, div_mul_cancel₀ _ hbne, one_smul]
    _ = (1 / b) • ((P ⟨i, hi⟩ : E3) - a • (P ⟨i + 1, hi1⟩ : E3)) := by
            rw [hbvec]
    _ = (1 / b) • (P ⟨i, hi⟩ : E3) + ((-a) / b) • (P ⟨i + 1, hi1⟩ : E3) := by
            rw [smul_sub, smul_smul]
            module

/-! ## Brick B: the edge-anchor determinant step. -/

/-- If `C` is in the open cone of fixed anchors `P,Q`, then the two weak
supports of the edge `(Y,C)` at `P` and `Q` force `Y` back into the same
anchor plane. -/
theorem edgeAnchor_prev_plane_of_next_openCone
    {P Q Y C : S2}
    (hC : OpenCone P Q C)
    (hYP : 0 ≤ sOrient Y C P)
    (hYQ : 0 ≤ sOrient Y C Q) :
    sOrient P Q Y = 0 := by
  rcases hC with ⟨c, d, hc, hd, hrep⟩
  set D : ℝ := det3 (P : E3) (Q : E3) (Y : E3)
  have hYP' : 0 ≤ -d * D := by
    have hid :
        det3 (Y : E3) (c • (P : E3) + d • (Q : E3)) (P : E3)
          = -d * D := by
      simp only [D, det3, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
      ring
    rw [sOrient, hrep] at hYP
    simpa [hid] using hYP
  have hYQ' : 0 ≤ c * D := by
    have hid :
        det3 (Y : E3) (c • (P : E3) + d • (Q : E3)) (Q : E3)
          = c * D := by
      simp only [D, det3, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
      ring
    rw [sOrient, hrep] at hYQ
    simpa [hid] using hYQ
  have hDle : D ≤ 0 := by nlinarith [hYP', hd]
  have hDge : 0 ≤ D := by nlinarith [hYQ', hc]
  have hD : D = 0 := by linarith
  simpa [sOrient, D] using hD

/-! ## The adjacent tail subcase. -/

/-- An open cone on a consecutive triple contradicts positive non-flat joints. -/
theorem openCone_consecutive_absurd
    {n : ℕ} {P B : Fin (n + 1) → S2}
    (hP : WeakConvexSphArm P) (hpos : PositiveJoints P)
    (hB : StrictConvexSphArm B) (hangle : JointLe P B)
    {i : ℕ} (hi : i < n + 1) (hi1 : i + 1 < n + 1) (hi2 : i + 2 < n + 1)
    (hcone : OpenCone (P ⟨i, hi⟩) (P ⟨i + 1, hi1⟩) (P ⟨i + 2, hi2⟩)) :
    False := by
  have hzero := hcone.sOrient_zero
  rw [sOrient] at hzero
  exact flat_interior_joint_absurd_public hP hpos hB hangle (r := i) (by omega) hzero

/-- The signed tail corner is impossible in the adjacent-tail case `i + 2 = n`. -/
theorem bpos_aneg_tail_adjacent_forbidden
    {n : ℕ} {P B : Fin (n + 1) → S2}
    (hP : WeakConvexSphArm P) (hpos : PositiveJoints P)
    (hB : StrictConvexSphArm B) (hangle : JointLe P B)
    {i : ℕ} (hi : i < n + 1) (hi1 : i + 1 < n + 1) (hn : n < n + 1)
    (htight : i + 2 = n)
    {a b : ℝ}
    (hspan :
      (P ⟨i, hi⟩ : E3) =
        a • (P ⟨i + 1, hi1⟩ : E3) + b • (P ⟨n, hn⟩ : E3))
    (hb : 0 < b) (ha : a < 0) :
    False := by
  have hcone := openCone_tail_of_aneg_bpos hi hi1 hn hspan hb ha
  have hi2 : i + 2 < n + 1 := by omega
  have hidx : (⟨n, hn⟩ : Fin (n + 1)) = ⟨i + 2, hi2⟩ := by
    apply Fin.ext
    exact htight.symm
  have hcone' : OpenCone (P ⟨i, hi⟩) (P ⟨i + 1, hi1⟩) (P ⟨i + 2, hi2⟩) := by
    simpa [hidx] using hcone
  exact openCone_consecutive_absurd hP hpos hB hangle hi hi1 hi2 hcone'

/-! ## Exact remaining sweep content. -/

/-- The precise core still needed to turn the local bricks into the live tail
residue: every non-adjacent signed tail cone must sweep backward until the
successor triple becomes flat. -/
def BPosANegTailForbiddenCore : Prop :=
  ∀ {n : ℕ} {P B : Fin (n + 1) → S2},
    WeakConvexSphArm P → PositiveJoints P → StrictConvexSphArm B →
    JointLe P B → NoNonadjacentRepeat P →
    (∃ h : E3, ‖h‖ = 1 ∧ ∀ r : Fin (n + 1), 0 < (⟪h, (P r : E3)⟫ : ℝ)) →
    ∀ {i : ℕ}, i + 1 < n →
    ∀ (hi : i < n + 1) (hi1 : i + 1 < n + 1) (hn : n < n + 1),
    ∀ {a b : ℝ},
      (P ⟨i, hi⟩ : E3) =
        a • (P ⟨i + 1, hi1⟩ : E3) + b • (P ⟨n, hn⟩ : E3) →
      0 < b → a < 0 → False

/-- Once the backward sweep core is supplied, the v9 signed-tail endpoint
residue follows without re-entering a boundary-zero consumer. -/
theorem bpos_aneg_tailCornerResidueV9_of_forbiddenCore
    (hcore : BPosANegTailForbiddenCore) :
    BPosANegTailCornerResidueV9 := by
  intro n P B hP hpos hB hside hangle hnr hhem ihdim i hitail hi hi1 hn a b hspan hb ha
  exact False.elim (hcore hP hpos hB hangle hnr hhem hitail hi hi1 hn hspan hb ha)

/-- FFCT81's final conditional wrapper, re-exposed at the FFCT83 boundary. -/
theorem spherical_arm_mono_final_ch13_v10_of_hcross_wrapNoTail_ffct83
    (hcross : CrossPieceNoCollisionAtSup)
    (hwrap : WrapPlanePropagationNoTail) :
    SphericalArmMonotone :=
  spherical_arm_mono_final_ch13_v10_of_hcross_wrapNoTail hcross hwrap

/-! ## Guards. -/

#print axioms OpenCone.sOrient_zero
#print axioms openCone_tail_of_aneg_bpos
#print axioms edgeAnchor_prev_plane_of_next_openCone
#print axioms openCone_consecutive_absurd
#print axioms bpos_aneg_tail_adjacent_forbidden
#print axioms bpos_aneg_tailCornerResidueV9_of_forbiddenCore
#print axioms spherical_arm_mono_final_ch13_v10_of_hcross_wrapNoTail_ffct83

end ProofsInTheBook.ZinanFFCT83
