import ProofsInTheBook.ZinanFFCT10

/-!
# `ZinanFFCT16` — statement audit: `GnomonicNoflatJoint` is FALSE as stated

## §3.3 finding (kernel-anchored here)

`ZinanFFCT8.GnomonicNoflatJoint` — the isolated "no-flat interior joint" residue of the Ch13 route —
is **false** as stated.  It claims that, under the full comparison context
(`WeakConvexSphArm A`, `StrictConvexSphArm B`, `SameSides A B`, `JointLe A B`, and an open
hemisphere normal `h` with `0 < ⟪h, A i⟫`), every interior gnomonic joint of `A` is a strict left
turn `0 < det3 (gproj h (A (v-1))) (gproj h (A v)) (gproj h (A (v+1)))`.

The hidden assumption is that `A` cannot *fold back on itself*.  But a weakly convex arm whose
vertices all lie on one great circle, doubling back at an interior vertex, satisfies every premise
while having a vanishing gnomonic interior orientation.

**Counterexample (`n = 2`, interior `v = 1`, all rational):**
* `A = [(3/5,0,4/5), (−3/5,0,4/5), (0,0,1)]` — three points on the great circle `y = 0`, with `A 2`
  on the arc from `A 1` back toward `A 0` (a fold-back at `A 1`).  All edge supports vanish (every
  triple is coplanar in `y = 0`), so `A` is weakly convex; the interior joint angle is `0`.
* `B = [(0,0,1), (24/25,0,7/25), (12/13,3/13,−4/13)]` — a genuinely strictly convex `B` with the
  SAME two side lengths as `A` (matching inners `7/25` and `4/5`) and a strictly larger interior
  joint (so `JointLe`).
* The refuted conclusion at `v = 1`: `gproj e₃ (A i)` scales `A i` (which has `y`-coordinate `0`)
  by a positive scalar, so all three gnomonic images still have `y = 0`; hence
  `det3 (gproj e₃ (A 0)) (gproj e₃ (A 1)) (gproj e₃ (A 2)) = 0`, contradicting `0 < …`.

This is a faithfulness defect of the residue itself (an over-strong predicate, playbook §3.3): the
fold-back degeneracy is exactly what the no-flat-joint exclusion was supposed to forbid, but the
named `Prop` does not see it.

No `sorry`, `axiom`, `admit`, or `native_decide`.
-/

noncomputable section
open scoped RealInnerProductSpace
open ProofsInTheBook.SphericalKernel ProofsInTheBook.SphericalArm
open ProofsInTheBook.SphericalSZInduction ProofsInTheBook.SphericalGnomonic
open ProofsInTheBook.ZinanFFCT8 ProofsInTheBook.ZinanFFCT10
open ProofsInTheBook.SphericalRotation

namespace ProofsInTheBook.ZinanFFCT16

set_option maxHeartbeats 1600000

/-! ## §1. The fold-back arm `A` and the strictly convex comparison arm `B`. -/

/-- `A 0 = (3/5, 0, 4/5)`. -/
def aP0 : E3 := !₂[(3/5 : ℝ), 0, 4/5]
/-- `A 1 = (−3/5, 0, 4/5)` (the fold vertex). -/
def aP1 : E3 := !₂[(-3/5 : ℝ), 0, 4/5]
/-- `A 2 = (0, 0, 1)` (lies on the arc from `A 1` back toward `A 0`). -/
def aP2 : E3 := !₂[(0 : ℝ), 0, 1]

theorem aP0_norm : ‖aP0‖ = 1 := by
  rw [EuclideanSpace.norm_eq, Fin.sum_univ_three, show (aP0:E3) 0 = 3/5 from rfl,
    show (aP0:E3) 1 = 0 from rfl, show (aP0:E3) 2 = 4/5 from rfl]; norm_num
theorem aP1_norm : ‖aP1‖ = 1 := by
  rw [EuclideanSpace.norm_eq, Fin.sum_univ_three, show (aP1:E3) 0 = -3/5 from rfl,
    show (aP1:E3) 1 = 0 from rfl, show (aP1:E3) 2 = 4/5 from rfl]; norm_num
theorem aP2_norm : ‖aP2‖ = 1 := by
  rw [EuclideanSpace.norm_eq, Fin.sum_univ_three, show (aP2:E3) 0 = 0 from rfl,
    show (aP2:E3) 1 = 0 from rfl, show (aP2:E3) 2 = 1 from rfl]; norm_num

def aQ0 : S2 := ⟨aP0, aP0_norm⟩
def aQ1 : S2 := ⟨aP1, aP1_norm⟩
def aQ2 : S2 := ⟨aP2, aP2_norm⟩

/-- The fold-back arm `A : Fin 3 → S2` (`n = 2`). -/
def aArm : Fin 3 → S2 := ![aQ0, aQ1, aQ2]

theorem aArm_y0 : ∀ i : Fin 3, (aArm i : E3) 1 = 0 := by
  intro i; fin_cases i
  · show (aP0:E3) 1 = 0; rfl
  · show (aP1:E3) 1 = 0; rfl
  · show (aP2:E3) 1 = 0; rfl

/-- `B 0 = (0, 0, 1)`. -/
def bP0 : E3 := !₂[(0 : ℝ), 0, 1]
/-- `B 1 = (24/25, 0, 7/25)`. -/
def bP1 : E3 := !₂[(24/25 : ℝ), 0, 7/25]
/-- `B 2 = (12/13, 3/13, −4/13)`. -/
def bP2 : E3 := !₂[(12/13 : ℝ), 3/13, -4/13]

theorem bP0_norm : ‖bP0‖ = 1 := by
  rw [EuclideanSpace.norm_eq, Fin.sum_univ_three, show (bP0:E3) 0 = 0 from rfl,
    show (bP0:E3) 1 = 0 from rfl, show (bP0:E3) 2 = 1 from rfl]; norm_num
theorem bP1_norm : ‖bP1‖ = 1 := by
  rw [EuclideanSpace.norm_eq, Fin.sum_univ_three, show (bP1:E3) 0 = 24/25 from rfl,
    show (bP1:E3) 1 = 0 from rfl, show (bP1:E3) 2 = 7/25 from rfl]; norm_num
theorem bP2_norm : ‖bP2‖ = 1 := by
  rw [EuclideanSpace.norm_eq, Fin.sum_univ_three, show (bP2:E3) 0 = 12/13 from rfl,
    show (bP2:E3) 1 = 3/13 from rfl, show (bP2:E3) 2 = -4/13 from rfl]; norm_num

def bQ0 : S2 := ⟨bP0, bP0_norm⟩
def bQ1 : S2 := ⟨bP1, bP1_norm⟩
def bQ2 : S2 := ⟨bP2, bP2_norm⟩

/-- The strictly convex comparison arm `B : Fin 3 → S2`. -/
def bArm : Fin 3 → S2 := ![bQ0, bQ1, bQ2]

/-- Coordinate-vector eval for `bArm` on raw `Fin.mk` indices (robust under `interval_cases`). -/
theorem bArm_eval (k : ℕ) (hk : k < 3) :
    (bArm ⟨k, hk⟩ : E3) = if k = 0 then bP0 else if k = 1 then bP1 else bP2 := by
  have h2 : k ≤ 2 := by omega
  interval_cases k <;> rfl

/-! ## §2. `A` is a weakly convex arm (all supports vanish; `y = 0`). -/

/-- `det3` vanishes when all three vectors lie in the plane `y = 0` (coordinate `1` is `0`). -/
theorem det3_y0 {a b c : E3} (ha : a 1 = 0) (hb : b 1 = 0) (hc : c 1 = 0) :
    det3 a b c = 0 := by
  simp only [det3, ha, hb, hc]; ring

theorem aArm_support_zero (i j : Fin 3) :
    sOrient (aArm i) (aArm (i+1)) (aArm j) = 0 :=
  det3_y0 (aArm_y0 i) (aArm_y0 (i+1)) (aArm_y0 j)

theorem aArm_weakConvex : WeakConvexSphArm aArm := by
  refine ⟨le_refl 2, le_refl 3, ?_, ?_, ?_⟩
  · -- edge_short
    intro i; fin_cases i
    · show ShortArc (aArm 0) (aArm (0+1))
      refine ⟨fun h => ?_, fun h => ?_⟩
      · have hh : (aArm 0:E3) 0 = (aArm (0+1):E3) 0 := by rw [h]
        rw [show (aArm 0:E3) 0 = 3/5 from rfl, show (aArm (0+1):E3) 0 = -3/5 from rfl] at hh
        norm_num at hh
      · have hh : (aArm 0:E3) 2 = (-(aArm (0+1):E3)) 2 := by rw [h]
        rw [show (aArm 0:E3) 2 = 4/5 from rfl, PiLp.neg_apply,
          show (aArm (0+1):E3) 2 = 4/5 from rfl] at hh
        norm_num at hh
    · show ShortArc (aArm 1) (aArm (1+1))
      refine ⟨fun h => ?_, fun h => ?_⟩
      · have hh : (aArm 1:E3) 0 = (aArm (1+1):E3) 0 := by rw [h]
        rw [show (aArm 1:E3) 0 = -3/5 from rfl, show (aArm (1+1):E3) 0 = 0 from rfl] at hh
        norm_num at hh
      · have hh : (aArm 1:E3) 2 = (-(aArm (1+1):E3)) 2 := by rw [h]
        rw [show (aArm 1:E3) 2 = 4/5 from rfl, PiLp.neg_apply,
          show (aArm (1+1):E3) 2 = 1 from rfl] at hh
        norm_num at hh
    · show ShortArc (aArm 2) (aArm (2+1))
      refine ⟨fun h => ?_, fun h => ?_⟩
      · have hh : (aArm 2:E3) 2 = (aArm (2+1):E3) 2 := by rw [h]
        rw [show (aArm 2:E3) 2 = 1 from rfl, show (aArm (2+1):E3) 2 = 4/5 from rfl] at hh
        norm_num at hh
      · have hh : (aArm 2:E3) 2 = (-(aArm (2+1):E3)) 2 := by rw [h]
        rw [show (aArm 2:E3) 2 = 1 from rfl, PiLp.neg_apply,
          show (aArm (2+1):E3) 2 = 4/5 from rfl] at hh
        norm_num at hh
  · -- edge_support: all supports vanish
    intro i j; rw [aArm_support_zero i j]
  · -- open_hemisphere: h = (0,0,1); inners 4/5, 4/5, 1 > 0
    refine ⟨!₂[(0:ℝ),0,1], ?_, ?_⟩
    · rw [EuclideanSpace.norm_eq, Fin.sum_univ_three,
        show (!₂[(0:ℝ),0,1] : E3) 0 = 0 from rfl, show (!₂[(0:ℝ),0,1] : E3) 1 = 0 from rfl,
        show (!₂[(0:ℝ),0,1] : E3) 2 = 1 from rfl]; norm_num
    · intro i
      fin_cases i
      · show (0:ℝ) < ⟪(!₂[(0:ℝ),0,1] : E3), (aArm 0 : E3)⟫
        rw [inner_eq_coord, show (!₂[(0:ℝ),0,1] : E3) 0 = 0 from rfl,
          show (!₂[(0:ℝ),0,1] : E3) 1 = 0 from rfl, show (!₂[(0:ℝ),0,1] : E3) 2 = 1 from rfl,
          show (aArm 0:E3) 2 = 4/5 from rfl]; norm_num
      · show (0:ℝ) < ⟪(!₂[(0:ℝ),0,1] : E3), (aArm 1 : E3)⟫
        rw [inner_eq_coord, show (!₂[(0:ℝ),0,1] : E3) 0 = 0 from rfl,
          show (!₂[(0:ℝ),0,1] : E3) 1 = 0 from rfl, show (!₂[(0:ℝ),0,1] : E3) 2 = 1 from rfl,
          show (aArm 1:E3) 2 = 4/5 from rfl]; norm_num
      · show (0:ℝ) < ⟪(!₂[(0:ℝ),0,1] : E3), (aArm 2 : E3)⟫
        rw [inner_eq_coord, show (!₂[(0:ℝ),0,1] : E3) 0 = 0 from rfl,
          show (!₂[(0:ℝ),0,1] : E3) 1 = 0 from rfl, show (!₂[(0:ℝ),0,1] : E3) 2 = 1 from rfl,
          show (aArm 2:E3) 2 = 1 from rfl]; norm_num

/-! ## §3. `B` is a strictly convex arm.  All three non-incident supports are `+72/325`. -/

theorem bArm_strictConvex : StrictConvexSphArm bArm := by
  refine ⟨le_refl 2, ?_, ?_, ?_, ?_, ?_⟩
  · -- three_le
    exact le_refl 3
  · -- edge_short
    intro i; fin_cases i
    · show ShortArc (bArm 0) (bArm (0+1))
      refine ⟨fun h => ?_, fun h => ?_⟩
      · have hh : (bArm 0:E3) 0 = (bArm (0+1):E3) 0 := by rw [h]
        rw [show (bArm 0:E3) 0 = 0 from rfl, show (bArm (0+1):E3) 0 = 24/25 from rfl] at hh
        norm_num at hh
      · have hh : (bArm 0:E3) 2 = (-(bArm (0+1):E3)) 2 := by rw [h]
        rw [show (bArm 0:E3) 2 = 1 from rfl, PiLp.neg_apply,
          show (bArm (0+1):E3) 2 = 7/25 from rfl] at hh
        norm_num at hh
    · show ShortArc (bArm 1) (bArm (1+1))
      refine ⟨fun h => ?_, fun h => ?_⟩
      · have hh : (bArm 1:E3) 0 = (bArm (1+1):E3) 0 := by rw [h]
        rw [show (bArm 1:E3) 0 = 24/25 from rfl, show (bArm (1+1):E3) 0 = 12/13 from rfl] at hh
        norm_num at hh
      · have hh : (bArm 1:E3) 1 = (-(bArm (1+1):E3)) 1 := by rw [h]
        rw [show (bArm 1:E3) 1 = 0 from rfl, PiLp.neg_apply,
          show (bArm (1+1):E3) 1 = 3/13 from rfl] at hh
        norm_num at hh
    · show ShortArc (bArm 2) (bArm (2+1))
      refine ⟨fun h => ?_, fun h => ?_⟩
      · have hh : (bArm 2:E3) 0 = (bArm (2+1):E3) 0 := by rw [h]
        rw [show (bArm 2:E3) 0 = 12/13 from rfl, show (bArm (2+1):E3) 0 = 0 from rfl] at hh
        norm_num at hh
      · have hh : (bArm 2:E3) 1 = (-(bArm (2+1):E3)) 1 := by rw [h]
        rw [show (bArm 2:E3) 1 = 3/13 from rfl, PiLp.neg_apply,
          show (bArm (2+1):E3) 1 = 0 from rfl] at hh
        norm_num at hh
  · -- edge_support: ∀ i j, 0 ≤ sOrient (B i) (B (i+1)) (B j).  Incident j gives 0; non-incident +72/325.
    intro i j
    show (0:ℝ) ≤ det3 (bArm i : E3) (bArm (i+1) : E3) (bArm j : E3)
    fin_cases i <;> fin_cases j <;>
      simp only [show ((⟨0,by omega⟩:Fin 3)+1) = ⟨1,by omega⟩ from rfl,
        show ((⟨1,by omega⟩:Fin 3)+1) = ⟨2,by omega⟩ from rfl,
        show ((⟨2,by omega⟩:Fin 3)+1) = ⟨0,by omega⟩ from rfl, bArm_eval] <;>
      norm_num [bP0, bP1, bP2, det3E3]
  · -- strict_nonincident: j ≠ i, j ≠ i+1.  In a 3-gon the only such j is the third vertex; +72/325 > 0.
    intro i j hji hji1
    show (0:ℝ) < det3 (bArm i : E3) (bArm (i+1) : E3) (bArm j : E3)
    fin_cases i <;> fin_cases j <;>
      first
        | (exfalso; revert hji hji1; decide)
        | (simp only [show ((⟨0,by omega⟩:Fin 3)+1) = ⟨1,by omega⟩ from rfl,
            show ((⟨1,by omega⟩:Fin 3)+1) = ⟨2,by omega⟩ from rfl,
            show ((⟨2,by omega⟩:Fin 3)+1) = ⟨0,by omega⟩ from rfl, bArm_eval] <;>
          norm_num [bP0, bP1, bP2, det3E3])
  · -- open_hemisphere: normalized h_B from raw w = (612, 75, 316); raw inners 316, 676, 485 > 0.
    refine ⟨(‖(!₂[(612:ℝ),75,316] : E3)‖)⁻¹ • (!₂[(612:ℝ),75,316] : E3), ?_, ?_⟩
    · -- ‖h_B‖ = 1
      have hw : (!₂[(612:ℝ),75,316] : E3) ≠ 0 := by
        intro h
        have : (!₂[(612:ℝ),75,316] : E3) 0 = (0 : E3) 0 := by rw [h]
        rw [show (!₂[(612:ℝ),75,316] : E3) 0 = 612 from rfl, PiLp.zero_apply] at this
        norm_num at this
      rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ (norm_ne_zero_iff.mpr hw)]
    · intro i
      have hwnorm : (0:ℝ) < ‖(!₂[(612:ℝ),75,316] : E3)‖ := by
        rw [norm_pos_iff]
        intro h
        have : (!₂[(612:ℝ),75,316] : E3) 0 = (0 : E3) 0 := by rw [h]
        rw [show (!₂[(612:ℝ),75,316] : E3) 0 = 612 from rfl, PiLp.zero_apply] at this
        norm_num at this
      rw [real_inner_smul_left]
      apply mul_pos (by positivity)
      fin_cases i
      · show (0:ℝ) < ⟪(!₂[(612:ℝ),75,316] : E3), (bArm 0 : E3)⟫
        rw [show (bArm 0:E3) = bP0 from rfl, bP0, innerE3]; norm_num
      · show (0:ℝ) < ⟪(!₂[(612:ℝ),75,316] : E3), (bArm 1 : E3)⟫
        rw [show (bArm 1:E3) = bP1 from rfl, bP1, innerE3]; norm_num
      · show (0:ℝ) < ⟪(!₂[(612:ℝ),75,316] : E3), (bArm 2 : E3)⟫
        rw [show (bArm 2:E3) = bP2 from rfl, bP2, innerE3]; norm_num

/-! ## §4. `SameSides aArm bArm`: equal side inners give equal side lengths. -/

/-- Side inner of `A`: `⟪A 0, A 1⟫ = 7/25`, `⟪A 1, A 2⟫ = 4/5`. -/
theorem aInner_side0 : sInner aQ0 aQ1 = 7/25 := by
  show (⟪(aP0:E3), (aP1:E3)⟫ : ℝ) = 7/25
  rw [aP0, aP1, innerE3]; norm_num
theorem aInner_side1 : sInner aQ1 aQ2 = 4/5 := by
  show (⟪(aP1:E3), (aP2:E3)⟫ : ℝ) = 4/5
  rw [aP1, aP2, innerE3]; norm_num

theorem bInner_side0 : sInner bQ0 bQ1 = 7/25 := by
  show (⟪(bP0:E3), (bP1:E3)⟫ : ℝ) = 7/25
  rw [bP0, bP1, innerE3]; norm_num
theorem bInner_side1 : sInner bQ1 bQ2 = 4/5 := by
  show (⟪(bP1:E3), (bP2:E3)⟫ : ℝ) = 4/5
  rw [bP1, bP2, innerE3]; norm_num

theorem aArm_bArm_sameSides : SameSides aArm bArm := by
  intro i
  fin_cases i
  · -- side 0
    show sDist (aArm 0) (aArm 1) = sDist (bArm 0) (bArm 1)
    show Real.arccos (sInner aQ0 aQ1) = Real.arccos (sInner bQ0 bQ1)
    rw [aInner_side0, bInner_side0]
  · -- side 1
    show sDist (aArm 1) (aArm 2) = sDist (bArm 1) (bArm 2)
    show Real.arccos (sInner aQ1 aQ2) = Real.arccos (sInner bQ1 bQ2)
    rw [aInner_side1, bInner_side1]

/-! ## §5. `JointLe aArm bArm`: the only interior joint of `A` has angle `0 ≤` that of `B`. -/

/-- The two tangent directions at the fold vertex `A 1` are positive multiples of each other:
`tangentTo A1 A2 = (5/8) • tangentTo A1 A0`.  Hence the spherical angle at `A 1` is `0`. -/
theorem tangent_parallel :
    tangentTo aQ1 aQ2 = (5/8 : ℝ) • tangentTo aQ1 aQ0 := by
  rw [tangentTo_eq, tangentTo_eq]
  have h21 : sInner aQ2 aQ1 = 4/5 := by
    show (⟪(aP2:E3), (aP1:E3)⟫ : ℝ) = 4/5; rw [aP2, aP1, innerE3]; norm_num
  have h01 : sInner aQ0 aQ1 = 7/25 := by
    show (⟪(aP0:E3), (aP1:E3)⟫ : ℝ) = 7/25; rw [aP0, aP1, innerE3]; norm_num
  rw [h21, h01]
  -- (A2) - (4/5)•(A1) = (5/8) • ((A0) - (7/25)•(A1))
  apply ext_coord <;>
    simp only [SphericalRotation.sub_apply, SphericalRotation.smul_apply,
      show (aQ0:E3) = aP0 from rfl, show (aQ1:E3) = aP1 from rfl, show (aQ2:E3) = aP2 from rfl,
      aP0, aP1, aP2, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      Matrix.cons_val_two, Matrix.tail_cons] <;> norm_num

theorem tangent_A1_A0_ne_zero : tangentTo aQ1 aQ0 ≠ 0 := by
  rw [tangentTo_ne_zero_iff]
  refine ⟨fun h => ?_, fun h => ?_⟩
  · have hh : (aQ1:E3) 0 = (aQ0:E3) 0 := by rw [h]
    rw [show (aQ1:E3) 0 = -3/5 from rfl, show (aQ0:E3) 0 = 3/5 from rfl] at hh
    norm_num at hh
  · have hh : (aQ1:E3) 2 = (-(aQ0:E3)) 2 := by rw [h]
    rw [show (aQ1:E3) 2 = 4/5 from rfl, PiLp.neg_apply, show (aQ0:E3) 2 = 4/5 from rfl] at hh
    norm_num at hh

/-- The spherical angle at the fold vertex is `0`. -/
theorem sphAngle_fold_zero : sphAngle aQ0 aQ1 aQ2 = 0 := by
  rw [sphAngle, InnerProductGeometry.angle_eq_zero_iff]
  exact ⟨tangent_A1_A0_ne_zero, 5/8, by norm_num, tangent_parallel⟩

theorem aArm_bArm_jointLe : JointLe aArm bArm := by
  intro i
  -- Fin (2 - 1) = Fin 1; the only joint is `i.val = 0`, the fold at vertex `1`.
  have hival : i.val = 0 := by have := i.isLt; omega
  -- jointAngle aArm i = sphAngle (A 0) (A 1) (A 2) = 0 ≤ jointAngle bArm i.
  have hA : jointAngle aArm i = 0 := by
    rw [jointAngle]
    have e0 : (aArm ⟨i.val, by have := i.isLt; omega⟩) = aQ0 := by
      have : (⟨i.val, by have := i.isLt; omega⟩ : Fin 3) = ⟨0, by omega⟩ := by
        apply Fin.ext; simp only [Fin.val_mk, hival]
      rw [this]; rfl
    have e1 : (aArm ⟨i.val + 1, by have := i.isLt; omega⟩) = aQ1 := by
      have : (⟨i.val + 1, by have := i.isLt; omega⟩ : Fin 3) = ⟨1, by omega⟩ := by
        apply Fin.ext; simp only [Fin.val_mk, hival]
      rw [this]; rfl
    have e2 : (aArm ⟨i.val + 2, by have := i.isLt; omega⟩) = aQ2 := by
      have : (⟨i.val + 2, by have := i.isLt; omega⟩ : Fin 3) = ⟨2, by omega⟩ := by
        apply Fin.ext; simp only [Fin.val_mk, hival]
      rw [this]; rfl
    rw [e0, e1, e2, sphAngle_fold_zero]
  rw [hA, jointAngle]
  exact sphAngle_nonneg _ _ _

/-! ## §6. The refuted conclusion: the gnomonic interior orientation vanishes. -/

/-- The plane normal `h = e₃`, an open hemisphere for `A` (inners `4/5, 4/5, 1 > 0`). -/
def aH : E3 := !₂[(0:ℝ), 0, 1]

theorem aH_pos : ∀ i : Fin 3, (0:ℝ) < ⟪aH, (aArm i : E3)⟫ := by
  intro i
  fin_cases i
  · show (0:ℝ) < ⟪aH, (aArm 0 : E3)⟫
    rw [aH, inner_eq_coord, coordE3_0, coordE3_1, coordE3_2,
      show (aArm 0:E3) 2 = 4/5 from rfl]; norm_num
  · show (0:ℝ) < ⟪aH, (aArm 1 : E3)⟫
    rw [aH, inner_eq_coord, coordE3_0, coordE3_1, coordE3_2,
      show (aArm 1:E3) 2 = 4/5 from rfl]; norm_num
  · show (0:ℝ) < ⟪aH, (aArm 2 : E3)⟫
    rw [aH, inner_eq_coord, coordE3_0, coordE3_1, coordE3_2,
      show (aArm 2:E3) 2 = 1 from rfl]; norm_num

/-- The gnomonic image of any vertex of `A` still has `y`-coordinate `0` (the projection scales). -/
theorem gproj_aArm_y0 (i : Fin 3) : (gproj aH (aArm i)) 1 = 0 := by
  rw [gproj, PiLp.smul_apply, smul_eq_mul, aArm_y0 i, mul_zero]

/-! ## §7. The headline falsification. -/

/-- **`GnomonicNoflatJoint` is FALSE.**  Instantiating it on the fold-back arm `A` (with comparison
arm `B`, `n = 2`, interior `v = 1`, normal `h = e₃`) would assert `0 < det3 (gproj e₃ (A 0))
(gproj e₃ (A 1)) (gproj e₃ (A 2))`, but all three gnomonic images lie in the plane `y = 0`, so that
determinant is `0` — a contradiction. -/
theorem gnomonicNoflatJoint_false : ¬ ProofsInTheBook.ZinanFFCT8.GnomonicNoflatJoint := by
  intro H
  -- Instantiate at n = 2, A = aArm, B = bArm, h = aH, v = 1.
  have hcontra : 0 < det3 (gproj aH (aArm ⟨1 - 1, by omega⟩)) (gproj aH (aArm ⟨1, by omega⟩))
      (gproj aH (aArm ⟨1 + 1, by omega⟩)) :=
    H (n := 2) (le_refl 2) aArm_weakConvex bArm_strictConvex aArm_bArm_sameSides
      aArm_bArm_jointLe (h := aH) aH_pos 1 (le_refl 1) (by omega)
  -- The three gnomonic images all have y = 0, so the determinant is 0.
  have hzero : det3 (gproj aH (aArm ⟨1 - 1, by omega⟩)) (gproj aH (aArm ⟨1, by omega⟩))
      (gproj aH (aArm ⟨1 + 1, by omega⟩)) = 0 :=
    det3_y0 (gproj_aArm_y0 _) (gproj_aArm_y0 _) (gproj_aArm_y0 _)
  rw [hzero] at hcontra
  exact lt_irrefl 0 hcontra

#print axioms ProofsInTheBook.ZinanFFCT16.gnomonicNoflatJoint_false

end ProofsInTheBook.ZinanFFCT16
