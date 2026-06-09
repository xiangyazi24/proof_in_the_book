import ProofsInTheBook.ZinanFFCT10

/-!
# `ZinanFFCT17` — statement audit: the Ch13 induction predicate `Main` is FALSE at `n = 3`;
# hence `SZOpeningStep` and `FoldedFlatCutTransport` are both false as stated

## §3.3 finding (kernel-anchored here)

`SphericalSZInduction.Main n` — the chapter's central per-level induction statement — quantifies the
LEFT arm over `WeakConvexSphArm`.  But `WeakConvexSphArm` is **vacuous on collinear configurations**:
every support `sOrient` of a family on one great circle is `0 ≥ 0`, so an arbitrary back-and-forth
*zigzag* on a single great circle is "weakly convex", with all interior joints `= 0` (so `JointLe`
against anything holds).  Such a zigzag is NOT a limit of strictly convex arms, and the arm-lemma
conclusion genuinely fails against a thin near-closed strictly convex companion:

**Counterexample (`n = 3`, all rational, all side-cosines `2/3`):**
* `A = [p, q, p, q]` with `p = (0,0,1)`, `q = (2/3, −1/3, 2/3)` — the two-point zigzag.  All closed
  supports vanish (every triple from `{p,q}` has a repeated vector), both interior joints are `0`,
  and `endpt A = sDist p q = arccos (2/3)`.
* `B = [(1/9,−8/9,4/9), (2/3,−1/3,2/3), (0,0,1), (−2/15,−11/15,2/3)]` — a genuinely strictly convex
  arm (all eight non-incident supports in `{1/5, 4/15, 8/15, 5/9}`), same three side-cosines `2/3`,
  and `endpt B = arccos (14/15) < arccos (2/3) = endpt A`.

Both arms live in explicit open hemispheres and satisfy every field of the respective predicates, so
`Main 3` is refuted.  Consequences, each kernel-anchored below:

* **`main_three_false : ¬ Main 3`** — the induction target itself is false as stated.
* **`szOpeningStep_false : ¬ SZOpeningStep`** — the chapter's named opening-step residue is false
  (it implies `Main 3` through the proven `main_all`).
* **`foldedFlatCutTransport_false : ¬ FoldedFlatCutTransport`** — the CUT-branch residue is false:
  the zigzag pair satisfies its hypotheses at the cut `(i, j) = (0, 2)` (the support `det3 p q p`
  vanishes; the diagonal inequality is `0 ≤ sDist (B 0) (B 2)`), and its `Main`-IH input is
  dischargeable by the PROVEN `main_of_lt_two` / `main_two`.

## Root cause and repair direction (recorded for the rerouting round)

The hole is in the *induction predicate*, not in any single proof: `WeakConvexSphArm` was meant to be
the closure of the strict class under the `δ*` opening, but it also contains collinear zigzags that no
opening of a strict arm can reach (a strict arm's `δ*`-limit has only the binding supports `= 0`, not
ALL supports).  Any repair must strengthen the left-arm predicate (e.g. to configurations reachable
from / approximable by strict arms, or a first-order surrogate excluding multi-fold collinear chains)
and re-prove the recursion for the strengthened predicate.  `jointAngle_lt_pi` (FFCT3) survives:
`JointLe` + strict `B` still forbids `π`-joints of `A`; what it cannot forbid is `0`-joints, and the
zigzag has only those.

No `sorry`, `axiom`, `admit`, or `native_decide`.
-/

noncomputable section
open scoped RealInnerProductSpace
open ProofsInTheBook.SphericalKernel ProofsInTheBook.SphericalArm
open ProofsInTheBook.SphericalSZInduction ProofsInTheBook.SphericalCutTransport
open ProofsInTheBook.SphericalRotation
open ProofsInTheBook.ZinanFFCT10

namespace ProofsInTheBook.ZinanFFCT17

set_option maxHeartbeats 1600000

/-! ## §1. The zigzag arm `A` and the thin strictly convex companion `B`. -/

/-- `p = (0, 0, 1)`. -/
def pP : E3 := !₂[(0 : ℝ), 0, 1]
/-- `q = (2/3, −1/3, 2/3)`; `⟪p, q⟫ = 2/3`. -/
def qP : E3 := !₂[(2/3 : ℝ), -1/3, 2/3]

theorem pP_norm : ‖pP‖ = 1 := by
  rw [EuclideanSpace.norm_eq, Fin.sum_univ_three, show (pP:E3) 0 = 0 from rfl,
    show (pP:E3) 1 = 0 from rfl, show (pP:E3) 2 = 1 from rfl]; norm_num
theorem qP_norm : ‖qP‖ = 1 := by
  rw [EuclideanSpace.norm_eq, Fin.sum_univ_three, show (qP:E3) 0 = 2/3 from rfl,
    show (qP:E3) 1 = -1/3 from rfl, show (qP:E3) 2 = 2/3 from rfl]; norm_num

def pQ : S2 := ⟨pP, pP_norm⟩
def qQ : S2 := ⟨qP, qP_norm⟩

/-- The zigzag arm `A = [p, q, p, q]` (`n = 3`). -/
def aArm : Fin 4 → S2 := ![pQ, qQ, pQ, qQ]

theorem aArm_eval (k : ℕ) (hk : k < 4) :
    (aArm ⟨k, hk⟩ : E3) = if k = 0 then pP else if k = 1 then qP
      else if k = 2 then pP else qP := by
  have h3 : k ≤ 3 := by omega
  interval_cases k <;> rfl

/-- `B 0 = (1/9, −8/9, 4/9)`. -/
def b0P : E3 := !₂[(1/9 : ℝ), -8/9, 4/9]
/-- `B 1 = (2/3, −1/3, 2/3)`. -/
def b1P : E3 := !₂[(2/3 : ℝ), -1/3, 2/3]
/-- `B 2 = (0, 0, 1)`. -/
def b2P : E3 := !₂[(0 : ℝ), 0, 1]
/-- `B 3 = (−2/15, −11/15, 2/3)`. -/
def b3P : E3 := !₂[(-2/15 : ℝ), -11/15, 2/3]

theorem b0P_norm : ‖b0P‖ = 1 := by
  rw [EuclideanSpace.norm_eq, Fin.sum_univ_three, show (b0P:E3) 0 = 1/9 from rfl,
    show (b0P:E3) 1 = -8/9 from rfl, show (b0P:E3) 2 = 4/9 from rfl]; norm_num
theorem b1P_norm : ‖b1P‖ = 1 := by
  rw [EuclideanSpace.norm_eq, Fin.sum_univ_three, show (b1P:E3) 0 = 2/3 from rfl,
    show (b1P:E3) 1 = -1/3 from rfl, show (b1P:E3) 2 = 2/3 from rfl]; norm_num
theorem b2P_norm : ‖b2P‖ = 1 := by
  rw [EuclideanSpace.norm_eq, Fin.sum_univ_three, show (b2P:E3) 0 = 0 from rfl,
    show (b2P:E3) 1 = 0 from rfl, show (b2P:E3) 2 = 1 from rfl]; norm_num
theorem b3P_norm : ‖b3P‖ = 1 := by
  rw [EuclideanSpace.norm_eq, Fin.sum_univ_three, show (b3P:E3) 0 = -2/15 from rfl,
    show (b3P:E3) 1 = -11/15 from rfl, show (b3P:E3) 2 = 2/3 from rfl]; norm_num

def b0Q : S2 := ⟨b0P, b0P_norm⟩
def b1Q : S2 := ⟨b1P, b1P_norm⟩
def b2Q : S2 := ⟨b2P, b2P_norm⟩
def b3Q : S2 := ⟨b3P, b3P_norm⟩

/-- The strictly convex companion `B`. -/
def bArm : Fin 4 → S2 := ![b0Q, b1Q, b2Q, b3Q]

theorem bArm_eval (k : ℕ) (hk : k < 4) :
    (bArm ⟨k, hk⟩ : E3) = if k = 0 then b0P else if k = 1 then b1P
      else if k = 2 then b2P else b3P := by
  have h3 : k ≤ 3 := by omega
  interval_cases k <;> rfl

/-! ## §2. `A` is a weakly convex arm (all supports vanish: every triple repeats a vector). -/

theorem aArm_weakConvex : WeakConvexSphArm aArm := by
  refine ⟨by omega, by omega, ?_, ?_, ?_⟩
  · -- edge_short: every edge is (p,q) or (q,p); distinct and non-antipodal via the z-coordinate.
    intro i; fin_cases i
    · show ShortArc (aArm 0) (aArm (0+1))
      refine ⟨fun h => ?_, fun h => ?_⟩
      · have hh : (aArm 0:E3) 2 = (aArm (0+1):E3) 2 := by rw [h]
        rw [show (aArm 0:E3) 2 = 1 from rfl, show (aArm (0+1):E3) 2 = 2/3 from rfl] at hh
        norm_num at hh
      · have hh : (aArm 0:E3) 2 = (-(aArm (0+1):E3)) 2 := by rw [h]
        rw [show (aArm 0:E3) 2 = 1 from rfl, PiLp.neg_apply,
          show (aArm (0+1):E3) 2 = 2/3 from rfl] at hh
        norm_num at hh
    · show ShortArc (aArm 1) (aArm (1+1))
      refine ⟨fun h => ?_, fun h => ?_⟩
      · have hh : (aArm 1:E3) 2 = (aArm (1+1):E3) 2 := by rw [h]
        rw [show (aArm 1:E3) 2 = 2/3 from rfl, show (aArm (1+1):E3) 2 = 1 from rfl] at hh
        norm_num at hh
      · have hh : (aArm 1:E3) 2 = (-(aArm (1+1):E3)) 2 := by rw [h]
        rw [show (aArm 1:E3) 2 = 2/3 from rfl, PiLp.neg_apply,
          show (aArm (1+1):E3) 2 = 1 from rfl] at hh
        norm_num at hh
    · show ShortArc (aArm 2) (aArm (2+1))
      refine ⟨fun h => ?_, fun h => ?_⟩
      · have hh : (aArm 2:E3) 2 = (aArm (2+1):E3) 2 := by rw [h]
        rw [show (aArm 2:E3) 2 = 1 from rfl, show (aArm (2+1):E3) 2 = 2/3 from rfl] at hh
        norm_num at hh
      · have hh : (aArm 2:E3) 2 = (-(aArm (2+1):E3)) 2 := by rw [h]
        rw [show (aArm 2:E3) 2 = 1 from rfl, PiLp.neg_apply,
          show (aArm (2+1):E3) 2 = 2/3 from rfl] at hh
        norm_num at hh
    · show ShortArc (aArm 3) (aArm (3+1))
      refine ⟨fun h => ?_, fun h => ?_⟩
      · have hh : (aArm 3:E3) 2 = (aArm (3+1):E3) 2 := by rw [h]
        rw [show (aArm 3:E3) 2 = 2/3 from rfl, show (aArm (3+1):E3) 2 = 1 from rfl] at hh
        norm_num at hh
      · have hh : (aArm 3:E3) 2 = (-(aArm (3+1):E3)) 2 := by rw [h]
        rw [show (aArm 3:E3) 2 = 2/3 from rfl, PiLp.neg_apply,
          show (aArm (3+1):E3) 2 = 1 from rfl] at hh
        norm_num at hh
  · -- edge_support: every triple from {p, q} has a repeated vector, so every det3 vanishes.
    intro i j
    show (0:ℝ) ≤ det3 (aArm i : E3) (aArm (i+1) : E3) (aArm j : E3)
    fin_cases i <;> fin_cases j <;>
      simp only [show ((⟨0,by omega⟩:Fin 4)+1) = ⟨1,by omega⟩ from rfl,
        show ((⟨1,by omega⟩:Fin 4)+1) = ⟨2,by omega⟩ from rfl,
        show ((⟨2,by omega⟩:Fin 4)+1) = ⟨3,by omega⟩ from rfl,
        show ((⟨3,by omega⟩:Fin 4)+1) = ⟨0,by omega⟩ from rfl, aArm_eval] <;>
      norm_num [pP, qP, det3E3]
  · -- open_hemisphere: normalized (2, −1, 5); both inners are 5.
    refine ⟨(‖(!₂[(2:ℝ),-1,5] : E3)‖)⁻¹ • (!₂[(2:ℝ),-1,5] : E3), ?_, ?_⟩
    · have hw : (!₂[(2:ℝ),-1,5] : E3) ≠ 0 := by
        intro h
        have : (!₂[(2:ℝ),-1,5] : E3) 0 = (0 : E3) 0 := by rw [h]
        rw [show (!₂[(2:ℝ),-1,5] : E3) 0 = 2 from rfl, PiLp.zero_apply] at this
        norm_num at this
      rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ (norm_ne_zero_iff.mpr hw)]
    · intro i
      have hwnorm : (0:ℝ) < ‖(!₂[(2:ℝ),-1,5] : E3)‖ := by
        rw [norm_pos_iff]
        intro h
        have : (!₂[(2:ℝ),-1,5] : E3) 0 = (0 : E3) 0 := by rw [h]
        rw [show (!₂[(2:ℝ),-1,5] : E3) 0 = 2 from rfl, PiLp.zero_apply] at this
        norm_num at this
      rw [real_inner_smul_left]
      apply mul_pos (by positivity)
      fin_cases i
      · show (0:ℝ) < ⟪(!₂[(2:ℝ),-1,5] : E3), (aArm 0 : E3)⟫
        rw [show (aArm 0:E3) = pP from rfl, pP, innerE3]; norm_num
      · show (0:ℝ) < ⟪(!₂[(2:ℝ),-1,5] : E3), (aArm 1 : E3)⟫
        rw [show (aArm 1:E3) = qP from rfl, qP, innerE3]; norm_num
      · show (0:ℝ) < ⟪(!₂[(2:ℝ),-1,5] : E3), (aArm 2 : E3)⟫
        rw [show (aArm 2:E3) = pP from rfl, pP, innerE3]; norm_num
      · show (0:ℝ) < ⟪(!₂[(2:ℝ),-1,5] : E3), (aArm 3 : E3)⟫
        rw [show (aArm 3:E3) = qP from rfl, qP, innerE3]; norm_num

/-! ## §3. `B` is a strictly convex arm (all eight non-incident supports positive). -/

theorem bArm_strictConvex : StrictConvexSphArm bArm := by
  refine ⟨by omega, by omega, ?_, ?_, ?_, ?_⟩
  · -- edge_short: distinct / non-antipodal via the x-coordinate of each pair.
    intro i; fin_cases i
    · show ShortArc (bArm 0) (bArm (0+1))
      refine ⟨fun h => ?_, fun h => ?_⟩
      · have hh : (bArm 0:E3) 0 = (bArm (0+1):E3) 0 := by rw [h]
        rw [show (bArm 0:E3) 0 = 1/9 from rfl, show (bArm (0+1):E3) 0 = 2/3 from rfl] at hh
        norm_num at hh
      · have hh : (bArm 0:E3) 0 = (-(bArm (0+1):E3)) 0 := by rw [h]
        rw [show (bArm 0:E3) 0 = 1/9 from rfl, PiLp.neg_apply,
          show (bArm (0+1):E3) 0 = 2/3 from rfl] at hh
        norm_num at hh
    · show ShortArc (bArm 1) (bArm (1+1))
      refine ⟨fun h => ?_, fun h => ?_⟩
      · have hh : (bArm 1:E3) 0 = (bArm (1+1):E3) 0 := by rw [h]
        rw [show (bArm 1:E3) 0 = 2/3 from rfl, show (bArm (1+1):E3) 0 = 0 from rfl] at hh
        norm_num at hh
      · have hh : (bArm 1:E3) 0 = (-(bArm (1+1):E3)) 0 := by rw [h]
        rw [show (bArm 1:E3) 0 = 2/3 from rfl, PiLp.neg_apply,
          show (bArm (1+1):E3) 0 = 0 from rfl] at hh
        norm_num at hh
    · show ShortArc (bArm 2) (bArm (2+1))
      refine ⟨fun h => ?_, fun h => ?_⟩
      · have hh : (bArm 2:E3) 0 = (bArm (2+1):E3) 0 := by rw [h]
        rw [show (bArm 2:E3) 0 = 0 from rfl, show (bArm (2+1):E3) 0 = -2/15 from rfl] at hh
        norm_num at hh
      · have hh : (bArm 2:E3) 0 = (-(bArm (2+1):E3)) 0 := by rw [h]
        rw [show (bArm 2:E3) 0 = 0 from rfl, PiLp.neg_apply,
          show (bArm (2+1):E3) 0 = -2/15 from rfl] at hh
        norm_num at hh
    · show ShortArc (bArm 3) (bArm (3+1))
      refine ⟨fun h => ?_, fun h => ?_⟩
      · have hh : (bArm 3:E3) 0 = (bArm (3+1):E3) 0 := by rw [h]
        rw [show (bArm 3:E3) 0 = -2/15 from rfl, show (bArm (3+1):E3) 0 = 1/9 from rfl] at hh
        norm_num at hh
      · have hh : (bArm 3:E3) 0 = (-(bArm (3+1):E3)) 0 := by rw [h]
        rw [show (bArm 3:E3) 0 = -2/15 from rfl, PiLp.neg_apply,
          show (bArm (3+1):E3) 0 = 1/9 from rfl] at hh
        norm_num at hh
  · -- edge_support: incident vanish, non-incident positive.
    intro i j
    show (0:ℝ) ≤ det3 (bArm i : E3) (bArm (i+1) : E3) (bArm j : E3)
    fin_cases i <;> fin_cases j <;>
      simp only [show ((⟨0,by omega⟩:Fin 4)+1) = ⟨1,by omega⟩ from rfl,
        show ((⟨1,by omega⟩:Fin 4)+1) = ⟨2,by omega⟩ from rfl,
        show ((⟨2,by omega⟩:Fin 4)+1) = ⟨3,by omega⟩ from rfl,
        show ((⟨3,by omega⟩:Fin 4)+1) = ⟨0,by omega⟩ from rfl, bArm_eval] <;>
      norm_num [b0P, b1P, b2P, b3P, det3E3]
  · -- strict_nonincident: the eight honest cases are positive; incident cases are excluded.
    intro i j hji hji1
    show (0:ℝ) < det3 (bArm i : E3) (bArm (i+1) : E3) (bArm j : E3)
    fin_cases i <;> fin_cases j <;>
      first
        | (exfalso; revert hji hji1; decide)
        | (simp only [show ((⟨0,by omega⟩:Fin 4)+1) = ⟨1,by omega⟩ from rfl,
            show ((⟨1,by omega⟩:Fin 4)+1) = ⟨2,by omega⟩ from rfl,
            show ((⟨2,by omega⟩:Fin 4)+1) = ⟨3,by omega⟩ from rfl,
            show ((⟨3,by omega⟩:Fin 4)+1) = ⟨0,by omega⟩ from rfl, bArm_eval] <;>
          norm_num [b0P, b1P, b2P, b3P, det3E3])
  · -- open_hemisphere: normalized (29, −88, 125); inners 137, 132, 125, 144.
    refine ⟨(‖(!₂[(29:ℝ),-88,125] : E3)‖)⁻¹ • (!₂[(29:ℝ),-88,125] : E3), ?_, ?_⟩
    · have hw : (!₂[(29:ℝ),-88,125] : E3) ≠ 0 := by
        intro h
        have : (!₂[(29:ℝ),-88,125] : E3) 0 = (0 : E3) 0 := by rw [h]
        rw [show (!₂[(29:ℝ),-88,125] : E3) 0 = 29 from rfl, PiLp.zero_apply] at this
        norm_num at this
      rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ (norm_ne_zero_iff.mpr hw)]
    · intro i
      have hwnorm : (0:ℝ) < ‖(!₂[(29:ℝ),-88,125] : E3)‖ := by
        rw [norm_pos_iff]
        intro h
        have : (!₂[(29:ℝ),-88,125] : E3) 0 = (0 : E3) 0 := by rw [h]
        rw [show (!₂[(29:ℝ),-88,125] : E3) 0 = 29 from rfl, PiLp.zero_apply] at this
        norm_num at this
      rw [real_inner_smul_left]
      apply mul_pos (by positivity)
      fin_cases i
      · show (0:ℝ) < ⟪(!₂[(29:ℝ),-88,125] : E3), (bArm 0 : E3)⟫
        rw [show (bArm 0:E3) = b0P from rfl, b0P, innerE3]; norm_num
      · show (0:ℝ) < ⟪(!₂[(29:ℝ),-88,125] : E3), (bArm 1 : E3)⟫
        rw [show (bArm 1:E3) = b1P from rfl, b1P, innerE3]; norm_num
      · show (0:ℝ) < ⟪(!₂[(29:ℝ),-88,125] : E3), (bArm 2 : E3)⟫
        rw [show (bArm 2:E3) = b2P from rfl, b2P, innerE3]; norm_num
      · show (0:ℝ) < ⟪(!₂[(29:ℝ),-88,125] : E3), (bArm 3 : E3)⟫
        rw [show (bArm 3:E3) = b3P from rfl, b3P, innerE3]; norm_num

/-! ## §4. Equal sides: every side-cosine is `2/3` on both arms. -/

theorem aArm_bArm_sameSides : SameSides aArm bArm := by
  intro i
  fin_cases i
  · show sDist (aArm 0) (aArm 1) = sDist (bArm 0) (bArm 1)
    show Real.arccos (sInner pQ qQ) = Real.arccos (sInner b0Q b1Q)
    have h1 : sInner pQ qQ = 2/3 := by
      show (⟪(pP:E3), (qP:E3)⟫ : ℝ) = 2/3; rw [pP, qP, innerE3]; norm_num
    have h2 : sInner b0Q b1Q = 2/3 := by
      show (⟪(b0P:E3), (b1P:E3)⟫ : ℝ) = 2/3; rw [b0P, b1P, innerE3]; norm_num
    rw [h1, h2]
  · show sDist (aArm 1) (aArm 2) = sDist (bArm 1) (bArm 2)
    show Real.arccos (sInner qQ pQ) = Real.arccos (sInner b1Q b2Q)
    have h1 : sInner qQ pQ = 2/3 := by
      show (⟪(qP:E3), (pP:E3)⟫ : ℝ) = 2/3; rw [qP, pP, innerE3]; norm_num
    have h2 : sInner b1Q b2Q = 2/3 := by
      show (⟪(b1P:E3), (b2P:E3)⟫ : ℝ) = 2/3; rw [b1P, b2P, innerE3]; norm_num
    rw [h1, h2]
  · show sDist (aArm 2) (aArm 3) = sDist (bArm 2) (bArm 3)
    show Real.arccos (sInner pQ qQ) = Real.arccos (sInner b2Q b3Q)
    have h1 : sInner pQ qQ = 2/3 := by
      show (⟪(pP:E3), (qP:E3)⟫ : ℝ) = 2/3; rw [pP, qP, innerE3]; norm_num
    have h2 : sInner b2Q b3Q = 2/3 := by
      show (⟪(b2P:E3), (b3P:E3)⟫ : ℝ) = 2/3; rw [b2P, b3P, innerE3]; norm_num
    rw [h1, h2]

/-! ## §5. `JointLe`: both interior joints of the zigzag are `0`. -/

/-- The zigzag joint `sphAngle u v u` is `0` for a genuine arc (`angle_self` on the tangent). -/
theorem sphAngle_self_zero {u v : S2} (h : ShortArc v u) : sphAngle u v u = 0 := by
  rw [sphAngle]
  exact InnerProductGeometry.angle_self (by rwa [tangentTo_ne_zero_iff])

theorem shortArc_qp : ShortArc qQ pQ := by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · have hh : (qQ:E3) 2 = (pQ:E3) 2 := by rw [h]
    rw [show (qQ:E3) 2 = 2/3 from rfl, show (pQ:E3) 2 = 1 from rfl] at hh
    norm_num at hh
  · have hh : (qQ:E3) 2 = (-(pQ:E3)) 2 := by rw [h]
    rw [show (qQ:E3) 2 = 2/3 from rfl, PiLp.neg_apply, show (pQ:E3) 2 = 1 from rfl] at hh
    norm_num at hh

theorem shortArc_pq : ShortArc pQ qQ := shortArc_qp.symm

theorem aArm_bArm_jointLe : JointLe aArm bArm := by
  intro i
  -- `Fin (3 - 1) = Fin 2`: the joints are at vertices 1 and 2, both zigzag-folded.
  have hival : i.val = 0 ∨ i.val = 1 := by have := i.isLt; omega
  have hA : jointAngle aArm i = 0 := by
    rw [jointAngle]
    rcases hival with h0 | h1
    · have e0 : (aArm ⟨i.val, by have := i.isLt; omega⟩) = pQ := by
        have : (⟨i.val, by have := i.isLt; omega⟩ : Fin 4) = ⟨0, by omega⟩ := by
          apply Fin.ext; simp only [Fin.val_mk, h0]
        rw [this]; rfl
      have e1 : (aArm ⟨i.val + 1, by have := i.isLt; omega⟩) = qQ := by
        have : (⟨i.val + 1, by have := i.isLt; omega⟩ : Fin 4) = ⟨1, by omega⟩ := by
          apply Fin.ext; simp only [Fin.val_mk, h0]
        rw [this]; rfl
      have e2 : (aArm ⟨i.val + 2, by have := i.isLt; omega⟩) = pQ := by
        have : (⟨i.val + 2, by have := i.isLt; omega⟩ : Fin 4) = ⟨2, by omega⟩ := by
          apply Fin.ext; simp only [Fin.val_mk, h0]
        rw [this]; rfl
      rw [e0, e1, e2]
      exact sphAngle_self_zero shortArc_qp
    · have e0 : (aArm ⟨i.val, by have := i.isLt; omega⟩) = qQ := by
        have : (⟨i.val, by have := i.isLt; omega⟩ : Fin 4) = ⟨1, by omega⟩ := by
          apply Fin.ext; simp only [Fin.val_mk, h1]
        rw [this]; rfl
      have e1 : (aArm ⟨i.val + 1, by have := i.isLt; omega⟩) = pQ := by
        have : (⟨i.val + 1, by have := i.isLt; omega⟩ : Fin 4) = ⟨2, by omega⟩ := by
          apply Fin.ext; simp only [Fin.val_mk, h1]
        rw [this]; rfl
      have e2 : (aArm ⟨i.val + 2, by have := i.isLt; omega⟩) = qQ := by
        have : (⟨i.val + 2, by have := i.isLt; omega⟩ : Fin 4) = ⟨3, by omega⟩ := by
          apply Fin.ext; simp only [Fin.val_mk, h1]
        rw [this]; rfl
      rw [e0, e1, e2]
      exact sphAngle_self_zero shortArc_pq
  rw [hA, jointAngle]
  exact sphAngle_nonneg _ _ _

/-! ## §6. The endpoint comparison fails: `arccos (14/15) < arccos (2/3)`. -/

theorem endpt_aArm : endpt aArm = Real.arccos (2/3) := by
  show sDist (aArm 0) (aArm (Fin.last 3)) = _
  show Real.arccos (sInner pQ qQ) = _
  have h1 : sInner pQ qQ = 2/3 := by
    show (⟪(pP:E3), (qP:E3)⟫ : ℝ) = 2/3; rw [pP, qP, innerE3]; norm_num
  rw [h1]

theorem endpt_bArm : endpt bArm = Real.arccos (14/15) := by
  show sDist (bArm 0) (bArm (Fin.last 3)) = _
  show Real.arccos (sInner b0Q b3Q) = _
  have h1 : sInner b0Q b3Q = 14/15 := by
    show (⟪(b0P:E3), (b3P:E3)⟫ : ℝ) = 14/15; rw [b0P, b3P, innerE3]; norm_num
  rw [h1]

theorem endpt_not_le : ¬ (endpt aArm ≤ endpt bArm) := by
  rw [endpt_aArm, endpt_bArm, not_le]
  exact Real.arccos_lt_arccos (by norm_num) (by norm_num) (by norm_num)

/-! ## §7. The three falsifications. -/

/-- **`Main 3` is FALSE.**  The zigzag pair satisfies every hypothesis of the induction statement,
but its endpoint comparison fails: `endpt A = arccos (2/3) > arccos (14/15) = endpt B`. -/
theorem main_three_false : ¬ Main 3 := by
  intro hM
  exact endpt_not_le
    (hM aArm bArm aArm_weakConvex bArm_strictConvex aArm_bArm_sameSides aArm_bArm_jointLe)

/-- **`SZOpeningStep` is FALSE** — it implies `Main 3` through the proven recursion `main_all`. -/
theorem szOpeningStep_false : ¬ SZOpeningStep :=
  fun h => main_three_false (main_all h 3 (by omega))

/-- The `Main`-IH input of `FoldedFlatCutTransport` at level `3` is dischargeable (the proven
`main_of_lt_two` / `main_two`). -/
theorem main_ih_below_three : ∀ m : ℕ, m < 3 → Main m := by
  intro m hm
  rcases Nat.lt_or_ge m 2 with h2 | h2
  · exact main_of_lt_two h2
  · have : m = 2 := by omega
    rw [this]; exact main_two

/-- **`FoldedFlatCutTransport` is FALSE.**  The zigzag pair satisfies its hypotheses at the cut
`(i, j) = (0, 2)`: the support `sOrient (A 0) (A 1) (A 2) = det3 p q p = 0` vanishes, and the diagonal
inequality is `sDist (A 0) (A 2) = sDist p p = 0 ≤ sDist (B 0) (B 2)`.  With the dischargeable IH the
transport would force `endpt A ≤ endpt B` — refuted. -/
theorem foldedFlatCutTransport_false : ¬ FoldedFlatCutTransport := by
  intro H
  have hsupp : sOrient (aArm ⟨0, by omega⟩) (aArm ⟨0 + 1, by omega⟩) (aArm ⟨2, by omega⟩) = 0 := by
    show det3 (aArm ⟨0, by omega⟩ : E3) (aArm ⟨0 + 1, by omega⟩ : E3) (aArm ⟨2, by omega⟩ : E3) = 0
    rw [aArm_eval 0 (by omega), aArm_eval (0 + 1) (by omega), aArm_eval 2 (by omega)]
    norm_num [pP, qP, det3E3]
  have hdiag : sDist (aArm ⟨0, by omega⟩) (aArm ⟨2, by omega⟩)
      ≤ sDist (bArm ⟨0, by omega⟩) (bArm ⟨2, by omega⟩) := by
    have hzero : sDist (aArm ⟨0, by omega⟩) (aArm ⟨2, by omega⟩) = 0 := by
      show Real.arccos (sInner pQ pQ) = 0
      rw [sInner_self, Real.arccos_one]
    rw [hzero]
    exact sDist_nonneg _ _
  exact endpt_not_le
    (H 3 (by omega) main_ih_below_three aArm bArm aArm_weakConvex bArm_strictConvex
      aArm_bArm_sameSides aArm_bArm_jointLe 0 2 (by omega) (by omega) (by omega) (by omega)
      hsupp hdiag)

#print axioms ProofsInTheBook.ZinanFFCT17.main_three_false
#print axioms ProofsInTheBook.ZinanFFCT17.szOpeningStep_false
#print axioms ProofsInTheBook.ZinanFFCT17.foldedFlatCutTransport_false

end ProofsInTheBook.ZinanFFCT17
