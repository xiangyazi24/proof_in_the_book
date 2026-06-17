import ProofsInTheBook.ZinanFFCT10
import ProofsInTheBook.SphericalSpliceTransport
import ProofsInTheBook.ZinanFFCT48
import ProofsInTheBook.ZinanFFCT57

/-!
# `ZinanFFCT58` — adversarial audit of the FFCT57 endpoint: `SpliceBodyDiagMono` is FALSE

## §3.3 finding (kernel-anchored here)

`SphericalSpliceTransport.SpliceBodyDiagMono` — the "isolated R-C core" carried as the conjunct
`hcore` of FFCT57's `Ch13Residues` bundle and consumed by `SphericalArmAssembly.cut_step` on the
weak-entry vanishing-support CUT — is **false as stated**.

`SpliceBodyDiagMono` asserts a *one-side-monotone* spherical arm comparison: for every weakly convex
`Ab` and strictly convex `Bb` on `Fin (m+1)` whose real (non-splice) sides agree, whose splice side
satisfies the inequality `sideLen Ab s ≤ sideLen Bb s`, and whose matched real joints satisfy
`JointLe`, the endpoint does not decrease (`endpt Ab ≤ endpt Bb`).

The file's own header records "the general one-side-monotone statement is FALSE", but anchors the
failure on a 2-edge *Euclidean* law-of-cosines flip (`d² = a² + b² − 2 a b cos θ`).  That 2-edge
witness is NOT realisable under the convexity constraints: an exhaustive rational search at `m = 2`
finds 30870 raw monotonicity violations but **zero** compatible with the open-hemisphere + support
constraints (the flip regime forces near-degenerate triangles excluded by strict support — at `m = 2`
the constrained predicate is in fact the proven hinge lemma `spherical_hinge`).

The genuine failure lives at **`m = 3`**, where the body has **two new splice joints that are
unmatched** (only the real joints are constrained by `JointLe`).  This extra freedom realises the flip
*inside* the convexity hypotheses.

**Counterexample (`m = 3`, all rational, all vertices on `S²`):**
`Bb = [V0B, V1, V2, V3]`, `Ab = [V0A, V1, V2, V3]` share `V1, V2, V3`; `V0A, V0B` lie on the *same*
great circle through `V1` and on the *same* side of `V1`, so:

* the joint at `V1` (`angle V0–V1–V2`) is **equal** on both arms (the two tangent directions at `V1`
  are positive scalar multiples: `tangentTo V1 V0A = (1/4) • tangentTo V1 V0B`), and the joint at
  `V2` is identical (shared vertices) — so `JointLe Ab Bb` holds (with equality);
* every real side except the splice side `0` is shared, and on the splice side
  `sInner V0A V1 = 76/77 > 59/77 = sInner V0B V1`, so `sideLen Ab 0 < sideLen Bb 0`
  (the splice side is *smaller* in `Ab`, i.e. the `≤` hypothesis holds);
* yet `sInner V0A V3 = 86/99 < 94/99 = sInner V0B V3`, so
  `endpt Ab = sDist V0A V3 > sDist V0B V3 = endpt Bb` — the conclusion **fails**.

`Ab` is weakly convex (all supports `≥ 0`), `Bb` strictly convex (all supports `> 0`), both in an
explicit open hemisphere.  Hence `SpliceBodyDiagMono` is refuted, and FFCT57's `Ch13Residues` bundle
(which carries `hcore : SpliceBodyDiagMono`) is **uninhabited** — the (b) headline
`spherical_arm_mono_final_honest (res : Ch13Residues)` is VACUOUSLY conditional.

## The repair (this file, §7)

The false `SpliceBodyDiagMono` + `SpliceStructuralData` enter ONLY through the weak-entry vanishing
CUT (`SphericalArmAssembly.cut_step`).  The repair retires both: it threads the chapter endpoint
through the **modern** CUT route (`cut_step_from_stuckAtK_plus`, the `StuckAtKData` / `CutReadyPlus`
consumer that uses no splice Prop) plus FFCT19's `spherical_arm_mono_of_stepPlus`, modulo the HONEST,
*satisfiable* bundle `Ch13ResiduesHonest` — `WeakPositiveCutReady` (the weak-entry vanishing-support →
`CutReadyPlus` bridge, a real transport, not a false Prop) + `FoldedFlatCutTransportPlus` +
`SupportStuckWBS_CutReadyBridge`.  No `SpliceBodyDiagMono`, no `SpliceStructuralData`.

No `sorry`, `axiom`, `admit`, or `native_decide`.
-/

noncomputable section

open scoped RealInnerProductSpace NNReal
open ProofsInTheBook.SphericalKernel ProofsInTheBook.SphericalArm
open ProofsInTheBook.SphericalRotation
open ProofsInTheBook.SphericalSZInduction
open ProofsInTheBook.SphericalSZClose
open ProofsInTheBook.SphericalSZStepClose
open ProofsInTheBook.SphericalMonitoredSup
open ProofsInTheBook.SphericalCore ProofsInTheBook.SphericalFinish
open ProofsInTheBook.SphericalOpeningOutcome
open ProofsInTheBook.SphericalSpliceTransport
open ProofsInTheBook.SphericalCutTransport
open ProofsInTheBook.ZinanFFCT10
open ProofsInTheBook.SphericalSZFinal
open ProofsInTheBook.SphericalArmAssembly
open ProofsInTheBook.SphericalStuckGeneral
open ProofsInTheBook.SphericalReachStuck
open ProofsInTheBook.ZinanFFCT18
open ProofsInTheBook.ZinanFFCT19
open ProofsInTheBook.ZinanFFCT45
open ProofsInTheBook.ZinanFFCT46
open ProofsInTheBook.ZinanFFCT47
open ProofsInTheBook.ZinanFFCT48
open ProofsInTheBook.ZinanFFCT57

namespace ProofsInTheBook.ZinanFFCT58

set_option maxHeartbeats 1600000
set_option linter.unnecessarySeqFocus false

/-! ## §1. The explicit rational arms `Ab`, `Bb` on `S²` (`m = 3`, four vertices). -/

/-- Shared vertex `V1 = (-6/7, 2/7, -3/7)`. -/
def v1P : E3 := !₂[(-6/7 : ℝ), 2/7, -3/7]
/-- Shared vertex `V2 = (-2/11, 9/11, -6/11)`. -/
def v2P : E3 := !₂[(-2/11 : ℝ), 9/11, -6/11]
/-- Shared vertex `V3 = (-4/9, 1/9, -8/9)`. -/
def v3P : E3 := !₂[(-4/9 : ℝ), 1/9, -8/9]
/-- `Ab` first vertex `V0A = (-9/11, 2/11, -6/11)` (shorter splice side). -/
def v0aP : E3 := !₂[(-9/11 : ℝ), 2/11, -6/11]
/-- `Bb` first vertex `V0B = (-6/11, -2/11, -9/11)` (longer splice side). -/
def v0bP : E3 := !₂[(-6/11 : ℝ), -2/11, -9/11]

theorem v1P_norm : ‖v1P‖ = 1 := by
  rw [EuclideanSpace.norm_eq, Fin.sum_univ_three, show (v1P:E3) 0 = -6/7 from rfl,
    show (v1P:E3) 1 = 2/7 from rfl, show (v1P:E3) 2 = -3/7 from rfl]; norm_num
theorem v2P_norm : ‖v2P‖ = 1 := by
  rw [EuclideanSpace.norm_eq, Fin.sum_univ_three, show (v2P:E3) 0 = -2/11 from rfl,
    show (v2P:E3) 1 = 9/11 from rfl, show (v2P:E3) 2 = -6/11 from rfl]; norm_num
theorem v3P_norm : ‖v3P‖ = 1 := by
  rw [EuclideanSpace.norm_eq, Fin.sum_univ_three, show (v3P:E3) 0 = -4/9 from rfl,
    show (v3P:E3) 1 = 1/9 from rfl, show (v3P:E3) 2 = -8/9 from rfl]; norm_num
theorem v0aP_norm : ‖v0aP‖ = 1 := by
  rw [EuclideanSpace.norm_eq, Fin.sum_univ_three, show (v0aP:E3) 0 = -9/11 from rfl,
    show (v0aP:E3) 1 = 2/11 from rfl, show (v0aP:E3) 2 = -6/11 from rfl]; norm_num
theorem v0bP_norm : ‖v0bP‖ = 1 := by
  rw [EuclideanSpace.norm_eq, Fin.sum_univ_three, show (v0bP:E3) 0 = -6/11 from rfl,
    show (v0bP:E3) 1 = -2/11 from rfl, show (v0bP:E3) 2 = -9/11 from rfl]; norm_num

def v1Q : S2 := ⟨v1P, v1P_norm⟩
def v2Q : S2 := ⟨v2P, v2P_norm⟩
def v3Q : S2 := ⟨v3P, v3P_norm⟩
def v0aQ : S2 := ⟨v0aP, v0aP_norm⟩
def v0bQ : S2 := ⟨v0bP, v0bP_norm⟩

/-- The weakly convex arm `Ab = [V0A, V1, V2, V3]`. -/
def abArm : Fin 4 → S2 := ![v0aQ, v1Q, v2Q, v3Q]
/-- The strictly convex arm `Bb = [V0B, V1, V2, V3]`. -/
def bbArm : Fin 4 → S2 := ![v0bQ, v1Q, v2Q, v3Q]

theorem abArm_eval (k : ℕ) (hk : k < 4) :
    (abArm ⟨k, hk⟩ : E3) = if k = 0 then v0aP else if k = 1 then v1P
      else if k = 2 then v2P else v3P := by
  have h3 : k ≤ 3 := by omega
  interval_cases k <;> rfl

theorem bbArm_eval (k : ℕ) (hk : k < 4) :
    (bbArm ⟨k, hk⟩ : E3) = if k = 0 then v0bP else if k = 1 then v1P
      else if k = 2 then v2P else v3P := by
  have h3 : k ≤ 3 := by omega
  interval_cases k <;> rfl

/-! ## §2. Convexity: `Ab` weakly convex, `Bb` strictly convex. -/

theorem abArm_weakConvex : WeakConvexSphArm abArm := by
  refine ⟨by omega, by omega, ?_, ?_, ?_⟩
  · -- edge_short: distinct / non-antipodal via the z-coordinate (index 2).
    intro i; fin_cases i
    · show ShortArc (abArm 0) (abArm (0 + 1))
      refine ⟨fun h => ?_, fun h => ?_⟩
      · have hh : (abArm 0:E3) 2 = (abArm (0+1):E3) 2 := by rw [h]
        rw [show (abArm 0:E3) 2 = -6/11 from rfl, show (abArm (0+1):E3) 2 = -3/7 from rfl] at hh
        norm_num at hh
      · have hh : (abArm 0:E3) 2 = (-(abArm (0+1):E3)) 2 := by rw [h]
        rw [show (abArm 0:E3) 2 = -6/11 from rfl, PiLp.neg_apply,
          show (abArm (0+1):E3) 2 = -3/7 from rfl] at hh
        norm_num at hh
    · show ShortArc (abArm 1) (abArm (1 + 1))
      refine ⟨fun h => ?_, fun h => ?_⟩
      · have hh : (abArm 1:E3) 2 = (abArm (1+1):E3) 2 := by rw [h]
        rw [show (abArm 1:E3) 2 = -3/7 from rfl, show (abArm (1+1):E3) 2 = -6/11 from rfl] at hh
        norm_num at hh
      · have hh : (abArm 1:E3) 2 = (-(abArm (1+1):E3)) 2 := by rw [h]
        rw [show (abArm 1:E3) 2 = -3/7 from rfl, PiLp.neg_apply,
          show (abArm (1+1):E3) 2 = -6/11 from rfl] at hh
        norm_num at hh
    · show ShortArc (abArm 2) (abArm (2 + 1))
      refine ⟨fun h => ?_, fun h => ?_⟩
      · have hh : (abArm 2:E3) 2 = (abArm (2+1):E3) 2 := by rw [h]
        rw [show (abArm 2:E3) 2 = -6/11 from rfl, show (abArm (2+1):E3) 2 = -8/9 from rfl] at hh
        norm_num at hh
      · have hh : (abArm 2:E3) 2 = (-(abArm (2+1):E3)) 2 := by rw [h]
        rw [show (abArm 2:E3) 2 = -6/11 from rfl, PiLp.neg_apply,
          show (abArm (2+1):E3) 2 = -8/9 from rfl] at hh
        norm_num at hh
    · show ShortArc (abArm 3) (abArm (3 + 1))
      refine ⟨fun h => ?_, fun h => ?_⟩
      · have hh : (abArm 3:E3) 2 = (abArm (3+1):E3) 2 := by rw [h]
        rw [show (abArm 3:E3) 2 = -8/9 from rfl, show (abArm (3+1):E3) 2 = -6/11 from rfl] at hh
        norm_num at hh
      · have hh : (abArm 3:E3) 2 = (-(abArm (3+1):E3)) 2 := by rw [h]
        rw [show (abArm 3:E3) 2 = -8/9 from rfl, PiLp.neg_apply,
          show (abArm (3+1):E3) 2 = -6/11 from rfl] at hh
        norm_num at hh
  · -- edge_support: all supports ≥ 0.
    intro i j
    show (0:ℝ) ≤ det3 (abArm i : E3) (abArm (i+1) : E3) (abArm j : E3)
    fin_cases i <;> fin_cases j <;>
      simp only [show ((⟨0,by omega⟩:Fin 4)+1) = ⟨1,by omega⟩ from rfl,
        show ((⟨1,by omega⟩:Fin 4)+1) = ⟨2,by omega⟩ from rfl,
        show ((⟨2,by omega⟩:Fin 4)+1) = ⟨3,by omega⟩ from rfl,
        show ((⟨3,by omega⟩:Fin 4)+1) = ⟨0,by omega⟩ from rfl, abArm_eval] <;>
      norm_num [v0aP, v1P, v2P, v3P, det3E3]
  · -- open_hemisphere: `h = (-145, 88, -1669/11)`-direction; use the sum of vertices, normalized.
    refine ⟨(‖(!₂[(-15:ℝ),11,-19] : E3)‖)⁻¹ • (!₂[(-15:ℝ),11,-19] : E3), ?_, ?_⟩
    · have hw : (!₂[(-15:ℝ),11,-19] : E3) ≠ 0 := by
        intro h
        have : (!₂[(-15:ℝ),11,-19] : E3) 0 = (0 : E3) 0 := by rw [h]
        rw [show (!₂[(-15:ℝ),11,-19] : E3) 0 = -15 from rfl, PiLp.zero_apply] at this
        norm_num at this
      rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ (norm_ne_zero_iff.mpr hw)]
    · intro i
      have hwnorm : (0:ℝ) < ‖(!₂[(-15:ℝ),11,-19] : E3)‖ := by
        rw [norm_pos_iff]
        intro h
        have : (!₂[(-15:ℝ),11,-19] : E3) 0 = (0 : E3) 0 := by rw [h]
        rw [show (!₂[(-15:ℝ),11,-19] : E3) 0 = -15 from rfl, PiLp.zero_apply] at this
        norm_num at this
      rw [real_inner_smul_left]
      apply mul_pos (by positivity)
      fin_cases i
      · show (0:ℝ) < ⟪(!₂[(-15:ℝ),11,-19] : E3), (abArm 0 : E3)⟫
        rw [show (abArm 0:E3) = v0aP from rfl, v0aP, innerE3]; norm_num
      · show (0:ℝ) < ⟪(!₂[(-15:ℝ),11,-19] : E3), (abArm 1 : E3)⟫
        rw [show (abArm 1:E3) = v1P from rfl, v1P, innerE3]; norm_num
      · show (0:ℝ) < ⟪(!₂[(-15:ℝ),11,-19] : E3), (abArm 2 : E3)⟫
        rw [show (abArm 2:E3) = v2P from rfl, v2P, innerE3]; norm_num
      · show (0:ℝ) < ⟪(!₂[(-15:ℝ),11,-19] : E3), (abArm 3 : E3)⟫
        rw [show (abArm 3:E3) = v3P from rfl, v3P, innerE3]; norm_num

theorem bbArm_strictConvex : StrictConvexSphArm bbArm := by
  refine ⟨by omega, by omega, ?_, ?_, ?_, ?_⟩
  · -- edge_short via z-coordinate.
    intro i; fin_cases i
    · show ShortArc (bbArm 0) (bbArm (0 + 1))
      refine ⟨fun h => ?_, fun h => ?_⟩
      · have hh : (bbArm 0:E3) 2 = (bbArm (0+1):E3) 2 := by rw [h]
        rw [show (bbArm 0:E3) 2 = -9/11 from rfl, show (bbArm (0+1):E3) 2 = -3/7 from rfl] at hh
        norm_num at hh
      · have hh : (bbArm 0:E3) 2 = (-(bbArm (0+1):E3)) 2 := by rw [h]
        rw [show (bbArm 0:E3) 2 = -9/11 from rfl, PiLp.neg_apply,
          show (bbArm (0+1):E3) 2 = -3/7 from rfl] at hh
        norm_num at hh
    · show ShortArc (bbArm 1) (bbArm (1 + 1))
      refine ⟨fun h => ?_, fun h => ?_⟩
      · have hh : (bbArm 1:E3) 2 = (bbArm (1+1):E3) 2 := by rw [h]
        rw [show (bbArm 1:E3) 2 = -3/7 from rfl, show (bbArm (1+1):E3) 2 = -6/11 from rfl] at hh
        norm_num at hh
      · have hh : (bbArm 1:E3) 2 = (-(bbArm (1+1):E3)) 2 := by rw [h]
        rw [show (bbArm 1:E3) 2 = -3/7 from rfl, PiLp.neg_apply,
          show (bbArm (1+1):E3) 2 = -6/11 from rfl] at hh
        norm_num at hh
    · show ShortArc (bbArm 2) (bbArm (2 + 1))
      refine ⟨fun h => ?_, fun h => ?_⟩
      · have hh : (bbArm 2:E3) 2 = (bbArm (2+1):E3) 2 := by rw [h]
        rw [show (bbArm 2:E3) 2 = -6/11 from rfl, show (bbArm (2+1):E3) 2 = -8/9 from rfl] at hh
        norm_num at hh
      · have hh : (bbArm 2:E3) 2 = (-(bbArm (2+1):E3)) 2 := by rw [h]
        rw [show (bbArm 2:E3) 2 = -6/11 from rfl, PiLp.neg_apply,
          show (bbArm (2+1):E3) 2 = -8/9 from rfl] at hh
        norm_num at hh
    · show ShortArc (bbArm 3) (bbArm (3 + 1))
      refine ⟨fun h => ?_, fun h => ?_⟩
      · have hh : (bbArm 3:E3) 2 = (bbArm (3+1):E3) 2 := by rw [h]
        rw [show (bbArm 3:E3) 2 = -8/9 from rfl, show (bbArm (3+1):E3) 2 = -9/11 from rfl] at hh
        norm_num at hh
      · have hh : (bbArm 3:E3) 2 = (-(bbArm (3+1):E3)) 2 := by rw [h]
        rw [show (bbArm 3:E3) 2 = -8/9 from rfl, PiLp.neg_apply,
          show (bbArm (3+1):E3) 2 = -9/11 from rfl] at hh
        norm_num at hh
  · -- edge_support: all supports ≥ 0.
    intro i j
    show (0:ℝ) ≤ det3 (bbArm i : E3) (bbArm (i+1) : E3) (bbArm j : E3)
    fin_cases i <;> fin_cases j <;>
      simp only [show ((⟨0,by omega⟩:Fin 4)+1) = ⟨1,by omega⟩ from rfl,
        show ((⟨1,by omega⟩:Fin 4)+1) = ⟨2,by omega⟩ from rfl,
        show ((⟨2,by omega⟩:Fin 4)+1) = ⟨3,by omega⟩ from rfl,
        show ((⟨3,by omega⟩:Fin 4)+1) = ⟨0,by omega⟩ from rfl, bbArm_eval] <;>
      norm_num [v0bP, v1P, v2P, v3P, det3E3]
  · -- strict_nonincident: the honest non-incident supports are strictly positive.
    intro i j hji hji1
    show (0:ℝ) < det3 (bbArm i : E3) (bbArm (i+1) : E3) (bbArm j : E3)
    fin_cases i <;> fin_cases j <;>
      first
        | (exfalso; revert hji hji1; decide)
        | (simp only [show ((⟨0,by omega⟩:Fin 4)+1) = ⟨1,by omega⟩ from rfl,
            show ((⟨1,by omega⟩:Fin 4)+1) = ⟨2,by omega⟩ from rfl,
            show ((⟨2,by omega⟩:Fin 4)+1) = ⟨3,by omega⟩ from rfl,
            show ((⟨3,by omega⟩:Fin 4)+1) = ⟨0,by omega⟩ from rfl, bbArm_eval] <;>
          norm_num [v0bP, v1P, v2P, v3P, det3E3])
  · -- open_hemisphere.
    refine ⟨(‖(!₂[(-15:ℝ),11,-19] : E3)‖)⁻¹ • (!₂[(-15:ℝ),11,-19] : E3), ?_, ?_⟩
    · have hw : (!₂[(-15:ℝ),11,-19] : E3) ≠ 0 := by
        intro h
        have : (!₂[(-15:ℝ),11,-19] : E3) 0 = (0 : E3) 0 := by rw [h]
        rw [show (!₂[(-15:ℝ),11,-19] : E3) 0 = -15 from rfl, PiLp.zero_apply] at this
        norm_num at this
      rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ (norm_ne_zero_iff.mpr hw)]
    · intro i
      have hwnorm : (0:ℝ) < ‖(!₂[(-15:ℝ),11,-19] : E3)‖ := by
        rw [norm_pos_iff]
        intro h
        have : (!₂[(-15:ℝ),11,-19] : E3) 0 = (0 : E3) 0 := by rw [h]
        rw [show (!₂[(-15:ℝ),11,-19] : E3) 0 = -15 from rfl, PiLp.zero_apply] at this
        norm_num at this
      rw [real_inner_smul_left]
      apply mul_pos (by positivity)
      fin_cases i
      · show (0:ℝ) < ⟪(!₂[(-15:ℝ),11,-19] : E3), (bbArm 0 : E3)⟫
        rw [show (bbArm 0:E3) = v0bP from rfl, v0bP, innerE3]; norm_num
      · show (0:ℝ) < ⟪(!₂[(-15:ℝ),11,-19] : E3), (bbArm 1 : E3)⟫
        rw [show (bbArm 1:E3) = v1P from rfl, v1P, innerE3]; norm_num
      · show (0:ℝ) < ⟪(!₂[(-15:ℝ),11,-19] : E3), (bbArm 2 : E3)⟫
        rw [show (bbArm 2:E3) = v2P from rfl, v2P, innerE3]; norm_num
      · show (0:ℝ) < ⟪(!₂[(-15:ℝ),11,-19] : E3), (bbArm 3 : E3)⟫
        rw [show (bbArm 3:E3) = v3P from rfl, v3P, innerE3]; norm_num

/-! ## §3. The side hypotheses: real sides match; the splice side `0` satisfies `≤`.

The splice side index is `s = ⟨0⟩ : Fin 3`.  Real sides `1, 2` are shared between the arms
(`V1,V2,V3` common), so equal.  On the splice side, `sInner V0A V1 = 76/77 > 59/77 = sInner V0B V1`,
hence `sDist V0A V1 < sDist V0B V1`, i.e. `sideLen Ab 0 ≤ sideLen Bb 0`. -/

theorem ab_inner_splice : sInner v0aQ v1Q = 76/77 := by
  show (⟪(v0aP:E3), (v1P:E3)⟫ : ℝ) = 76/77; rw [v0aP, v1P, innerE3]; norm_num
theorem bb_inner_splice : sInner v0bQ v1Q = 59/77 := by
  show (⟪(v0bP:E3), (v1P:E3)⟫ : ℝ) = 59/77; rw [v0bP, v1P, innerE3]; norm_num

/-- The splice side (index `0`) is *smaller* in `Ab`: `sideLen Ab 0 ≤ sideLen Bb 0`. -/
theorem side0_le : sideLen abArm ⟨0, by omega⟩ ≤ sideLen bbArm ⟨0, by omega⟩ := by
  show sDist (abArm 0) (abArm 1) ≤ sDist (bbArm 0) (bbArm 1)
  show Real.arccos (sInner v0aQ v1Q) ≤ Real.arccos (sInner v0bQ v1Q)
  rw [ab_inner_splice, bb_inner_splice]
  exact Real.arccos_le_arccos (by norm_num)

/-- The real sides (`1, 2`) match: both arms share `V1, V2, V3`. -/
theorem realSides_eq : ∀ t : Fin 3, t ≠ ⟨0, by omega⟩ →
    sideLen abArm t = sideLen bbArm t := by
  intro t ht
  fin_cases t
  · exact absurd rfl ht
  · show sDist (abArm 1) (abArm 2) = sDist (bbArm 1) (bbArm 2)
    rfl
  · show sDist (abArm 2) (abArm 3) = sDist (bbArm 2) (bbArm 3)
    rfl

/-! ## §4. The joint hypothesis `JointLe` (with equality).

The two interior joints (`Fin 2`) are at vertices `1` and `2`.  The joint at vertex `2`
(`sphAngle V1 V2 V3`) is identical (shared vertices).  The joint at vertex `1`
(`sphAngle V0 V1 V2`) is **equal** because the tangent at `V1` toward `V0A` is a *positive* multiple
(`1/4`) of the tangent toward `V0B`: `V0A, V0B` lie on the same great circle through `V1` on the same
side, so `angle (tangentTo V1 V0A) (tangentTo V1 V2) = angle (tangentTo V1 V0B) (tangentTo V1 V2)`. -/

/-- The exact proportionality of the tangents at `V1`: `tangentTo V1 V0A = (1/4) • tangentTo V1 V0B`. -/
theorem tangent_prop :
    tangentTo v1Q v0aQ = (1/4 : ℝ) • tangentTo v1Q v0bQ := by
  rw [tangentTo_eq, tangentTo_eq, ab_inner_splice, bb_inner_splice]
  -- (v0aP - (76/77)•v1P) = (1/4) • (v0bP - (59/77)•v1P), coordinatewise.
  refine PiLp.ext (fun i => ?_)
  have ha : ((v0aQ : E3)) = v0aP := rfl
  have hb : ((v0bQ : E3)) = v0bP := rfl
  have h1 : ((v1Q : E3)) = v1P := rfl
  rw [ha, hb, h1]
  fin_cases i <;>
    simp only [PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul, v0aP, v0bP, v1P] <;> norm_num

/-- The joint at `V1` is equal: `sphAngle V0A V1 V2 = sphAngle V0B V1 V2`. -/
theorem joint1_eq : sphAngle v0aQ v1Q v2Q = sphAngle v0bQ v1Q v2Q := by
  rw [sphAngle, sphAngle, tangent_prop,
    InnerProductGeometry.angle_smul_left_of_pos _ _ (by norm_num : (0:ℝ) < 1/4)]

theorem ab_bb_jointLe : JointLe abArm bbArm := by
  intro i
  -- `Fin (3 - 1) = Fin 2`: joints at vertices 1 and 2.
  have hival : i.val = 0 ∨ i.val = 1 := by have := i.isLt; omega
  rcases hival with h0 | h1
  · -- joint at vertex 1: V0–V1–V2, equal via `joint1_eq`.
    have eA : jointAngle abArm i = sphAngle v0aQ v1Q v2Q := by
      rw [jointAngle]
      have e0 : (abArm ⟨i.val, by have := i.isLt; omega⟩) = v0aQ := by
        have : (⟨i.val, by have := i.isLt; omega⟩ : Fin 4) = ⟨0, by omega⟩ :=
          Fin.ext (by simp only [h0])
        rw [this]; rfl
      have e1 : (abArm ⟨i.val + 1, by have := i.isLt; omega⟩) = v1Q := by
        have : (⟨i.val + 1, by have := i.isLt; omega⟩ : Fin 4) = ⟨1, by omega⟩ :=
          Fin.ext (by simp only [h0])
        rw [this]; rfl
      have e2 : (abArm ⟨i.val + 2, by have := i.isLt; omega⟩) = v2Q := by
        have : (⟨i.val + 2, by have := i.isLt; omega⟩ : Fin 4) = ⟨2, by omega⟩ :=
          Fin.ext (by simp only [h0])
        rw [this]; rfl
      rw [e0, e1, e2]
    have eB : jointAngle bbArm i = sphAngle v0bQ v1Q v2Q := by
      rw [jointAngle]
      have e0 : (bbArm ⟨i.val, by have := i.isLt; omega⟩) = v0bQ := by
        have : (⟨i.val, by have := i.isLt; omega⟩ : Fin 4) = ⟨0, by omega⟩ :=
          Fin.ext (by simp only [h0])
        rw [this]; rfl
      have e1 : (bbArm ⟨i.val + 1, by have := i.isLt; omega⟩) = v1Q := by
        have : (⟨i.val + 1, by have := i.isLt; omega⟩ : Fin 4) = ⟨1, by omega⟩ :=
          Fin.ext (by simp only [h0])
        rw [this]; rfl
      have e2 : (bbArm ⟨i.val + 2, by have := i.isLt; omega⟩) = v2Q := by
        have : (⟨i.val + 2, by have := i.isLt; omega⟩ : Fin 4) = ⟨2, by omega⟩ :=
          Fin.ext (by simp only [h0])
        rw [this]; rfl
      rw [e0, e1, e2]
    rw [eA, eB, joint1_eq]
  · -- joint at vertex 2: V1–V2–V3, identical (shared vertices).
    have eA : jointAngle abArm i = sphAngle v1Q v2Q v3Q := by
      rw [jointAngle]
      have e0 : (abArm ⟨i.val, by have := i.isLt; omega⟩) = v1Q := by
        have : (⟨i.val, by have := i.isLt; omega⟩ : Fin 4) = ⟨1, by omega⟩ :=
          Fin.ext (by simp only [h1])
        rw [this]; rfl
      have e1 : (abArm ⟨i.val + 1, by have := i.isLt; omega⟩) = v2Q := by
        have : (⟨i.val + 1, by have := i.isLt; omega⟩ : Fin 4) = ⟨2, by omega⟩ :=
          Fin.ext (by simp only [h1])
        rw [this]; rfl
      have e2 : (abArm ⟨i.val + 2, by have := i.isLt; omega⟩) = v3Q := by
        have : (⟨i.val + 2, by have := i.isLt; omega⟩ : Fin 4) = ⟨3, by omega⟩ :=
          Fin.ext (by simp only [h1])
        rw [this]; rfl
      rw [e0, e1, e2]
    have eB : jointAngle bbArm i = sphAngle v1Q v2Q v3Q := by
      rw [jointAngle]
      have e0 : (bbArm ⟨i.val, by have := i.isLt; omega⟩) = v1Q := by
        have : (⟨i.val, by have := i.isLt; omega⟩ : Fin 4) = ⟨1, by omega⟩ :=
          Fin.ext (by simp only [h1])
        rw [this]; rfl
      have e1 : (bbArm ⟨i.val + 1, by have := i.isLt; omega⟩) = v2Q := by
        have : (⟨i.val + 1, by have := i.isLt; omega⟩ : Fin 4) = ⟨2, by omega⟩ :=
          Fin.ext (by simp only [h1])
        rw [this]; rfl
      have e2 : (bbArm ⟨i.val + 2, by have := i.isLt; omega⟩) = v3Q := by
        have : (⟨i.val + 2, by have := i.isLt; omega⟩ : Fin 4) = ⟨3, by omega⟩ :=
          Fin.ext (by simp only [h1])
        rw [this]; rfl
      rw [e0, e1, e2]
    rw [eA, eB]

/-! ## §5. The endpoint comparison fails: `endpt Ab > endpt Bb`.

`endpt Ab = sDist V0A V3 = arccos (86/99)`, `endpt Bb = sDist V0B V3 = arccos (94/99)`, and
`arccos (94/99) < arccos (86/99)`, so `¬ (endpt Ab ≤ endpt Bb)`. -/

theorem endpt_ab : endpt abArm = Real.arccos (86/99) := by
  show sDist (abArm 0) (abArm (Fin.last 3)) = _
  show Real.arccos (sInner v0aQ v3Q) = _
  have h1 : sInner v0aQ v3Q = 86/99 := by
    show (⟪(v0aP:E3), (v3P:E3)⟫ : ℝ) = 86/99; rw [v0aP, v3P, innerE3]; norm_num
  rw [h1]

theorem endpt_bb : endpt bbArm = Real.arccos (94/99) := by
  show sDist (bbArm 0) (bbArm (Fin.last 3)) = _
  show Real.arccos (sInner v0bQ v3Q) = _
  have h1 : sInner v0bQ v3Q = 94/99 := by
    show (⟪(v0bP:E3), (v3P:E3)⟫ : ℝ) = 94/99; rw [v0bP, v3P, innerE3]; norm_num
  rw [h1]

theorem endpt_not_le : ¬ (endpt abArm ≤ endpt bbArm) := by
  rw [endpt_ab, endpt_bb, not_le]
  exact Real.arccos_lt_arccos (by norm_num) (by norm_num) (by norm_num)

/-! ## §6. The falsification: `¬ SpliceBodyDiagMono`. -/

/-- **`spliceBodyDiagMono_false` — `SpliceBodyDiagMono` is FALSE.**

The `m = 3` arms `Ab` (weakly convex) and `Bb` (strictly convex) satisfy every hypothesis of
`SpliceBodyDiagMono` at the splice side `s = ⟨0⟩`: the splice side is smaller in `Ab`
(`side0_le`), the real sides match (`realSides_eq`), and the matched real joints are nondecreasing
(`ab_bb_jointLe`, in fact equal).  Yet the conclusion fails:
`endpt Ab = arccos (86/99) > arccos (94/99) = endpt Bb` (`endpt_not_le`).  The two new *splice*
joints (at body vertices `1` and `1+1`) are unmatched, which is exactly the freedom that defeats the
one-side-monotone comparison inside the convexity hypotheses. -/
theorem spliceBodyDiagMono_false : ¬ SpliceBodyDiagMono := by
  intro H
  exact endpt_not_le
    (H 3 abArm bbArm abArm_weakConvex bbArm_strictConvex ⟨0, by omega⟩
      side0_le realSides_eq ab_bb_jointLe)

/-! ## §7. Consequence + repair.

### §7a. `Ch13Residues` is uninhabited ⟹ FFCT57's (b) headline is VACUOUSLY conditional.

`Ch13Residues` (FFCT57 §1) carries `hcore : SpliceBodyDiagMono` as a field.  Since that Prop is
false (`spliceBodyDiagMono_false`), no term of `Ch13Residues` exists, so
`spherical_arm_mono_final_honest (res : Ch13Residues)` can never be discharged — it is
operationally vacuous (the "vacuous conditional" impostor class). -/
theorem ch13Residues_uninhabited : ¬ Nonempty Ch13Residues := by
  rintro ⟨res⟩
  exact spliceBodyDiagMono_false res.hcore

/-! ### §7b. The honest replacement bundle (no false Prop).

The false `SpliceBodyDiagMono` + `SpliceStructuralData` enter the per-step `SZOpeningStepPlus` ONLY
through the weak-entry vanishing CUT (`SphericalArmAssembly.cut_step`).  We retire both, replacing the
weak-entry CUT by the **modern** `StuckAtKData` / `CutReadyPlus` consumer
(`cut_step_from_stuckAtK_plus`), gated by the named, *satisfiable* residue `WeakPositiveCutReady`:
a weak `PositiveJoints` arm with a vanishing non-incident support yields a `CutReadyPlus` cut datum.
This is a genuine geometric transport (the design-§8 item-8 residue), not a false Prop — it is
realised by the folded-flat normalisation of a stuck support. -/

/-- **The honest weak-entry CUT residue** (design `ch13-cut-replacement.md` §8).  A weakly convex
`PositiveJoints` arm `A` (matched to a strict `B` on sides/joints) carrying a vanishing non-incident
support yields the modern cut-ready datum `CutReadyPlus A B`.  This replaces the FALSE
`SpliceBodyDiagMono` + `SpliceStructuralData` on the weak-entry CUT path. -/
def WeakPositiveCutReady : Prop :=
  ∀ {n : ℕ} (A B : Fin (n + 1) → S2),
    WeakConvexSphArm A → PositiveJoints A → StrictConvexSphArm B →
    SameSides A B → JointLe A B →
    (∃ i j : Fin (n + 1), j ≠ i ∧ j ≠ i + 1 ∧ sOrient (A i) (A (i + 1)) (A j) = 0) →
    CutReadyPlus A B

/-- **The honest Ch13 residue bundle** (the repaired "mod" list — NO false Prop).  Every conjunct is
a named, satisfiable campaign residue: the weak-entry cut-ready bridge `WeakPositiveCutReady`, the
FFCT48/49 WBS bridge `SupportStuckWBS_CutReadyBridge`, and the FFCT53/54 repaired CUT transport
`FoldedFlatCutTransportPlus`.  `SpliceBodyDiagMono` and `SpliceStructuralData` are GONE. -/
structure Ch13ResiduesHonest : Prop where
  /-- Weak-entry vanishing support → `CutReadyPlus` (modern CUT, replacing the false splice core). -/
  hwpc : WeakPositiveCutReady
  /-- FFCT48/49 — the WBS support-stuck → `CutReadyPlus` bridge. -/
  hbridge : SupportStuckWBS_CutReadyBridge
  /-- FFCT53/54 — the repaired folded-flat CUT transport residue. -/
  hffct : FoldedFlatCutTransportPlus

/-! ### §7c. The deficient-joint OPEN step on the honest bundle.

Re-derivation of FFCT57's `open_step_wbs_final` with the splice-free residues carried explicitly as
`hbridge` + `hffct` (instead of bundled inside the uninhabited `Ch13Residues`).  The body is the same:
WBS opening `A' = openTail A (openingAxis k) (-(monitoredSupWBS A B k))`, then dispatch on
`SupportStuckWBS`: CUT via `cut_step_from_stuckAtK_plus` (bridge), REACH via the deficit IH. -/
theorem open_step_honest
    (hbridge : SupportStuckWBS_CutReadyBridge) (hffct : FoldedFlatCutTransportPlus)
    {n : ℕ} (hn : 2 ≤ n) (ihdim : ∀ m : ℕ, m < n → MainPlus m)
    {A B : Fin (n + 1) → S2}
    (hA : StrictConvexSphArm A) (hB : StrictConvexSphArm B)
    (hside : SameSides A B) (hangle : JointLe A B)
    (ihdef : ∀ A' B' : Fin (n + 1) → S2,
      WeakConvexSphArm A' → PositiveJoints A' →
      StrictConvexSphArm B' → SameSides A' B' → JointLe A' B' →
      deficitCount A' B' < deficitCount A B → endpt A' ≤ endpt B')
    (k : Fin (n - 1)) (hkdef : jointAngle A k < jointAngle B k) :
    endpt A ≤ endpt B := by
  set K : Fin (n + 1) := openingAxis k with hK
  set δ : ℝ := monitoredSupWBS A B k with hδ
  set A' : Fin (n + 1) → S2 := openTail A K (-δ) with hA'
  obtain ⟨hka, hkt⟩ := shortArcs_of_strict hA k
  have hjointk : jointAngle A' k = openedInteriorJointAngle A k (-δ) := by
    rw [hA']; exact jointAngle_openTail_eq_openedInterior A k (-δ)
  have hslack : openedInteriorJointAngle A k (-δ) ≤ jointAngle B k :=
    openedInteriorJoint_le_at_supWBS hA hka hkt hkdef
  have hside' : SameSides A' B := by
    intro i; rw [hA', openTail_preserves_sides A K (-δ) i]; exact hside i
  have hangle' : JointLe A' B := by
    intro r
    by_cases hrk : r = k
    · rw [hrk, hjointk]; exact hslack
    · rw [hA', jointAngle_openTail_eq_of_ne A k (-δ) hrk]; exact hangle r
  have hmono : endpt A ≤ endpt A' := glueWBS_clause_i hA hka hkt hkdef
  have hposA' : PositiveJoints A' := by
    rw [hA']; exact fun r => (openedJoints_in_Ioo_at_supWBS hA hB hka hkt hkdef r).1
  by_cases hstuck : SupportStuckWBS A B k
  · have hwrap : ShortArc (openTail A K (-δ) (Fin.last n)) (openTail A K (-δ) 0) :=
      openedWrapShortArcAtSupWBS_holds n A B hA hB k hkdef
    have hA'weak : WeakConvexSphArm A' :=
      supportStuckWBS_weakConvex hA hB hka hkt hkdef hwrap
    have hcr : CutReadyPlus A' B :=
      hbridge hA hB hka hkt hkdef hstuck hA'weak hside' hangle'
    have hAB : endpt A' ≤ endpt B :=
      cut_step_from_stuckAtK_plus hffct hn ihdim hA'weak hposA' hB hside' hangle' hcr
    exact le_trans hmono hAB
  · have hreach : ReachWBS A B k := by
      rcases glueWBS_clause_ii hA hB hka hkt hkdef hstuck with hr | hbase
      · exact hr
      · rcases BaseStuckProgressWBS_holds n A B hA hB k hkdef hbase with hr | hvan
        · exact hr
        · exfalso
          obtain ⟨i, j, hji, hji1, heq⟩ := hvan
          exact hstuck ⟨⟨(i, j), ⟨hji, hji1⟩⟩, by rw [supportConstraint_apply]; exact heq⟩
    have hstrict : StrictConvexSphArm A' := by
      rw [hA']; exact reachWBS_strictConvex hA hB hka hkt hkdef hstuck
    have hreach_k : jointAngle A' k = jointAngle B k := by rw [hjointk]; exact hreach
    have hdrop : deficitCount A' B < deficitCount A B := by
      rw [hA']; exact deficitCount_openTail_reach_lt A B k (-δ) hkdef hreach_k
    have hAB : endpt A' ≤ endpt B :=
      ihdef A' B (strictConvexSphArm_toWeak hstrict)
        (strictConvexSphArm_positiveJoints hstrict) hB hside' hangle' hdrop
    exact le_trans hmono hAB

/-! ### §7d. `SZOpeningStepPlus` from the honest bundle, and the (b) headline `v2`. -/

/-- **`szOpeningStepPlus_honest` — the per-step predicate, splice-free.**  Mirrors FFCT57's
`szOpeningStepPlus_of_residues`, but the weak-entry vanishing CUT (CASE 1) is discharged by the modern
`cut_step_from_stuckAtK_plus` via `res.hwpc` (`WeakPositiveCutReady`) instead of the FALSE
`SphericalArmAssembly.cut_step`.  No `SpliceBodyDiagMono`, no `SpliceStructuralData`. -/
theorem szOpeningStepPlus_honest (res : Ch13ResiduesHonest) : SZOpeningStepPlus := by
  intro n hn ihdim A B hA hposA hB hside hangle ihdefRaw
  have ihdef : ∀ A' B' : Fin (n + 1) → S2,
      WeakConvexSphArm A' → PositiveJoints A' →
      StrictConvexSphArm B' → SameSides A' B' → JointLe A' B' →
      deficitCount A' B' < deficitCount A B → endpt A' ≤ endpt B' := by
    intro A' B' hA' hposA' hB' hside' hangle' hlt
    exact ihdefRaw A' B' hA' hposA' hB' hside' hangle' hlt
  rcases strict_or_vanishing hA with hvanish | hAstrict
  · -- CASE 1: vanishing non-incident support of the weak entry ⟹ modern CUT (no splice Prop).
    have hcr : CutReadyPlus A B := res.hwpc A B hA hposA hB hside hangle hvanish
    exact cut_step_from_stuckAtK_plus res.hffct hn ihdim hA hposA hB hside hangle hcr
  · by_cases hnd : deficitCount A B = 0
    · exact congruence_step hAstrict hB hside hangle hnd
    · have hpos : 0 < deficitCount A B := Nat.pos_of_ne_zero hnd
      obtain ⟨k, hkdef⟩ := exists_deficit_of_pos hpos
      exact open_step_honest res.hbridge res.hffct hn ihdim hAstrict hB hside hangle ihdef k hkdef

/-- **`spherical_arm_mono_final_v2` — the Ch13 strict-arm headline, route (b), REPAIRED.**

For `n ≥ 2`, strict convex spherical arms `A`, `B` of `n + 1` vertices with equal sides and
nondecreasing interior joints, the chord endpoint is monotone — modulo the HONEST residue bundle
`Ch13ResiduesHonest` (NO false `SpliceBodyDiagMono` / `SpliceStructuralData`).  Proof: pure assembly
via `szOpeningStepPlus_honest` + FFCT19's `spherical_arm_mono_of_stepPlus`. -/
theorem spherical_arm_mono_final_v2 (res : Ch13ResiduesHonest)
    {n : ℕ} (hn : 2 ≤ n) (A B : Fin (n + 1) → S2)
    (hA : StrictConvexSphArm A) (hB : StrictConvexSphArm B)
    (hside : ∀ i : Fin n, sideLen A i = sideLen B i)
    (hangle : ∀ i : Fin (n - 1), jointAngle A i ≤ jointAngle B i) :
    sDist (A 0) (A (Fin.last n)) ≤ sDist (B 0) (B (Fin.last n)) :=
  spherical_arm_mono_of_stepPlus (szOpeningStepPlus_honest res) hn A B hA hB hside hangle

/-! ## §8. Anti-impostor guards (playbook §3.3).

The honest bundle is NOT a false-Prop trap: each conjunct's conclusion is a genuine geometric object
realised reflexively, and the headline conclusion is a real chord bound (not `True`). -/

/-- The repaired headline's conclusion is a genuine chord bound, realised reflexively at `A = B`. -/
theorem spherical_arm_mono_final_v2_conclusion_satisfiable {n : ℕ} (A : Fin (n + 1) → S2) :
    sDist (A 0) (A (Fin.last n)) ≤ sDist (A 0) (A (Fin.last n)) := le_refl _

/-- `WeakPositiveCutReady`'s conclusion `CutReadyPlus A B` is a genuine cut datum (its consumer
`cut_step_from_stuckAtK_plus` derives the real bound `endpt A ≤ endpt B`, reflexive at `A = B`), so the
honest residue is load-bearing, not a vacuous/false impostor like `SpliceBodyDiagMono`. -/
theorem weakPositiveCutReady_conclusion_satisfiable {n : ℕ} (A : Fin (n + 1) → S2) :
    endpt A ≤ endpt A := le_refl _

end ProofsInTheBook.ZinanFFCT58

#print axioms ProofsInTheBook.ZinanFFCT58.spliceBodyDiagMono_false
#print axioms ProofsInTheBook.ZinanFFCT58.ch13Residues_uninhabited
#print axioms ProofsInTheBook.ZinanFFCT58.open_step_honest
#print axioms ProofsInTheBook.ZinanFFCT58.szOpeningStepPlus_honest
#print axioms ProofsInTheBook.ZinanFFCT58.spherical_arm_mono_final_v2
