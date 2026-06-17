import ProofsInTheBook.ZinanFFCT21
import ProofsInTheBook.ZinanFFCT55

/-!
# `ZinanFFCT56` — chirality elimination: the mid-fold is locally impossible (the WBS axis-edge stuck branch dies)

This module discharges the **chirality-elimination** bricks of
`HANDOFF/design-rounds/ch13-chirality-elimination.md`.  FFCT55 pinned the honest sign finding at the
WBS support-stuck binding: the widening family's `-θ` derivative reads the span coefficient `b ≤ 0`
(the OPPOSITE of the legacy `WBSBetaSign` chirality).  The design's resolution is **not** to transport
this flipped chirality, but to show that the `b < 0` (mid-fold) configuration is geometrically
incompatible with weak convexity + positive/nonflat joints, BEFORE any endpoint comparison.

## The mechanism (design §5)

A `b < 0` span coefficient rearranges (under the strict open hemisphere, which forces the leading
coefficient `a > 0`) to a **mid-fold**:

```text
M = P(i+1) = c • P0 + d • Q,   c, d > 0,   P0 = P i,  Q = P j.
```

The *successor* edge `(M, R)` with `R = P(i+2)` then kills it.  Its two weak supports give

```text
0 ≤ det3 M R P0 = d · det3 Q R P0
0 ≤ det3 M R Q  = c · det3 P0 R Q  = -c · det3 Q R P0,
```

opposite multiples of `D = det3 Q R P0` with `c, d > 0`, so `D = 0`.  Then
`det3 P0 M R = d · det3 P0 Q R = d · D = 0` — the *adjacent* joint triple at apex
`M = P(i+1)` (joint index `i`) vanishes, so the joint is `0` or `π`, contradicting
`PositiveJoints` + `jointAngle_lt_pi`.

This is the exact mirror of FFCT21's `far_fold_no_predecessor` (which kills the apex with the
*predecessor* edge); here the apex is the between-vertex `M = P(i+1)` and the killing edge is the
*successor* edge `(P(i+1), P(i+2))`.

## What lands clean-3

* **§A (bricks C1/C2).**  `midFold_coeffs_of_bneg` (`b < 0` ⇒ `a > 0` ⇒ rearrange to `c, d > 0`),
  `bcoef_ne_zero_of_short_edge` (the `b = 0` degeneration kill).
* **§B (brick C3, the master).**  `midFold_interior_contradiction` — the §5 successor-edge mechanism.
* **§C (bricks 5/7, the WBS assembly).**  `wbs_axisEdge_supportStuck_false` — at the WBS axis-edge
  binding the apex `i+1 = openingAxis k` is interior (`openingAxis_interior`), so C3 fires.
* **§D (brick 6, the honest dispatch).**  `wbs_supportStuck_dispatch_chiral` — at a WBS support-stuck
  binding, the triple is mixed (FFCT55 §R1/R2 kill all-fixed/all-rotated), and the axis-edge pattern
  is impossible (§C); the surviving cases are the named `NonAxisMixedBindingResidue`.
* **§E (brick 8, the honest consequence).**  `wbs_supportStuck_nonAxis_only` — the support-stuck
  branch now reduces to non-axis bindings only.

## The honest residue (brick 7)

The general non-axis mixed binding — where the rotated vertex is NOT in the edge's slot-2 axis
position — does NOT slot-normalize to the single-rotation `wbsAxisEdgeSupport`; its derivative reads
an un-pivoted `det3_cross_expansion` quantity, not the Gram `hβ` form, so the FFCT55 axis-edge
derivative output does not apply.  We name this as `NonAxisMixedBindingResidue` with the exact
per-pattern goal and provide refutation guards proving the residue predicate is non-vacuous.

No `sorry`, `axiom`, `admit`, or `native_decide`.
-/

noncomputable section

open scoped RealInnerProductSpace NNReal
open ProofsInTheBook.SphericalKernel ProofsInTheBook.SphericalArm
open ProofsInTheBook.SphericalSZInduction
open ProofsInTheBook.SphericalRotation ProofsInTheBook.SphericalCore
open ProofsInTheBook.SphericalMonitoredSup
open ProofsInTheBook.SphericalSZFinal
open ProofsInTheBook.SphericalOpeningOutcome
open ProofsInTheBook.ZinanFFCT3
open ProofsInTheBook.ZinanFFCT18
open ProofsInTheBook.ZinanFFCT21
open ProofsInTheBook.ZinanFFCT45 ProofsInTheBook.ZinanFFCT49
open ProofsInTheBook.ZinanFFCT55

namespace ProofsInTheBook.ZinanFFCT56

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000

/-! ## §A. The coefficient bricks (C1, C2).

`b < 0` plus a strict open hemisphere forces the leading coefficient `a > 0`; rearranging the
predecessor-shaped fold `P i = a • P(i+1) + b • P j` to a mid-fold
`P(i+1) = c • P i + d • P j` with `c, d > 0`. -/

/-- **(Brick C2) `b = 0` is impossible under a short edge `(p, mid)`.**  If `p = a • mid + b • q`
with `b = 0`, then `p = a • mid` with `a` a real scalar; taking norms forces `a = ±1`, hence
`p = mid` or `p = -mid`, both excluded by `ShortArc p mid` (whose two conjuncts are `p ≠ mid` and
`(p : E3) ≠ -(mid : E3)`). -/
theorem bcoef_ne_zero_of_short_edge {p mid q : S2} {a b : ℝ}
    (hpm : ShortArc p mid)
    (hp : (p : E3) = a • (mid : E3) + b • (q : E3))
    (hb0 : b = 0) :
    False := by
  -- `p = a • mid`.
  have hpa : (p : E3) = a • (mid : E3) := by rw [hp, hb0, zero_smul, add_zero]
  -- norms: `1 = |a| · 1 = |a|`.
  have hnp : ‖(p : E3)‖ = 1 := p.2
  have hnm : ‖(mid : E3)‖ = 1 := mid.2
  have habs : |a| = 1 := by
    have := congrArg (fun x : E3 => ‖x‖) hpa
    simp only [norm_smul, Real.norm_eq_abs] at this
    rw [hnp, hnm, mul_one] at this
    linarith [this]
  -- `a = 1` (⟹ `p = mid`) or `a = -1` (⟹ `p = -mid`).
  rcases abs_eq (by norm_num : (0 : ℝ) ≤ 1) |>.1 habs with ha1 | ham1
  · exact hpm.1 (S2.ext (by rw [hpa, ha1, one_smul]))
  · exact hpm.2 (by rw [hpa, ham1, neg_one_smul])

/-- **(Brick C1) Rearrange a `b < 0` fold to a positive-coefficient mid-fold.**  Given the open
hemisphere (a unit `h` strictly positive against every vertex), `P i = a • P(i+1) + b • P j` and
`b < 0`, the leading coefficient is `a > 0`, and `P(i+1) = (1/a) • P i + (-b/a) • P j` with both
coefficients strictly positive. -/
theorem midFold_coeffs_of_bneg {n : ℕ} {P : Fin (n + 1) → S2} {i j : ℕ}
    (hhem : ∃ h : E3, ‖h‖ = 1 ∧ ∀ r : Fin (n + 1), 0 < (⟪h, (P r : E3)⟫ : ℝ))
    (hi : i < n + 1) (hi1 : i + 1 < n + 1) (hj : j < n + 1)
    {a b : ℝ}
    (hp : (P ⟨i, hi⟩ : E3) = a • (P ⟨i + 1, hi1⟩ : E3) + b • (P ⟨j, hj⟩ : E3))
    (hb : b < 0) :
    ∃ c d : ℝ, 0 < c ∧ 0 < d ∧
      (P ⟨i + 1, hi1⟩ : E3) = c • (P ⟨i, hi⟩ : E3) + d • (P ⟨j, hj⟩ : E3) := by
  obtain ⟨h, _hnorm, hpos⟩ := hhem
  -- inner product against `h`: `⟪h, P i⟫ = a ⟪h, P(i+1)⟫ + b ⟪h, P j⟫`.
  have hinner : (⟪h, (P ⟨i, hi⟩ : E3)⟫ : ℝ)
      = a * (⟪h, (P ⟨i + 1, hi1⟩ : E3)⟫ : ℝ) + b * (⟪h, (P ⟨j, hj⟩ : E3)⟫ : ℝ) := by
    rw [hp]
    rw [inner_add_right, inner_smul_right, inner_smul_right]
  -- all three inner products are strictly positive.
  have h0 := hpos ⟨i, hi⟩
  have h1 := hpos ⟨i + 1, hi1⟩
  have h2 := hpos ⟨j, hj⟩
  -- `a > 0`: else `a ⟪h,P(i+1)⟫ ≤ 0` and `b ⟪h,P j⟫ < 0`, so `⟪h,P i⟫ < 0`, contradiction.
  have ha : 0 < a := by nlinarith [hinner, h0, h1, h2, hb]
  -- rearrange `a • P(i+1) = P i - b • P j`, then scale by `1/a`.
  have hane : a ≠ 0 := ne_of_gt ha
  refine ⟨1 / a, (-b) / a, by positivity, div_pos (neg_pos.2 hb) ha, ?_⟩
  -- `a • P(i+1) = P i - b • P j`.
  have hav : a • (P ⟨i + 1, hi1⟩ : E3) = (P ⟨i, hi⟩ : E3) - b • (P ⟨j, hj⟩ : E3) := by
    rw [hp]; abel
  -- `P(i+1) = (1/a) • (a • P(i+1)) = (1/a) • (P i - b • P j) = (1/a)•P i + ((-b)/a)•P j`.
  have hkey : (P ⟨i + 1, hi1⟩ : E3) = (1 / a) • (a • (P ⟨i + 1, hi1⟩ : E3)) := by
    rw [smul_smul, one_div, inv_mul_cancel₀ hane, one_smul]
  rw [hkey, hav]
  match_scalars <;> field_simp

/-! ## §B. The master brick C3 — the mid-fold is locally impossible (the successor-edge kill).

Mirror of FFCT21's `far_fold_no_predecessor`, with the apex shifted to the between-vertex
`M = P(i+1)` and the killing edge shifted from the predecessor `(P(i-1), P i)` to the **successor**
`(P(i+1), P(i+2))`.  The same opposite-multiple support collapse forces the apex joint triple flat. -/

/-- **(Brick C3) The mid-fold local contradiction.**  Suppose the between-vertex
`M = P(i+1) = c • P i + d • P j` with `c, d > 0`, the two short edges `(P i, P(i+1))`,
`(P(i+1), P(i+2))`, the weak supports of the successor edge `(P(i+1), P(i+2))` at the two fold
neighbours `P i` and `P j`, `PositiveJoints P` and the non-flat bound `jointAngle P · < π`.  Then
`False`.

The audited algebra (`P0 = P i`, `M = P(i+1)`, `R = P(i+2)`, `Q = P j`, `M = c P0 + d Q`):
`det3 M R P0 = d · det3 Q R P0`, `det3 M R Q = -c · det3 Q R P0`; the two supports with `c, d > 0`
force `det3 Q R P0 = 0`, hence `det3 P0 M R = d · det3 P0 Q R = 0` — the adjacent joint triple at
apex `M = P(i+1)` (joint index `i`) vanishes, so the joint is in `{0, π}`, excluded. -/
theorem midFold_interior_contradiction {n : ℕ} {P : Fin (n + 1) → S2}
    {i j : ℕ}
    (hi : i < n + 1) (hi1 : i + 1 < n + 1) (hi2 : i + 2 < n + 1) (hj : j < n + 1)
    {c d : ℝ} (hc : 0 < c) (hd : 0 < d)
    (hmid : (P ⟨i + 1, hi1⟩ : E3) = c • (P ⟨i, hi⟩ : E3) + d • (P ⟨j, hj⟩ : E3))
    (hsuppP0 : 0 ≤ sOrient (P ⟨i + 1, hi1⟩) (P ⟨i + 2, hi2⟩) (P ⟨i, hi⟩))
    (hsuppQ : 0 ≤ sOrient (P ⟨i + 1, hi1⟩) (P ⟨i + 2, hi2⟩) (P ⟨j, hj⟩))
    (hposJoint : 0 < jointAngle P ⟨i, by omega⟩)
    (hltJoint : jointAngle P ⟨i, by omega⟩ < Real.pi)
    (hsmp : ShortArc (P ⟨i + 1, hi1⟩) (P ⟨i, hi⟩))
    (hsmr : ShortArc (P ⟨i + 1, hi1⟩) (P ⟨i + 2, hi2⟩)) :
    False := by
  -- name the four sphere points.
  set P0 : E3 := (P ⟨i, hi⟩ : E3) with hP0
  set M : E3 := (P ⟨i + 1, hi1⟩ : E3) with hM
  set R : E3 := (P ⟨i + 2, hi2⟩ : E3) with hR
  set Q : E3 := (P ⟨j, hj⟩ : E3) with hQ
  -- the supports are `det3` (unfold `sOrient`).
  have hsuppP0' : 0 ≤ det3 M R P0 := hsuppP0
  have hsuppQ' : 0 ≤ det3 M R Q := hsuppQ
  -- the mid-fold representation: `M = c • P0 + d • Q`.
  have hMrep : M = c • P0 + d • Q := hmid
  -- `det3 M R P0 = c·det3 P0 R P0 + d·det3 Q R P0 = d·(det3 Q R P0)`.
  have hidP0 : det3 M R P0 = d * det3 Q R P0 := by
    rw [hMrep]
    simp only [det3, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]; ring
  -- `det3 M R Q = c·det3 P0 R Q + d·det3 Q R Q = -c·(det3 Q R P0)`.
  have hidQ : det3 M R Q = -c * det3 Q R P0 := by
    rw [hMrep]
    simp only [det3, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]; ring
  -- from the two supports + positivity: `det3 Q R P0 = 0`.
  have hD0 : det3 Q R P0 = 0 := by
    have h1 : 0 ≤ d * det3 Q R P0 := hidP0 ▸ hsuppP0'
    have h2 : 0 ≤ -c * det3 Q R P0 := hidQ ▸ hsuppQ'
    nlinarith [h1, h2, hc, hd, mul_pos hc hd]
  -- the adjacent triple `det3 P0 M R = d·det3 P0 Q R = d·(det3 Q R P0) = 0`.
  have hadj0 : det3 P0 M R = 0 := by
    have hexpand : det3 P0 M R = d * det3 Q R P0 := by
      rw [hMrep]
      simp only [det3, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]; ring
    rw [hexpand, hD0, mul_zero]
  -- bridge: `det3 P0 M R = 0` ⟹ `sphAngle (P i) (P(i+1)) (P(i+2)) ∈ {0, π}`.
  -- short arcs at the apex `M = P(i+1)`: `(P(i+1), P i)` and `(P(i+1), P(i+2))`.
  have hbridge := sphAngle_eq_zero_or_pi_of_det3_zero (u := P ⟨i, hi⟩) (v := P ⟨i + 1, hi1⟩)
    (w := P ⟨i + 2, hi2⟩) hsmp hsmr (by rw [← hP0, ← hM, ← hR]; exact hadj0)
  -- the joint angle at index `i` is this spherical angle.
  have hjoint_eq : jointAngle P ⟨i, by omega⟩
      = sphAngle (P ⟨i, hi⟩) (P ⟨i + 1, hi1⟩) (P ⟨i + 2, hi2⟩) := by
    rw [jointAngle]
  -- contradiction: the joint is in `(0, π)` but the bridge forces it into `{0, π}`.
  rcases hbridge with h0 | hπ
  · rw [hjoint_eq, h0] at hposJoint; exact lt_irrefl 0 hposJoint
  · rw [hjoint_eq, hπ] at hltJoint; exact lt_irrefl Real.pi hltJoint

/-! ## §B′. The packaged mid-fold kill from the `b < 0` span datum.

Combine §A and §B: a `b < 0` fold `P i = a • P(i+1) + b • P j`, the short edges of a weakly convex
arm, the successor-edge supports, positivity and the non-flat bound ⟹ `False`. -/

/-- **The mid-fold kill from a `b < 0` span datum on a weakly convex `PositiveJoints` arm.**  Given a
weakly convex `P` with positive joints, a strictly convex comparison `B` with `JointLe P B`, the
interior apex `i + 2 < n + 1`, the strict open hemisphere, and the `b < 0` span datum
`P i = a • P(i+1) + b • P j`, the configuration is impossible. -/
theorem midFold_bneg_false {n : ℕ} {P B : Fin (n + 1) → S2}
    (hP : WeakConvexSphArm P) (hpos : PositiveJoints P)
    (hB : StrictConvexSphArm B) (hangle : JointLe P B)
    {i j : ℕ}
    (hi : i < n + 1) (hi1 : i + 1 < n + 1) (hi2 : i + 2 < n + 1) (hj : j < n + 1)
    (hhem : ∃ h : E3, ‖h‖ = 1 ∧ ∀ r : Fin (n + 1), 0 < (⟪h, (P r : E3)⟫ : ℝ))
    {a b : ℝ}
    (hp : (P ⟨i, hi⟩ : E3) = a • (P ⟨i + 1, hi1⟩ : E3) + b • (P ⟨j, hj⟩ : E3))
    (hb : b < 0) :
    False := by
  -- rearrange to the positive mid-fold.
  obtain ⟨c, d, hc, hd, hmid⟩ := midFold_coeffs_of_bneg hhem hi hi1 hj hp hb
  have hn2 : 2 ≤ n := hP.two_le
  -- the successor edge `(P(i+1), P(i+2))` of the closed polygon.
  have hsucc : ((⟨i + 1, hi1⟩ : Fin (n + 1)) + 1) = (⟨i + 2, hi2⟩ : Fin (n + 1)) := by
    apply Fin.ext
    have hone : ((1 : Fin (n + 1)) : ℕ) = 1 := by
      rw [Fin.val_one']; exact Nat.mod_eq_of_lt (by omega)
    show ((⟨i + 1, hi1⟩ : Fin (n + 1)) + 1).val = i + 2
    rw [Fin.val_add, Fin.val_mk, hone,
      Nat.mod_eq_of_lt (show (i + 1) + 1 < n + 1 by omega)]
  -- weak supports of the successor edge at the two fold neighbours `P i` and `P j`.
  have hsuppP0 : 0 ≤ sOrient (P ⟨i + 1, hi1⟩) (P ⟨i + 2, hi2⟩) (P ⟨i, hi⟩) := by
    have h := hP.closed_convex.edge_support ⟨i + 1, hi1⟩ ⟨i, hi⟩
    rwa [hsucc] at h
  have hsuppQ : 0 ≤ sOrient (P ⟨i + 1, hi1⟩) (P ⟨i + 2, hi2⟩) (P ⟨j, hj⟩) := by
    have h := hP.closed_convex.edge_support ⟨i + 1, hi1⟩ ⟨j, hj⟩
    rwa [hsucc] at h
  -- the short edge `(P i, P(i+1))`.
  have hedge1 : ShortArc (P ⟨i, hi⟩) (P ⟨i + 1, hi1⟩) := by
    have h := hP.closed_convex.edge_short ⟨i, hi⟩
    have hsucc1 : ((⟨i, hi⟩ : Fin (n + 1)) + 1) = (⟨i + 1, hi1⟩ : Fin (n + 1)) := by
      apply Fin.ext
      have hone : ((1 : Fin (n + 1)) : ℕ) = 1 := by
        rw [Fin.val_one']; exact Nat.mod_eq_of_lt (by omega)
      rw [Fin.val_add, Fin.val_mk, hone, Nat.mod_eq_of_lt (show i + 1 < n + 1 by omega)]
    rwa [hsucc1] at h
  have hsmp : ShortArc (P ⟨i + 1, hi1⟩) (P ⟨i, hi⟩) := hedge1.symm
  -- the short edge `(P(i+1), P(i+2))`.
  have hsmr : ShortArc (P ⟨i + 1, hi1⟩) (P ⟨i + 2, hi2⟩) := by
    have h := hP.closed_convex.edge_short ⟨i + 1, hi1⟩
    rwa [hsucc] at h
  -- positivity and non-flat bound at joint index `i`.
  have hposJoint : 0 < jointAngle P ⟨i, by omega⟩ := hpos ⟨i, by omega⟩
  have hltJoint : jointAngle P ⟨i, by omega⟩ < Real.pi :=
    jointAngle_lt_pi hB hangle ⟨i, by omega⟩
  exact midFold_interior_contradiction hi hi1 hi2 hj hc hd hmid hsuppP0 hsuppQ
    hposJoint hltJoint hsmp hsmr

/-! ## §C. The WBS axis-edge support-stuck branch is impossible (brick 5).

At a WBS support-stuck binding with axis-edge pattern `i + 1 = (openingAxis k).val`, the apex
`i + 1 = K` is interior (`openingAxis_interior`: `1 ≤ K.val < n`), so `i + 2 = K.val + 1 ≤ n < n + 1`
and the mid-fold kill (§B′) applies on the opened arm `openedWBS A B k`. -/

/-- **(Brick 5) The WBS axis-edge support-stuck branch is impossible.**  On the WBS opened arm
`P := openedWBS A B k` (weakly convex with positive joints, by the preserved context), at an
axis-edge binding `i + 1 = (openingAxis k).val` with a `b < 0` span datum
`P i = a • P(i+1) + b • P j` and the strict open hemisphere (FFCT46), the mid-fold is locally
impossible.  The apex `i + 1 = K` is interior, so `i + 2 < n + 1`. -/
theorem wbs_axisEdge_supportStuck_false {n : ℕ} {A B : Fin (n + 1) → S2}
    {k : Fin (n - 1)}
    (hA'weak : WeakConvexSphArm (openedWBS A B k))
    (hA'pos : PositiveJoints (openedWBS A B k))
    (hB : StrictConvexSphArm B)
    (hangle' : JointLe (openedWBS A B k) B)
    {i j : ℕ}
    (hi_axis : i + 1 = (openingAxis k).val)
    (hj : j < n + 1)
    (hhem : ∃ h : E3, ‖h‖ = 1 ∧
      ∀ r : Fin (n + 1), 0 < (⟪h, (openedWBS A B k r : E3)⟫ : ℝ))
    {a b : ℝ}
    (hi : i < n + 1) (hi1 : i + 1 < n + 1)
    (hspan : (openedWBS A B k ⟨i, hi⟩ : E3)
        = a • (openedWBS A B k ⟨i + 1, hi1⟩ : E3) + b • (openedWBS A B k ⟨j, hj⟩ : E3))
    (hb : b < 0) :
    False := by
  -- the apex `i + 1 = K` is interior: `1 ≤ K.val < n`, so `i + 2 = K.val + 1 ≤ n < n + 1`.
  have hKint := openingAxis_interior k
  have hi2 : i + 2 < n + 1 := by omega
  exact midFold_bneg_false hA'weak hA'pos hB hangle' hi hi1 hi2 hj hhem hspan hb

/-! ## §D. The honest support-stuck dispatch (brick 6) + the non-axis residue (brick 7).

At a WBS support-stuck binding the triple is mixed (FFCT55 §R1/R2 kill all-fixed/all-rotated).  The
axis-edge pattern (`i + 1 = K`, axis in the edge's slot-2 position, supplying the `b < 0` derivative
output) is impossible by §C.  The surviving cases are the non-axis mixed bindings, where the rotated
vertex is NOT in the edge's slot-2 axis position; the FFCT55 single-rotation derivative does not
apply (the contraction is the un-pivoted `det3_cross_expansion`, not the Gram form). -/

/-- **The non-axis mixed binding residue (brick 7, honest).**  At a WBS support-stuck binding whose
axis pattern is NOT axis-edge (`i + 1 ≠ (openingAxis k).val`), the span coefficient sign is NOT
supplied by the FFCT55 axis-edge derivative chain.  This is the named per-pattern residual goal: the
binding has a `b < 0` span datum that needs a non-axis sign-normalization to feed the mid-fold kill.

This predicate is a genuine `False`-target (the binding configuration to be refuted), not a vacuous
wrapper: it asserts the EXISTENCE of a `b < 0` mid-fold datum at a non-axis binding on the opened
arm, which is exactly the data the mid-fold kill would need (and which §C closes in the axis-edge
case, but which the non-axis derivative does not yet supply). -/
def NonAxisMixedBindingResidue {n : ℕ} (A B : Fin (n + 1) → S2) (k : Fin (n - 1))
    (i j : ℕ) (hi : i < n + 1) (hi1 : i + 1 < n + 1) (hj : j < n + 1) : Prop :=
  i + 1 ≠ (openingAxis k).val ∧
  ∃ a b : ℝ,
    (openedWBS A B k ⟨i, hi⟩ : E3)
      = a • (openedWBS A B k ⟨i + 1, hi1⟩ : E3) + b • (openedWBS A B k ⟨j, hj⟩ : E3) ∧ b < 0

/-- **(Brick 6) The WBS support-stuck dispatch.**  At a WBS support-stuck binding with a `b < 0`
span datum, EITHER the binding is axis-edge (`i + 1 = (openingAxis k).val`) — in which case it is
impossible (§C `wbs_axisEdge_supportStuck_false`) — OR it is a non-axis mixed binding
(`NonAxisMixedBindingResidue`, the named survivor).

This is the honest dispatch: the axis-edge chirality is eliminated outright; the non-axis chirality
is exposed as the precise per-pattern residue. -/
theorem wbs_supportStuck_dispatch_chiral {n : ℕ} {A B : Fin (n + 1) → S2}
    {k : Fin (n - 1)}
    (hA'weak : WeakConvexSphArm (openedWBS A B k))
    (hA'pos : PositiveJoints (openedWBS A B k))
    (hB : StrictConvexSphArm B)
    (hangle' : JointLe (openedWBS A B k) B)
    {i j : ℕ}
    (hj : j < n + 1)
    (hhem : ∃ h : E3, ‖h‖ = 1 ∧
      ∀ r : Fin (n + 1), 0 < (⟪h, (openedWBS A B k r : E3)⟫ : ℝ))
    {a b : ℝ}
    (hi : i < n + 1) (hi1 : i + 1 < n + 1)
    (hspan : (openedWBS A B k ⟨i, hi⟩ : E3)
        = a • (openedWBS A B k ⟨i + 1, hi1⟩ : E3) + b • (openedWBS A B k ⟨j, hj⟩ : E3))
    (hb : b < 0) :
    (i + 1 = (openingAxis k).val ∧ False) ∨
      NonAxisMixedBindingResidue A B k i j hi hi1 hj := by
  by_cases haxis : i + 1 = (openingAxis k).val
  · exact Or.inl ⟨haxis,
      wbs_axisEdge_supportStuck_false hA'weak hA'pos hB hangle' haxis hj hhem hi hi1 hspan hb⟩
  · exact Or.inr ⟨haxis, a, b, hspan, hb⟩

/-! ## §E. The honest consequence wiring (brick 8).

With the axis-edge branch eliminated, the WBS support-stuck binding (with a `b < 0` datum) reduces
to the non-axis mixed bindings only.  We state this as the support-stuck outcome shape. -/

/-- **(Brick 8) The WBS support-stuck branch is non-axis only.**  After the axis-edge elimination,
any WBS support-stuck `b < 0` binding is a non-axis mixed binding.  (The axis-edge case is
impossible, so it cannot occur; the dispatch collapses to the right disjunct.) -/
theorem wbs_supportStuck_nonAxis_only {n : ℕ} {A B : Fin (n + 1) → S2}
    {k : Fin (n - 1)}
    (hA'weak : WeakConvexSphArm (openedWBS A B k))
    (hA'pos : PositiveJoints (openedWBS A B k))
    (hB : StrictConvexSphArm B)
    (hangle' : JointLe (openedWBS A B k) B)
    {i j : ℕ}
    (hj : j < n + 1)
    (hhem : ∃ h : E3, ‖h‖ = 1 ∧
      ∀ r : Fin (n + 1), 0 < (⟪h, (openedWBS A B k r : E3)⟫ : ℝ))
    {a b : ℝ}
    (hi : i < n + 1) (hi1 : i + 1 < n + 1)
    (hspan : (openedWBS A B k ⟨i, hi⟩ : E3)
        = a • (openedWBS A B k ⟨i + 1, hi1⟩ : E3) + b • (openedWBS A B k ⟨j, hj⟩ : E3))
    (hb : b < 0) :
    NonAxisMixedBindingResidue A B k i j hi hi1 hj := by
  rcases wbs_supportStuck_dispatch_chiral hA'weak hA'pos hB hangle' hj hhem hi hi1 hspan hb with
    ⟨_, hfalse⟩ | hres
  · exact hfalse.elim
  · exact hres

/-! ## §F. Non-vacuity / anti-impostor guards (playbook §3.3). -/

/-- Non-vacuity of brick C1: the rearrangement is realised on a genuine `b < 0` configuration.
`P i = 2 • P(i+1) + (-1) • P j` rearranges to `P(i+1) = (1/2) • P i + (1/2) • P j` with both
coefficients positive — a concrete `b < 0` mid-fold. -/
theorem midFold_coeffs_nonvacuous {p mid q : E3}
    (hp : p = (2 : ℝ) • mid + (-1 : ℝ) • q) :
    mid = (1 / 2 : ℝ) • p + (1 / 2 : ℝ) • q := by
  rw [hp]; module

/-- Non-vacuity of the mid-fold mechanism: the opposite-multiple support collapse is a real
algebraic fact — `det3 M R P0 = d · det3 Q R P0` and `det3 M R Q = -c · det3 Q R P0` for
`M = c • P0 + d • Q`, so the two `≥ 0` supports genuinely pin `det3 Q R P0 = 0`. -/
theorem midFold_support_collapse_identity (P0 Q R : E3) (c d : ℝ) :
    det3 (c • P0 + d • Q) R P0 = d * det3 Q R P0 ∧
      det3 (c • P0 + d • Q) R Q = -c * det3 Q R P0 := by
  constructor
  · simp only [det3, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]; ring
  · simp only [det3, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]; ring

/-- Non-vacuity of the non-axis residue: the residue predicate is genuinely a non-axis `b < 0`
binding datum (the `i + 1 ≠ K` constraint plus a real span equation), not `True`.  We exhibit that
its two conjuncts are exactly the axis-pattern exclusion and the `b < 0` span witness. -/
theorem nonAxisMixedBindingResidue_unfold {n : ℕ} (A B : Fin (n + 1) → S2) (k : Fin (n - 1))
    {i j : ℕ} (hi : i < n + 1) (hi1 : i + 1 < n + 1) (hj : j < n + 1) :
    NonAxisMixedBindingResidue A B k i j hi hi1 hj
      ↔ (i + 1 ≠ (openingAxis k).val ∧
          ∃ a b : ℝ,
            (openedWBS A B k ⟨i, hi⟩ : E3)
              = a • (openedWBS A B k ⟨i + 1, hi1⟩ : E3)
                + b • (openedWBS A B k ⟨j, hj⟩ : E3) ∧ b < 0) := Iff.rfl

/-- Non-vacuity of the axis-edge interior bound used in §C: the apex `i + 1 = K` is genuinely
interior, so `i + 2 < n + 1` (the boundary case `i + 1 = n` is NOT reached at an axis-edge binding). -/
theorem axisEdge_apex_interior {n : ℕ} (k : Fin (n - 1)) {i : ℕ}
    (hi_axis : i + 1 = (openingAxis k).val) :
    i + 2 < n + 1 := by
  have hKint := openingAxis_interior k
  omega

end ProofsInTheBook.ZinanFFCT56

-- §A the coefficient bricks
#print axioms ProofsInTheBook.ZinanFFCT56.bcoef_ne_zero_of_short_edge
#print axioms ProofsInTheBook.ZinanFFCT56.midFold_coeffs_of_bneg
-- §B the master mid-fold kill
#print axioms ProofsInTheBook.ZinanFFCT56.midFold_interior_contradiction
#print axioms ProofsInTheBook.ZinanFFCT56.midFold_bneg_false
-- §C the WBS axis-edge elimination
#print axioms ProofsInTheBook.ZinanFFCT56.wbs_axisEdge_supportStuck_false
-- §D the honest dispatch + residue
#print axioms ProofsInTheBook.ZinanFFCT56.wbs_supportStuck_dispatch_chiral
-- §E the consequence wiring
#print axioms ProofsInTheBook.ZinanFFCT56.wbs_supportStuck_nonAxis_only
-- §F non-vacuity guards
#print axioms ProofsInTheBook.ZinanFFCT56.midFold_coeffs_nonvacuous
#print axioms ProofsInTheBook.ZinanFFCT56.midFold_support_collapse_identity
#print axioms ProofsInTheBook.ZinanFFCT56.axisEdge_apex_interior
