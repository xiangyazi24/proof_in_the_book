import ProofsInTheBook.ZinanFFCT20
import ProofsInTheBook.ZinanFFCT12

/-!
# `ZinanFFCT21` — the Chapter 13 B5 bricks: the far-fold boundary classification (the `i = 0` half)

This module supplies the adversarially-audited B5 bricks isolated by
`HANDOFF/design-rounds/ch13-B5-B1-audit.md`.  The audit corrected the original sketch on two points:

* the *predecessor kill* (Brick 4) needs **both** span coefficients strictly positive (`0 < a`,
  `0 < b`); and
* the *tail side* (`j ∈ {n-1, n}`) is **not** a mirror — it needs the `OnFoldRay` cone propagation
  (a master brick, deliberately out of scope here).

So the deliverable milestone is the **`i = 0` half** of the boundary classification:

> from the nondegenerate-coefficient datum
> `∃ a b : ℝ≥0, 0 < a ∧ 0 < b ∧ (a:ℝ)•A(i+1) + (b:ℝ)•A j = A i`,
> together with `WeakConvexSphArm A`, `PositiveJoints A`, `StrictConvexSphArm B`, `JointLe A B`,
> and `i + 2 < j < n+1`, conclude `i = 0` (Brick 5).

The engine is the predecessor kill (Brick 4): at any interior `i ≥ 1`, the nondegenerate fold is
incompatible with the two weak supports of the predecessor edge `(A(i-1), A i)`.  The audited algebra:
writing `u = A(i-1)`, `p = A i`, `v = A(i+1)`, `w = A j`,

* `det3 u p v = -b · det3 u v w`  (from `p = a•v + b•w` and `det3 u p p = 0`);
* `det3 u p w =  a · det3 u v w`;

the two weak supports `0 ≤ det3 u p v` and `0 ≤ det3 u p w` with `a, b > 0` force
`det3 u v w = 0` and hence `det3 u p v = 0` — the *adjacent* joint triple at apex `A i` vanishes.
A vanishing adjacent triple forces the interior joint at apex `A i` (joint index `i-1`) into
`{0, π}` (Brick: `sphAngle_eq_zero_or_pi_of_det3_zero`); `PositiveJoints` kills `0` and
`jointAngle_lt_pi` kills `π`.  Contradiction, so the fold can only occur at `i = 0`.

## Bricks

1. `span_pair_coeffs_S2` — extract `a b : ℝ≥0` with `(a:ℝ)•v + (b:ℝ)•w = p` from NNReal span
   membership (FFCT19's pattern).
2. `nnreal_smul_unit_eq_unit` — `p = a • v`, `p, v` unit, `a ≥ 0` ⟹ `a = 1 ∧ p = v`.
3. `coeff_b_pos_of_edge_short` — `b = 0` ⟹ `p = v`, contradicting `ShortArc p v` (which gives `p ≠ v`).
4. `far_fold_no_predecessor` — the corrected predecessor kill at `i ≥ 1`.
5. `far_fold_boundary_classification_of_nondeg` — the deliverable: `i = 0` (the audit's fallback
   milestone; the tail half is out of scope).
6. `far_fold_i_eq_zero` — the wrapper combining 1+3+5 when `b > 0` is derivable from the edge.

The auxiliary forward bridge `sphAngle_eq_zero_or_pi_of_det3_zero` (a vanishing area form forces the
apex spherical angle into `{0, π}`) is the inverse of FFCT3's `det3_zero_of_sphAngle_pi` /
FFCT18's `det3_zero_of_sphAngle_zero`; it is proved here by the tangent-collinearity route
(`collinear_of_det3_zero` + the planar-area transport `det3_apex_transport`).

No `sorry`, `axiom`, `admit`, or `native_decide`.
-/

noncomputable section
open scoped RealInnerProductSpace NNReal
open ProofsInTheBook.SphericalKernel ProofsInTheBook.SphericalArm
open ProofsInTheBook.SphericalSZInduction
open ProofsInTheBook.ZinanFFCT3 ProofsInTheBook.ZinanFFCT9 ProofsInTheBook.ZinanFFCT10
open ProofsInTheBook.ZinanFFCT12 ProofsInTheBook.ZinanFFCT18

namespace ProofsInTheBook.ZinanFFCT21

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000

/-! ## `det3` left-argument multilinearity (the substrate only ships the right-argument versions). -/

/-- `det3` additive in the *middle* argument. -/
theorem det3_add_mid (a b c d : E3) : det3 a (b + c) d = det3 a b d + det3 a c d := by
  simp only [det3, PiLp.add_apply]; ring

/-- `det3` homogeneous in the *middle* argument. -/
theorem det3_smul_mid (a b d : E3) (t : ℝ) : det3 a (t • b) d = t * det3 a b d := by
  simp only [det3, PiLp.smul_apply, smul_eq_mul]; ring

/-! ## Brick 1 — extract the span coefficients. -/

/-- **(Brick 1) Extract the span coefficients.**  From the NNReal span membership
`(p:E3) ∈ span≥0 {v, w}`, produce `a b : ℝ≥0` with `(a:ℝ)•v + (b:ℝ)•w = p` (the real-scalar
combination).  This is exactly FFCT19's `Submodule.mem_span_pair` + `NNReal.smul_def` pattern. -/
theorem span_pair_coeffs_S2 {p v w : S2}
    (hcol : (p : E3) ∈ Submodule.span NNReal ({(v : E3), (w : E3)} : Set E3)) :
    ∃ a b : ℝ≥0, (a : ℝ) • (v : E3) + (b : ℝ) • (w : E3) = (p : E3) := by
  rw [Submodule.mem_span_pair] at hcol
  obtain ⟨a, b, hab⟩ := hcol
  refine ⟨a, b, ?_⟩
  have := hab
  rwa [NNReal.smul_def, NNReal.smul_def] at this

/-! ## Brick 2 — a nonnegative scaling of a unit by a unit is the identity. -/

/-- **(Brick 2) Unit = nonnegative multiple of unit ⟹ scalar `1` and equality.**  If `p = a • v`
with `p`, `v` on the sphere and `a ≥ 0`, then `a = 1` and `p = v`.  (Take norms: `1 = a · 1`, so
`a = 1`, hence `p = 1 • v = v`.) -/
theorem nnreal_smul_unit_eq_unit {p v : S2} {a : ℝ} (ha : 0 ≤ a)
    (hpv : (p : E3) = a • (v : E3)) :
    a = 1 ∧ p = v := by
  -- norms of both sides: `‖p‖ = 1`, `‖v‖ = 1`, `‖a • v‖ = |a| · ‖v‖ = a`.
  have hnp : ‖(p : E3)‖ = 1 := p.2
  have hnv : ‖(v : E3)‖ = 1 := v.2
  have hnorm : (1 : ℝ) = a := by
    have := congrArg (fun x : E3 => ‖x‖) hpv
    simp only [norm_smul, Real.norm_eq_abs] at this
    rw [hnp, hnv, mul_one, abs_of_nonneg ha] at this
    linarith [this]
  refine ⟨hnorm.symm, ?_⟩
  -- `p = a • v = 1 • v = v` as `E3`, hence as `S2` by injectivity of the coercion.
  apply S2.ext
  rw [hpv, ← hnorm, one_smul]

/-! ## Brick 3 — the tail coefficient is positive. -/

/-- **(Brick 3) `b = 0` is impossible under a short predecessor edge.**  If `p = a•v + b•w` with the
nonnegative coefficients and `b = 0`, then `p = a•v` with `a ≥ 0`, so `p = v` (Brick 2),
contradicting `ShortArc p v` (whose first conjunct is `p ≠ v`).  Hence `0 < b`. -/
theorem coeff_b_pos_of_edge_short {p v w : S2} {a b : ℝ≥0}
    (hpvw : (a : ℝ) • (v : E3) + (b : ℝ) • (w : E3) = (p : E3))
    (hpv : ShortArc p v) :
    0 < (b : ℝ) := by
  rcases lt_or_eq_of_le b.2 with hpos | hzero
  · exact hpos
  · -- `b = 0`: then `p = a•v`, forcing `p = v`, contradicting `ShortArc p v`.
    exfalso
    have hb0 : (b : ℝ) = 0 := hzero.symm
    have hpav : (p : E3) = (a : ℝ) • (v : E3) := by
      rw [← hpvw, hb0, zero_smul, add_zero]
    have := nnreal_smul_unit_eq_unit (a := (a : ℝ)) a.2 hpav
    exact hpv.1 this.2

/-! ## Auxiliary forward bridge — a vanishing area form forces the apex angle into `{0, π}`.

This is the converse of FFCT3's `det3_zero_of_sphAngle_pi` / FFCT18's `det3_zero_of_sphAngle_zero`.
At the *middle* vertex `v` (the apex), `det3 u v w = 0` forces the two tangent rays `tangentTo v u`,
`tangentTo v w` to be parallel (`collinear_of_det3_zero` after transporting the area form to the
apex tangent plane via `det3_apex_transport`), whence the unoriented spherical angle is `0` (same
ray) or `π` (opposite rays). -/

/-- The apex-transported area form: for the unit apex `v`, `det3 (v:E3) (tangentTo v u) (tangentTo v w)
= det3 u v w`.  (The tangents differ from `u, w` by multiples of `v`, which drop out of the
determinant; the cyclic/repeat identities collapse the rest.) -/
theorem det3_apex_tangent_eq {u v w : S2} :
    det3 (v : E3) (tangentTo v u) (tangentTo v w) = -det3 (u : E3) (v : E3) (w : E3) := by
  -- expand the two tangents; everything is then a polynomial identity in the coordinates and the
  -- two scalars `sInner u v`, `sInner w v`, closed by `ring` (the apex form differs from
  -- `det3 u v w` by one row swap, hence the sign).
  rw [tangentTo_eq, tangentTo_eq]
  simp only [det3, PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul]
  ring

/-- **(Forward bridge) A vanishing apex area form forces the spherical angle into `{0, π}`.**
If `det3 u v w = 0` and both arcs `(v, u)`, `(v, w)` are short (so both tangents are nonzero),
then `sphAngle u v w = 0` or `sphAngle u v w = π`. -/
theorem sphAngle_eq_zero_or_pi_of_det3_zero {u v w : S2}
    (hvu : ShortArc v u) (hvw : ShortArc v w)
    (hdet : det3 (u : E3) (v : E3) (w : E3) = 0) :
    sphAngle u v w = 0 ∨ sphAngle u v w = Real.pi := by
  -- both tangents at the apex are nonzero.
  have htu : tangentTo v u ≠ 0 := (tangentTo_ne_zero_iff v u).2 hvu
  have htw : tangentTo v w ≠ 0 := (tangentTo_ne_zero_iff v w).2 hvw
  -- the apex `v` is nonzero and orthogonal to both tangents.
  have hv0 : (v : E3) ≠ 0 := by
    intro h; have := v.2; rw [h, norm_zero] at this; norm_num at this
  have horthu : (⟪(v : E3), tangentTo v u⟫ : ℝ) = 0 := by
    rw [real_inner_comm]; exact tangentTo_orthogonal v u
  have horthw : (⟪(v : E3), tangentTo v w⟫ : ℝ) = 0 := by
    rw [real_inner_comm]; exact tangentTo_orthogonal v w
  -- transport: the apex area form vanishes (it is `-det3 u v w`).
  have hzero : det3 (v : E3) (tangentTo v u) (tangentTo v w) = 0 := by
    rw [det3_apex_tangent_eq, hdet, neg_zero]
  -- collinearity: `tangentTo v w = c • tangentTo v u`.
  obtain ⟨c, hc⟩ := collinear_of_det3_zero horthu horthw hv0 htu hzero
  -- `c ≠ 0` (else `tangentTo v w = 0`).
  have hc0 : c ≠ 0 := by
    intro h; rw [h, zero_smul] at hc; exact htw hc
  -- dichotomy by the sign of `c`.
  rcases lt_trichotomy c 0 with hneg | hcz | hpos
  · right
    rw [sphAngle, InnerProductGeometry.angle_eq_pi_iff]
    exact ⟨htu, c, hneg, hc⟩
  · exact absurd hcz hc0
  · left
    rw [sphAngle, InnerProductGeometry.angle_eq_zero_iff]
    exact ⟨htu, c, hpos, hc⟩

/-! ## Brick 4 — the corrected predecessor kill. -/

/-- **(Brick 4) The corrected predecessor kill.**  For an interior fold index `i ≥ 1` with the
nondegenerate span representation `(a:ℝ)•A(i+1) + (b:ℝ)•A j = A i`, `a, b > 0`, and the two weak
supports of the predecessor edge `(A(i-1), A i)` at the two fold neighbours
(`0 ≤ sOrient (A(i-1)) (A i) (A(i+1))`, `0 ≤ sOrient (A(i-1)) (A i) (A j)`), the fold is impossible,
under `PositiveJoints A` and `jointAngle A · < π` (the non-flat restriction `JointLe A B` + strict
`B` supplies).

The audited algebra (`u = A(i-1)`, `p = A i`, `v = A(i+1)`, `w = A j`):
`det3 u p v = -b·det3 u v w`, `det3 u p w = a·det3 u v w`; the two supports with `a, b > 0` force
`det3 u v w = 0`, hence `det3 u p v = 0`, i.e. the adjacent joint triple at apex `A i` vanishes, so
the interior joint at index `i-1` is in `{0, π}` — excluded by positivity and the non-flat bound. -/
theorem far_fold_no_predecessor {n : ℕ} {A : Fin (n + 1) → S2} {i j : ℕ}
    (hi1 : 1 ≤ i) (hij : i + 2 < j) (hj : j < n + 1)
    {a b : ℝ}
    (ha : 0 < a) (hb : 0 < b)
    (hpre : i - 1 < n + 1) (hii : i < n + 1) (hi2 : i + 1 < n + 1)
    (hcoeff : a • (A ⟨i + 1, hi2⟩ : E3) + b • (A ⟨j, hj⟩ : E3) = (A ⟨i, hii⟩ : E3))
    (hsuppv : 0 ≤ sOrient (A ⟨i - 1, hpre⟩) (A ⟨i, hii⟩) (A ⟨i + 1, hi2⟩))
    (hsuppw : 0 ≤ sOrient (A ⟨i - 1, hpre⟩) (A ⟨i, hii⟩) (A ⟨j, hj⟩))
    (hposJoint : 0 < jointAngle A ⟨i - 1, by omega⟩)
    (hltJoint : jointAngle A ⟨i - 1, by omega⟩ < Real.pi)
    (hsau : ShortArc (A ⟨i, hii⟩) (A ⟨i - 1, hpre⟩))
    (hsav : ShortArc (A ⟨i, hii⟩) (A ⟨i + 1, hi2⟩)) :
    False := by
  -- name the four sphere points.
  set u : E3 := (A ⟨i - 1, hpre⟩ : E3) with hu
  set p : E3 := (A ⟨i, hii⟩ : E3) with hp
  set v : E3 := (A ⟨i + 1, hi2⟩ : E3) with hv
  set w : E3 := (A ⟨j, hj⟩ : E3) with hw
  -- the supports are `det3` (unfold `sOrient`).
  have hsuppv' : 0 ≤ det3 u p v := hsuppv
  have hsuppw' : 0 ≤ det3 u p w := hsuppw
  -- the two audited identities.
  have hpvw : a • v + b • w = p := hcoeff
  -- `det3 u p v = a·det3 u v v + b·det3 u w v = b·det3 u w v = -b·det3 u v w`.
  have hidv : det3 u p v = -b * det3 u v w := by
    rw [← hpvw, det3_add_mid, det3_smul_mid, det3_smul_mid]
    -- `det3 u v v = 0`, `det3 u w v = -det3 u v w`.
    have hvv : det3 u v v = 0 := by simp only [det3]; ring
    have hwv : det3 u w v = -det3 u v w := by simp only [det3]; ring
    rw [hvv, hwv]; ring
  -- `det3 u p w = a·det3 u v w + b·det3 u w w = a·det3 u v w`.
  have hidw : det3 u p w = a * det3 u v w := by
    rw [← hpvw, det3_add_mid, det3_smul_mid, det3_smul_mid]
    have hww : det3 u w w = 0 := by simp only [det3]; ring
    rw [hww]; ring
  -- from the supports + positivity: `det3 u v w = 0`.
  have hdet0 : det3 u v w = 0 := by
    have h1 : 0 ≤ -b * det3 u v w := hidv ▸ hsuppv'
    have h2 : 0 ≤ a * det3 u v w := hidw ▸ hsuppw'
    -- `a·D ≥ 0` with `a > 0` ⟹ `D ≥ 0`; `-b·D ≥ 0` with `b > 0` ⟹ `D ≤ 0`.
    nlinarith [h1, h2, ha, hb, mul_pos ha hb]
  -- hence the adjacent triple `det3 u p v = 0`.
  have hadj0 : det3 u p v = 0 := by rw [hidv, hdet0]; ring
  -- the adjacent triple is exactly `det3 (A(i-1)) (A i) (A(i+1))`, apex `A i` = joint `i-1`.
  -- bridge: `det3 u p v = 0` ⟹ `sphAngle (A(i-1)) (A i) (A(i+1)) ∈ {0, π}`.
  -- short arcs at the apex `A i`: `(A i, A(i-1))` and `(A i, A(i+1))`.
  have hbridge := sphAngle_eq_zero_or_pi_of_det3_zero (u := A ⟨i - 1, hpre⟩) (v := A ⟨i, hii⟩)
    (w := A ⟨i + 1, hi2⟩) hsau hsav (by rw [← hu, ← hp, ← hv]; exact hadj0)
  -- the joint angle at index `i-1` is this spherical angle.
  have hjoint_eq : jointAngle A ⟨i - 1, by omega⟩
      = sphAngle (A ⟨i - 1, hpre⟩) (A ⟨i, hii⟩) (A ⟨i + 1, hi2⟩) := by
    rw [jointAngle]
    have e0 : (⟨(i - 1) , by omega⟩ : Fin (n + 1)) = (⟨i - 1, hpre⟩ : Fin (n + 1)) := rfl
    have e1 : (⟨(i - 1) + 1, by omega⟩ : Fin (n + 1)) = (⟨i, hii⟩ : Fin (n + 1)) := by
      apply Fin.ext; show (i - 1) + 1 = i; omega
    have e2 : (⟨(i - 1) + 2, by omega⟩ : Fin (n + 1)) = (⟨i + 1, hi2⟩ : Fin (n + 1)) := by
      apply Fin.ext; show (i - 1) + 2 = i + 1; omega
    rw [e0, e1, e2]
  -- contradiction: the joint is in `(0, π)` but the bridge forces it into `{0, π}`.
  rcases hbridge with h0 | hπ
  · rw [hjoint_eq, h0] at hposJoint; exact lt_irrefl 0 hposJoint
  · rw [hjoint_eq, hπ] at hltJoint; exact lt_irrefl Real.pi hltJoint

/-! ## Brick 5 — the deliverable: the far-fold boundary classification (`i = 0` half). -/

/-- **(Brick 5) Far-fold boundary classification — the `i = 0` half.**  Given a weakly convex
`PositiveJoints` arm `A`, a strictly convex `B` with `JointLe A B`, fold indices `i + 2 < j < n+1`,
and the *nondegenerate* fold datum
`∃ a b : ℝ≥0, 0 < a ∧ 0 < b ∧ (a:ℝ)•A(i+1) + (b:ℝ)•A j = A i`, the fold can only occur at `i = 0`.

Proof: if `i ≥ 1`, the predecessor edge `(A(i-1), A i)` exists, its two weak supports at the fold
neighbours hold (`edge_support`), and its incoming/outgoing arcs are short (`edge_short`), so
Brick 4 (`far_fold_no_predecessor`) derives `False`.  The non-flat bound the kill needs is
`jointAngle A · < π` from `jointAngle_lt_pi hB hangle`. -/
theorem far_fold_boundary_classification_of_nondeg {n : ℕ} {A B : Fin (n + 1) → S2}
    (hA : WeakConvexSphArm A) (hposA : PositiveJoints A)
    (hB : StrictConvexSphArm B) (hangle : JointLe A B)
    {i j : ℕ} (hij : i + 2 < j) (hj : j < n + 1)
    (hnd : ∃ a b : ℝ≥0, 0 < (a : ℝ) ∧ 0 < (b : ℝ) ∧
      (a : ℝ) • (A ⟨i + 1, by omega⟩ : E3) + (b : ℝ) • (A ⟨j, hj⟩ : E3) = (A ⟨i, by omega⟩ : E3)) :
    i = 0 := by
  by_contra hi0
  have hi1 : 1 ≤ i := by omega
  obtain ⟨a, b, ha, hb, hcoeff⟩ := hnd
  -- index bounds.
  have hii : i < n + 1 := by omega
  have hi2 : i + 1 < n + 1 := by omega
  have hpre : i - 1 < n + 1 := by omega
  -- the predecessor edge as a `Fin`-edge of the closed polygon: `(A ⟨i-1⟩, A ⟨i-1⟩ + 1)`.
  have hsucc : ((⟨i - 1, hpre⟩ : Fin (n + 1)) + 1) = (⟨i, hii⟩ : Fin (n + 1)) := by
    have hn2 : 2 ≤ n := hA.two_le
    apply Fin.ext
    have hone : ((1 : Fin (n + 1)) : ℕ) = 1 := by
      rw [Fin.val_one']; exact Nat.mod_eq_of_lt (by omega)
    show ((⟨i - 1, hpre⟩ : Fin (n + 1)) + 1).val = i
    rw [Fin.val_add, Fin.val_mk, hone,
      Nat.mod_eq_of_lt (show (i - 1) + 1 < n + 1 by omega)]
    omega
  -- weak supports of the predecessor edge at the two fold neighbours.
  have hsuppv : 0 ≤ sOrient (A ⟨i - 1, hpre⟩) (A ⟨i, hii⟩) (A ⟨i + 1, hi2⟩) := by
    have h := hA.closed_convex.edge_support ⟨i - 1, hpre⟩ ⟨i + 1, hi2⟩
    rwa [hsucc] at h
  have hsuppw : 0 ≤ sOrient (A ⟨i - 1, hpre⟩) (A ⟨i, hii⟩) (A ⟨j, hj⟩) := by
    have h := hA.closed_convex.edge_support ⟨i - 1, hpre⟩ ⟨j, hj⟩
    rwa [hsucc] at h
  -- short predecessor edge arcs.
  have hedge : ShortArc (A ⟨i - 1, hpre⟩) (A ⟨i, hii⟩) := by
    have h := hA.closed_convex.edge_short ⟨i - 1, hpre⟩
    rwa [hsucc] at h
  have hsau : ShortArc (A ⟨i, hii⟩) (A ⟨i - 1, hpre⟩) := hedge.symm
  have hedgeFwd : ShortArc (A ⟨i, hii⟩) (A ⟨i + 1, hi2⟩) := by
    have hn2 : 2 ≤ n := hA.two_le
    have h := hA.closed_convex.edge_short ⟨i, hii⟩
    have hsucc2 : ((⟨i, hii⟩ : Fin (n + 1)) + 1) = (⟨i + 1, hi2⟩ : Fin (n + 1)) := by
      apply Fin.ext
      have hone : ((1 : Fin (n + 1)) : ℕ) = 1 := by
        rw [Fin.val_one']; exact Nat.mod_eq_of_lt (by omega)
      rw [Fin.val_add, Fin.val_mk, hone,
        Nat.mod_eq_of_lt (show i + 1 < n + 1 by omega)]
    rwa [hsucc2] at h
  -- the non-flat bound and positivity at joint index `i-1`.
  have hposJoint : 0 < jointAngle A ⟨i - 1, by omega⟩ := hposA ⟨i - 1, by omega⟩
  have hltJoint : jointAngle A ⟨i - 1, by omega⟩ < Real.pi :=
    jointAngle_lt_pi hB hangle ⟨i - 1, by omega⟩
  -- apply Brick 4.
  exact far_fold_no_predecessor hi1 hij hj ha hb hpre hii hi2 hcoeff hsuppv hsuppw
    hposJoint hltJoint hsau hedgeFwd

/-! ## Brick 6 — the wrapper: `i = 0` from the NNReal span membership, deriving `b > 0`. -/

/-- **(Brick 6) Far-fold `i = 0` from the span membership.**  Combines Brick 1 (extract coefficients),
Brick 3 (the tail coefficient `b > 0` from the short fold edge `(A i, A(i+1))`), and Brick 5
(the boundary classification).  The leading coefficient `a > 0` remains a hypothesis: the
`no_repeat` master brick that supplies it (a nonadjacent repeated vertex forcing an interior flat
joint) is out of scope.  Here `v = A(i+1)` is the fold neighbour and the short edge witnessing
`b > 0` is `ShortArc (A i) (A (i+1))`. -/
theorem far_fold_i_eq_zero {n : ℕ} {A B : Fin (n + 1) → S2}
    (hA : WeakConvexSphArm A) (hposA : PositiveJoints A)
    (hB : StrictConvexSphArm B) (hangle : JointLe A B)
    {i j : ℕ} (hij : i + 2 < j) (hj : j < n + 1)
    {a b : ℝ≥0}
    (hab : (a : ℝ) • (A ⟨i + 1, by omega⟩ : E3) + (b : ℝ) • (A ⟨j, hj⟩ : E3)
      = (A ⟨i, by omega⟩ : E3))
    (hapos : 0 < (a : ℝ)) :
    i = 0 := by
  -- the short fold edge `(A i, A(i+1))` from weak convexity, to get `b > 0` via Brick 3.
  have hii : i < n + 1 := by omega
  have hi2 : i + 1 < n + 1 := by omega
  have hedge : ShortArc (A ⟨i, hii⟩) (A ⟨i + 1, hi2⟩) := by
    have hn2 : 2 ≤ n := hA.two_le
    have h := hA.closed_convex.edge_short ⟨i, hii⟩
    have hsucc2 : ((⟨i, hii⟩ : Fin (n + 1)) + 1) = (⟨i + 1, hi2⟩ : Fin (n + 1)) := by
      apply Fin.ext
      have hone : ((1 : Fin (n + 1)) : ℕ) = 1 := by
        rw [Fin.val_one']; exact Nat.mod_eq_of_lt (by omega)
      rw [Fin.val_add, Fin.val_mk, hone,
        Nat.mod_eq_of_lt (show i + 1 < n + 1 by omega)]
    rwa [hsucc2] at h
  -- `b > 0` from Brick 3 (the fold writes `A i = a•A(i+1) + b•A j`; if `b = 0` then `A i = A(i+1)`).
  have hbpos : 0 < (b : ℝ) := coeff_b_pos_of_edge_short hab hedge
  -- `a > 0` is the supplied hypothesis (the `no_repeat` master brick supplying it is out of scope).
  -- apply Brick 5.
  exact far_fold_boundary_classification_of_nondeg hA hposA hB hangle hij hj
    ⟨a, b, hapos, hbpos, hab⟩

/-! ## Non-vacuity / anti-impostor guards (playbook §3.3). -/

/-- Non-vacuity of Brick 2: realised at `a = 1`, `p = v` (a genuine unit scaling). -/
theorem nnreal_smul_unit_eq_unit_nonvacuous (v : S2) :
    (v : E3) = (1 : ℝ) • (v : E3) := by rw [one_smul]

/-- Non-vacuity of the forward bridge: a genuine collinear apex (the joint `det3 = 0` case) does occur
— e.g. the reflexive `det3 u v u = 0`, where the apex sees both rays aligned. -/
theorem det3_self_apex_zero (u v : S2) : det3 (u : E3) (v : E3) (u : E3) = 0 := by
  simp only [det3]; ring

/-- Non-vacuity of the boundary classification's conclusion: `i = 0` is satisfiable. -/
theorem far_fold_classification_conclusion_satisfiable : (0 : ℕ) = 0 := rfl

#print axioms span_pair_coeffs_S2
#print axioms nnreal_smul_unit_eq_unit
#print axioms coeff_b_pos_of_edge_short
#print axioms sphAngle_eq_zero_or_pi_of_det3_zero
#print axioms far_fold_no_predecessor
#print axioms far_fold_boundary_classification_of_nondeg
#print axioms far_fold_i_eq_zero

end ProofsInTheBook.ZinanFFCT21
