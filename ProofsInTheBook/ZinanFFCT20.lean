import ProofsInTheBook.ZinanFFCT19
import ProofsInTheBook.SphericalSZClose
import ProofsInTheBook.SphericalOpeningOutcome
import ProofsInTheBook.ZinanFFCT18

/-!
# `ZinanFFCT20` — the Chapter 13 A2 bricks: the oriented tangent action of the opening rotation

This module supplies the two A2 prerequisites isolated by the substrate design
(`HANDOFF/design-rounds/ch13-A2-substrate.md`) plus their packaging:

* **Brick 1** `tangentTo_axis_rotS2` — the tangent at the axis `a` toward the rotated point
  `rotS2 a δ p` is the rotation of the tangent toward `p`.  This is the special case of the general
  `tangentTo_rotS2` at base point `= a` (the axis is fixed by `rotS2`).
* **Brick 2** `sphAngle_axis_rotS2_eq_add_of_oriented` — the **oriented angle-addition formula**:
  under the orientation hypothesis `⟪u, a × w⟫ = −‖u‖‖w‖ sin γ` (the hidden hypothesis of the
  substrate), opening the joint at the axis `a` by `δ` *adds* `δ` to the joint angle (within the
  branch `[0, π]`).  The cosine of the opened angle is computed by the planar-rotation law
  `inner_rot_tangent`, then collapsed by the cosine angle-addition identity; both angles lie in
  `[0, π]`, so equality follows from injectivity of `cos` there.
* **Brick 3** `OpeningDirectionPositive` — the orientation hypothesis as a named predicate at the
  joint's two tangents.
* **Brick 4** `openedInteriorJointAngle_eq_add` — the joint-angle additivity of the opening on the
  interior opened joint, obtained by instantiating Brick 2 at the joint's tangents.
* **Brick 5** `openTail_positiveJoints` — `PositiveJoints` is preserved by `openTail` at admissible
  `δ ≥ 0` (off-axis joints unchanged; the opened joint becomes `γ + δ ≥ γ > 0`).

No `sorry`, `axiom`, `admit`, or `native_decide`.
-/

noncomputable section

open scoped RealInnerProductSpace
open ProofsInTheBook.SphericalKernel ProofsInTheBook.SphericalArm
open ProofsInTheBook.SphericalRotation
open ProofsInTheBook.SphericalSZFinal
open ProofsInTheBook.SphericalSZClose
open ProofsInTheBook.SphericalOpeningOutcome
open ProofsInTheBook.SphericalSZInduction
open ProofsInTheBook.ZinanFFCT18

namespace ProofsInTheBook.ZinanFFCT20

/-! ## Brick 1 — the tangent action at the axis. -/

/-- **Brick 1.**  At the rotation axis `a`, the tangent toward the rotated point `rotS2 a δ p` is the
rotation of the tangent toward `p`.  This is `tangentTo_rotS2` at base point `= a`, using that the
axis is fixed (`rotS2 a δ a = a`). -/
theorem tangentTo_axis_rotS2 (a p : S2) (δ : ℝ) :
    tangentTo a (rotS2 a δ p) = rot (a : E3) δ (tangentTo a p) := by
  -- The axis is fixed by `rotS2`: `rotS2 a δ a = a`.
  have hfix : rotS2 a δ a = a := by
    apply S2.ext
    rw [rotS2_coe, rot_axis a.2]
  -- rewrite the LEFT base `a` as `rotS2 a δ a`, then apply the general tangent action.
  calc tangentTo a (rotS2 a δ p)
      = tangentTo (rotS2 a δ a) (rotS2 a δ p) := by rw [hfix]
    _ = rot (a : E3) δ (tangentTo a p) := tangentTo_rotS2 a δ a p

/-! ## Brick 3 — the orientation predicate.

The opening rotation `rotS2 a δ` rotates the outgoing tangent `w = tangentTo a q` by `δ` in the
right-hand sense about the axis `a` (`w` moves toward `a × w` for `δ > 0`).  For the *opened* joint
angle (measured from the fixed incoming tangent `u = tangentTo a p`) to be `γ + δ` rather than
`γ − δ`, the planar orientation of the pair `(u, w)` must be the negative one, i.e. the signed area
`⟪u, a × w⟫` must equal `−‖u‖‖w‖ sin γ`.  This is exactly the hidden hypothesis isolated by the
substrate; we name it `OpeningDirectionPositive`. -/

/-- **Brick 3.**  The orientation hypothesis at the joint `k`'s two tangents:
`⟪u, a × w⟫ = −‖u‖‖w‖ sin γ`, with `u`/`w` the incoming/outgoing tangents at the axis
`a = A (openingAxis k)` and `γ = jointAngle A k`. -/
def OpeningDirectionPositive {n : ℕ} (A : Fin (n + 1) → S2) (k : Fin (n - 1)) : Prop :=
  (⟪tangentTo (A (openingAxis k)) (jointPrev A k),
      cross (A (openingAxis k) : E3) (tangentTo (A (openingAxis k)) (jointNext A k))⟫ : ℝ)
    = -‖tangentTo (A (openingAxis k)) (jointPrev A k)‖
        * ‖tangentTo (A (openingAxis k)) (jointNext A k)‖
        * Real.sin (jointAngle A k)

/-! ## Brick 2 — the oriented angle-addition formula. -/

/-- **Brick 2.**  *Oriented angle addition for the opening rotation.*  Let `a` be the axis, `p` the
fixed incoming neighbour, `q` the outgoing neighbour to be rotated, and `γ = sphAngle p a q` the
original joint angle.  Under the orientation hypothesis
`⟪tangentTo a p, a × tangentTo a q⟫ = −‖·‖‖·‖ sin γ` and the branch control `0 ≤ γ + δ ≤ π`,

`sphAngle p a (rotS2 a δ q) = γ + δ`.

The short-arc hypotheses guarantee the two tangents are nonzero (so the cosine quotients are valid);
the proof computes `cos (sphAngle p a (rotS2 a δ q))` by the planar-rotation law `inner_rot_tangent`,
collapses it to `cos (γ + δ)` by the cosine addition identity, and concludes by injectivity of
`cos` on `[0, π]`. -/
theorem sphAngle_axis_rotS2_eq_add_of_oriented {a p q : S2} {δ γ : ℝ}
    (hp : ShortArc a p) (hq : ShortArc a q)
    (hγ : γ = sphAngle p a q)
    (horient : (⟪tangentTo a p, cross (a : E3) (tangentTo a q)⟫ : ℝ)
      = -‖tangentTo a p‖ * ‖tangentTo a q‖ * Real.sin γ)
    (hbranch0 : 0 ≤ γ + δ) (hbranchπ : γ + δ ≤ Real.pi) :
    sphAngle p a (rotS2 a δ q) = γ + δ := by
  -- Abbreviations for the two tangents.
  set u : E3 := tangentTo a p with hu
  set w : E3 := tangentTo a q with hw
  -- Both tangents are nonzero (short arcs).
  have hu0 : u ≠ 0 := (tangentTo_ne_zero_iff a p).2 hp
  have hw0 : w ≠ 0 := (tangentTo_ne_zero_iff a q).2 hq
  have hnu : (0 : ℝ) < ‖u‖ := norm_pos_iff.2 hu0
  have hnw : (0 : ℝ) < ‖w‖ := norm_pos_iff.2 hw0
  -- The outgoing tangent is orthogonal to the axis.
  have horth : (⟪w, (a : E3)⟫ : ℝ) = 0 := tangentTo_orthogonal a q
  -- `γ = angle u w`, so `⟪u, w⟫ = cos γ * (‖u‖ * ‖w‖)`.
  have hangle_uw : γ = InnerProductGeometry.angle u w := by
    rw [hγ, sphAngle]
  have hinner_uw : (⟪u, w⟫ : ℝ) = Real.cos γ * (‖u‖ * ‖w‖) := by
    have h := InnerProductGeometry.cos_angle_mul_norm_mul_norm u w
    rw [← hangle_uw] at h; linarith [h]
  -- LHS angle is `angle u (rot a δ w)` after Brick 1.
  have hLHS : sphAngle p a (rotS2 a δ q) = InnerProductGeometry.angle u (rot (a : E3) δ w) := by
    rw [sphAngle]
    congr 1
    rw [hw]; exact tangentTo_axis_rotS2 a q δ
  -- Compute `⟪u, rot a δ w⟫` by the planar rotation law and substitute.
  have hinner_rot : (⟪u, rot (a : E3) δ w⟫ : ℝ)
      = Real.cos (γ + δ) * (‖u‖ * ‖w‖) := by
    rw [inner_rot_tangent (a : E3) δ horth, hinner_uw, horient, Real.cos_add]
    ring
  -- Norms: `‖rot a δ w‖ = ‖w‖`.
  have hnorm_rot : ‖rot (a : E3) δ w‖ = ‖w‖ := norm_rot a.2 δ w
  -- `cos (LHS) = cos (γ + δ)`.
  have hcosLHS : Real.cos (sphAngle p a (rotS2 a δ q)) = Real.cos (γ + δ) := by
    rw [hLHS, InnerProductGeometry.cos_angle, hnorm_rot, hinner_rot]
    field_simp
  -- Both angles lie in `[0, π]`; conclude by injectivity of `cos`.
  have hmem1 : sphAngle p a (rotS2 a δ q) ∈ Set.Icc (0 : ℝ) Real.pi :=
    ⟨sphAngle_nonneg _ _ _, sphAngle_le_pi _ _ _⟩
  have hmem2 : γ + δ ∈ Set.Icc (0 : ℝ) Real.pi := ⟨hbranch0, hbranchπ⟩
  exact Real.injOn_cos.eq_iff hmem1 hmem2 |>.1 hcosLHS

/-! ## Brick 4 — the opened interior joint angle adds `δ`. -/

/-- **Brick 4.**  The opened interior joint angle is the original plus `δ`.  From the short-arc
hypotheses at the axis (the two arm edges meeting the apex), the orientation hypothesis
`OpeningDirectionPositive`, and the branch control `0 ≤ δ`, `jointAngle A k + δ ≤ π`:

`openedInteriorJointAngle A k δ = jointAngle A k + δ`.

This instantiates Brick 2 at `a = A (openingAxis k)`, `p = jointPrev A k`, `q = jointNext A k`,
`γ = jointAngle A k`. -/
theorem openedInteriorJointAngle_eq_add {n : ℕ} {A : Fin (n + 1) → S2} {k : Fin (n - 1)} {δ : ℝ}
    (hka : ShortArc (A (openingAxis k)) (jointPrev A k))
    (hkt : ShortArc (A (openingAxis k)) (jointNext A k))
    (hApos : OpeningDirectionPositive A k)
    (hδ : 0 ≤ δ) (hbranch : jointAngle A k + δ ≤ Real.pi) :
    openedInteriorJointAngle A k δ = jointAngle A k + δ := by
  -- `jointAngle A k = sphAngle (jointPrev A k) (A (openingAxis k)) (jointNext A k)`.
  have hγ : jointAngle A k
      = sphAngle (jointPrev A k) (A (openingAxis k)) (jointNext A k) := by
    simp only [jointAngle, jointPrev, jointNext, openingAxis]
  -- `jointAngle A k ≥ 0` (spherical angles are nonnegative).
  have hγnn : 0 ≤ jointAngle A k := by
    rw [hγ]; exact sphAngle_nonneg _ _ _
  rw [openedInteriorJointAngle]
  exact sphAngle_axis_rotS2_eq_add_of_oriented (a := A (openingAxis k))
    (p := jointPrev A k) (q := jointNext A k) (δ := δ) (γ := jointAngle A k) hka hkt hγ
    hApos (add_nonneg hγnn hδ) hbranch

/-! ## Brick 5 — `PositiveJoints` is preserved by `openTail` at admissible `δ`.

Opening the deficient joint `k` about its apex `K = openingAxis k` by `δ ≥ 0`:

* every off-axis joint `r ≠ k` is *unchanged* (`jointAngle_openTail_eq_of_ne`), hence stays positive
  from `PositiveJoints A`;
* the opened joint `k` becomes `jointAngle A k + δ` (Brick 4 via
  `jointAngle_openTail_eq_openedInterior`), which is `≥ jointAngle A k > 0` since `δ ≥ 0`.

Both cases keep the joint strictly positive, so `PositiveJoints (openTail A K δ)` holds. -/
theorem openTail_positiveJoints {n : ℕ} {A : Fin (n + 1) → S2} {k : Fin (n - 1)} {δ : ℝ}
    (hpos : PositiveJoints A)
    (hka : ShortArc (A (openingAxis k)) (jointPrev A k))
    (hkt : ShortArc (A (openingAxis k)) (jointNext A k))
    (hApos : OpeningDirectionPositive A k)
    (hδ : 0 ≤ δ) (hbranch : jointAngle A k + δ ≤ Real.pi) :
    PositiveJoints (openTail A (openingAxis k) δ) := by
  intro r
  by_cases hr : r = k
  · -- the opened joint: `jointAngle = jointAngle A k + δ ≥ jointAngle A k > 0`.
    subst hr
    rw [jointAngle_openTail_eq_openedInterior A r δ,
      openedInteriorJointAngle_eq_add hka hkt hApos hδ hbranch]
    have := hpos r
    linarith [this, hδ]
  · -- off-axis joint: unchanged, stays positive.
    rw [jointAngle_openTail_eq_of_ne A k δ hr]
    exact hpos r

end ProofsInTheBook.ZinanFFCT20
