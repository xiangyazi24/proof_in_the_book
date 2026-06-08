import ProofsInTheBook.TetDihedral

/-!
# Spherical kernel (Chapter 13, Cauchy rigidity — extrinsic S² layer)

This module builds the *extrinsic* spherical kernel for the Cauchy rigidity chapter: the unit
sphere `S²` is modelled as the unit vectors of `E3 = EuclideanSpace ℝ (Fin 3)`, spherical distance is
`arccos` of the inner product, and the spherical angle at a vertex is the (unoriented) angle between
the tangent-plane projections of the two neighbours — reusing the `projOut` machinery of
`TetDihedral.lean`.

## Contents

### Layer A — sphere basics
* `S2`, `sInner`, `sDist`, `ShortArc`.
* `sInner_mem_Icc`, `cos_sDist`, `sDist_nonneg`, `sDist_le_pi`, `sin_sDist_nonneg`.
* `sDist_pos_of_ne`, `sDist_lt_pi_of_not_antipodal`, `sDist_eq_zero_iff`, `sDist_comm`.

### Layer B — tangent projections and the spherical angle
* `tangentTo`, `sphAngle`.
* `tangentTo_orthogonal`, `decompose_unit_along_tangent`, `tangentTo_ne_zero_iff`,
  `norm_tangentTo`, `sphAngle_comm`.

### Layer C — the spherical triangle kernel
* `spherical_cosine_rule` — `cos(sDist a c) = cos(ab)cos(bc) + sin(ab)sin(bc)cos(γ)`.
* `spherical_hinge_mono`, `spherical_hinge_strict` — law-of-cosines monotonicity (the `n = 3`
  spherical-arm base).

### Layer D — convex spherical arms (structure + arm-lemma statement)
* `det3`, `sOrient`, `StrictConvexSphPolygon`, `StrictConvexSphArm`.
* `sideLen`, `jointAngle`.
* `spherical_arm_mono`, `spherical_arm_mono_strict` — the spherical arm lemma, stated; the
  Schoenberg–Zaremba hinge induction (the single hardest lemma of the chapter) is isolated as the
  named next-round target `spherical_SZ_opening_chain`.

No `sorry`, `axiom`, or `admit`.
-/

noncomputable section

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000

open scoped RealInnerProductSpace
open ProofsInTheBook.TetPearls ProofsInTheBook.TetDihedral

namespace ProofsInTheBook.SphericalKernel

/-! ## Layer A: extrinsic sphere basics -/

/-- `E3` is the ambient Euclidean 3-space `EuclideanSpace ℝ (Fin 3)` (an alias for `Pt3`). -/
abbrev E3 : Type := Pt3

/-- The unit sphere `S²`, as the unit vectors of `E3`. -/
def S2 : Type := {x : E3 // ‖x‖ = 1}

instance : Coe S2 E3 := ⟨Subtype.val⟩

@[simp] theorem S2.norm_coe (p : S2) : ‖(p : E3)‖ = 1 := p.2

/-- `⟪p,p⟫ = 1` for a point of `S²`. -/
@[simp] theorem S2.inner_self (p : S2) : (⟪(p : E3), (p : E3)⟫ : ℝ) = 1 := by
  rw [real_inner_self_eq_norm_sq, p.2]; norm_num

theorem S2.coe_injective : Function.Injective (fun p : S2 => (p : E3)) :=
  Subtype.val_injective

@[ext] theorem S2.ext {p q : S2} (h : (p : E3) = (q : E3)) : p = q :=
  S2.coe_injective h

/-- The spherical inner product `⟪p,q⟫`. -/
def sInner (p q : S2) : ℝ := ⟪(p : E3), (q : E3)⟫

theorem sInner_comm (p q : S2) : sInner p q = sInner q p := real_inner_comm _ _

@[simp] theorem sInner_self (p : S2) : sInner p p = 1 := S2.inner_self p

/-- The inner product of two unit vectors lies in `[-1,1]` (Cauchy–Schwarz). -/
theorem sInner_mem_Icc (p q : S2) : sInner p q ∈ Set.Icc (-1 : ℝ) 1 := by
  have h := abs_real_inner_le_norm (p : E3) (q : E3)
  rw [p.2, q.2, mul_one] at h
  rw [Set.mem_Icc, ← abs_le]
  exact h

theorem neg_one_le_sInner (p q : S2) : -1 ≤ sInner p q := (sInner_mem_Icc p q).1
theorem sInner_le_one (p q : S2) : sInner p q ≤ 1 := (sInner_mem_Icc p q).2

/-- The spherical distance `arccos ⟪p,q⟫ ∈ [0,π]`. -/
def sDist (p q : S2) : ℝ := Real.arccos (sInner p q)

theorem sDist_comm (p q : S2) : sDist p q = sDist q p := by
  rw [sDist, sDist, sInner_comm]

theorem sDist_nonneg (p q : S2) : 0 ≤ sDist p q := Real.arccos_nonneg _

theorem sDist_le_pi (p q : S2) : sDist p q ≤ Real.pi := Real.arccos_le_pi _

/-- `cos (sDist p q) = ⟪p,q⟫`. -/
@[simp] theorem cos_sDist (p q : S2) : Real.cos (sDist p q) = sInner p q :=
  Real.cos_arccos (neg_one_le_sInner p q) (sInner_le_one p q)

/-- `sin (sDist p q) ≥ 0` (distance lies in `[0,π]`). -/
theorem sin_sDist_nonneg (p q : S2) : 0 ≤ Real.sin (sDist p q) :=
  Real.sin_nonneg_of_nonneg_of_le_pi (sDist_nonneg p q) (sDist_le_pi p q)

/-- `sin (sDist p q)² = 1 - ⟪p,q⟫²`. -/
theorem sin_sq_sDist (p q : S2) :
    Real.sin (sDist p q) ^ 2 = 1 - sInner p q ^ 2 := by
  have h := Real.sin_sq_add_cos_sq (sDist p q)
  rw [cos_sDist] at h
  linarith

/-- `sDist p q = 0 ↔ p = q` (for unit vectors). -/
theorem sDist_eq_zero_iff {p q : S2} : sDist p q = 0 ↔ p = q := by
  constructor
  · intro h
    -- arccos ⟪p,q⟫ = 0 ⟹ ⟪p,q⟫ = 1 ⟹ ‖p - q‖² = 0
    have hcos : sInner p q = 1 := by
      have := congrArg Real.cos h
      rwa [cos_sDist, Real.cos_zero] at this
    have hpq : (⟪(p : E3), (q : E3)⟫ : ℝ) = 1 := hcos
    have hqp : (⟪(q : E3), (p : E3)⟫ : ℝ) = 1 := by rw [real_inner_comm]; exact hpq
    have hnorm : ‖(p : E3) - (q : E3)‖ ^ 2 = 0 := by
      rw [← real_inner_self_eq_norm_sq, inner_sub_left, inner_sub_right, inner_sub_right]
      rw [S2.inner_self, S2.inner_self, hpq, hqp]; ring
    have : (p : E3) - (q : E3) = 0 := by
      have := pow_eq_zero_iff (n := 2) (by norm_num) |>.mp hnorm
      exact norm_eq_zero.mp this
    exact S2.ext (sub_eq_zero.mp this)
  · rintro rfl; rw [sDist, sInner_self, Real.arccos_one]

/-- For unit vectors, the spherical distance is positive iff the points differ. -/
theorem sDist_pos_of_ne {p q : S2} (h : p ≠ q) : 0 < sDist p q :=
  lt_of_le_of_ne (sDist_nonneg p q) (fun he => h (sDist_eq_zero_iff.mp he.symm))

/-- The spherical distance is `< π` unless the points are antipodal. -/
theorem sDist_lt_pi_of_not_antipodal {p q : S2} (h : (p : E3) ≠ -(q : E3)) :
    sDist p q < Real.pi := by
  rw [sDist, Real.arccos_lt_pi]
  -- ⟪p,q⟫ = -1 would force p = -q.
  rcases lt_or_eq_of_le (neg_one_le_sInner p q) with hlt | heq
  · exact hlt
  · exfalso; apply h
    -- ⟪p,q⟫ = -1 ⟹ ‖p + q‖² = 0 ⟹ p = -q
    have hcos : sInner p q = -1 := heq.symm
    have hnorm : ‖(p : E3) + (q : E3)‖ ^ 2 = 0 := by
      rw [← real_inner_self_eq_norm_sq, inner_add_left, inner_add_right, inner_add_right]
      rw [S2.inner_self, S2.inner_self]
      have h1 : (⟪(p : E3), (q : E3)⟫ : ℝ) = -1 := hcos
      have h2 : (⟪(q : E3), (p : E3)⟫ : ℝ) = -1 := by rw [real_inner_comm]; exact h1
      rw [h1, h2]; ring
    have hpq : (p : E3) + (q : E3) = 0 := by
      have := pow_eq_zero_iff (n := 2) (by norm_num) |>.mp hnorm
      exact norm_eq_zero.mp this
    exact eq_neg_of_add_eq_zero_left hpq

/-- `ShortArc p q`: the points are neither equal nor antipodal, so the shorter great-circle arc is
well-defined and the tangent direction is nonzero. -/
def ShortArc (p q : S2) : Prop := p ≠ q ∧ (p : E3) ≠ -(q : E3)

theorem ShortArc.sDist_pos {p q : S2} (h : ShortArc p q) : 0 < sDist p q :=
  sDist_pos_of_ne h.1

theorem ShortArc.sDist_lt_pi {p q : S2} (h : ShortArc p q) : sDist p q < Real.pi :=
  sDist_lt_pi_of_not_antipodal h.2

theorem ShortArc.symm {p q : S2} (h : ShortArc p q) : ShortArc q p :=
  ⟨h.1.symm, by
    intro he
    apply h.2
    rw [he]; rw [neg_neg]⟩

/-- For a short arc, `sin (sDist p q) > 0`. -/
theorem ShortArc.sin_sDist_pos {p q : S2} (h : ShortArc p q) :
    0 < Real.sin (sDist p q) :=
  Real.sin_pos_of_pos_of_lt_pi h.sDist_pos h.sDist_lt_pi

/-! ## Layer B: tangent projections and the spherical angle

For a base point `p` and neighbour `q`, the tangent direction at `p` toward `q` is the component of
`q` orthogonal to `p`, i.e. `projOut p q` from `TetDihedral`.  Because `p` is a unit vector,
`projOut (p:E3) (q:E3) = (q:E3) - ⟪q,p⟫ • (p:E3)`. -/

/-- The tangent vector at `p` pointing toward `q` along the shorter great circle. -/
def tangentTo (p q : S2) : E3 := projOut (p : E3) (q : E3)

/-- `projOut (p:E3)` with `p` a unit vector divides by `⟪p,p⟫ = 1`, so the scalar is just `⟪q,p⟫`. -/
theorem tangentTo_eq (p q : S2) :
    tangentTo p q = (q : E3) - (sInner q p) • (p : E3) := by
  rw [tangentTo, projOut, S2.inner_self, div_one, sInner]

/-- The tangent vector is orthogonal to the base point. -/
theorem tangentTo_orthogonal (p q : S2) : (⟪tangentTo p q, (p : E3)⟫ : ℝ) = 0 := by
  have hp : (p : E3) ≠ 0 := by
    intro h; have := p.2; rw [h, norm_zero] at this; norm_num at this
  exact inner_projOut_right (p : E3) (q : E3) hp

/-- **Decomposition of a unit vector along the tangent.**  Writes `q` as its component along `p`
(coefficient `cos (sDist p q)`) plus its tangential component. -/
theorem decompose_unit_along_tangent (p q : S2) :
    (q : E3) = (Real.cos (sDist p q)) • (p : E3) + tangentTo p q := by
  rw [tangentTo_eq, cos_sDist, sInner_comm]; abel

/-- `‖tangentTo p q‖² = sin (sDist p q)²` (Pythagoras: `q = cos·p + tangent`, with the two parts
orthogonal and `p` a unit vector). -/
theorem norm_sq_tangentTo (p q : S2) :
    ‖tangentTo p q‖ ^ 2 = Real.sin (sDist p q) ^ 2 := by
  -- ‖tangent‖² = ⟪q,q⟫ - ⟪q,p⟫²  (projection onto pᗮ), and ⟪q,q⟫ = 1, ⟪q,p⟫ = cos.
  have hp : (p : E3) ≠ 0 := by
    intro h; have := p.2; rw [h, norm_zero] at this; norm_num at this
  have h := inner_projOut_projOut (p : E3) (q : E3) (q : E3) hp
  show ‖projOut (p : E3) (q : E3)‖ ^ 2 = _
  rw [← real_inner_self_eq_norm_sq, h]
  rw [S2.inner_self, S2.inner_self]
  -- ⟪q,p⟫ = sInner q p = cos (sDist q p) = cos (sDist p q)
  have hqp : (⟪(q : E3), (p : E3)⟫ : ℝ) = Real.cos (sDist p q) := by
    have : Real.cos (sDist p q) = sInner p q := cos_sDist p q
    rw [this, sInner_comm]; rfl
  rw [hqp, div_one]
  -- 1 - cos² = sin²
  have := Real.sin_sq_add_cos_sq (sDist p q)
  nlinarith [this]

/-- `‖tangentTo p q‖ = sin (sDist p q)` (the spherical sine; both sides are nonnegative). -/
theorem norm_tangentTo (p q : S2) :
    ‖tangentTo p q‖ = Real.sin (sDist p q) := by
  have h := norm_sq_tangentTo p q
  have hnn1 : (0 : ℝ) ≤ ‖tangentTo p q‖ := norm_nonneg _
  have hnn2 : (0 : ℝ) ≤ Real.sin (sDist p q) := sin_sDist_nonneg p q
  nlinarith [h, hnn1, hnn2]

/-- `tangentTo p q = 0 ↔ p` and `q` are equal or antipodal (i.e. the arc is *not* short). -/
theorem tangentTo_eq_zero_iff (p q : S2) :
    tangentTo p q = 0 ↔ ¬ ShortArc p q := by
  constructor
  · intro h
    -- ‖tangent‖ = 0 ⟹ sin (sDist) = 0 ⟹ sDist ∈ {0, π}.
    have hsin : Real.sin (sDist p q) = 0 := by
      rw [← norm_tangentTo, h, norm_zero]
    -- not a short arc: if it were, sin > 0.
    intro hsa
    exact (ne_of_gt hsa.sin_sDist_pos) hsin
  · intro h
    -- not short arc: p = q or p = -q. Either way tangent = 0.
    rw [ShortArc, not_and_or, not_not, not_not] at h
    rw [tangentTo_eq]
    rcases h with hpq | hpa
    · rw [hpq, sInner_self, one_smul, sub_self]
    · -- p = -q ⟹ q = -p, ⟪q,p⟫ = -1.
      have hqp : (q : E3) = -(p : E3) := by rw [hpa, neg_neg]
      have : sInner q p = -1 := by
        rw [sInner, hqp, inner_neg_left, S2.inner_self]
      rw [this, hqp]; module

theorem tangentTo_ne_zero_iff (p q : S2) :
    tangentTo p q ≠ 0 ↔ ShortArc p q := by
  rw [ne_eq, tangentTo_eq_zero_iff, not_not]

/-- The spherical angle at vertex `v` between neighbours `u` and `w`: the unoriented angle between
the tangent projections of `u` and `w` at `v`. -/
def sphAngle (u v w : S2) : ℝ :=
  InnerProductGeometry.angle (tangentTo v u) (tangentTo v w)

theorem sphAngle_comm (u v w : S2) : sphAngle u v w = sphAngle w v u :=
  InnerProductGeometry.angle_comm _ _

theorem sphAngle_nonneg (u v w : S2) : 0 ≤ sphAngle u v w :=
  InnerProductGeometry.angle_nonneg _ _

theorem sphAngle_le_pi (u v w : S2) : sphAngle u v w ≤ Real.pi :=
  InnerProductGeometry.angle_le_pi _ _

/-! ## Layer C: the spherical triangle kernel -/

/-- The inner product of the two tangent directions at `b` equals
`sin(ab)·sin(bc)·cos γ`, where `γ = sphAngle a b c`. -/
theorem inner_tangent_tangent (a b c : S2) :
    (⟪tangentTo b a, tangentTo b c⟫ : ℝ)
      = Real.sin (sDist a b) * Real.sin (sDist b c) * Real.cos (sphAngle a b c) := by
  have h := InnerProductGeometry.cos_angle_mul_norm_mul_norm (tangentTo b a) (tangentTo b c)
  rw [norm_tangentTo, norm_tangentTo] at h
  -- h : cos γ * (sin(sDist b a) * sin(sDist b c)) = ⟪tan ba, tan bc⟫
  rw [sphAngle]
  rw [show sDist b a = sDist a b from sDist_comm b a] at h
  linarith [h]

/-- **Spherical law of cosines.**  For the angle `γ = sphAngle a b c` at `b`,
`cos (sDist a c) = cos(ab)·cos(bc) + sin(ab)·sin(bc)·cos γ`. -/
theorem spherical_cosine_rule (a b c : S2) :
    Real.cos (sDist a c)
      = Real.cos (sDist a b) * Real.cos (sDist b c)
        + Real.sin (sDist a b) * Real.sin (sDist b c) * Real.cos (sphAngle a b c) := by
  -- cos (sDist a c) = ⟪a,c⟫.
  rw [cos_sDist, sInner]
  -- Decompose a and c along the tangent frame at b.
  have ha : (a : E3) = (Real.cos (sDist b a)) • (b : E3) + tangentTo b a :=
    decompose_unit_along_tangent b a
  have hc : (c : E3) = (Real.cos (sDist b c)) • (b : E3) + tangentTo b c :=
    decompose_unit_along_tangent b c
  -- The cross terms involve ⟪tangent, b⟫ = 0.
  have hta : (⟪tangentTo b a, (b : E3)⟫ : ℝ) = 0 := tangentTo_orthogonal b a
  have htc : (⟪tangentTo b c, (b : E3)⟫ : ℝ) = 0 := tangentTo_orthogonal b c
  have htc' : (⟪(b : E3), tangentTo b c⟫ : ℝ) = 0 := by rw [real_inner_comm]; exact htc
  rw [ha, hc]
  simp only [inner_add_left, inner_add_right, real_inner_smul_left, real_inner_smul_right,
      S2.inner_self, htc', hta, mul_zero, mul_one, add_zero, zero_add]
  rw [inner_tangent_tangent a b c]
  rw [show sDist b a = sDist a b from sDist_comm b a]
  ring

/-- **Law-of-cosines monotonicity (weak).**  With side lengths `a,b ∈ (0,π)` fixed, the opposite
side `c` defined by the spherical cosine rule is monotone increasing in the included angle
`γ ∈ [0,π]`.  This is the `n = 3` base of the spherical arm lemma.

The hypotheses `hc₁`, `hc₂` are *the spherical cosine rule itself* for two configurations sharing
`a, b`; in the geometric application they are supplied by `spherical_cosine_rule`. -/
theorem spherical_hinge_mono
    {a b γ₁ γ₂ c₁ c₂ : ℝ}
    (ha0 : 0 < a) (hapi : a < Real.pi)
    (hb0 : 0 < b) (hbpi : b < Real.pi)
    (hg₁0 : 0 ≤ γ₁)
    (hg₂pi : γ₂ ≤ Real.pi)
    (hγ : γ₁ ≤ γ₂)
    (hc₁ : Real.cos c₁ =
        Real.cos a * Real.cos b + Real.sin a * Real.sin b * Real.cos γ₁)
    (hc₂ : Real.cos c₂ =
        Real.cos a * Real.cos b + Real.sin a * Real.sin b * Real.cos γ₂)
    (hc₁range : 0 ≤ c₁ ∧ c₁ ≤ Real.pi)
    (hc₂range : 0 ≤ c₂ ∧ c₂ ≤ Real.pi) :
    c₁ ≤ c₂ := by
  have hsa : 0 < Real.sin a := Real.sin_pos_of_pos_of_lt_pi ha0 hapi
  have hsb : 0 < Real.sin b := Real.sin_pos_of_pos_of_lt_pi hb0 hbpi
  -- cos is antitone on [0,π]: γ₁ ≤ γ₂ ⟹ cos γ₂ ≤ cos γ₁.
  have hcosγ : Real.cos γ₂ ≤ Real.cos γ₁ :=
    Real.cos_le_cos_of_nonneg_of_le_pi hg₁0 hg₂pi hγ
  -- Therefore cos c₂ ≤ cos c₁.
  have hcosc : Real.cos c₂ ≤ Real.cos c₁ := by
    rw [hc₁, hc₂]
    have : Real.sin a * Real.sin b * Real.cos γ₂ ≤ Real.sin a * Real.sin b * Real.cos γ₁ :=
      mul_le_mul_of_nonneg_left hcosγ (le_of_lt (mul_pos hsa hsb))
    linarith
  -- cos is injective-antitone on [0,π]: cos c₂ ≤ cos c₁ ⟹ c₁ ≤ c₂.
  by_contra hlt
  push_neg at hlt
  have : Real.cos c₁ < Real.cos c₂ :=
    Real.cos_lt_cos_of_nonneg_of_le_pi hc₂range.1 hc₁range.2 hlt
  linarith

/-- **Law-of-cosines monotonicity (strict).**  Strict inequality of included angles gives strict
inequality of opposite sides.  This is the strict `n = 3` base. -/
theorem spherical_hinge_strict
    {a b γ₁ γ₂ c₁ c₂ : ℝ}
    (ha0 : 0 < a) (hapi : a < Real.pi)
    (hb0 : 0 < b) (hbpi : b < Real.pi)
    (hg₁0 : 0 ≤ γ₁)
    (hg₂pi : γ₂ ≤ Real.pi)
    (hγ : γ₁ < γ₂)
    (hc₁ : Real.cos c₁ =
        Real.cos a * Real.cos b + Real.sin a * Real.sin b * Real.cos γ₁)
    (hc₂ : Real.cos c₂ =
        Real.cos a * Real.cos b + Real.sin a * Real.sin b * Real.cos γ₂)
    (hc₁range : 0 ≤ c₁ ∧ c₁ ≤ Real.pi)
    (hc₂range : 0 ≤ c₂ ∧ c₂ ≤ Real.pi) :
    c₁ < c₂ := by
  have hsa : 0 < Real.sin a := Real.sin_pos_of_pos_of_lt_pi ha0 hapi
  have hsb : 0 < Real.sin b := Real.sin_pos_of_pos_of_lt_pi hb0 hbpi
  -- cos strictly antitone on [0,π]: γ₁ < γ₂ ⟹ cos γ₂ < cos γ₁.
  have hcosγ : Real.cos γ₂ < Real.cos γ₁ :=
    Real.cos_lt_cos_of_nonneg_of_le_pi hg₁0 hg₂pi hγ
  have hcosc : Real.cos c₂ < Real.cos c₁ := by
    rw [hc₁, hc₂]
    have : Real.sin a * Real.sin b * Real.cos γ₂ < Real.sin a * Real.sin b * Real.cos γ₁ :=
      mul_lt_mul_of_pos_left hcosγ (mul_pos hsa hsb)
    linarith
  by_contra hle
  push_neg at hle
  have : Real.cos c₁ ≤ Real.cos c₂ :=
    Real.cos_le_cos_of_nonneg_of_le_pi hc₂range.1 hc₁range.2 hle
  linarith

/-! ## Layer D: convex spherical polygons and arms

The orientation/hemisphere conditions are encoded with the scalar triple product
`det3 a b c = ⟪a, b ×₃ c⟫`, written here in explicit coordinates of `EuclideanSpace ℝ (Fin 3)`.
A great-circle edge `(P i, P (i+1))` *supports* the polygon when every other vertex `P j` lies on
the nonnegative side: `0 ≤ sOrient (P i) (P (i+1)) (P j)`. -/

/-- The scalar triple product `det ![a, b, c]` of three vectors of `E3`, in explicit coordinates. -/
def det3 (a b c : E3) : ℝ :=
  a 0 * (b 1 * c 2 - b 2 * c 1)
    - a 1 * (b 0 * c 2 - b 2 * c 0)
    + a 2 * (b 0 * c 1 - b 1 * c 0)

/-- The oriented (signed) volume of the parallelepiped spanned by three sphere points. -/
def sOrient (a b c : S2) : ℝ := det3 (a : E3) (b : E3) (c : E3)

/-- A strictly convex spherical polygon: a cyclic tuple `P : Fin n → S²` of `n ≥ 3` vertices whose
edges are short arcs, each oriented great-circle edge supports all vertices on the nonnegative side,
non-incident vertices are strictly on the positive side, and all vertices lie in one open
hemisphere.  This is exactly what a convex-polyhedron vertex link provides. -/
structure StrictConvexSphPolygon {n : ℕ} [NeZero n] (P : Fin n → S2) : Prop where
  three_le : 3 ≤ n
  edge_short : ∀ i : Fin n, ShortArc (P i) (P (i + 1))
  edge_support : ∀ i j : Fin n, 0 ≤ sOrient (P i) (P (i + 1)) (P j)
  strict_nonincident : ∀ i j : Fin n, j ≠ i → j ≠ i + 1 →
      0 < sOrient (P i) (P (i + 1)) (P j)
  open_hemisphere : ∃ h : E3, ‖h‖ = 1 ∧ ∀ i : Fin n, 0 < ⟪h, (P i : E3)⟫

/-- A strictly convex spherical *arm* with `n` edges and `n+1` vertices: the closure (adding the
endpoint chord `A n → A 0`) is a strictly convex spherical polygon.  This is the structure the
Cauchy vertex links present after deleting one edge. -/
structure StrictConvexSphArm {n : ℕ} (A : Fin (n + 1) → S2) : Prop where
  two_le : 2 ≤ n
  closed_convex : StrictConvexSphPolygon (n := n + 1) A

/-- The `i`-th side length of an arm: the spherical distance between consecutive vertices. -/
def sideLen {n : ℕ} (A : Fin (n + 1) → S2) (i : Fin n) : ℝ :=
  sDist (A i.castSucc) (A i.succ)

/-- The internal joint angle at the `(i+1)`-st vertex of an arm: the spherical angle at vertex
`A ⟨i+1⟩` between its two neighbours `A ⟨i⟩` and `A ⟨i+2⟩`.  Here `i : Fin (n-1)` ranges over the
`n-1` internal joints; `i.isLt : i.val < n - 1` makes all three indices fall in `Fin (n+1)`. -/
def jointAngle {n : ℕ} (A : Fin (n + 1) → S2) (i : Fin (n - 1)) : ℝ :=
  sphAngle (A ⟨i.val, by have := i.isLt; omega⟩)
    (A ⟨i.val + 1, by have := i.isLt; omega⟩)
    (A ⟨i.val + 2, by have := i.isLt; omega⟩)

/-! ### The spherical arm lemma — statement only

The single hardest theorem of the chapter is the Schoenberg–Zaremba hinge induction.  Per the
design, we deliver the base case (`spherical_hinge_mono`/`_strict`), the structure (above), and the
*statement* of the arm lemma here, isolating the induction as the named next-round target
`spherical_SZ_opening_chain`.

To keep this file `sorry`-free, the arm-lemma statements are phrased as implications taking the
Schoenberg–Zaremba opening chain as an explicit hypothesis (`SZChain`).  Once
`spherical_SZ_opening_chain` is proven in the next round, these become unconditional. -/

/-- A *hinge opening chain* witnessing that arm `B` is reachable from arm `A` by a finite sequence of
nonnegative spherical hinge openings preserving side lengths.  This is the data the Schoenberg–
Zaremba induction must produce; it is exactly what makes endpoint distance monotone.

We package it abstractly: `SZChain A B` records that endpoint distance does not decrease from `A` to
`B`, and strictly increases if some joint of `B` is strictly more open than the corresponding joint
of `A` (the conclusion the hinge chain delivers via `spherical_hinge_mono`/`_strict`). -/
structure SZChain {n : ℕ} (A B : Fin (n + 1) → S2) : Prop where
  /-- Endpoint distance does not decrease from `A` to `B`. -/
  endpoint_mono : sDist (A 0) (A (Fin.last n)) ≤ sDist (B 0) (B (Fin.last n))
  /-- If some joint strictly opens, endpoint distance strictly increases. -/
  endpoint_strict : (∃ i : Fin (n - 1), jointAngle A i < jointAngle B i) →
      sDist (A 0) (A (Fin.last n)) < sDist (B 0) (B (Fin.last n))

/-- **Spherical arm lemma (weak), conditional on the Schoenberg–Zaremba opening chain.**

If two strictly convex spherical arms have equal side lengths and every joint of `B` is at least as
open as the corresponding joint of `A`, then `B`'s endpoint distance is at least `A`'s.  The genuine
content — that the equal-side / wider-angle hypothesis yields an `SZChain` — is the isolated
next-round target `SchoenbergZarembaTarget`. -/
theorem spherical_arm_mono
    {n : ℕ} (A B : Fin (n + 1) → S2)
    (hChain : SZChain A B) :
    sDist (A 0) (A (Fin.last n)) ≤ sDist (B 0) (B (Fin.last n)) :=
  hChain.endpoint_mono

/-- **Spherical arm lemma (strict), conditional on the Schoenberg–Zaremba opening chain.**

The strict version Cauchy needs: under the hypotheses of `spherical_arm_mono` together with one
strictly wider joint, the endpoint distance strictly increases. -/
theorem spherical_arm_mono_strict
    {n : ℕ} (A B : Fin (n + 1) → S2)
    (hChain : SZChain A B)
    (hStrict : ∃ i : Fin (n - 1), jointAngle A i < jointAngle B i) :
    sDist (A 0) (A (Fin.last n)) < sDist (B 0) (B (Fin.last n)) :=
  hChain.endpoint_strict hStrict

/-! ### Next-round target (isolated)

The remaining mathematical content of the chapter is the construction of the `SZChain` from the
equal-side / wider-angle hypotheses.  We record its statement here as the named target for the next
round; it is *not* proved in this file (its proof is the full Schoenberg–Zaremba hinge induction,
which exceeds one file).  It is stated as a `def : Prop` so that this file contains **no** `sorry`
and the obligation is explicit and unmistakable.

The proof factors (per the design §8) through: `rotAbout` (Rodrigues rotation about a sphere axis),
`HingeMove`/`hinge_endpoint_mono` (a single hinge step, built on `spherical_hinge_mono` above),
`convex_hinge_open_small` (local convexity persistence), and `convex_stuck_gives_cut` (the planar
"stuck case" — a coplanarity `det3 = 0` cuts the arm into two smaller convex arms).  The `n = 2`
base of that induction **is** `spherical_hinge_strict`, already proved above. -/

/-- The next-round Schoenberg–Zaremba obligation, as an explicit `Prop` (statement only, not proved
in this file).  Discharging this turns `spherical_arm_mono`/`spherical_arm_mono_strict` into
unconditional theorems. -/
def SchoenbergZarembaTarget : Prop :=
  ∀ {n : ℕ}, 2 ≤ n →
    ∀ (A B : Fin (n + 1) → S2),
      StrictConvexSphArm A → StrictConvexSphArm B →
      (∀ i : Fin n, sideLen A i = sideLen B i) →
      (∀ i : Fin (n - 1), jointAngle A i ≤ jointAngle B i) →
      SZChain A B

end ProofsInTheBook.SphericalKernel
