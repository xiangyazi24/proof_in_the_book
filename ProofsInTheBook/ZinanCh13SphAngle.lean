import ProofsInTheBook.ZinanCh13EuclLink

/-!
# Chapter 13 spherical link angles and dihedral angles

This file isolates the pure `ℝ³` vector identity relating the spherical link
angle at a unit vector to the supplement of the angle between consistently
oriented face normals.
-/

noncomputable section

open scoped Classical RealInnerProductSpace
open ProofsInTheBook.PlanarMap ProofsInTheBook.PlanarMap.CombMap
open ProofsInTheBook.Ch13Euclidean
open ProofsInTheBook.Ch13VertexStar
open ProofsInTheBook.SphericalKernel (S2 tangentTo tangentTo_eq jointAngle sphAngle)
open ProofsInTheBook.SphericalRotation

namespace ProofsInTheBook.Ch13SphAngle

/-- Projection of `u` to the tangent plane at a unit vector `v`. -/
def tangentToVec (v u : E3) : E3 :=
  u - (inner ℝ u v) • v

lemma inner_tangent_tangent_unit {a b c : E3} (hb : ‖b‖ = 1) :
    inner ℝ (tangentToVec b a) (tangentToVec b c)
      = inner ℝ a c - inner ℝ a b * inner ℝ b c := by
  unfold tangentToVec
  have hb_inner : inner ℝ b b = (1 : ℝ) := by
    rw [real_inner_self_eq_norm_sq, hb]
    norm_num
  simp [inner_sub_left, inner_sub_right, real_inner_smul_left, real_inner_smul_right,
    hb_inner, real_inner_comm]
  rw [hb]
  ring_nf

lemma inner_cross_cross_unit {a b c : E3} (hb : ‖b‖ = 1) :
    inner ℝ (cross a b) (cross b c)
      = inner ℝ a b * inner ℝ b c - inner ℝ a c := by
  have hb_inner : inner ℝ b b = (1 : ℝ) := by
    rw [real_inner_self_eq_norm_sq, hb]
    norm_num
  rw [inner_cross_cross, hb_inner]
  ring

lemma inner_tangent_eq_neg_inner_cross {a b c : E3}
    (ha : ‖a‖ = 1) (hb : ‖b‖ = 1) (hc : ‖c‖ = 1) :
    inner ℝ (tangentToVec b a) (tangentToVec b c)
      = - inner ℝ (cross a b) (cross b c) := by
  rw [inner_tangent_tangent_unit hb, inner_cross_cross_unit hb]
  ring

lemma norm_tangent_sq_unit {a b : E3} (ha : ‖a‖ = 1) (hb : ‖b‖ = 1) :
    ‖tangentToVec b a‖ ^ 2 = 1 - (inner ℝ a b) ^ 2 := by
  rw [← real_inner_self_eq_norm_sq, inner_tangent_tangent_unit (a := a) (b := b) (c := a) hb]
  have ha_inner : inner ℝ a a = (1 : ℝ) := by
    rw [real_inner_self_eq_norm_sq, ha]
    norm_num
  rw [ha_inner]
  rw [real_inner_comm b a]
  ring

lemma norm_cross_sq_unit {a b : E3} (ha : ‖a‖ = 1) (hb : ‖b‖ = 1) :
    ‖cross a b‖ ^ 2 = 1 - (inner ℝ a b) ^ 2 := by
  rw [norm_sq_cross, ha, hb]
  ring

lemma norm_tangent_eq_norm_cross_left {a b : E3} (ha : ‖a‖ = 1) (hb : ‖b‖ = 1) :
    ‖tangentToVec b a‖ = ‖cross a b‖ := by
  have hsq : ‖tangentToVec b a‖ ^ 2 = ‖cross a b‖ ^ 2 := by
    rw [norm_tangent_sq_unit ha hb, norm_cross_sq_unit ha hb]
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp hsq with h | h
  · exact h
  · have h1 : 0 ≤ ‖tangentToVec b a‖ := norm_nonneg _
    have h2 : 0 ≤ ‖cross a b‖ := norm_nonneg _
    linarith

lemma norm_tangent_eq_norm_cross_right {b c : E3} (hb : ‖b‖ = 1) (hc : ‖c‖ = 1) :
    ‖tangentToVec b c‖ = ‖cross b c‖ := by
  have hsq : ‖tangentToVec b c‖ ^ 2 = ‖cross b c‖ ^ 2 := by
    rw [norm_tangent_sq_unit hc hb, norm_cross_sq_unit hb hc]
    rw [real_inner_comm c b]
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp hsq with h | h
  · exact h
  · have h1 : 0 ≤ ‖tangentToVec b c‖ := norm_nonneg _
    have h2 : 0 ≤ ‖cross b c‖ := norm_nonneg _
    linarith

lemma cos_tangent_eq_neg_cos_cross {a b c : E3}
    (ha : ‖a‖ = 1) (hb : ‖b‖ = 1) (hc : ‖c‖ = 1)
    (hta : tangentToVec b a ≠ 0) (htc : tangentToVec b c ≠ 0)
    (hX : cross a b ≠ 0) (hY : cross b c ≠ 0) :
    Real.cos (InnerProductGeometry.angle (tangentToVec b a) (tangentToVec b c))
      =
    - Real.cos (InnerProductGeometry.angle (cross a b) (cross b c)) := by
  rw [InnerProductGeometry.cos_angle, InnerProductGeometry.cos_angle,
    inner_tangent_eq_neg_inner_cross ha hb hc,
    norm_tangent_eq_norm_cross_left ha hb,
    norm_tangent_eq_norm_cross_right hb hc]
  field_simp [norm_pos_iff.mpr hX, norm_pos_iff.mpr hY]

lemma tangent_angle_eq_pi_sub_cross_angle {a b c : E3}
    (ha : ‖a‖ = 1) (hb : ‖b‖ = 1) (hc : ‖c‖ = 1)
    (hta : tangentToVec b a ≠ 0) (htc : tangentToVec b c ≠ 0)
    (hX : cross a b ≠ 0) (hY : cross b c ≠ 0) :
    InnerProductGeometry.angle (tangentToVec b a) (tangentToVec b c)
      =
    Real.pi - InnerProductGeometry.angle (cross a b) (cross b c) := by
  apply Real.injOn_cos.eq_iff
    (s := Set.Icc (0 : ℝ) Real.pi)
    ⟨InnerProductGeometry.angle_nonneg _ _, InnerProductGeometry.angle_le_pi _ _⟩
    ⟨by linarith [InnerProductGeometry.angle_le_pi (cross a b) (cross b c)],
      by linarith [InnerProductGeometry.angle_nonneg (cross a b) (cross b c)]⟩ |>.1
  rw [cos_tangent_eq_neg_cos_cross ha hb hc hta htc hX hY]
  rw [Real.cos_pi_sub]

lemma angle_normals_eq_cross {a b c n_f n_g : E3}
    (horient :
      ∃ l m : ℝ,
        0 < l ∧ 0 < m ∧
          ((n_f = l • cross a b ∧ n_g = m • cross b c) ∨
           (n_f = l • (-(cross a b)) ∧ n_g = m • (-(cross b c))))) :
    InnerProductGeometry.angle n_f n_g
      =
    InnerProductGeometry.angle (cross a b) (cross b c) := by
  rcases horient with ⟨l, m, hl, hm, hcase⟩
  rcases hcase with ⟨hf, hg⟩ | ⟨hf, hg⟩
  · rw [hf, hg]
    rw [InnerProductGeometry.angle_smul_left_of_pos _ _ hl]
    rw [InnerProductGeometry.angle_smul_right_of_pos _ _ hm]
  · rw [hf, hg]
    rw [InnerProductGeometry.angle_smul_left_of_pos _ _ hl]
    rw [InnerProductGeometry.angle_smul_right_of_pos _ _ hm]
    rw [InnerProductGeometry.angle_neg_neg]

theorem sphAngle_eq_pi_sub_normal_angle {a b c n_f n_g : E3}
    (ha : ‖a‖ = 1) (hb : ‖b‖ = 1) (hc : ‖c‖ = 1)
    (hta : tangentToVec b a ≠ 0) (htc : tangentToVec b c ≠ 0)
    (hX : cross a b ≠ 0) (hY : cross b c ≠ 0)
    (horient :
      ∃ l m : ℝ,
        0 < l ∧ 0 < m ∧
          ((n_f = l • cross a b ∧ n_g = m • cross b c) ∨
           (n_f = l • (-(cross a b)) ∧ n_g = m • (-(cross b c))))) :
    InnerProductGeometry.angle (tangentToVec b a) (tangentToVec b c)
      =
    Real.pi - InnerProductGeometry.angle n_f n_g := by
  calc
    InnerProductGeometry.angle (tangentToVec b a) (tangentToVec b c)
        = Real.pi - InnerProductGeometry.angle (cross a b) (cross b c) :=
            tangent_angle_eq_pi_sub_cross_angle ha hb hc hta htc hX hY
    _ = Real.pi - InnerProductGeometry.angle n_f n_g := by
      rw [angle_normals_eq_cross horient]

lemma tangentTo_eq_tangentToVec (p q : S2) :
    tangentTo p q = tangentToVec (p : E3) (q : E3) := by
  rw [tangentTo_eq]
  rfl

theorem jointAngle_vertexLink_eq_pi_sub_normal_angle
    (S : VertexStar) (i : Fin (S.n - 1)) {n_f n_g : E3}
    (hta :
      tangentToVec (S.edgeDir (S.jIdx1 i) : E3) (S.edgeDir (S.jIdx0 i) : E3) ≠ 0)
    (htc :
      tangentToVec (S.edgeDir (S.jIdx1 i) : E3) (S.edgeDir (S.jIdx2 i) : E3) ≠ 0)
    (hX : cross (S.edgeDir (S.jIdx0 i) : E3) (S.edgeDir (S.jIdx1 i) : E3) ≠ 0)
    (hY : cross (S.edgeDir (S.jIdx1 i) : E3) (S.edgeDir (S.jIdx2 i) : E3) ≠ 0)
    (horient :
      ∃ l m : ℝ,
        0 < l ∧ 0 < m ∧
          ((n_f = l • cross (S.edgeDir (S.jIdx0 i) : E3) (S.edgeDir (S.jIdx1 i) : E3) ∧
              n_g = m • cross (S.edgeDir (S.jIdx1 i) : E3) (S.edgeDir (S.jIdx2 i) : E3)) ∨
           (n_f = l • (-(cross (S.edgeDir (S.jIdx0 i) : E3) (S.edgeDir (S.jIdx1 i) : E3))) ∧
              n_g = m • (-(cross (S.edgeDir (S.jIdx1 i) : E3) (S.edgeDir (S.jIdx2 i) : E3)))))) :
    jointAngle S.vertexLink i = Real.pi - InnerProductGeometry.angle n_f n_g := by
  rw [jointAngle]
  simp only [VertexStar.vertexLink_apply]
  rw [sphAngle]
  show InnerProductGeometry.angle
      (tangentTo (S.edgeDir (S.jIdx1 i)) (S.edgeDir (S.jIdx0 i)))
      (tangentTo (S.edgeDir (S.jIdx1 i)) (S.edgeDir (S.jIdx2 i)))
        = Real.pi - InnerProductGeometry.angle n_f n_g
  rw [tangentTo_eq_tangentToVec, tangentTo_eq_tangentToVec]
  exact sphAngle_eq_pi_sub_normal_angle
    (a := (S.edgeDir (S.jIdx0 i) : E3))
    (b := (S.edgeDir (S.jIdx1 i) : E3))
    (c := (S.edgeDir (S.jIdx2 i) : E3))
    (n_f := n_f) (n_g := n_g)
    (S.edgeDir (S.jIdx0 i)).2 (S.edgeDir (S.jIdx1 i)).2 (S.edgeDir (S.jIdx2 i)).2
    hta htc hX hY horient

theorem tangent_angle_eq_dihedralAngleAtDart_of_oriented
    {D : Type*} [Fintype D] [DecidableEq D] {M : CombMap D}
    (P : TriangulatedEuclideanPolyhedron M) (d : D) {a b c : E3}
    (ha : ‖a‖ = 1) (hb : ‖b‖ = 1) (hc : ‖c‖ = 1)
    (hta : tangentToVec b a ≠ 0) (htc : tangentToVec b c ≠ 0)
    (hX : cross a b ≠ 0) (hY : cross b c ≠ 0)
    (horient :
      ∃ l m : ℝ,
        0 < l ∧ 0 < m ∧
          ((dartNormal P d = l • cross a b ∧
              dartNormal P (M.α d) = m • cross b c) ∨
           (dartNormal P d = l • (-(cross a b)) ∧
              dartNormal P (M.α d) = m • (-(cross b c))))) :
    InnerProductGeometry.angle (tangentToVec b a) (tangentToVec b c)
      = dihedralAngleAtDart P d := by
  rw [dihedralAngleAtDart]
  exact sphAngle_eq_pi_sub_normal_angle
    (a := a) (b := b) (c := c)
    (n_f := dartNormal P d) (n_g := dartNormal P (M.α d))
    ha hb hc hta htc hX hY horient

#print axioms ProofsInTheBook.Ch13SphAngle.sphAngle_eq_pi_sub_normal_angle
#print axioms ProofsInTheBook.Ch13SphAngle.jointAngle_vertexLink_eq_pi_sub_normal_angle
#print axioms ProofsInTheBook.Ch13SphAngle.tangent_angle_eq_dihedralAngleAtDart_of_oriented

end ProofsInTheBook.Ch13SphAngle
