import ProofsInTheBook.ZinanCh13EuclLink
import ProofsInTheBook.SphericalCongruence

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

lemma eq_smul_axis_of_cross_zero_unit {k v : E3} (hk : ‖k‖ = 1) (h : cross k v = 0) :
    v = (⟪v, k⟫ : ℝ) • k := by
  have hkk : (⟪k, k⟫ : ℝ) = 1 := by
    rw [real_inner_self_eq_norm_sq, hk]
    norm_num
  set t : E3 := v - (⟪v, k⟫ : ℝ) • k with ht
  have htk : (⟪t, k⟫ : ℝ) = 0 := by
    rw [ht, inner_sub_left, real_inner_smul_left, hkk, mul_one, sub_self]
  have hct : cross k t = 0 := by
    rw [ht, show v - (⟪v, k⟫ : ℝ) • k = v + (-(⟪v, k⟫ : ℝ)) • k by module,
      cross_add_right, cross_smul_right, cross_self, smul_zero, add_zero, h]
  have hkt : (⟪k, t⟫ : ℝ) = 0 := by
    rw [real_inner_comm]
    exact htk
  have hnorm : ‖t‖ ^ 2 = 0 := by
    have hl := norm_sq_cross k t
    rw [hct, norm_zero] at hl
    rw [hk, hkt] at hl
    nlinarith [hl]
  have : t = 0 := by
    have := pow_eq_zero_iff (n := 2) (by norm_num) |>.mp hnorm
    exact norm_eq_zero.mp this
  rw [ht] at this
  linear_combination (norm := module) this

lemma cross_ne_zero_of_linearIndependent_pair {u v : E3}
    (hli : LinearIndependent ℝ ![u, v]) :
    cross u v ≠ 0 := by
  intro hcross
  have hu : u ≠ 0 := by
    intro hu0
    exact hli.ne_zero 0 (by simpa using hu0)
  have hnormu : ‖u‖ ≠ 0 := by
    simpa [norm_eq_zero] using hu
  set k : E3 := ‖u‖⁻¹ • u with hkdef
  have hk : ‖k‖ = 1 := by
    rw [hkdef, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hnormu]
  have hkv : cross k v = 0 := by
    rw [hkdef, cross_smul_left, hcross, smul_zero]
  have hvk : v = (⟪v, k⟫ : ℝ) • k :=
    eq_smul_axis_of_cross_zero_unit hk hkv
  have hvu : v = ((⟪v, k⟫ : ℝ) * ‖u‖⁻¹) • u := by
    calc
      v = (⟪v, k⟫ : ℝ) • k := hvk
      _ = ((⟪v, k⟫ : ℝ) * ‖u‖⁻¹) • u := by
        rw [hkdef, smul_smul]
  have hcontra := ((LinearIndependent.pair_iff' (K := ℝ) (x := u) (y := v) hu).mp hli)
      (((⟪v, k⟫ : ℝ) * ‖u‖⁻¹))
  exact hcontra hvu.symm

lemma perp_two_imp_parallel_cross {u v n : E3}
    (hnu : (⟪n, u⟫ : ℝ) = 0) (hnv : (⟪n, v⟫ : ℝ) = 0)
    (hli : LinearIndependent ℝ ![u, v]) :
    ∃ s : ℝ, n = s • cross u v := by
  set X : E3 := cross u v with hXdef
  have hX : X ≠ 0 := by
    rw [hXdef]
    exact cross_ne_zero_of_linearIndependent_pair hli
  let s : ℝ := (⟪n, X⟫ : ℝ) / ‖X‖ ^ 2
  refine ⟨s, ?_⟩
  apply ProofsInTheBook.SphericalCongruence.eq_of_inner_frame_eq hX
  · have hux : (⟪u, cross u v⟫ : ℝ) = 0 := by
      rw [real_inner_comm]
      exact inner_cross_left u v
    rw [real_inner_smul_right, hXdef, hux, mul_zero]
    rw [real_inner_comm]
    exact hnu
  · have hvx : (⟪v, cross u v⟫ : ℝ) = 0 := by
      rw [real_inner_comm]
      exact inner_cross_right u v
    rw [real_inner_smul_right, hXdef, hvx, mul_zero]
    rw [real_inner_comm]
    exact hnv
  · have hcrossne : cross u v ≠ 0 := by
      rwa [← hXdef]
    rw [real_inner_smul_right, hXdef]
    change (⟪cross u v, n⟫ : ℝ) =
      s * (⟪cross u v, cross u v⟫ : ℝ)
    rw [show (⟪cross u v, n⟫ : ℝ) = ⟪n, cross u v⟫ by rw [real_inner_comm],
      real_inner_self_eq_norm_sq]
    unfold s
    have hnorm : ‖cross u v‖ ^ 2 ≠ 0 := by
      positivity
    field_simp [hnorm]
    ring

def fin2NeZeroFin3Equiv : Fin 2 ≃ {x : Fin 3 // x ≠ 0} where
  toFun i := match i with
    | 0 => ⟨1, by decide⟩
    | 1 => ⟨2, by decide⟩
  invFun i := if i.1 = 1 then 0 else 1
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    rcases i with ⟨i, hi⟩
    fin_cases i
    · exact False.elim (hi rfl)
    · rfl
    · rfl

lemma linearIndependent_pair_vsub_of_affineIndependent_fin3 {p : Fin 3 → E3}
    (hai : AffineIndependent ℝ p) :
    LinearIndependent ℝ ![p 1 - p 0, p 2 - p 0] := by
  rw [affineIndependent_iff_linearIndependent_vsub ℝ p (0 : Fin 3)] at hai
  convert (linearIndependent_equiv (R := ℝ) (M := E3)
    fin2NeZeroFin3Equiv
    (f := fun i : {x : Fin 3 // x ≠ 0} => (p i -ᵥ p (0 : Fin 3) : E3))).mpr hai using 1
  funext i
  fin_cases i <;> rfl

lemma inner_sub_of_plane_eq {normal point x y : E3}
    (hx : inner ℝ normal (x - point) = 0)
    (hy : inner ℝ normal (y - point) = 0) :
    inner ℝ normal (x - y) = 0 := by
  calc
    inner ℝ normal (x - y)
        = inner ℝ normal ((x - point) - (y - point)) := by
            congr 1
            module
    _ = inner ℝ normal (x - point) - inner ℝ normal (y - point) := by
            rw [inner_sub_right]
    _ = 0 := by rw [hx, hy, sub_self]

theorem outward_normal_parallel_faceDart_cross
    {D : Type*} [Fintype D] [DecidableEq D] {M : CombMap D}
    (P : TriangulatedEuclideanPolyhedron M) (f : M.Face) :
    ∃ s : ℝ,
      P.outward_normal f =
        s • cross
          (P.pos (M.tail (M.φ (P.faceDart f))) - P.pos (M.tail (P.faceDart f)))
          (P.pos (M.tail (M.φ (M.φ (P.faceDart f)))) - P.pos (M.tail (P.faceDart f))) := by
  let p : Fin 3 → E3 :=
    ![P.pos (M.tail (P.faceDart f)),
      P.pos (M.tail (M.φ (P.faceDart f))),
      P.pos (M.tail (M.φ (M.φ (P.faceDart f))))]
  have hli : LinearIndependent ℝ ![p 1 - p 0, p 2 - p 0] :=
    linearIndependent_pair_vsub_of_affineIndependent_fin3 (P.face_nondegenerate f)
  have hv0 : P.faceVertex f 0 = M.tail (P.faceDart f) := by
    have h := congrFun (P.face_vertices_match f) 0
    simpa using h
  have hv1 : P.faceVertex f 1 = M.tail (M.φ (P.faceDart f)) := by
    have h := congrFun (P.face_vertices_match f) 1
    simpa using h
  have hv2 : P.faceVertex f 2 = M.tail (M.φ (M.φ (P.faceDart f))) := by
    have h := congrFun (P.face_vertices_match f) 2
    simpa using h
  have hp0 : inner ℝ (P.outward_normal f)
      (P.pos (M.tail (P.faceDart f)) - P.face_point f) = 0 := by
    simpa [hv0] using P.face_plane f 0
  have hp1 : inner ℝ (P.outward_normal f)
      (P.pos (M.tail (M.φ (P.faceDart f))) - P.face_point f) = 0 := by
    simpa [hv1] using P.face_plane f 1
  have hp2 : inner ℝ (P.outward_normal f)
      (P.pos (M.tail (M.φ (M.φ (P.faceDart f)))) - P.face_point f) = 0 := by
    simpa [hv2] using P.face_plane f 2
  have hperp1 : inner ℝ (P.outward_normal f)
      (P.pos (M.tail (M.φ (P.faceDart f))) - P.pos (M.tail (P.faceDart f))) = 0 :=
    inner_sub_of_plane_eq hp1 hp0
  have hperp2 : inner ℝ (P.outward_normal f)
      (P.pos (M.tail (M.φ (M.φ (P.faceDart f)))) - P.pos (M.tail (P.faceDart f))) = 0 :=
    inner_sub_of_plane_eq hp2 hp0
  simpa [p] using perp_two_imp_parallel_cross hperp1 hperp2 hli

theorem face_supporting_halfspace_from_faceDart_base
    {D : Type*} [Fintype D] [DecidableEq D] {M : CombMap D}
    (P : TriangulatedEuclideanPolyhedron M) (f : M.Face) (w : M.Vertex) :
    inner ℝ (P.outward_normal f)
      (P.pos w - P.pos (M.tail (P.faceDart f))) ≤ 0 := by
  have hv0 : P.faceVertex f 0 = M.tail (P.faceDart f) := by
    have h := congrFun (P.face_vertices_match f) 0
    simpa using h
  have hp0 : inner ℝ (P.outward_normal f)
      (P.pos (M.tail (P.faceDart f)) - P.face_point f) = 0 := by
    simpa [hv0] using P.face_plane f 0
  have hsupport := P.face_supporting_halfspace f w
  have hrewrite :
      inner ℝ (P.outward_normal f)
        (P.pos w - P.pos (M.tail (P.faceDart f)))
        =
      inner ℝ (P.outward_normal f) (P.pos w - P.face_point f)
        - inner ℝ (P.outward_normal f)
          (P.pos (M.tail (P.faceDart f)) - P.face_point f) := by
    calc
      inner ℝ (P.outward_normal f)
          (P.pos w - P.pos (M.tail (P.faceDart f)))
          =
        inner ℝ (P.outward_normal f)
          ((P.pos w - P.face_point f)
            - (P.pos (M.tail (P.faceDart f)) - P.face_point f)) := by
            congr 1
            module
      _ =
        inner ℝ (P.outward_normal f) (P.pos w - P.face_point f)
          - inner ℝ (P.outward_normal f)
            (P.pos (M.tail (P.faceDart f)) - P.face_point f) := by
            rw [inner_sub_right]
  rw [hrewrite, hp0, sub_zero]
  exact hsupport

theorem face_parallel_scalar_support_le
    {D : Type*} [Fintype D] [DecidableEq D] {M : CombMap D}
    (P : TriangulatedEuclideanPolyhedron M) (f : M.Face) (w : M.Vertex) {s : ℝ}
    (hs :
      P.outward_normal f =
        s • cross
          (P.pos (M.tail (M.φ (P.faceDart f))) - P.pos (M.tail (P.faceDart f)))
          (P.pos (M.tail (M.φ (M.φ (P.faceDart f)))) - P.pos (M.tail (P.faceDart f)))) :
    s * inner ℝ
      (cross
        (P.pos (M.tail (M.φ (P.faceDart f))) - P.pos (M.tail (P.faceDart f)))
        (P.pos (M.tail (M.φ (M.φ (P.faceDart f)))) - P.pos (M.tail (P.faceDart f))))
      (P.pos w - P.pos (M.tail (P.faceDart f))) ≤ 0 := by
  have hsupport := face_supporting_halfspace_from_faceDart_base P f w
  rw [hs, real_inner_smul_left] at hsupport
  exact hsupport

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
#print axioms ProofsInTheBook.Ch13SphAngle.perp_two_imp_parallel_cross
#print axioms ProofsInTheBook.Ch13SphAngle.outward_normal_parallel_faceDart_cross
#print axioms ProofsInTheBook.Ch13SphAngle.face_parallel_scalar_support_le

end ProofsInTheBook.Ch13SphAngle
