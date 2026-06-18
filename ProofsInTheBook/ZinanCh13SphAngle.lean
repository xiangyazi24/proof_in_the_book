import ProofsInTheBook.ZinanCh13EuclLink
import ProofsInTheBook.SphericalCongruence
import ProofsInTheBook.Ch13ArmVertexFull

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
open ProofsInTheBook.Ch13EuclLink
open ProofsInTheBook.Ch13VertexStar
open ProofsInTheBook.Ch13ArmVertexFull (linkAngle)
open ProofsInTheBook.SphericalKernel
  (S2 ShortArc tangentTo tangentTo_eq tangentTo_eq_zero_iff jointAngle sphAngle)
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

private theorem faceDart_phi_ne_self
    {D : Type*} [Fintype D] [DecidableEq D] {M : CombMap D}
    (P : TriangulatedEuclideanPolyhedron M) (f : M.Face) :
    M.φ (P.faceDart f) ≠ P.faceDart f := by
  intro h
  let p : Fin 3 → E3 :=
    ![P.pos (M.tail (P.faceDart f)),
      P.pos (M.tail (M.φ (P.faceDart f))),
      P.pos (M.tail (M.φ (M.φ (P.faceDart f))))]
  have hinj : Function.Injective p := (P.face_nondegenerate f).injective
  have hpts : p 1 = p 0 := by
    simp [p, h]
  have h10 : (1 : Fin 3) = 0 := hinj hpts
  norm_num at h10

/-- A dart on a triangular face is one of the three `φ`-successive darts from the
stored representative of that face. -/
theorem dart_eq_faceDart_or_phi_or_phi2_of_dartFace_eq
    {D : Type*} [Fintype D] [DecidableEq D] {M : CombMap D}
    (P : TriangulatedEuclideanPolyhedron M) {f : M.Face} {d : D}
    (hd : M.dartFace d = f) :
    d = P.faceDart f ∨
      d = M.φ (P.faceDart f) ∨
      d = M.φ (M.φ (P.faceDart f)) := by
  let fd := P.faceDart f
  have hφne : M.φ fd ≠ fd := by
    simpa [fd] using faceDart_phi_ne_self P f
  have hlen : M.faceLen f = 3 := by
    simpa [CombMap.faceLen] using P.every_face_triangle f
  have hcard : (M.φ.cycleOf fd).support.card = 3 := by
    rw [← faceLen_dartFace_eq_card_support_cycleOf M hφne]
    simpa [fd, P.faceDart_face f] using hlen
  have hsame : M.φ.SameCycle fd d := by
    have hq : M.dartFace d = M.dartFace fd := by
      rw [hd, P.faceDart_face f]
    exact (Quotient.exact hq).symm
  have hsupp : fd ∈ M.φ.support := Equiv.Perm.mem_support.mpr hφne
  obtain ⟨i, hi, hpow⟩ := hsame.exists_pow_eq_of_mem_support hsupp
  rw [hcard] at hi
  interval_cases i
  · left
    simpa [fd] using hpow.symm
  · right
    left
    simpa [fd] using hpow.symm
  · right
    right
    simpa [fd, pow_succ] using hpow.symm

/-- Every dart tail is one of the three stored vertices of its dart face. -/
theorem tail_mem_faceVertex
    {D : Type*} [Fintype D] [DecidableEq D] {M : CombMap D}
    (P : TriangulatedEuclideanPolyhedron M) (d : D) :
    ∃ k : Fin 3, M.tail d = P.faceVertex (M.dartFace d) k := by
  rcases dart_eq_faceDart_or_phi_or_phi2_of_dartFace_eq P (f := M.dartFace d) (d := d) rfl with
    h | h | h
  · refine ⟨0, ?_⟩
    rw [h]
    have hv := congrFun (P.face_vertices_match (M.dartFace d)) 0
    simpa [P.faceDart_face (M.dartFace d)] using hv.symm
  · refine ⟨1, ?_⟩
    rw [h]
    have hv := congrFun (P.face_vertices_match (M.dartFace d)) 1
    simpa [P.faceDart_face (M.dartFace d)] using hv.symm
  · refine ⟨2, ?_⟩
    rw [h]
    have hv := congrFun (P.face_vertices_match (M.dartFace d)) 2
    simpa [P.faceDart_face (M.dartFace d)] using hv.symm

/-- The selected face plane contains the tail of every dart on that face, not only
the stored representative's three tails. -/
theorem face_plane_dart
    {D : Type*} [Fintype D] [DecidableEq D] {M : CombMap D}
    (P : TriangulatedEuclideanPolyhedron M) (d : D) :
    inner ℝ (P.outward_normal (M.dartFace d))
      (P.pos (M.tail d) - P.face_point (M.dartFace d)) = 0 := by
  obtain ⟨k, hk⟩ := tail_mem_faceVertex P d
  rw [hk]
  exact P.face_plane (M.dartFace d) k

private theorem faceDart_phi_cube_eq_self
    {D : Type*} [Fintype D] [DecidableEq D] {M : CombMap D}
    (P : TriangulatedEuclideanPolyhedron M) (f : M.Face) :
    (M.φ ^ 3) (P.faceDart f) = P.faceDart f := by
  let fd := P.faceDart f
  have hφne : M.φ fd ≠ fd := by
    simpa [fd] using faceDart_phi_ne_self P f
  have hlen : M.faceLen f = 3 := by
    simpa [CombMap.faceLen] using P.every_face_triangle f
  have hcard : (M.φ.cycleOf fd).support.card = 3 := by
    rw [← faceLen_dartFace_eq_card_support_cycleOf M hφne]
    simpa [fd, P.faceDart_face f] using hlen
  have hpow := Equiv.Perm.pow_mod_card_support_cycleOf_self_apply M.φ 3 fd
  rw [hcard, Nat.mod_self] at hpow
  simpa [fd] using hpow.symm

theorem phi_cube_eq_self_of_triangular_euclidean
    {D : Type*} [Fintype D] [DecidableEq D] {M : CombMap D}
    (P : TriangulatedEuclideanPolyhedron M) (d : D) :
    (M.φ ^ 3) d = d := by
  rcases dart_eq_faceDart_or_phi_or_phi2_of_dartFace_eq P (f := M.dartFace d) (d := d) rfl with
    h | h | h
  · rw [h]
    exact faceDart_phi_cube_eq_self P (M.dartFace d)
  · rw [h]
    exact congrArg M.φ (faceDart_phi_cube_eq_self P (M.dartFace d))
  · rw [h]
    exact congrArg (fun x => M.φ (M.φ x))
      (faceDart_phi_cube_eq_self P (M.dartFace d))

theorem tail_phi_phi_eq_head_sigma_symm_of_triangular_euclidean
    {D : Type*} [Fintype D] [DecidableEq D] {M : CombMap D}
    (P : TriangulatedEuclideanPolyhedron M) (d : D) :
    M.tail (M.φ (M.φ d)) = M.head (M.σ.symm d) := by
  have hcube := phi_cube_eq_self_of_triangular_euclidean P d
  have hpred : M.φ (M.φ d) = M.φ.symm d := by
    apply M.φ.injective
    rw [Equiv.apply_symm_apply]
    simpa [pow_succ, Equiv.Perm.coe_mul, Function.comp_apply] using hcube
  have hsymm : M.φ.symm d = M.α (M.σ.symm d) := by
    apply M.φ.injective
    rw [Equiv.apply_symm_apply]
    symm
    change (M.σ * M.α) (M.α (M.σ.symm d)) = d
    rw [Equiv.Perm.mul_apply, M.alpha_alpha, Equiv.apply_symm_apply]
  rw [hpred, hsymm, M.tail_alpha]

/-- The stored face vertices are the three tails of any dart on the same
triangular face, up to cyclic rotation. -/
theorem faceVertex_eq_tail_or_head_or_tail_phi2_of_dartFace_eq
    {D : Type*} [Fintype D] [DecidableEq D] {M : CombMap D}
    (P : TriangulatedEuclideanPolyhedron M) {f : M.Face} {e : D}
    (he : M.dartFace e = f) (k : Fin 3) :
    P.faceVertex f k = M.tail e ∨
      P.faceVertex f k = M.head e ∨
      P.faceVertex f k = M.tail (M.φ (M.φ e)) := by
  rcases dart_eq_faceDart_or_phi_or_phi2_of_dartFace_eq P (f := f) (d := e) he with
    h | h | h
  · subst h
    fin_cases k
    · left
      have hv := congrFun (P.face_vertices_match f) 0
      simpa using hv
    · right; left
      have hv := congrFun (P.face_vertices_match f) 1
      simpa [M.tail_phi] using hv
    · right; right
      have hv := congrFun (P.face_vertices_match f) 2
      simpa using hv
  · subst h
    fin_cases k
    · right; right
      have hv := congrFun (P.face_vertices_match f) 0
      have hcube := faceDart_phi_cube_eq_self P f
      have hcube' : M.φ (M.φ (M.φ (P.faceDart f))) = P.faceDart f := by
        simpa [pow_succ, Equiv.Perm.coe_mul, Function.comp_apply] using hcube
      have htail : M.tail (P.faceDart f) =
          M.tail (M.φ (M.φ (M.φ (P.faceDart f)))) := by
        rw [hcube']
      exact hv.trans htail
    · left
      have hv := congrFun (P.face_vertices_match f) 1
      simpa [M.tail_phi] using hv
    · right; left
      have hv := congrFun (P.face_vertices_match f) 2
      simpa [M.tail_phi] using hv
  · subst h
    fin_cases k
    · right; left
      have hv := congrFun (P.face_vertices_match f) 0
      have hcube := faceDart_phi_cube_eq_self P f
      have hcube' : M.φ (M.φ (M.φ (P.faceDart f))) = P.faceDart f := by
        simpa [pow_succ, Equiv.Perm.coe_mul, Function.comp_apply] using hcube
      have htail : M.tail (P.faceDart f) =
          M.head (M.φ (M.φ (P.faceDart f))) := by
        rw [← M.tail_phi (M.φ (M.φ (P.faceDart f))), hcube']
      exact hv.trans htail
    · right; right
      have hv := congrFun (P.face_vertices_match f) 1
      have hcube := faceDart_phi_cube_eq_self P f
      have hcube' : M.φ (M.φ (M.φ (P.faceDart f))) = P.faceDart f := by
        simpa [pow_succ, Equiv.Perm.coe_mul, Function.comp_apply] using hcube
      have htail : M.tail (M.φ (P.faceDart f)) =
          M.tail (M.φ (M.φ (M.φ (M.φ (P.faceDart f))))) := by
        rw [hcube']
      exact hv.trans htail
    · left
      have hv := congrFun (P.face_vertices_match f) 2
      simpa using hv

lemma linearIndependent_pair_of_cross_ne_zero {u v : E3}
    (hcross : cross u v ≠ 0) :
    LinearIndependent ℝ ![u, v] := by
  by_cases hu : u = 0
  · exfalso
    apply hcross
    rw [hu]
    have hzero := cross_smul_left (0 : ℝ) v v
    simpa using hzero
  rw [LinearIndependent.pair_iff' hu]
  intro a hv
  apply hcross
  rw [← hv, cross_smul_right, cross_self, smul_zero]

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

theorem normal_eq_pos_smul_neg_cross_of_support {n u v w : E3}
    (hnu : (⟪n, u⟫ : ℝ) = 0) (hnv : (⟪n, v⟫ : ℝ) = 0)
    (hli : LinearIndependent ℝ ![u, v])
    (hopp : (⟪n, w⟫ : ℝ) < 0)
    (hdet : 0 < (⟪cross u v, w⟫ : ℝ)) :
    ∃ lam : ℝ, 0 < lam ∧ n = lam • (-(cross u v)) := by
  obtain ⟨s, hs⟩ := perp_two_imp_parallel_cross hnu hnv hli
  have hsneg : s < 0 := by
    have hdot : (⟪n, w⟫ : ℝ) = s * ⟪cross u v, w⟫ := by
      rw [hs, real_inner_smul_left]
    nlinarith
  refine ⟨-s, by linarith, ?_⟩
  rw [hs]
  module

theorem face_normal_eq_pos_smul_neg_cross_of_coplanar_edges
    {D : Type*} [Fintype D] [DecidableEq D] {M : CombMap D}
    (P : TriangulatedEuclideanPolyhedron M) (f : M.Face)
    (v a b w : M.Vertex)
    (hv : inner ℝ (P.outward_normal f) (P.pos v - P.face_point f) = 0)
    (ha : inner ℝ (P.outward_normal f) (P.pos a - P.face_point f) = 0)
    (hb : inner ℝ (P.outward_normal f) (P.pos b - P.face_point f) = 0)
    (hli : LinearIndependent ℝ ![P.pos a - P.pos v, P.pos b - P.pos v])
    (hw : ∀ i, w ≠ P.faceVertex f i)
    (hdet : 0 < inner ℝ (cross (P.pos a - P.pos v) (P.pos b - P.pos v))
      (P.pos w - P.pos v)) :
    ∃ lam : ℝ, 0 < lam ∧
      P.outward_normal f = lam • (-(cross (P.pos a - P.pos v) (P.pos b - P.pos v))) := by
  have hstrict0 := P.face_support_strict f w hw
  have hstrict : inner ℝ (P.outward_normal f) (P.pos w - P.pos v) < 0 := by
    have hrewrite :
        inner ℝ (P.outward_normal f) (P.pos w - P.pos v) =
          inner ℝ (P.outward_normal f) (P.pos w - P.face_point f) -
            inner ℝ (P.outward_normal f) (P.pos v - P.face_point f) := by
      calc
        inner ℝ (P.outward_normal f) (P.pos w - P.pos v)
            = inner ℝ (P.outward_normal f)
                ((P.pos w - P.face_point f) - (P.pos v - P.face_point f)) := by
                congr 1
                module
        _ = inner ℝ (P.outward_normal f) (P.pos w - P.face_point f) -
              inner ℝ (P.outward_normal f) (P.pos v - P.face_point f) := by
                rw [inner_sub_right]
    rw [hrewrite, hv, sub_zero]
    exact hstrict0
  have hperp1 : inner ℝ (P.outward_normal f) (P.pos a - P.pos v) = 0 :=
    inner_sub_of_plane_eq ha hv
  have hperp2 : inner ℝ (P.outward_normal f) (P.pos b - P.pos v) = 0 :=
    inner_sub_of_plane_eq hb hv
  exact normal_eq_pos_smul_neg_cross_of_support hperp1 hperp2 hli hstrict hdet

/-- The outward normal of `dartFace e` is the negative cross product of the two
face edges emanating from `tail e`, up to a positive scalar, once a strict
off-face vertex supplies the sign. -/
theorem face_normal_eq_pos_smul_neg_cross_of_dart_edges
    {D : Type*} [Fintype D] [DecidableEq D] {M : CombMap D}
    (P : TriangulatedEuclideanPolyhedron M) (e : D) (w : M.Vertex)
    (hw : ∀ i, w ≠ P.faceVertex (M.dartFace e) i)
    (hdet : 0 < inner ℝ
      (cross
        (P.pos (M.head e) - P.pos (M.tail e))
        (P.pos (M.tail (M.φ (M.φ e))) - P.pos (M.tail e)))
      (P.pos w - P.pos (M.tail e))) :
    ∃ lam : ℝ, 0 < lam ∧
      P.outward_normal (M.dartFace e) =
        lam • (-
          cross
            (P.pos (M.head e) - P.pos (M.tail e))
            (P.pos (M.tail (M.φ (M.φ e))) - P.pos (M.tail e))) := by
  have hv : inner ℝ (P.outward_normal (M.dartFace e))
      (P.pos (M.tail e) - P.face_point (M.dartFace e)) = 0 :=
    face_plane_dart P e
  have ha : inner ℝ (P.outward_normal (M.dartFace e))
      (P.pos (M.head e) - P.face_point (M.dartFace e)) = 0 := by
    have h := face_plane_dart P (M.φ e)
    simpa [M.tail_phi] using h
  have hb : inner ℝ (P.outward_normal (M.dartFace e))
      (P.pos (M.tail (M.φ (M.φ e))) - P.face_point (M.dartFace e)) = 0 := by
    have h := face_plane_dart P (M.φ (M.φ e))
    simpa using h
  have hcrossne :
      cross
        (P.pos (M.head e) - P.pos (M.tail e))
        (P.pos (M.tail (M.φ (M.φ e))) - P.pos (M.tail e)) ≠ 0 := by
    intro hzero
    rw [hzero] at hdet
    simp at hdet
  have hli : LinearIndependent ℝ
      ![P.pos (M.head e) - P.pos (M.tail e),
        P.pos (M.tail (M.φ (M.φ e))) - P.pos (M.tail e)] :=
    linearIndependent_pair_of_cross_ne_zero hcrossne
  exact face_normal_eq_pos_smul_neg_cross_of_coplanar_edges
    (P := P) (f := M.dartFace e)
    (v := M.tail e) (a := M.head e)
    (b := M.tail (M.φ (M.φ e))) (w := w)
    hv ha hb hli hw hdet

private lemma fin_sub_one_add_one {n : ℕ} [NeZero n] (i : Fin n) :
    i - 1 + 1 = i := by
  rw [sub_add_cancel]

private lemma vertexLinkGeometry_exists_noninc_face
    {D : Type*} [Fintype D] [DecidableEq D] {M : CombMap D}
    {P : TriangulatedEuclideanPolyhedron M} {v : M.Vertex}
    (LG : VertexLinkGeometry P v) (i : Fin (LG.n + 1)) :
    ∃ j : Fin (LG.n + 1), j ≠ i ∧ j ≠ i + 1 := by
  by_contra hcon
  push_neg at hcon
  have hsub : (Finset.univ : Finset (Fin (LG.n + 1))) ⊆ {i, i + 1} := by
    intro j _
    rcases eq_or_ne j i with hji | hji
    · simp [hji]
    · have := hcon j hji
      simp [this]
  have hle := Finset.card_le_card hsub
  simp only [Finset.card_univ, Fintype.card_fin] at hle
  have hle2 : ({i, i + 1} : Finset (Fin (LG.n + 1))).card ≤ 2 :=
    le_trans (Finset.card_insert_le _ _) (by simp)
  have := LG.hn
  omega

private lemma normal_neg_raw_cross_to_edgeDir_cross
    (S : VertexStar) (i j : Fin (S.n + 1)) {normal : E3}
    {lam : ℝ} (hlam : 0 < lam)
    (hraw : normal = lam • (-(cross (S.rawDir i) (S.rawDir j)))) :
    ∃ lam' : ℝ, 0 < lam' ∧
      normal = lam' • (-(cross (S.edgeDir i : E3) (S.edgeDir j : E3))) := by
  let c : ℝ := ‖S.rawDir i‖⁻¹ * ‖S.rawDir j‖⁻¹
  have hcpos : 0 < c := mul_pos (S.inv_norm_pos i) (S.inv_norm_pos j)
  have hcross :
      cross (S.edgeDir i : E3) (S.edgeDir j : E3) =
        c • cross (S.rawDir i) (S.rawDir j) := by
    rw [S.edgeDir_coe i, S.edgeDir_coe j, cross_smul_left, cross_smul_right]
    simp [c, smul_smul, mul_comm, mul_left_comm, mul_assoc]
  refine ⟨lam / c, div_pos hlam hcpos, ?_⟩
  rw [hraw, hcross]
  have hcne : c ≠ 0 := ne_of_gt hcpos
  have hcoef : lam / c * c = lam := by
    field_simp [hcne]
  have hcoef_neg : lam / c * -c = -lam := by
    nlinarith
  conv_lhs => rw [smul_neg, ← neg_smul]
  conv_rhs => rw [← neg_smul, smul_smul]
  rw [hcoef_neg]

theorem face_normal_eq_pos_smul_neg_cross_of_strict_support
    {D : Type*} [Fintype D] [DecidableEq D] {M : CombMap D}
    (P : TriangulatedEuclideanPolyhedron M) (f : M.Face) (w : M.Vertex)
    (hw : ∀ i, w ≠ P.faceVertex f i)
    (hdet : 0 < inner ℝ
      (cross
        (P.pos (M.tail (M.φ (P.faceDart f))) - P.pos (M.tail (P.faceDart f)))
        (P.pos (M.tail (M.φ (M.φ (P.faceDart f)))) - P.pos (M.tail (P.faceDart f))))
      (P.pos w - P.pos (M.tail (P.faceDart f)))) :
    ∃ lam : ℝ, 0 < lam ∧
      P.outward_normal f =
        lam • (-
          cross
            (P.pos (M.tail (M.φ (P.faceDart f))) - P.pos (M.tail (P.faceDart f)))
            (P.pos (M.tail (M.φ (M.φ (P.faceDart f)))) - P.pos (M.tail (P.faceDart f)))) := by
  let u : E3 :=
    P.pos (M.tail (M.φ (P.faceDart f))) - P.pos (M.tail (P.faceDart f))
  let v : E3 :=
    P.pos (M.tail (M.φ (M.φ (P.faceDart f)))) - P.pos (M.tail (P.faceDart f))
  have hpar := outward_normal_parallel_faceDart_cross P f
  obtain ⟨s, hs⟩ := hpar
  have hv0 : P.faceVertex f 0 = M.tail (P.faceDart f) := by
    have h := congrFun (P.face_vertices_match f) 0
    simpa using h
  have hp0 : inner ℝ (P.outward_normal f)
      (P.pos (M.tail (P.faceDart f)) - P.face_point f) = 0 := by
    simpa [hv0] using P.face_plane f 0
  have hstrict0 := P.face_support_strict f w hw
  have hstrict : inner ℝ (P.outward_normal f)
      (P.pos w - P.pos (M.tail (P.faceDart f))) < 0 := by
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
    exact hstrict0
  have hli : LinearIndependent ℝ ![u, v] := by
    let p : Fin 3 → E3 :=
      ![P.pos (M.tail (P.faceDart f)),
        P.pos (M.tail (M.φ (P.faceDart f))),
        P.pos (M.tail (M.φ (M.φ (P.faceDart f))))]
    have hli0 : LinearIndependent ℝ ![p 1 - p 0, p 2 - p 0] :=
      linearIndependent_pair_vsub_of_affineIndependent_fin3 (P.face_nondegenerate f)
    simpa [p, u, v] using hli0
  have hperp1 : inner ℝ (P.outward_normal f) u = 0 := by
    have hv1 : P.faceVertex f 1 = M.tail (M.φ (P.faceDart f)) := by
      have h := congrFun (P.face_vertices_match f) 1
      simpa using h
    have hp1 : inner ℝ (P.outward_normal f)
        (P.pos (M.tail (M.φ (P.faceDart f))) - P.face_point f) = 0 := by
      simpa [hv1] using P.face_plane f 1
    simpa [u] using inner_sub_of_plane_eq hp1 hp0
  have hperp2 : inner ℝ (P.outward_normal f) v = 0 := by
    have hv2 : P.faceVertex f 2 = M.tail (M.φ (M.φ (P.faceDart f))) := by
      have h := congrFun (P.face_vertices_match f) 2
      simpa using h
    have hp2 : inner ℝ (P.outward_normal f)
        (P.pos (M.tail (M.φ (M.φ (P.faceDart f)))) - P.face_point f) = 0 := by
      simpa [hv2] using P.face_plane f 2
    simpa [v] using inner_sub_of_plane_eq hp2 hp0
  have hdet' : 0 < inner ℝ (cross u v) (P.pos w - P.pos (M.tail (P.faceDart f))) := by
    simpa [u, v] using hdet
  exact normal_eq_pos_smul_neg_cross_of_support hperp1 hperp2 hli hstrict hdet'

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

theorem linkAngle_vertexLink_eq_pi_sub_normal_angle
    (S : VertexStar) (i : Fin (S.n + 1)) {n_f n_g : E3}
    (hta :
      tangentToVec (S.edgeDir i : E3) (S.edgeDir (i - 1) : E3) ≠ 0)
    (htc :
      tangentToVec (S.edgeDir i : E3) (S.edgeDir (i + 1) : E3) ≠ 0)
    (hX : cross (S.edgeDir (i - 1) : E3) (S.edgeDir i : E3) ≠ 0)
    (hY : cross (S.edgeDir i : E3) (S.edgeDir (i + 1) : E3) ≠ 0)
    (horient :
      ∃ l m : ℝ,
        0 < l ∧ 0 < m ∧
          ((n_f = l • cross (S.edgeDir (i - 1) : E3) (S.edgeDir i : E3) ∧
              n_g = m • cross (S.edgeDir i : E3) (S.edgeDir (i + 1) : E3)) ∨
           (n_f = l • (-(cross (S.edgeDir (i - 1) : E3) (S.edgeDir i : E3))) ∧
              n_g = m • (-(cross (S.edgeDir i : E3) (S.edgeDir (i + 1) : E3)))))) :
    linkAngle S.vertexLink i = Real.pi - InnerProductGeometry.angle n_f n_g := by
  rw [linkAngle]
  simp only [VertexStar.vertexLink_apply]
  rw [sphAngle]
  show InnerProductGeometry.angle
      (tangentTo (S.edgeDir i) (S.edgeDir (i - 1)))
      (tangentTo (S.edgeDir i) (S.edgeDir (i + 1)))
        = Real.pi - InnerProductGeometry.angle n_f n_g
  rw [tangentTo_eq_tangentToVec, tangentTo_eq_tangentToVec]
  exact sphAngle_eq_pi_sub_normal_angle
    (a := (S.edgeDir (i - 1) : E3))
    (b := (S.edgeDir i : E3))
    (c := (S.edgeDir (i + 1) : E3))
    (n_f := n_f) (n_g := n_g)
    (S.edgeDir (i - 1)).2 (S.edgeDir i).2 (S.edgeDir (i + 1)).2
    hta htc hX hY horient

theorem dihedralAngleAtDart_eq_linkAngle_of_neighbors
    {D : Type*} [Fintype D] [DecidableEq D] {M : CombMap D}
    (P : TriangulatedEuclideanPolyhedron M) (d : D)
    (LG : VertexLinkGeometry P (M.tail d)) (J : Fin (LG.n + 1))
    (hprev : LG.nbr (J - 1) = M.head (M.σ d))
    (hcenter : LG.nbr J = M.head d)
    (hnext : LG.nbr (J + 1) = M.head (M.σ.symm d)) :
    dihedralAngleAtDart P d =
      linkAngle (vertexStarOfEuclidean P (M.tail d) LG).vertexLink J := by
  let S : VertexStar := vertexStarOfEuclidean P (M.tail d) LG
  let cJ : Fin (S.n + 1) := (show Fin (S.n + 1) from J)
  change dihedralAngleAtDart P d = linkAngle S.vertexLink cJ
  have hJprev_next : (J - 1) + 1 = J := fin_sub_one_add_one J
  have hcJprev_next : (cJ - 1) + 1 = cJ := fin_sub_one_add_one cJ
  obtain ⟨wF, hwF_ne0, hwF_ne1⟩ := vertexLinkGeometry_exists_noninc_face LG (J - 1)
  obtain ⟨wG, hwG_ne0, hwG_ne1⟩ := vertexLinkGeometry_exists_noninc_face LG J
  have hface_sigma : M.dartFace (M.σ d) = M.dartFace (M.α d) := by
    have hσφ : M.σ d = M.φ (M.α d) := by
      change M.σ d = (M.σ * M.α) (M.α d)
      rw [Equiv.Perm.mul_apply, M.alpha_alpha]
    rw [hσφ, M.dartFace_phi]
  have htail_sigma : M.tail (M.σ d) = M.tail d := M.tail_sigma d
  have htail_phi2_sigma :
      M.tail (M.φ (M.φ (M.σ d))) = M.head d := by
    rw [tail_phi_phi_eq_head_sigma_symm_of_triangular_euclidean P (M.σ d),
      Equiv.symm_apply_apply]
  have hhead_phi_sigma : M.head (M.φ (M.σ d)) = M.head d := by
    simpa [M.tail_phi] using htail_phi2_sigma
  have htail_phi2_d :
      M.tail (M.φ (M.φ d)) = M.head (M.σ.symm d) :=
    tail_phi_phi_eq_head_sigma_symm_of_triangular_euclidean P d
  have hhead_phi_d : M.head (M.φ d) = M.head (M.σ.symm d) := by
    simpa [M.tail_phi] using htail_phi2_d
  have hdetF : 0 < inner ℝ
      (cross
        (P.pos (M.head (M.σ d)) - P.pos (M.tail d))
        (P.pos (M.head d) - P.pos (M.tail d)))
      (P.pos (LG.nbr wF) - P.pos (M.tail d)) := by
    have h := LG.turn_strict (J - 1) wF hwF_ne0 hwF_ne1
    rw [← det3_eq_spherical, det3_eq_inner_cross] at h
    simpa [hprev, hcenter, hJprev_next] using h
  have hwF_face : ∀ k, LG.nbr wF ≠ P.faceVertex (M.dartFace (M.σ d)) k := by
    intro k heq
    have hcases := faceVertex_eq_tail_or_head_or_tail_phi2_of_dartFace_eq
      (P := P) (e := M.σ d) (f := M.dartFace (M.σ d)) rfl k
    rw [← heq, htail_sigma, htail_phi2_sigma] at hcases
    have hnon := LG.nonincident (J - 1) wF hwF_ne0 hwF_ne1
    have hnon' :
        ¬LG.nbr wF = M.tail d ∧
          ¬LG.nbr wF = M.head (M.σ d) ∧ ¬LG.nbr wF = M.head d := by
      simpa [hprev, hJprev_next, hcenter] using hnon
    rcases hcases with htail | hsig | hhead
    · exact hnon'.1 htail
    · exact hnon'.2.1 hsig
    · exact hnon'.2.2 hhead
  obtain ⟨lamF, hlamF, hnormalFraw⟩ :=
    face_normal_eq_pos_smul_neg_cross_of_dart_edges P (M.σ d) (LG.nbr wF)
      hwF_face (by simpa [htail_sigma, htail_phi2_sigma] using hdetF)
  have hrawF_left :
      S.rawDir (cJ - 1) =
        P.pos (M.head (M.σ d)) - P.pos (M.tail d) := by
    unfold S cJ vertexStarOfEuclidean VertexLinkGeometry.toVertexStar VertexStar.rawDir
    change P.pos (LG.nbr (J - 1)) - P.pos (M.tail d) =
      P.pos (M.head (M.σ d)) - P.pos (M.tail d)
    rw [hprev]
  have hrawF_right :
      S.rawDir cJ =
        P.pos (M.head d) - P.pos (M.tail d) := by
    unfold S cJ vertexStarOfEuclidean VertexLinkGeometry.toVertexStar VertexStar.rawDir
    change P.pos (LG.nbr J) - P.pos (M.tail d) =
      P.pos (M.head d) - P.pos (M.tail d)
    rw [hcenter]
  have hnormalFraw' :
      dartNormal P (M.α d) =
        lamF • (-(cross
          (S.rawDir (cJ - 1))
          (S.rawDir cJ))) := by
    rw [hrawF_left, hrawF_right]
    unfold dartNormal
    rw [← hface_sigma]
    simpa [htail_sigma, hhead_phi_sigma, smul_neg] using hnormalFraw
  obtain ⟨lamF', hlamF', hnormalF⟩ :=
    normal_neg_raw_cross_to_edgeDir_cross S
      (cJ - 1) cJ hlamF hnormalFraw'
  have hdetG : 0 < inner ℝ
      (cross
        (P.pos (M.head d) - P.pos (M.tail d))
        (P.pos (M.head (M.σ.symm d)) - P.pos (M.tail d)))
      (P.pos (LG.nbr wG) - P.pos (M.tail d)) := by
    have h := LG.turn_strict J wG hwG_ne0 hwG_ne1
    rw [← det3_eq_spherical, det3_eq_inner_cross] at h
    simpa [hcenter, hnext] using h
  have hwG_face : ∀ k, LG.nbr wG ≠ P.faceVertex (M.dartFace d) k := by
    intro k heq
    have hcases := faceVertex_eq_tail_or_head_or_tail_phi2_of_dartFace_eq
      (P := P) (e := d) (f := M.dartFace d) rfl k
    rw [← heq, htail_phi2_d] at hcases
    have hnon := LG.nonincident J wG hwG_ne0 hwG_ne1
    have hnon' :
        ¬LG.nbr wG = M.tail d ∧
          ¬LG.nbr wG = M.head d ∧ ¬LG.nbr wG = M.head (M.σ.symm d) := by
      simpa [hcenter, hnext] using hnon
    rcases hcases with htail | hhead | hnext'
    · exact hnon'.1 htail
    · exact hnon'.2.1 hhead
    · exact hnon'.2.2 hnext'
  obtain ⟨lamG, hlamG, hnormalGraw⟩ :=
    face_normal_eq_pos_smul_neg_cross_of_dart_edges P d (LG.nbr wG)
      hwG_face (by simpa [htail_phi2_d] using hdetG)
  have hrawG_right :
      S.rawDir (cJ + 1) =
        P.pos (M.head (M.σ.symm d)) - P.pos (M.tail d) := by
    unfold S cJ vertexStarOfEuclidean VertexLinkGeometry.toVertexStar VertexStar.rawDir
    change P.pos (LG.nbr (J + 1)) - P.pos (M.tail d) =
      P.pos (M.head (M.σ.symm d)) - P.pos (M.tail d)
    rw [hnext]
  have hnormalGraw' :
      dartNormal P d =
        lamG • (-(cross
          (S.rawDir cJ)
          (S.rawDir (cJ + 1)))) := by
    rw [hrawF_right, hrawG_right]
    unfold dartNormal
    simpa [hhead_phi_d, smul_neg] using hnormalGraw
  obtain ⟨lamG', hlamG', hnormalG⟩ :=
    normal_neg_raw_cross_to_edgeDir_cross S
      cJ (cJ + 1) hlamG hnormalGraw'
  have hta :
      tangentToVec (S.edgeDir cJ : E3)
          (S.edgeDir (cJ - 1) : E3) ≠ 0 := by
    intro hzero
    have ht : tangentTo (S.edgeDir cJ)
        (S.edgeDir (cJ - 1)) = 0 := by
      simpa [tangentTo_eq_tangentToVec] using hzero
    have hnot := (tangentTo_eq_zero_iff
      (S.edgeDir cJ)
      (S.edgeDir (cJ - 1))).mp ht
    have hsa : ShortArc (S.edgeDir cJ)
        (S.edgeDir (cJ - 1)) := by
      have h0 := S.edgeDir_shortArc (cJ - 1)
      simpa [hcJprev_next] using h0.symm
    exact hnot hsa
  have htc :
      tangentToVec (S.edgeDir cJ : E3)
          (S.edgeDir (cJ + 1) : E3) ≠ 0 := by
    intro hzero
    have ht : tangentTo (S.edgeDir cJ)
        (S.edgeDir (cJ + 1)) = 0 := by
      simpa [tangentTo_eq_tangentToVec] using hzero
    have hnot := (tangentTo_eq_zero_iff
      (S.edgeDir cJ)
      (S.edgeDir (cJ + 1))).mp ht
    exact hnot (S.edgeDir_shortArc cJ)
  have hX :
      cross (S.edgeDir (cJ - 1) : E3)
        (S.edgeDir cJ : E3) ≠ 0 := by
    have hsa := S.edgeDir_shortArc (cJ - 1)
    exact ProofsInTheBook.SphericalCongruence.cross_ne_zero_of_shortArc
      (by simpa [hcJprev_next] using hsa)
  have hY :
      cross (S.edgeDir cJ : E3)
        (S.edgeDir (cJ + 1) : E3) ≠ 0 :=
    ProofsInTheBook.SphericalCongruence.cross_ne_zero_of_shortArc
      (S.edgeDir_shortArc cJ)
  have hlink := linkAngle_vertexLink_eq_pi_sub_normal_angle
    (S := S) (i := cJ)
    (n_f := dartNormal P (M.α d)) (n_g := dartNormal P d)
    hta htc hX hY
    ⟨lamF', lamG', hlamF', hlamG', Or.inr ⟨hnormalF, hnormalG⟩⟩
  unfold dihedralAngleAtDart
  rw [hlink, InnerProductGeometry.angle_comm]

theorem dihedralAngleAtDart_eq_linkAngle
    {D : Type*} [Fintype D] [DecidableEq D] {M : CombMap D}
    (P : TriangulatedEuclideanPolyhedron M) (d : D)
    (LG : VertexLinkGeometry P (M.tail d)) (J : Fin (LG.n + 1))
    (hprev : LG.nbr (J - 1) = M.head (M.σ d))
    (hcenter : LG.nbr J = M.head d)
    (hnext : LG.nbr (J + 1) = M.head (M.σ.symm d)) :
    dihedralAngleAtDart P d =
      linkAngle (vertexStarOfEuclidean P (M.tail d) LG).vertexLink J :=
  dihedralAngleAtDart_eq_linkAngle_of_neighbors P d LG J hprev hcenter hnext

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
#print axioms ProofsInTheBook.Ch13SphAngle.linkAngle_vertexLink_eq_pi_sub_normal_angle
#print axioms ProofsInTheBook.Ch13SphAngle.tangent_angle_eq_dihedralAngleAtDart_of_oriented
#print axioms ProofsInTheBook.Ch13SphAngle.perp_two_imp_parallel_cross
#print axioms ProofsInTheBook.Ch13SphAngle.outward_normal_parallel_faceDart_cross
#print axioms ProofsInTheBook.Ch13SphAngle.face_parallel_scalar_support_le
#print axioms ProofsInTheBook.Ch13SphAngle.normal_eq_pos_smul_neg_cross_of_support
#print axioms ProofsInTheBook.Ch13SphAngle.face_normal_eq_pos_smul_neg_cross_of_coplanar_edges
#print axioms ProofsInTheBook.Ch13SphAngle.face_normal_eq_pos_smul_neg_cross_of_strict_support
#print axioms ProofsInTheBook.Ch13SphAngle.tail_mem_faceVertex
#print axioms ProofsInTheBook.Ch13SphAngle.face_plane_dart
#print axioms ProofsInTheBook.Ch13SphAngle.phi_cube_eq_self_of_triangular_euclidean
#print axioms ProofsInTheBook.Ch13SphAngle.tail_phi_phi_eq_head_sigma_symm_of_triangular_euclidean
#print axioms ProofsInTheBook.Ch13SphAngle.face_normal_eq_pos_smul_neg_cross_of_dart_edges
#print axioms ProofsInTheBook.Ch13SphAngle.dihedralAngleAtDart_eq_linkAngle

end ProofsInTheBook.Ch13SphAngle
