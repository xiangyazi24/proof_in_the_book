import ProofsInTheBook.Ch13Realization
import ProofsInTheBook.Ch13ComponentClose
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Geometry.Euclidean.Angle.Unoriented.Basic
import Mathlib.LinearAlgebra.AffineSpace.Independent
import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
import Mathlib.Data.Fin.Tuple.Reflection

/-!
# Euclidean polyhedron witnesses for Chapter 13

This file starts the avenue-(b) Euclidean realization interface: actual
coordinates in `ℝ³`, triangular faces matched to the combinatorial map, and
supporting planes for convexity.
-/

noncomputable section

open scoped Classical
open ProofsInTheBook.PlanarMap ProofsInTheBook.PlanarMap.CombMap
open ProofsInTheBook.Ch13MarkedSphere

namespace ProofsInTheBook.Ch13Euclidean

variable {D : Type*} [Fintype D] [DecidableEq D]

/-- The ambient Euclidean space for the chapter-13 geometric witness. -/
abbrev E3 : Type := EuclideanSpace ℝ (Fin 3)

/-- Three vertices assigned to a face, in cyclic combinatorial order. -/
abbrev FaceVertices (M : CombMap D) := M.Face → Fin 3 → M.Vertex

/--
A triangulated Euclidean polyhedron carried by a combinatorial map.

The field `faceDart` chooses a dart on every face; `faceVertex` is required to
be the three tails of that face in the `φ`-order from the chosen dart.  The
supporting halfspace certificate orients every face normal outward, so all
vertices lie in the non-positive halfspace of the face plane.

The vertex-link cyclic order is deliberately not part of this b1 interface;
that is the later b3 residue.
-/
structure TriangulatedEuclideanPolyhedron (M : CombMap D) where
  /-- Vertex coordinates in `ℝ³`. -/
  pos : M.Vertex → E3
  /-- A representative dart on each face. -/
  faceDart : M.Face → D
  /-- The representative really lies on the face it represents. -/
  faceDart_face : ∀ f, M.dartFace (faceDart f) = f
  /-- The three combinatorial vertices of a face, in cyclic order. -/
  faceVertex : FaceVertices M
  /-- Face vertices are exactly the tails along one `φ`-cycle from `faceDart`. -/
  face_vertices_match : ∀ f,
    faceVertex f =
      ![M.tail (faceDart f),
        M.tail (M.φ (faceDart f)),
        M.tail (M.φ (M.φ (faceDart f)))]
  /-- Every combinatorial face is triangular. -/
  every_face_triangle : M.FaceRegular 3
  /-- Edges are realized by distinct points. -/
  edge_nondegenerate : ∀ d, pos (M.tail d) ≠ pos (M.head d)
  /-- The three points of each face are affinely independent. -/
  face_nondegenerate : ∀ f,
    AffineIndependent ℝ
      (![pos (M.tail (faceDart f)),
        pos (M.tail (M.φ (faceDart f))),
        pos (M.tail (M.φ (M.φ (faceDart f))))] : Fin 3 → E3)
  /-- A selected point on each supporting face plane. -/
  face_point : M.Face → E3
  /-- An outward normal for each face plane. -/
  outward_normal : M.Face → E3
  /-- The three face vertices lie on the chosen plane. -/
  face_plane : ∀ f i,
    inner ℝ (outward_normal f) (pos (faceVertex f i) - face_point f) = 0
  /-- Convexity as a supporting halfspace certificate for every face. -/
  face_supporting_halfspace : ∀ f v,
    inner ℝ (outward_normal f) (pos v - face_point f) ≤ 0

/-! ## The regular tetrahedron witness -/

/-- The first tetrahedron vertex. -/
def tetraPoint₀ : E3 := !₂[(1 : ℝ), 1, 1]

/-- The second tetrahedron vertex. -/
def tetraPoint₁ : E3 := !₂[(1 : ℝ), -1, -1]

/-- The third tetrahedron vertex. -/
def tetraPoint₂ : E3 := !₂[(-1 : ℝ), 1, -1]

/-- The fourth tetrahedron vertex. -/
def tetraPoint₃ : E3 := !₂[(-1 : ℝ), -1, 1]

/-- The tetrahedron point carried by a dart, constant on each `σ`-cycle. -/
def tetraDartPoint : Fin 12 → E3
  | 0 | 1 | 2 => tetraPoint₀
  | 3 | 4 | 5 => tetraPoint₁
  | 6 | 7 | 8 => tetraPoint₂
  | _ => tetraPoint₃

private theorem tetraDartPoint_sigma_same {a b : Fin 12}
    (h : tetraMap.σ.SameCycle a b) : tetraDartPoint a = tetraDartPoint b := by
  fin_cases a <;> fin_cases b <;>
    first | rfl | exfalso; exact (by decide : ¬ tetraMap.σ.SameCycle _ _) h

/-- The tetrahedron vertex-coordinate map. -/
def tetraPos (v : tetraMap.Vertex) : E3 :=
  Quotient.lift tetraDartPoint (fun _ _ h => tetraDartPoint_sigma_same h) v

@[simp] private theorem tetraPos_tail (d : Fin 12) :
    tetraPos (tetraMap.tail d) = tetraDartPoint d := rfl

@[simp] private theorem tetraPos_mk (d : Fin 12) :
    tetraPos (Quotient.mk (cycleSetoid tetraMap.σ) d) = tetraDartPoint d := rfl

@[simp] private theorem tetraPos_mk_sigma (d : Fin 12) :
    tetraPos (Quotient.mk (cycleSetoid tetraSigma) d) = tetraDartPoint d := rfl

@[simp] private theorem tetraAlpha_apply (d : Fin 12) :
    tetraAlpha d =
      match d with
      | 0 => 3 | 1 => 6 | 2 => 9 | 3 => 0 | 4 => 7 | 5 => 10
      | 6 => 1 | 7 => 4 | 8 => 11 | 9 => 2 | 10 => 5 | _ => 8 := by
  fin_cases d <;> decide

@[simp] private theorem tetraPhi_apply (d : Fin 12) :
    tetraMap.φ d =
      match d with
      | 0 => 5 | 5 => 9 | 9 => 0
      | 1 => 7 | 7 => 3 | 3 => 1
      | 2 => 11 | 11 => 6 | 6 => 2
      | 4 => 8 | 8 => 10 | _ => 4 := by
  fin_cases d <;> decide

/-- A canonical dart representative for each tetrahedron face. -/
def tetraFaceRepDart : Fin 12 → Fin 12
  | 0 | 5 | 9 => 0
  | 1 | 7 | 3 => 1
  | 2 | 11 | 6 => 2
  | _ => 4

private theorem tetraFaceRepDart_phi_same {a b : Fin 12}
    (h : tetraMap.φ.SameCycle a b) : tetraFaceRepDart a = tetraFaceRepDart b := by
  fin_cases a <;> fin_cases b <;>
    first | rfl | exfalso; exact (by decide : ¬ tetraMap.φ.SameCycle _ _) h

/-- The selected dart on a tetrahedron face. -/
def tetraFaceDart (f : tetraMap.Face) : Fin 12 :=
  Quotient.lift tetraFaceRepDart (fun _ _ h => tetraFaceRepDart_phi_same h) f

theorem tetraFaceDart_face (f : tetraMap.Face) :
    tetraMap.dartFace (tetraFaceDart f) = f := by
  refine Quotient.inductionOn f ?_
  intro d
  fin_cases d <;> decide

/-- The three vertices of a tetrahedron face in `φ`-order from `tetraFaceDart`. -/
def tetraFaceVertex (f : tetraMap.Face) : Fin 3 → tetraMap.Vertex :=
  ![tetraMap.tail (tetraFaceDart f),
    tetraMap.tail (tetraMap.φ (tetraFaceDart f)),
    tetraMap.tail (tetraMap.φ (tetraMap.φ (tetraFaceDart f)))]

private def fin2NeZeroEquiv : Fin 2 ≃ {x : Fin 3 // x ≠ 0} where
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

private theorem affineIndependent_tetraFace₀ :
    AffineIndependent ℝ (![tetraPoint₀, tetraPoint₁, tetraPoint₃] : Fin 3 → E3) := by
  rw [affineIndependent_iff_linearIndependent_vsub ℝ _ (0 : Fin 3)]
  refine (linearIndependent_equiv fin2NeZeroEquiv).mp ?_
  rw [linearIndependent_fin2]
  constructor
  · intro h
    have h0 := congrArg (fun x : E3 => WithLp.ofLp x (0 : Fin 3)) h
    simp [fin2NeZeroEquiv, tetraPoint₀, tetraPoint₁, tetraPoint₃] at h0
    norm_num at h0
  · intro a h
    have h0 := congrArg (fun x : E3 => WithLp.ofLp x (0 : Fin 3)) h
    have h1 := congrArg (fun x : E3 => WithLp.ofLp x (1 : Fin 3)) h
    simp [fin2NeZeroEquiv, tetraPoint₀, tetraPoint₁, tetraPoint₃] at h0 h1
    norm_num at h0 h1
    nlinarith

private theorem affineIndependent_tetraFace₁ :
    AffineIndependent ℝ (![tetraPoint₀, tetraPoint₂, tetraPoint₁] : Fin 3 → E3) := by
  rw [affineIndependent_iff_linearIndependent_vsub ℝ _ (0 : Fin 3)]
  refine (linearIndependent_equiv fin2NeZeroEquiv).mp ?_
  rw [linearIndependent_fin2]
  constructor
  · intro h
    have h1 := congrArg (fun x : E3 => WithLp.ofLp x (1 : Fin 3)) h
    simp [fin2NeZeroEquiv, tetraPoint₀, tetraPoint₁, tetraPoint₂] at h1
    norm_num at h1
  · intro a h
    have h0 := congrArg (fun x : E3 => WithLp.ofLp x (0 : Fin 3)) h
    simp [fin2NeZeroEquiv, tetraPoint₀, tetraPoint₁, tetraPoint₂] at h0
    norm_num at h0

private theorem affineIndependent_tetraFace₂ :
    AffineIndependent ℝ (![tetraPoint₀, tetraPoint₃, tetraPoint₂] : Fin 3 → E3) := by
  rw [affineIndependent_iff_linearIndependent_vsub ℝ _ (0 : Fin 3)]
  refine (linearIndependent_equiv fin2NeZeroEquiv).mp ?_
  rw [linearIndependent_fin2]
  constructor
  · intro h
    have h0 := congrArg (fun x : E3 => WithLp.ofLp x (0 : Fin 3)) h
    simp [fin2NeZeroEquiv, tetraPoint₀, tetraPoint₂, tetraPoint₃] at h0
    norm_num at h0
  · intro a h
    have h1 := congrArg (fun x : E3 => WithLp.ofLp x (1 : Fin 3)) h
    simp [fin2NeZeroEquiv, tetraPoint₀, tetraPoint₂, tetraPoint₃] at h1
    norm_num at h1

private theorem affineIndependent_tetraFace₃ :
    AffineIndependent ℝ (![tetraPoint₁, tetraPoint₂, tetraPoint₃] : Fin 3 → E3) := by
  rw [affineIndependent_iff_linearIndependent_vsub ℝ _ (0 : Fin 3)]
  refine (linearIndependent_equiv fin2NeZeroEquiv).mp ?_
  rw [linearIndependent_fin2]
  constructor
  · intro h
    have h0 := congrArg (fun x : E3 => WithLp.ofLp x (0 : Fin 3)) h
    simp [fin2NeZeroEquiv, tetraPoint₁, tetraPoint₂, tetraPoint₃] at h0
    norm_num at h0
  · intro a h
    have h1 := congrArg (fun x : E3 => WithLp.ofLp x (1 : Fin 3)) h
    simp [fin2NeZeroEquiv, tetraPoint₁, tetraPoint₂, tetraPoint₃] at h1
    norm_num at h1

private theorem tetra_edge_nondegenerate :
    ∀ d, tetraPos (tetraMap.tail d) ≠ tetraPos (tetraMap.head d) := by
  intro d h
  fin_cases d <;>
    (have hx := congrArg (fun x : E3 => WithLp.ofLp x (0 : Fin 3)) h <;>
     have hy := congrArg (fun x : E3 => WithLp.ofLp x (1 : Fin 3)) h <;>
     have hz := congrArg (fun x : E3 => WithLp.ofLp x (2 : Fin 3)) h <;>
     simp [tetraPos, tetraDartPoint, tetraMap, tetraAlpha_apply, CombMap.tail, CombMap.head,
       tetraPoint₀, tetraPoint₁, tetraPoint₂, tetraPoint₃] at hx hy hz <;>
     try norm_num at hx <;> try norm_num at hy <;> try norm_num at hz <;> linarith)

/-- Outward normal of the selected tetrahedron face. -/
def tetraOutwardNormal (f : tetraMap.Face) : E3 :=
  match tetraFaceDart f with
  | 0 => -tetraPoint₂
  | 1 => -tetraPoint₃
  | 2 => -tetraPoint₁
  | _ => -tetraPoint₀

/-- A point on the selected tetrahedron face plane. -/
def tetraFacePoint (f : tetraMap.Face) : E3 :=
  tetraPos (tetraMap.tail (tetraFaceDart f))

private theorem tetra_face_nondegenerate :
    ∀ f,
      AffineIndependent ℝ
        (![tetraPos (tetraMap.tail (tetraFaceDart f)),
          tetraPos (tetraMap.tail (tetraMap.φ (tetraFaceDart f))),
          tetraPos (tetraMap.tail (tetraMap.φ (tetraMap.φ (tetraFaceDart f))))] :
            Fin 3 → E3) := by
  intro f
  refine Quotient.inductionOn f ?_
  intro d
  fin_cases d <;>
    first
    | simpa [tetraFaceDart, tetraFaceRepDart, tetraDartPoint, tetraPhi_apply,
        tetraPoint₀, tetraPoint₁, tetraPoint₂, tetraPoint₃] using affineIndependent_tetraFace₀
    | simpa [tetraFaceDart, tetraFaceRepDart, tetraDartPoint, tetraPhi_apply,
        tetraPoint₀, tetraPoint₁, tetraPoint₂, tetraPoint₃] using affineIndependent_tetraFace₁
    | simpa [tetraFaceDart, tetraFaceRepDart, tetraDartPoint, tetraPhi_apply,
        tetraPoint₀, tetraPoint₁, tetraPoint₂, tetraPoint₃] using affineIndependent_tetraFace₂
    | simpa [tetraFaceDart, tetraFaceRepDart, tetraDartPoint, tetraPhi_apply,
        tetraPoint₀, tetraPoint₁, tetraPoint₂, tetraPoint₃] using affineIndependent_tetraFace₃

private theorem tetra_face_plane :
    ∀ f i, inner ℝ (tetraOutwardNormal f)
      (tetraPos (tetraFaceVertex f i) - tetraFacePoint f) = 0 := by
  intro f i
  refine Quotient.inductionOn f ?_
  intro d
  fin_cases d <;> fin_cases i <;>
    rw [PiLp.inner_apply, Fin.sum_univ_three] <;>
    simp [tetraOutwardNormal, tetraFacePoint, tetraFaceVertex, tetraFaceDart, tetraFaceRepDart,
      tetraPos, tetraDartPoint, tetraPhi_apply, CombMap.tail,
      tetraPoint₀, tetraPoint₁, tetraPoint₂, tetraPoint₃]

set_option maxHeartbeats 1000000 in
private theorem tetra_supporting_halfspace :
    ∀ f v, inner ℝ (tetraOutwardNormal f) (tetraPos v - tetraFacePoint f) ≤ 0 := by
  intro f v
  refine Quotient.inductionOn f ?_
  intro d
  refine Quotient.inductionOn v ?_
  intro x
  fin_cases d <;> fin_cases x <;>
    rw [PiLp.inner_apply, Fin.sum_univ_three] <;>
    simp [tetraOutwardNormal, tetraFacePoint, tetraFaceDart, tetraFaceRepDart,
      tetraPos, tetraDartPoint, tetraPhi_apply, CombMap.tail,
      tetraPoint₀, tetraPoint₁, tetraPoint₂, tetraPoint₃]

/-- The regular tetrahedron as a genuine Euclidean triangulated polyhedron. -/
def tetraEuclideanPolyhedron : TriangulatedEuclideanPolyhedron tetraMap where
  pos := tetraPos
  faceDart := tetraFaceDart
  faceDart_face := tetraFaceDart_face
  faceVertex := tetraFaceVertex
  face_vertices_match := by
    intro f
    rfl
  every_face_triangle := tetraMap_faceRegular_three
  edge_nondegenerate := tetra_edge_nondegenerate
  face_nondegenerate := tetra_face_nondegenerate
  face_point := tetraFacePoint
  outward_normal := tetraOutwardNormal
  face_plane := tetra_face_plane
  face_supporting_halfspace := tetra_supporting_halfspace

/-! ## Dihedral angles -/

/-- The outward normal on the face to the left of a dart. -/
def dartNormal {M : CombMap D} (P : TriangulatedEuclideanPolyhedron M) (d : D) : E3 :=
  P.outward_normal (M.dartFace d)

/-- The cosine of the interior dihedral angle along a dart-represented edge. -/
def dihedralCosAtDart {M : CombMap D} (P : TriangulatedEuclideanPolyhedron M) (d : D) : ℝ :=
  - inner ℝ (dartNormal P d) (dartNormal P (M.α d)) /
    (‖dartNormal P d‖ * ‖dartNormal P (M.α d)‖)

/--
The interior dihedral angle along a dart-represented edge.

With outward normals `n_f,n_g`, this is `π - angle n_f n_g`.
-/
def dihedralAngleAtDart {M : CombMap D} (P : TriangulatedEuclideanPolyhedron M) (d : D) : ℝ :=
  Real.pi - InnerProductGeometry.angle (dartNormal P d) (dartNormal P (M.α d))

theorem dihedralAngleAtDart_nonneg {M : CombMap D}
    (P : TriangulatedEuclideanPolyhedron M) (d : D) :
    0 ≤ dihedralAngleAtDart P d := by
  unfold dihedralAngleAtDart
  linarith [InnerProductGeometry.angle_le_pi (dartNormal P d) (dartNormal P (M.α d))]

theorem dihedralAngleAtDart_le_pi {M : CombMap D}
    (P : TriangulatedEuclideanPolyhedron M) (d : D) :
    dihedralAngleAtDart P d ≤ Real.pi := by
  unfold dihedralAngleAtDart
  linarith [InnerProductGeometry.angle_nonneg (dartNormal P d) (dartNormal P (M.α d))]

theorem dihedralAngleAtDart_alpha {M : CombMap D}
    (P : TriangulatedEuclideanPolyhedron M) (d : D) :
    dihedralAngleAtDart P (M.α d) = dihedralAngleAtDart P d := by
  unfold dihedralAngleAtDart dartNormal
  rw [M.alpha_alpha, InnerProductGeometry.angle_comm]

theorem dihedralCosAtDart_alpha {M : CombMap D}
    (P : TriangulatedEuclideanPolyhedron M) (d : D) :
    dihedralCosAtDart P (M.α d) = dihedralCosAtDart P d := by
  unfold dihedralCosAtDart dartNormal
  rw [M.alpha_alpha, real_inner_comm, mul_comm]

theorem cos_dihedralAngleAtDart {M : CombMap D}
    (P : TriangulatedEuclideanPolyhedron M) (d : D) :
    Real.cos (dihedralAngleAtDart P d) = dihedralCosAtDart P d := by
  unfold dihedralAngleAtDart dihedralCosAtDart
  rw [Real.cos_pi_sub, InnerProductGeometry.cos_angle]
  ring

/-- The dihedral-difference sign carried by a dart. -/
def dihedralSignAtDart {M : CombMap D}
    (P Q : TriangulatedEuclideanPolyhedron M) (d : D) : ProofsInTheBook.Chapter13.EdgeSign :=
  ProofsInTheBook.Ch13Realization.realSignToEdgeSign
    (dihedralAngleAtDart Q d - dihedralAngleAtDart P d)

theorem dihedralSignAtDart_alpha {M : CombMap D}
    (P Q : TriangulatedEuclideanPolyhedron M) (d : D) :
    dihedralSignAtDart P Q (M.α d) = dihedralSignAtDart P Q d := by
  unfold dihedralSignAtDart
  rw [dihedralAngleAtDart_alpha P d, dihedralAngleAtDart_alpha Q d]

private theorem tetraPoint_norm₀ : ‖tetraPoint₀‖ = Real.sqrt 3 := by
  rw [norm_eq_sqrt_real_inner, PiLp.inner_apply, Fin.sum_univ_three]
  simp [tetraPoint₀]
  norm_num

private theorem tetraPoint_norm₁ : ‖tetraPoint₁‖ = Real.sqrt 3 := by
  rw [norm_eq_sqrt_real_inner, PiLp.inner_apply, Fin.sum_univ_three]
  simp [tetraPoint₁]
  norm_num

private theorem tetraPoint_norm₂ : ‖tetraPoint₂‖ = Real.sqrt 3 := by
  rw [norm_eq_sqrt_real_inner, PiLp.inner_apply, Fin.sum_univ_three]
  simp [tetraPoint₂]
  norm_num

private theorem tetraPoint_norm₃ : ‖tetraPoint₃‖ = Real.sqrt 3 := by
  rw [norm_eq_sqrt_real_inner, PiLp.inner_apply, Fin.sum_univ_three]
  simp [tetraPoint₃]
  norm_num

private theorem sqrt_three_mul_sqrt_three : Real.sqrt 3 * Real.sqrt 3 = (3 : ℝ) := by
  rw [← sq, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)]

private theorem tetra_dihedralCos_pair₀₁ :
    - inner ℝ tetraPoint₀ tetraPoint₁ / (‖tetraPoint₀‖ * ‖tetraPoint₁‖)
      = (1 : ℝ) / 3 := by
  rw [tetraPoint_norm₀, tetraPoint_norm₁]
  rw [show inner ℝ tetraPoint₀ tetraPoint₁ = (-1 : ℝ) by
    rw [PiLp.inner_apply, Fin.sum_univ_three]
    simp [tetraPoint₀, tetraPoint₁]]
  rw [sqrt_three_mul_sqrt_three]
  norm_num

private theorem tetra_dihedralCos_pair₀₂ :
    - inner ℝ tetraPoint₀ tetraPoint₂ / (‖tetraPoint₀‖ * ‖tetraPoint₂‖)
      = (1 : ℝ) / 3 := by
  rw [tetraPoint_norm₀, tetraPoint_norm₂]
  rw [show inner ℝ tetraPoint₀ tetraPoint₂ = (-1 : ℝ) by
    rw [PiLp.inner_apply, Fin.sum_univ_three]
    simp [tetraPoint₀, tetraPoint₂]]
  rw [sqrt_three_mul_sqrt_three]
  norm_num

private theorem tetra_dihedralCos_pair₀₃ :
    - inner ℝ tetraPoint₀ tetraPoint₃ / (‖tetraPoint₀‖ * ‖tetraPoint₃‖)
      = (1 : ℝ) / 3 := by
  rw [tetraPoint_norm₀, tetraPoint_norm₃]
  rw [show inner ℝ tetraPoint₀ tetraPoint₃ = (-1 : ℝ) by
    rw [PiLp.inner_apply, Fin.sum_univ_three]
    simp [tetraPoint₀, tetraPoint₃]]
  rw [sqrt_three_mul_sqrt_three]
  norm_num

private theorem tetra_dihedralCos_pair₁₂ :
    - inner ℝ tetraPoint₁ tetraPoint₂ / (‖tetraPoint₁‖ * ‖tetraPoint₂‖)
      = (1 : ℝ) / 3 := by
  rw [tetraPoint_norm₁, tetraPoint_norm₂]
  rw [show inner ℝ tetraPoint₁ tetraPoint₂ = (-1 : ℝ) by
    rw [PiLp.inner_apply, Fin.sum_univ_three]
    simp [tetraPoint₁, tetraPoint₂]]
  rw [sqrt_three_mul_sqrt_three]
  norm_num

private theorem tetra_dihedralCos_pair₁₃ :
    - inner ℝ tetraPoint₁ tetraPoint₃ / (‖tetraPoint₁‖ * ‖tetraPoint₃‖)
      = (1 : ℝ) / 3 := by
  rw [tetraPoint_norm₁, tetraPoint_norm₃]
  rw [show inner ℝ tetraPoint₁ tetraPoint₃ = (-1 : ℝ) by
    rw [PiLp.inner_apply, Fin.sum_univ_three]
    simp [tetraPoint₁, tetraPoint₃]]
  rw [sqrt_three_mul_sqrt_three]
  norm_num

private theorem tetra_dihedralCos_pair₂₃ :
    - inner ℝ tetraPoint₂ tetraPoint₃ / (‖tetraPoint₂‖ * ‖tetraPoint₃‖)
      = (1 : ℝ) / 3 := by
  rw [tetraPoint_norm₂, tetraPoint_norm₃]
  rw [show inner ℝ tetraPoint₂ tetraPoint₃ = (-1 : ℝ) by
    rw [PiLp.inner_apply, Fin.sum_univ_three]
    simp [tetraPoint₂, tetraPoint₃]]
  rw [sqrt_three_mul_sqrt_three]
  norm_num

theorem tetra_dihedralCosAtDart (d : Fin 12) :
    dihedralCosAtDart tetraEuclideanPolyhedron d = (1 : ℝ) / 3 := by
  fin_cases d <;>
    simp [dihedralCosAtDart, dartNormal, tetraEuclideanPolyhedron, tetraOutwardNormal,
      tetraFaceDart, tetraFaceRepDart, tetraMap, CombMap.dartFace, tetraAlpha_apply] <;>
    first
    | exact tetra_dihedralCos_pair₀₁
    | exact tetra_dihedralCos_pair₀₂
    | exact tetra_dihedralCos_pair₀₃
    | exact tetra_dihedralCos_pair₁₂
    | exact tetra_dihedralCos_pair₁₃
    | exact tetra_dihedralCos_pair₂₃
    | simpa [real_inner_comm, mul_comm] using tetra_dihedralCos_pair₀₁
    | simpa [real_inner_comm, mul_comm] using tetra_dihedralCos_pair₀₂
    | simpa [real_inner_comm, mul_comm] using tetra_dihedralCos_pair₀₃
    | simpa [real_inner_comm, mul_comm] using tetra_dihedralCos_pair₁₂
    | simpa [real_inner_comm, mul_comm] using tetra_dihedralCos_pair₁₃
    | simpa [real_inner_comm, mul_comm] using tetra_dihedralCos_pair₂₃

theorem tetra_cos_dihedralAngleAtDart (d : Fin 12) :
    Real.cos (dihedralAngleAtDart tetraEuclideanPolyhedron d) = (1 : ℝ) / 3 := by
  rw [cos_dihedralAngleAtDart, tetra_dihedralCosAtDart]

#print axioms tetraEuclideanPolyhedron
#print axioms tetra_dihedralCosAtDart
#print axioms tetra_cos_dihedralAngleAtDart

end ProofsInTheBook.Ch13Euclidean
