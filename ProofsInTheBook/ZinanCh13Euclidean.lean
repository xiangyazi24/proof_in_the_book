import ProofsInTheBook.Ch13Realization
import ProofsInTheBook.Ch13ComponentClose
import Mathlib.Analysis.InnerProductSpace.PiL2
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

#print axioms tetraEuclideanPolyhedron

end ProofsInTheBook.Ch13Euclidean
