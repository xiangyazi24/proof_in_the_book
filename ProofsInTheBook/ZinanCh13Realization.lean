import ProofsInTheBook.Ch13Realization
import ProofsInTheBook.Ch13ComponentClose

/-!
# Non-vacuous Ch13 realization headline

This file checks that `ConvexPolytopeRealization` is satisfiable, then exposes the
thin rigidity wrapper through that realization interface.
-/

noncomputable section

open scoped Classical
open ProofsInTheBook.PlanarMap ProofsInTheBook.PlanarMap.CombMap
open ProofsInTheBook.Chapter13 EdgeSign
open ProofsInTheBook.Ch13ArmVertex
open ProofsInTheBook.Ch13ArmVertexFull
open ProofsInTheBook.Ch13MarkedSphere
open ProofsInTheBook.Ch13VertexStar
open ProofsInTheBook.SphericalKernel

namespace ProofsInTheBook.Ch13Realization

variable {D : Type*} [Fintype D] [DecidableEq D]

/-- A canonical dart representative for a vertex quotient. -/
def tetraVertexRep (Q : tetraMap.Vertex) : Fin 12 :=
  Quotient.out Q

theorem tetraVertexRep_tail (Q : tetraMap.Vertex) :
    tetraMap.tail (tetraVertexRep Q) = Q :=
  Quotient.out_eq Q

/-- Identical link realizations have no full cyclic sign changes. -/
theorem signChangesFull_self {n : ℕ} (A : Fin (n + 1) → S2) :
    signChangesFull A A = 0 := by
  unfold signChangesFull
  have hdiff : linkDiff A A = fun _ => (0 : ℝ) := by
    funext i
    unfold linkDiff
    ring
  rw [hdiff]
  simp [nzSigns, cyclicFlips]

/-- The all-zero edge signing has no active vertices. -/
theorem not_activeVertex_zero (M : CombMap D) (d : D) :
    ¬ ActiveVertex M (fun _ => EdgeSign.zero) d := by
  rintro ⟨x, _hx, hx⟩
  exact hx rfl

/-- Every vertex cycle of the tetrahedron has three all-zero edge signs. -/
theorem tetra_zero_vertexSignList (d : Fin 12) :
    (tetraMap.σ.toList d).map (fun _ => EdgeSign.zero) =
      [EdgeSign.zero, EdgeSign.zero, EdgeSign.zero] := by
  fin_cases d <;> decide

/-- The cube-corner self-link has three zero real signs. -/
theorem cubeCornerStar_self_linkSigns :
    (List.ofFn (linkDiff cubeCornerStar.vertexLink cubeCornerStar.vertexLink)).map
        realSignToEdgeSign =
      [EdgeSign.zero, EdgeSign.zero, EdgeSign.zero] := by
  have hdiff :
      linkDiff cubeCornerStar.vertexLink cubeCornerStar.vertexLink = fun _ => (0 : ℝ) := by
    funext i
    unfold linkDiff
    ring
  rw [hdiff]
  simp [realSignToEdgeSign]
  norm_num [cubeCornerStar]
  simp

/-- A concrete, trivial (`P = Q`) realization on the tetrahedron map. -/
def tetraCubeCornerRealization : ConvexPolytopeRealization tetraMap where
  isSphere := tetraMap_isSphereMap
  triangle := tetraMap_faceRegular_three
  isSimple := ProofsInTheBook.Ch13ComponentClose.tetraMap_isSimpleGraph
  starP := fun _ => cubeCornerStar
  starQ := fun _ => cubeCornerStar
  hnn := fun _ => rfl
  edgeSign := fun _ => EdgeSign.zero
  edgeSign_inv := fun _ => rfl
  sides_eq := by
    intro Q i
    change sideLen cubeCornerStar.vertexLink i = sideLen cubeCornerStar.vertexLink i
    rfl
  close_eq := by
    intro Q
    change sDist (cubeCornerStar.vertexLink 0) (cubeCornerStar.vertexLink (Fin.last cubeCornerStar.n))
        = sDist (cubeCornerStar.vertexLink 0) (cubeCornerStar.vertexLink (Fin.last cubeCornerStar.n))
    rfl
  dartRep := tetraVertexRep
  dartRep_tail := tetraVertexRep_tail
  interiorActive := by
    intro Q hactive
    exact False.elim (not_activeVertex_zero tetraMap (tetraVertexRep Q) hactive)
  twoArc := by
    intro Q htwo
    have hzero :
        signChangesFull cubeCornerStar.vertexLink
          (linkQcast tetraMap (fun _ : tetraMap.Vertex => cubeCornerStar)
            (fun _ : tetraMap.Vertex => cubeCornerStar) (fun _ => rfl) Q) = 0 := by
      simpa [linkQcast] using signChangesFull_self cubeCornerStar.vertexLink
    omega
  linkOrder := by
    intro Q
    calc
      (tetraMap.σ.toList (tetraVertexRep Q)).map (fun _ => EdgeSign.zero)
          = [EdgeSign.zero, EdgeSign.zero, EdgeSign.zero] :=
            tetra_zero_vertexSignList (tetraVertexRep Q)
      _ = (List.ofFn
            (linkDiff cubeCornerStar.vertexLink
              (linkQcast tetraMap (fun _ : tetraMap.Vertex => cubeCornerStar)
                (fun _ : tetraMap.Vertex => cubeCornerStar) (fun _ => rfl) Q))).map
            realSignToEdgeSign := by
            simpa [linkQcast] using cubeCornerStar_self_linkSigns.symm

theorem convexPolytopeRealization_inhabited :
    ∃ (M : CombMap (Fin 12)), Nonempty (ConvexPolytopeRealization M) :=
  ⟨tetraMap, ⟨tetraCubeCornerRealization⟩⟩

/-- Ch13 Cauchy rigidity, through the non-empty realization interface. -/
theorem chapter13_realization {M : CombMap D} (R : ConvexPolytopeRealization M) :
    ∀ (Q : M.Vertex) (i : Fin ((R.starP Q).n - 1)),
      (R.starP Q).dihedral i
        = (R.starQ Q).dihedral (Fin.cast (by rw [← R.hnn Q]) i) :=
  R.realization_rigid

theorem chapter13_realization_all_edgeSign_zero {M : CombMap D}
    (R : ConvexPolytopeRealization M) :
    ∀ d, R.edgeSign d = EdgeSign.zero :=
  R.realization_all_edgeSign_zero

end ProofsInTheBook.Ch13Realization

#print axioms ProofsInTheBook.Ch13Realization.chapter13_realization
#print axioms ProofsInTheBook.Ch13Realization.convexPolytopeRealization_inhabited
