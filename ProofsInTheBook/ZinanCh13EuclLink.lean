import ProofsInTheBook.ZinanCh13Euclidean
import ProofsInTheBook.Ch13VertexStar
import ProofsInTheBook.Ch13Realization
import ProofsInTheBook.SphericalRotation
import Mathlib.Data.Fin.Rev

/-!
# Chapter 13 Euclidean vertex links

This file separates the design-independent part of the Euclidean-to-`VertexStar`
bridge from the genuine local convexity theorem still to be proved.

The incident neighbours of a vertex are read in the combinatorial `σ` order from
the dart orbit.  The easy `VertexStar` fields (`n`, `hn`, `o`, `p`, `apex_ne`)
come directly from this data and from b1 edge nondegeneracy.  The remaining
strict vertex-cone convexity predicates are derived from `VertexLinkGeometry`.
-/

noncomputable section

set_option maxHeartbeats 3000000

open scoped Classical RealInnerProductSpace
open ProofsInTheBook.PlanarMap ProofsInTheBook.PlanarMap.CombMap
open ProofsInTheBook.Ch13Euclidean
open ProofsInTheBook.Ch13VertexStar
open ProofsInTheBook.Ch13MarkedSphere
open ProofsInTheBook.SphericalRotation

namespace ProofsInTheBook.Ch13EuclLink

variable {D : Type*} [Fintype D] [DecidableEq D]
variable {M : CombMap D}

/-! ## Part 1: σ-ordered incident darts and candidate neighbour data -/

/-- The incident darts at a vertex, rooted at `Quotient.out v` and ordered by `σ`. -/
def incidentDarts (P : TriangulatedEuclideanPolyhedron M) (v : M.Vertex) : List D :=
  M.σ.toList (Quotient.out v)

/-- The combinatorial degree read from the `σ`-cycle list. -/
def vDeg (P : TriangulatedEuclideanPolyhedron M) (v : M.Vertex) : ℕ :=
  (incidentDarts P v).length

/-- The `i`-th incident dart in the `σ`-cycle. -/
def incidentDart (P : TriangulatedEuclideanPolyhedron M) (v : M.Vertex)
    (i : Fin (vDeg P v)) : D :=
  (incidentDarts P v).get i

/-- Every dart read from the incident list has tail `v`. -/
theorem incidentDart_tail (P : TriangulatedEuclideanPolyhedron M) (v : M.Vertex)
    (i : Fin (vDeg P v)) :
    M.tail (incidentDart P v i) = v := by
  unfold incidentDart
  have hmem : (incidentDarts P v).get i ∈ incidentDarts P v :=
    List.get_mem _ _
  unfold incidentDarts at hmem ⊢
  have hsame : M.σ.SameCycle (Quotient.out v) ((M.σ.toList (Quotient.out v)).get i) :=
    (Equiv.Perm.mem_toList_iff.mp hmem).1
  calc
    M.tail ((M.σ.toList (Quotient.out v)).get i) = M.tail (Quotient.out v) :=
      Quotient.sound hsame.symm
    _ = v := Quotient.out_eq v

/-- The `VertexStar.n` associated to a vertex of degree `vDeg`: there are `n + 1` neighbours. -/
def starN (P : TriangulatedEuclideanPolyhedron M) (v : M.Vertex) : ℕ :=
  vDeg P v - 1

/-- A `VertexStar` index converted to the corresponding degree-list index. -/
def starIndexToDeg (P : TriangulatedEuclideanPolyhedron M) (v : M.Vertex)
    (hdeg : 3 ≤ vDeg P v) (i : Fin (starN P v + 1)) : Fin (vDeg P v) :=
  ⟨i.1, by
    have hi := i.2
    unfold starN at hi
    omega⟩

/-- The `i`-th incident dart, indexed in the eventual `VertexStar` convention. -/
def incidentDartOfStarIndex (P : TriangulatedEuclideanPolyhedron M) (v : M.Vertex)
    (hdeg : 3 ≤ vDeg P v) (i : Fin (starN P v + 1)) : D :=
  incidentDart P v (starIndexToDeg P v hdeg i)

theorem incidentDartOfStarIndex_tail (P : TriangulatedEuclideanPolyhedron M) (v : M.Vertex)
    (hdeg : 3 ≤ vDeg P v) (i : Fin (starN P v + 1)) :
    M.tail (incidentDartOfStarIndex P v hdeg i) = v := by
  unfold incidentDartOfStarIndex
  exact incidentDart_tail P v (starIndexToDeg P v hdeg i)

/-- Candidate neighbour point in the `σ`-ordered Euclidean vertex link. -/
def linkPoint (P : TriangulatedEuclideanPolyhedron M) (v : M.Vertex)
    (hdeg : 3 ≤ vDeg P v) (i : Fin (starN P v + 1)) : E3 :=
  P.pos (M.head (incidentDartOfStarIndex P v hdeg i))

/-- Candidate raw edge vector in the `σ`-ordered Euclidean vertex link. -/
def linkVec (P : TriangulatedEuclideanPolyhedron M) (v : M.Vertex)
    (hdeg : 3 ≤ vDeg P v) (i : Fin (starN P v + 1)) : E3 :=
  linkPoint P v hdeg i - P.pos v

theorem starN_ge_two (P : TriangulatedEuclideanPolyhedron M) (v : M.Vertex)
    (hdeg : 3 ≤ vDeg P v) : 2 ≤ starN P v := by
  unfold starN
  omega

theorem linkPoint_apex_ne (P : TriangulatedEuclideanPolyhedron M) (v : M.Vertex)
    (hdeg : 3 ≤ vDeg P v) (i : Fin (starN P v + 1)) :
    linkPoint P v hdeg i ≠ P.pos v := by
  intro h
  exact P.edge_nondegenerate (incidentDartOfStarIndex P v hdeg i) (by
    rw [incidentDartOfStarIndex_tail P v hdeg i]
    exact h.symm)

/-! ## Part 2: oriented face support and derived vertex-link geometry -/

/-- Local scalar triple product, in the same coordinate convention as `SphericalKernel.det3`. -/
def det3 (u v w : E3) : ℝ :=
  u 0 * (v 1 * w 2 - v 2 * w 1)
    - u 1 * (v 0 * w 2 - v 2 * w 0)
    + u 2 * (v 0 * w 1 - v 1 * w 0)

theorem det3_eq_spherical (u v w : E3) :
    det3 u v w = ProofsInTheBook.SphericalKernel.det3 u v w := rfl

theorem det3_eq_inner_cross (u v z : E3) :
    det3 u v z = (⟪cross u v, z⟫ : ℝ) := by
  rw [det3_eq_spherical]
  calc
    ProofsInTheBook.SphericalKernel.det3 u v z = (⟪u, cross v z⟫ : ℝ) := by
      rw [inner_cross_eq_det3]
    _ = (⟪z, cross u v⟫ : ℝ) := inner_cross_cyclic u v z
    _ = (⟪cross u v, z⟫ : ℝ) := (real_inner_comm z (cross u v)).symm

/--
An oriented supporting triangle through `v,a,b`.

This is the non-circular local geometry: the determinant functional of the
oriented triangle is identified with a supporting face normal, with a positive
scale and exact equality set.
-/
structure OrientedTriangleSupport (P : TriangulatedEuclideanPolyhedron M)
    (v a b : M.Vertex) where
  normal : E3
  normal_unit : ‖normal‖ = 1
  c : ℝ
  c_pos : 0 < c
  det_eq :
    ∀ z : E3,
      det3 (P.pos a - P.pos v) (P.pos b - P.pos v) z = -c * inner ℝ normal z
  support : ∀ w : M.Vertex, inner ℝ normal (P.pos w - P.pos v) ≤ 0
  eq_iff :
    ∀ w : M.Vertex,
      inner ℝ normal (P.pos w - P.pos v) = 0 ↔ (w = v ∨ w = a ∨ w = b)

/--
Local vertex-link geometry in the outward-normal orientation, i.e. the reverse
of the map's `σ` order at the vertex.  The determinant and hemisphere fields of
`VertexStar` are derived from the oriented triangle supports below.
-/
structure VertexLinkGeometry (P : TriangulatedEuclideanPolyhedron M) (v : M.Vertex) where
  n : ℕ
  hn : 2 ≤ n
  nbr : Fin (n + 1) → M.Vertex
  nbr_is_sigma :
    ∃ hdeg : 3 ≤ vDeg P v, ∃ e : n = starN P v,
      ∀ i : Fin (n + 1),
        nbr i =
          M.head (incidentDartOfStarIndex P v hdeg
            (Fin.rev (Fin.cast (by rw [← e]) i)))
  oriented : ∀ i : Fin (n + 1), OrientedTriangleSupport P v (nbr i) (nbr (i + 1))
  nbr_apex_ne : ∀ i : Fin (n + 1), P.pos (nbr i) ≠ P.pos v
  nonincident :
    ∀ i j : Fin (n + 1), j ≠ i → j ≠ i + 1 →
      ¬(nbr j = v ∨ nbr j = nbr i ∨ nbr j = nbr (i + 1))

namespace VertexLinkGeometry

variable {P : TriangulatedEuclideanPolyhedron M} {v : M.Vertex}
variable (LG : VertexLinkGeometry P v)

/-- Sum of oriented supporting normals around the vertex. -/
def normalSum : E3 :=
  ∑ i : Fin (LG.n + 1), (LG.oriented i).normal

theorem exists_nonincident (j : Fin (LG.n + 1)) :
    ∃ i : Fin (LG.n + 1), j ≠ i ∧ j ≠ i + 1 := by
  by_contra hcon
  push_neg at hcon
  have hsub : (Finset.univ : Finset (Fin (LG.n + 1))) ⊆ {j, j - 1} := by
    intro i _
    rcases eq_or_ne j i with hji | hji
    · simp [hji]
    · have hnext := hcon i hji
      have him1 : i = j - 1 := by
        rw [eq_sub_iff_add_eq]
        exact hnext.symm
      simp [him1]
  have hle := Finset.card_le_card hsub
  have hcard : ({j, j - 1} : Finset (Fin (LG.n + 1))).card ≤ 2 :=
    le_trans (Finset.card_insert_le _ _) (by simp)
  simp only [Finset.card_univ, Fintype.card_fin] at hle
  have hle2 : LG.n + 1 ≤ 2 := le_trans hle hcard
  have hn : 2 ≤ LG.n := LG.hn
  omega

theorem normal_inner_nbr_lt (j : Fin (LG.n + 1)) :
    inner ℝ LG.normalSum (P.pos (LG.nbr j) - P.pos v) < 0 := by
  rw [normalSum, sum_inner]
  have hle :
      ∀ i ∈ (Finset.univ : Finset (Fin (LG.n + 1))),
        inner ℝ (LG.oriented i).normal (P.pos (LG.nbr j) - P.pos v) ≤ 0 := by
    intro i _
    exact (LG.oriented i).support (LG.nbr j)
  have hlt :
      ∃ i ∈ (Finset.univ : Finset (Fin (LG.n + 1))),
        inner ℝ (LG.oriented i).normal (P.pos (LG.nbr j) - P.pos v) < 0 := by
    obtain ⟨i, hji, hjnext⟩ := LG.exists_nonincident j
    refine ⟨i, by simp, ?_⟩
    have hle_i := (LG.oriented i).support (LG.nbr j)
    have hne :
        inner ℝ (LG.oriented i).normal (P.pos (LG.nbr j) - P.pos v) ≠ 0 := by
      intro hz
      exact LG.nonincident i j hji hjnext (((LG.oriented i).eq_iff (LG.nbr j)).1 hz)
    exact lt_of_le_of_ne hle_i hne
  have hsum := Finset.sum_lt_sum hle hlt
  simpa using hsum

theorem normalSum_ne_zero : LG.normalSum ≠ 0 := by
  intro hzero
  have hlt := LG.normal_inner_nbr_lt (0 : Fin (LG.n + 1))
  rw [hzero] at hlt
  simp at hlt

theorem open_hemi :
    ∃ h : E3, ‖h‖ = 1 ∧
      ∀ i : Fin (LG.n + 1), 0 < inner ℝ h (P.pos (LG.nbr i) - P.pos v) := by
  let N := LG.normalSum
  have hN : N ≠ 0 := LG.normalSum_ne_zero
  refine ⟨-(‖N‖)⁻¹ • N, ?_, ?_⟩
  · rw [norm_smul, norm_neg, Real.norm_eq_abs,
      abs_of_nonneg (inv_nonneg.mpr (norm_nonneg N))]
    exact inv_mul_cancel₀ (norm_ne_zero_iff.mpr hN)
  · intro i
    have hlt : inner ℝ N (P.pos (LG.nbr i) - P.pos v) < 0 := LG.normal_inner_nbr_lt i
    rw [real_inner_smul_left]
    have hpos : 0 < (‖N‖)⁻¹ := inv_pos.mpr (norm_pos_iff.mpr hN)
    nlinarith [mul_pos hpos (neg_pos.mpr hlt)]

theorem turn_support (i j : Fin (LG.n + 1)) :
    0 ≤ ProofsInTheBook.SphericalKernel.det3
      (P.pos (LG.nbr i) - P.pos v)
      (P.pos (LG.nbr (i + 1)) - P.pos v)
      (P.pos (LG.nbr j) - P.pos v) := by
  have hdet := (LG.oriented i).det_eq (P.pos (LG.nbr j) - P.pos v)
  rw [det3_eq_spherical] at hdet
  rw [hdet]
  have hs := (LG.oriented i).support (LG.nbr j)
  nlinarith [(LG.oriented i).c_pos, hs]

theorem turn_strict (i j : Fin (LG.n + 1)) (hji : j ≠ i) (hjnext : j ≠ i + 1) :
    0 < ProofsInTheBook.SphericalKernel.det3
      (P.pos (LG.nbr i) - P.pos v)
      (P.pos (LG.nbr (i + 1)) - P.pos v)
      (P.pos (LG.nbr j) - P.pos v) := by
  have hdet := (LG.oriented i).det_eq (P.pos (LG.nbr j) - P.pos v)
  rw [det3_eq_spherical] at hdet
  rw [hdet]
  have hs_le := (LG.oriented i).support (LG.nbr j)
  have hs_ne :
      inner ℝ (LG.oriented i).normal (P.pos (LG.nbr j) - P.pos v) ≠ 0 := by
    intro hz
    exact LG.nonincident i j hji hjnext (((LG.oriented i).eq_iff (LG.nbr j)).1 hz)
  have hs_lt : inner ℝ (LG.oriented i).normal (P.pos (LG.nbr j) - P.pos v) < 0 :=
    lt_of_le_of_ne hs_le hs_ne
  nlinarith [(LG.oriented i).c_pos, hs_lt]

/-- Assemble the `VertexStar` from honest local vertex-link geometry. -/
def toVertexStar : VertexStar where
  n := LG.n
  hn := LG.hn
  o := P.pos v
  p := fun i => P.pos (LG.nbr i)
  apex_ne := LG.nbr_apex_ne
  open_hemi := LG.open_hemi
  turn_support := LG.turn_support
  turn_strict := LG.turn_strict

end VertexLinkGeometry

/-- Public assembly name for the Euclidean vertex star bridge. -/
def vertexStarOfEuclidean (P : TriangulatedEuclideanPolyhedron M) (v : M.Vertex)
    (LG : VertexLinkGeometry P v) : VertexStar :=
  LG.toVertexStar

/-! ## Part 3: tetrahedron diagnostics -/

theorem tetra_sigma_toList_length (d : Fin 12) :
    (tetraMap.σ.toList d).length = 3 := by
  fin_cases d <;> decide

theorem tetra_vDeg (v : tetraMap.Vertex) :
    vDeg tetraEuclideanPolyhedron v = 3 := by
  unfold vDeg incidentDarts
  exact tetra_sigma_toList_length (Quotient.out v)

theorem tetra_vDeg_ge_three (v : tetraMap.Vertex) :
    3 ≤ vDeg tetraEuclideanPolyhedron v := by
  rw [tetra_vDeg]

@[simp] theorem tetraAlpha_apply_link (d : Fin 12) :
    tetraAlpha d =
      match d with
      | 0 => 3 | 1 => 6 | 2 => 9 | 3 => 0 | 4 => 7 | 5 => 10
      | 6 => 1 | 7 => 4 | 8 => 11 | 9 => 2 | 10 => 5 | _ => 8 := by
  fin_cases d <;> decide

theorem tetraSigma_toList (d : Fin 12) :
    tetraSigma.toList d =
      match d with
      | 0 => [0, 1, 2] | 1 => [1, 2, 0] | 2 => [2, 0, 1]
      | 3 => [3, 5, 4] | 4 => [4, 3, 5] | 5 => [5, 4, 3]
      | 6 => [6, 7, 8] | 7 => [7, 8, 6] | 8 => [8, 6, 7]
      | 9 => [9, 11, 10] | 10 => [10, 9, 11] | _ => [11, 10, 9] := by
  fin_cases d <;> decide

theorem tetraMap_sigma_toList (d : Fin 12) :
    tetraMap.σ.toList d =
      match d with
      | 0 => [0, 1, 2] | 1 => [1, 2, 0] | 2 => [2, 0, 1]
      | 3 => [3, 5, 4] | 4 => [4, 3, 5] | 5 => [5, 4, 3]
      | 6 => [6, 7, 8] | 7 => [7, 8, 6] | 8 => [8, 6, 7]
      | 9 => [9, 11, 10] | 10 => [10, 9, 11] | _ => [11, 10, 9] := by
  simpa [tetraMap] using tetraSigma_toList d

/-- The `i`-th dart in the tetrahedron `σ`-cycle rooted at `d`, reindexed by `Fin 3`. -/
def tetraSigmaDart (d : Fin 12) (i : Fin 3) : Fin 12 :=
  (tetraMap.σ.toList d).get ⟨i.1, by
    rw [tetra_sigma_toList_length d]
    exact i.2⟩

/-- The Euclidean edge vector for the tetrahedron `σ`-cycle rooted at `d`. -/
def tetraSigmaVec (d : Fin 12) (i : Fin 3) : E3 :=
  tetraEuclideanPolyhedron.pos (tetraMap.head (tetraSigmaDart d i))
    - tetraEuclideanPolyhedron.pos (tetraMap.tail d)

/--
With the current tetrahedron coordinates and the map's `σ` orientation, the
ordered vertex-link determinant is negative.  Thus the PART3 certificate with
`turn_support : 0 ≤ det3 (p i) (p (i+1)) (p j)` is not true for the σ order as
stated; the reversed cyclic order would have the positive sign.
-/
theorem tetra_sigma_order_det_negative (d : Fin 12) :
    ProofsInTheBook.SphericalKernel.det3
      (tetraSigmaVec d 0) (tetraSigmaVec d 1) (tetraSigmaVec d 2) = (-16 : ℝ) := by
  fin_cases d <;>
    norm_num [tetraSigmaVec, tetraSigmaDart, tetraMap_sigma_toList, tetraSigma_toList,
      tetraEuclideanPolyhedron, tetraPos, tetraDartPoint, tetraMap, CombMap.tail, CombMap.head,
      tetraPoint₀, tetraPoint₁, tetraPoint₂, tetraPoint₃,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
      Matrix.tail_cons,
      ProofsInTheBook.SphericalKernel.det3]

/-- Concrete reverse on `Fin 3`, used to keep tetrahedron coordinate proofs reducible. -/
def fin3Rev : Fin 3 → Fin 3
  | 0 => 2
  | 1 => 1
  | _ => 0

theorem fin3Rev_eq_rev (i : Fin 3) : fin3Rev i = Fin.rev i := by
  fin_cases i <;> rfl

/-- The reversed `σ` order has the positive determinant required by `VertexStar`. -/
theorem tetra_sigma_reverse_order_det_positive (d : Fin 12) :
    ProofsInTheBook.SphericalKernel.det3
      (tetraSigmaVec d (fin3Rev 0)) (tetraSigmaVec d (fin3Rev 1))
      (tetraSigmaVec d (fin3Rev 2)) = (16 : ℝ) := by
  fin_cases d <;>
    norm_num [fin3Rev, tetraSigmaVec, tetraSigmaDart, tetraMap_sigma_toList, tetraSigma_toList,
      tetraEuclideanPolyhedron, tetraPos, tetraDartPoint, tetraMap, CombMap.tail, CombMap.head,
      tetraPoint₀, tetraPoint₁, tetraPoint₂, tetraPoint₃,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
      Matrix.tail_cons,
      ProofsInTheBook.SphericalKernel.det3]

/-- The reversed-`σ` neighbour vertex at a tetrahedron dart root. -/
def tetraRevNbr (d : Fin 12) (i : Fin 3) : tetraMap.Vertex :=
  tetraMap.head (tetraSigmaDart d (fin3Rev i))

/-- The supporting face normal for the oriented triangle
`tail d, tetraRevNbr d i, tetraRevNbr d (i+1)`, normalized to unit length. -/
def tetraSupportNormal (d : Fin 12) (i : Fin 3) : E3 :=
  (Real.sqrt 3)⁻¹ •
    (tetraEuclideanPolyhedron.pos (tetraMap.tail d)
      + tetraEuclideanPolyhedron.pos (tetraRevNbr d i)
      + tetraEuclideanPolyhedron.pos (tetraRevNbr d (i + 1)))

theorem tetraSupportNormal_unit (d : Fin 12) (i : Fin 3) :
    ‖tetraSupportNormal d i‖ = 1 := by
  fin_cases d <;> fin_cases i <;>
    rw [tetraSupportNormal, norm_smul, Real.norm_eq_abs,
      abs_of_nonneg (inv_nonneg.mpr (Real.sqrt_nonneg 3)),
      EuclideanSpace.norm_eq, Fin.sum_univ_three] <;>
    norm_num [fin3Rev, Fin.add_def, tetraRevNbr, tetraSigmaDart, tetraMap_sigma_toList, tetraSigma_toList,
      tetraEuclideanPolyhedron, tetraPos, tetraDartPoint, tetraMap, CombMap.tail, CombMap.head,
      tetraPoint₀, tetraPoint₁, tetraPoint₂, tetraPoint₃,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
      Matrix.tail_cons, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)]

private theorem sqrt_three_ne_zero : Real.sqrt 3 ≠ 0 := by
  positivity

private theorem sqrt_three_mul_inv : Real.sqrt 3 * (Real.sqrt 3)⁻¹ = (1 : ℝ) :=
  mul_inv_cancel₀ sqrt_three_ne_zero

theorem tetra_cross_eq_neg_smul_normal (d : Fin 12) (i : Fin 3) :
    cross
        (tetraEuclideanPolyhedron.pos (tetraRevNbr d i)
          - tetraEuclideanPolyhedron.pos (tetraMap.tail d))
        (tetraEuclideanPolyhedron.pos (tetraRevNbr d (i + 1))
          - tetraEuclideanPolyhedron.pos (tetraMap.tail d))
      = -(4 * Real.sqrt 3) • tetraSupportNormal d i := by
  fin_cases d <;> fin_cases i <;>
    apply ext_coord <;>
    simp only [cross_apply_zero, cross_apply_one, cross_apply_two, neg_smul,
      PiLp.smul_apply, PiLp.neg_apply] <;>
    norm_num [fin3Rev, Fin.add_def, tetraSupportNormal, tetraRevNbr, tetraSigmaDart,
      tetraMap_sigma_toList, tetraSigma_toList, tetraEuclideanPolyhedron, tetraPos,
      tetraDartPoint, tetraMap, CombMap.tail, CombMap.head, tetraPoint₀, tetraPoint₁,
      tetraPoint₂, tetraPoint₃, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons] <;>
    rw [show Real.sqrt 3 * (Real.sqrt 3)⁻¹ = (1 : ℝ) from sqrt_three_mul_inv] <;>
    ring

/-- The four vertex-coordinate classes carried by tetrahedron darts. -/
def tetraDartClass : Fin 12 → Fin 4
  | 0 | 1 | 2 => 0
  | 3 | 4 | 5 => 1
  | 6 | 7 | 8 => 2
  | _ => 3

/-- The point attached to a tetrahedron vertex class. -/
def tetraClassPoint : Fin 4 → E3
  | 0 => tetraPoint₀
  | 1 => tetraPoint₁
  | 2 => tetraPoint₂
  | _ => tetraPoint₃

theorem tetraDartPoint_eq_classPoint (d : Fin 12) :
    tetraDartPoint d = tetraClassPoint (tetraDartClass d) := by
  fin_cases d <;> rfl

theorem tetraClassPoint_inner (a b : Fin 4) :
    inner ℝ (tetraClassPoint a) (tetraClassPoint b) =
      if a = b then (3 : ℝ) else (-1 : ℝ) := by
  fin_cases a <;> fin_cases b <;>
    rw [PiLp.inner_apply, Fin.sum_univ_three] <;>
    simp [tetraClassPoint, tetraPoint₀, tetraPoint₁, tetraPoint₂, tetraPoint₃] <;>
    norm_num

/-- The omitted vertex class of the oriented tetrahedron face at `(d,i)`. -/
def tetraOmitClass : Fin 12 → Fin 3 → Fin 4
  | 0, 0 => 1 | 0, 1 => 3 | 0, _ => 2
  | 1, 0 => 2 | 1, 1 => 1 | 1, _ => 3
  | 2, 0 => 3 | 2, 1 => 2 | 2, _ => 1
  | 3, 0 => 0 | 3, 1 => 2 | 3, _ => 3
  | 4, 0 => 2 | 4, 1 => 3 | 4, _ => 0
  | 5, 0 => 3 | 5, 1 => 0 | 5, _ => 2
  | 6, 0 => 0 | 6, 1 => 3 | 6, _ => 1
  | 7, 0 => 1 | 7, 1 => 0 | 7, _ => 3
  | 8, 0 => 3 | 8, 1 => 1 | 8, _ => 0
  | 9, 0 => 0 | 9, 1 => 1 | 9, _ => 2
  | 10, 0 => 1 | 10, 1 => 2 | 10, _ => 0
  | _, 0 => 2 | _, 1 => 0 | _, _ => 1

theorem tetraOmitClass_ne_tail (d : Fin 12) (i : Fin 3) :
    tetraOmitClass d i ≠ tetraDartClass d := by
  fin_cases d <;> fin_cases i <;> decide

theorem tetraSupportNormal_eq_omit (d : Fin 12) (i : Fin 3) :
    tetraSupportNormal d i =
      -((Real.sqrt 3)⁻¹) • tetraClassPoint (tetraOmitClass d i) := by
  fin_cases d <;> fin_cases i <;>
    apply ext_coord <;>
    norm_num [fin3Rev, Fin.add_def, tetraSupportNormal, tetraRevNbr, tetraSigmaDart,
      tetraMap_sigma_toList, tetraSigma_toList, tetraEuclideanPolyhedron, tetraPos,
      tetraDartPoint, tetraMap, CombMap.tail, CombMap.head, tetraDartClass, tetraClassPoint,
      tetraOmitClass, tetraPoint₀, tetraPoint₁, tetraPoint₂, tetraPoint₃,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
      Matrix.tail_cons]

theorem tetraSupportNormal_support (d : Fin 12) (i : Fin 3) (w : tetraMap.Vertex) :
    inner ℝ (tetraSupportNormal d i)
      (tetraEuclideanPolyhedron.pos w - tetraEuclideanPolyhedron.pos (tetraMap.tail d)) ≤ 0 := by
  refine Quotient.inductionOn w ?_
  intro x
  rw [tetraSupportNormal_eq_omit]
  change inner ℝ (-((Real.sqrt 3)⁻¹) • tetraClassPoint (tetraOmitClass d i))
      (tetraDartPoint x - tetraDartPoint d) ≤ 0
  rw [tetraDartPoint_eq_classPoint x, tetraDartPoint_eq_classPoint d]
  rw [real_inner_smul_left, inner_sub_right, tetraClassPoint_inner, tetraClassPoint_inner]
  have htail : tetraOmitClass d i ≠ tetraDartClass d := tetraOmitClass_ne_tail d i
  have hpos : 0 < (Real.sqrt 3)⁻¹ := by positivity
  by_cases hx : tetraOmitClass d i = tetraDartClass x
  · rw [if_pos hx, if_neg htail]
    ring_nf
    have hnonneg : 0 ≤ (Real.sqrt 3)⁻¹ := le_of_lt hpos
    nlinarith [hnonneg]
  · rw [if_neg hx, if_neg htail]
    ring_nf
    nlinarith [le_of_lt hpos]

theorem tetra_vertex_eq_iff_class (x y : Fin 12) :
    (Quotient.mk (cycleSetoid tetraMap.σ) x = Quotient.mk (cycleSetoid tetraMap.σ) y) ↔
      tetraDartClass x = tetraDartClass y := by
  fin_cases x <;> fin_cases y <;> decide

theorem tetra_nonomit_iff_face_class (d : Fin 12) (i : Fin 3) (c : Fin 4) :
    c ≠ tetraOmitClass d i ↔
      c = tetraDartClass d ∨
        c = tetraDartClass (tetraAlpha (tetraSigmaDart d (fin3Rev i))) ∨
        c = tetraDartClass (tetraAlpha (tetraSigmaDart d (fin3Rev (i + 1)))) := by
  fin_cases d <;> fin_cases i <;> fin_cases c <;>
    simp [fin3Rev, Fin.add_def, tetraOmitClass, tetraDartClass, tetraSigmaDart,
      tetraMap_sigma_toList, tetraSigma_toList, tetraAlpha_apply_link] <;>
    decide

theorem tetraSupportNormal_inner_zero_iff_class (d : Fin 12) (i : Fin 3) (x : Fin 12) :
    inner ℝ (tetraSupportNormal d i) (tetraDartPoint x - tetraDartPoint d) = 0 ↔
      tetraDartClass x ≠ tetraOmitClass d i := by
  rw [tetraSupportNormal_eq_omit]
  rw [tetraDartPoint_eq_classPoint x, tetraDartPoint_eq_classPoint d]
  rw [real_inner_smul_left, inner_sub_right, tetraClassPoint_inner, tetraClassPoint_inner]
  have htail : tetraOmitClass d i ≠ tetraDartClass d := tetraOmitClass_ne_tail d i
  have hpos : 0 < (Real.sqrt 3)⁻¹ := by positivity
  by_cases hx : tetraOmitClass d i = tetraDartClass x
  · rw [if_pos hx, if_neg htail]
    constructor
    · intro hzero
      ring_nf at hzero
      nlinarith [hpos]
    · intro hne
      exact False.elim (hne hx.symm)
  · rw [if_neg hx, if_neg htail]
    ring_nf
    exact ⟨fun _ => fun h => hx h.symm, fun _ => trivial⟩

theorem tetraSupportNormal_eq_iff (d : Fin 12) (i : Fin 3) (w : tetraMap.Vertex) :
    inner ℝ (tetraSupportNormal d i)
        (tetraEuclideanPolyhedron.pos w - tetraEuclideanPolyhedron.pos (tetraMap.tail d)) = 0 ↔
      (w = tetraMap.tail d ∨ w = tetraRevNbr d i ∨ w = tetraRevNbr d (i + 1)) := by
  refine Quotient.inductionOn w ?_
  intro x
  change inner ℝ (tetraSupportNormal d i) (tetraDartPoint x - tetraDartPoint d) = 0 ↔
      (Quotient.mk (cycleSetoid tetraMap.σ) x = tetraMap.tail d ∨
        Quotient.mk (cycleSetoid tetraMap.σ) x = tetraRevNbr d i ∨
        Quotient.mk (cycleSetoid tetraMap.σ) x = tetraRevNbr d (i + 1))
  rw [tetraSupportNormal_inner_zero_iff_class]
  rw [tetra_nonomit_iff_face_class d i (tetraDartClass x)]
  constructor
  · rintro (h | h | h)
    · left
      change Quotient.mk (cycleSetoid tetraMap.σ) x =
        Quotient.mk (cycleSetoid tetraMap.σ) d
      exact (tetra_vertex_eq_iff_class x d).2 h
    · right; left
      change Quotient.mk (cycleSetoid tetraMap.σ) x =
        Quotient.mk (cycleSetoid tetraMap.σ) (tetraAlpha (tetraSigmaDart d (fin3Rev i)))
      exact (tetra_vertex_eq_iff_class x
        (tetraAlpha (tetraSigmaDart d (fin3Rev i)))).2 h
    · right; right
      change Quotient.mk (cycleSetoid tetraMap.σ) x =
        Quotient.mk (cycleSetoid tetraMap.σ)
          (tetraAlpha (tetraSigmaDart d (fin3Rev (i + 1))))
      exact (tetra_vertex_eq_iff_class x
        (tetraAlpha (tetraSigmaDart d (fin3Rev (i + 1))))).2 h
  · rintro (h | h | h)
    · left
      change Quotient.mk (cycleSetoid tetraMap.σ) x =
        Quotient.mk (cycleSetoid tetraMap.σ) d at h
      exact (tetra_vertex_eq_iff_class x d).1 h
    · right; left
      change Quotient.mk (cycleSetoid tetraMap.σ) x =
        Quotient.mk (cycleSetoid tetraMap.σ) (tetraAlpha (tetraSigmaDart d (fin3Rev i))) at h
      exact (tetra_vertex_eq_iff_class x
        (tetraAlpha (tetraSigmaDart d (fin3Rev i)))).1 h
    · right; right
      change Quotient.mk (cycleSetoid tetraMap.σ) x =
        Quotient.mk (cycleSetoid tetraMap.σ)
          (tetraAlpha (tetraSigmaDart d (fin3Rev (i + 1)))) at h
      exact (tetra_vertex_eq_iff_class x
        (tetraAlpha (tetraSigmaDart d (fin3Rev (i + 1))))).1 h

/-- Oriented supporting-face certificate for the tetrahedron at a dart-rooted reversed σ edge. -/
def tetraOrientedSupportDart (d : Fin 12) (i : Fin 3) :
    OrientedTriangleSupport tetraEuclideanPolyhedron (tetraMap.tail d)
      (tetraRevNbr d i) (tetraRevNbr d (i + 1)) where
  normal := tetraSupportNormal d i
  normal_unit := tetraSupportNormal_unit d i
  c := 4 * Real.sqrt 3
  c_pos := by positivity
  det_eq := by
    intro z
    rw [det3_eq_inner_cross, tetra_cross_eq_neg_smul_normal]
    rw [real_inner_smul_left]
  support := tetraSupportNormal_support d i
  eq_iff := tetraSupportNormal_eq_iff d i

theorem tetraSigmaDart_tail_eq (d : Fin 12) (i : Fin 3) :
    tetraMap.tail (tetraSigmaDart d (fin3Rev i)) = tetraMap.tail d := by
  fin_cases d <;> fin_cases i <;> decide

theorem tetraRevNbr_ne_tail (d : Fin 12) (i : Fin 3) :
    tetraRevNbr d i ≠ tetraMap.tail d := by
  intro h
  have hc : tetraDartClass (tetraAlpha (tetraSigmaDart d (fin3Rev i))) =
      tetraDartClass d := by
    exact (tetra_vertex_eq_iff_class
      (tetraAlpha (tetraSigmaDart d (fin3Rev i))) d).1 h
  revert hc
  fin_cases d <;> fin_cases i <;>
    simp [fin3Rev, tetraDartClass, tetraSigmaDart, tetraMap_sigma_toList,
      tetraAlpha_apply_link] <;>
    decide

theorem tetraRevNbr_class_injective (d : Fin 12) :
    Function.Injective
      (fun i : Fin 3 => tetraDartClass (tetraAlpha (tetraSigmaDart d (fin3Rev i)))) := by
  intro i j h
  fin_cases d <;> fin_cases i <;> fin_cases j <;>
    simp [fin3Rev, tetraDartClass, tetraSigmaDart, tetraMap_sigma_toList,
      tetraSigma_toList, tetraAlpha_apply_link] at h <;>
    decide

theorem tetraRevNbr_injective (d : Fin 12) : Function.Injective (tetraRevNbr d) := by
  intro i j h
  have hc : tetraDartClass (tetraAlpha (tetraSigmaDart d (fin3Rev i))) =
      tetraDartClass (tetraAlpha (tetraSigmaDart d (fin3Rev j))) :=
    (tetra_vertex_eq_iff_class
      (tetraAlpha (tetraSigmaDart d (fin3Rev i)))
      (tetraAlpha (tetraSigmaDart d (fin3Rev j)))).1 h
  exact tetraRevNbr_class_injective d hc

theorem tetraRevNbr_reverse_incident (v : tetraMap.Vertex) (i : Fin 3) :
    tetraRevNbr (Quotient.out v) i =
      tetraMap.head
        (incidentDartOfStarIndex tetraEuclideanPolyhedron v
          (tetra_vDeg_ge_three v)
          (Fin.rev (Fin.cast (by rw [starN, tetra_vDeg]) i))) := by
  apply Quotient.sound
  generalize hd : Quotient.out v = d
  fin_cases d <;> fin_cases i <;>
    simp [hd, fin3Rev, tetraRevNbr, incidentDartOfStarIndex, incidentDart, starIndexToDeg,
      incidentDarts, vDeg, starN, tetra_vDeg, tetraSigmaDart, tetraMap_sigma_toList,
      tetraSigma_toList] <;>
    decide

/-- The tetrahedron vertex-link geometry, in the outward-normal (reverse-σ) order. -/
def tetraVertexLinkGeometry (v : tetraMap.Vertex) :
    VertexLinkGeometry tetraEuclideanPolyhedron v := by
  let d : Fin 12 := Quotient.out v
  have hv : tetraMap.tail d = v := Quotient.out_eq v
  refine
    { n := 2
      hn := le_rfl
      nbr := fun i => tetraRevNbr d i
      nbr_is_sigma := ?_
      oriented := ?_
      nbr_apex_ne := ?_
      nonincident := ?_ }
  · refine ⟨tetra_vDeg_ge_three v, ?_, ?_⟩
    · rw [starN, tetra_vDeg]
    · intro i
      exact tetraRevNbr_reverse_incident v i
  · intro i
    rw [← hv]
    exact tetraOrientedSupportDart d i
  · intro i h
    rw [← hv] at h
    have hnd := tetraEuclideanPolyhedron.edge_nondegenerate (tetraSigmaDart d (fin3Rev i))
    exact hnd (by
      change tetraEuclideanPolyhedron.pos (tetraMap.tail (tetraSigmaDart d (fin3Rev i))) =
        tetraEuclideanPolyhedron.pos (tetraMap.head (tetraSigmaDart d (fin3Rev i)))
      rw [tetraSigmaDart_tail_eq d i]
      exact h.symm)
  · intro i j hji hjnext hbad
    rcases hbad with htail | heq | hnext
    · have htail' : tetraRevNbr d j = tetraMap.tail d := by
        rw [hv]
        exact htail
      exact tetraRevNbr_ne_tail d j htail'
    · exact hji ((tetraRevNbr_injective d heq))
    · exact hjnext ((tetraRevNbr_injective d hnext))

/-- The concrete tetrahedron vertex star obtained from Euclidean coordinates. -/
def tetraVertexStar (v : tetraMap.Vertex) : VertexStar :=
  vertexStarOfEuclidean tetraEuclideanPolyhedron v (tetraVertexLinkGeometry v)

/-!
### General residual for the next geometry round

The remaining theorem should have the following shape:

`theorem vertexLinkGeometry_of_supporting_halfspaces
  (P : TriangulatedEuclideanPolyhedron M) (v : M.Vertex)
  (hSphere/simple/embedded-orientation hypotheses as needed) :
  VertexLinkGeometry P v`

It must prove the strict exposed-vertex open hemisphere and the oriented
σ-link determinant inequalities from the face-level supporting halfspaces.
-/

end ProofsInTheBook.Ch13EuclLink

#print axioms ProofsInTheBook.Ch13EuclLink.vertexStarOfEuclidean
#print axioms ProofsInTheBook.Ch13EuclLink.tetra_vDeg
#print axioms ProofsInTheBook.Ch13EuclLink.tetraVertexLinkGeometry
#print axioms ProofsInTheBook.Ch13EuclLink.tetraVertexStar
