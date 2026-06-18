import ProofsInTheBook.ZinanCh13SphAngle
import ProofsInTheBook.ZinanCh13EuclLink
import ProofsInTheBook.Ch13Realization
import ProofsInTheBook.Ch13LinkSides
import ProofsInTheBook.Ch13SubArcWrap
import Mathlib.Geometry.Euclidean.Triangle

/-!
# Chapter 13 Euclidean Cauchy assembly

This file starts the final Euclidean assembly layer.  The fully automatic
extraction of the local vertex-link geometry and the two-arc cut is wired here:
the remaining geometric payload in `ConvexEuclideanPolyhedron` is the faithful
rotation/simple-map input from which the link geometry is derived.
-/

noncomputable section

open scoped Classical RealInnerProductSpace
open ProofsInTheBook.PlanarMap ProofsInTheBook.PlanarMap.CombMap
open ProofsInTheBook.Chapter13
open ProofsInTheBook.Ch13Euclidean
open ProofsInTheBook.Ch13EuclLink
open ProofsInTheBook.Ch13Realization
open ProofsInTheBook.Ch13VertexStar
open ProofsInTheBook.Ch13ArmVertexFull
open ProofsInTheBook.Ch13ArmVertex
open ProofsInTheBook.Ch13SubArc
open ProofsInTheBook.Ch13SubArcWrap
open ProofsInTheBook.Ch13MarkedSphere
open ProofsInTheBook.SphericalKernel

namespace ProofsInTheBook.Ch13VertexStar

namespace VertexStar

/-- Rotate the cyclic neighbor order of a vertex star. -/
noncomputable abbrev rotate (S : VertexStar) (k : Fin (S.n + 1)) : VertexStar where
  n := S.n
  hn := S.hn
  o := S.o
  p := fun i => S.p (i + k)
  apex_ne := fun i => S.apex_ne (i + k)
  open_hemi := by
    rcases S.open_hemi with ⟨h, hnorm, hpos⟩
    exact ⟨h, hnorm, fun i => hpos (i + k)⟩
  turn_support := by
    intro i j
    have hnext : (i + 1 : Fin (S.n + 1)) + k = (i + k) + 1 := by
      rw [add_right_comm]
    simpa [hnext] using S.turn_support (i + k) (j + k)
  turn_strict := by
    intro i j hji hji1
    have hnext : (i + 1 : Fin (S.n + 1)) + k = (i + k) + 1 := by
      rw [add_right_comm]
    have hne0 : j + k ≠ i + k := by
      intro h
      exact hji (add_right_cancel h)
    have hne1 : j + k ≠ (i + k) + 1 := by
      intro h
      apply hji1
      apply add_right_cancel (b := k)
      rw [hnext]
      exact h
    simpa [hnext] using S.turn_strict (i + k) (j + k) hne0 hne1

theorem vertexLink_rotate (S : VertexStar) (k : Fin (S.n + 1)) :
    (S.rotate k).vertexLink = rotPoly S.vertexLink k := by
  funext i
  rfl

end VertexStar

end ProofsInTheBook.Ch13VertexStar

namespace ProofsInTheBook.Ch13Cauchy3D

variable {D : Type*} [Fintype D] [DecidableEq D]
variable {M : CombMap D}

/-- Compatibility abbreviation for this assembly layer: it already carries the local link geometry. -/
private abbrev vertexStarOfEuclidean
    (P : TriangulatedEuclideanPolyhedron M) (v : M.Vertex)
    (LG : VertexLinkGeometry P v) : VertexStar :=
  LG.toVertexStar

/--
A convex Euclidean polyhedron is a triangulated Euclidean realization together
with the faithful rotation and simple-graph hypotheses from which the local
vertex-link geometry is derived.

The `isSimple` field is included because the downstream Cauchy realization
interface requires a simple triangulated sphere.
-/
structure ConvexEuclideanPolyhedron (M : CombMap D)
    extends TriangulatedEuclideanPolyhedron M where
  degree_ge_three :
    ∀ (v : M.Vertex), 3 ≤ vDeg toTriangulatedEuclideanPolyhedron v
  faithful : RotationFaithful toTriangulatedEuclideanPolyhedron
  sphere : M.IsSphereMap
  triangle : M.FaceRegular 3
  isSimple : M.IsSimpleGraph

namespace ConvexEuclideanPolyhedron

/-- The underlying triangulated Euclidean realization. -/
abbrev toTri (P : ConvexEuclideanPolyhedron M) : TriangulatedEuclideanPolyhedron M :=
  P.toTriangulatedEuclideanPolyhedron

/-- The derived local vertex-link geometry at a vertex. -/
def linkGeom (P : ConvexEuclideanPolyhedron M) (v : M.Vertex)
    (hdeg : 3 ≤ vDeg P.toTri v) : VertexLinkGeometry P.toTri v :=
  vertexLinkGeometryOfEuclidean P.toTri P.faithful P.isSimple v hdeg

/-- The derived vertex-link geometry with the stored degree lower bound supplied. -/
def linkGeomAt (P : ConvexEuclideanPolyhedron M) (v : M.Vertex) :
    VertexLinkGeometry P.toTri v :=
  P.linkGeom v (P.degree_ge_three v)

/-- The Euclidean vertex star attached to a convex Euclidean polyhedron. -/
def vertexStar (P : ConvexEuclideanPolyhedron M) (v : M.Vertex) : VertexStar :=
  vertexStarOfEuclidean P.toTri v (P.linkGeomAt v)

end ConvexEuclideanPolyhedron

/-- The regular tetrahedron as a convex Euclidean polyhedron. -/
def tetraConvexEuclideanPolyhedron : ConvexEuclideanPolyhedron tetraMap where
  toTriangulatedEuclideanPolyhedron := tetraEuclideanPolyhedron
  degree_ge_three := tetra_vDeg_ge_three
  faithful := tetra_rotationFaithful
  sphere := tetraMap_isSphereMap
  triangle := tetraMap_faceRegular_three
  isSimple := ProofsInTheBook.Ch13ComponentClose.tetraMap_isSimpleGraph

/-- Edge-length congruence for two Euclidean realizations on the same combinatorial map. -/
def CongruentFaces (P Q : TriangulatedEuclideanPolyhedron M) : Prop :=
  ∀ d : D,
    ‖P.pos (M.head d) - P.pos (M.tail d)‖ =
      ‖Q.pos (M.head d) - Q.pos (M.tail d)‖

theorem euclidean_angle_eq_of_three_dist_eq
    {a b c a' b' c' : Ch13Euclidean.E3}
    (hab : dist b a = dist b' a')
    (hac : dist c a = dist c' a')
    (hbc : dist b c = dist b' c')
    (hba : b ≠ a) (hca : c ≠ a) :
    EuclideanGeometry.angle b a c = EuclideanGeometry.angle b' a' c' := by
  have hcos₁ := EuclideanGeometry.law_cos b a c
  have hcos₂ := EuclideanGeometry.law_cos b' a' c'
  rw [← hab, ← hac, ← hbc] at hcos₂
  have hprod : 2 * dist b a * dist c a ≠ 0 := by
    exact mul_ne_zero (mul_ne_zero (by norm_num) (dist_ne_zero.mpr hba))
      (dist_ne_zero.mpr hca)
  have hcos :
      Real.cos (EuclideanGeometry.angle b a c) =
        Real.cos (EuclideanGeometry.angle b' a' c') := by
    have hmul :
        (2 * dist b a * dist c a) * Real.cos (EuclideanGeometry.angle b a c) =
          (2 * dist b a * dist c a) * Real.cos (EuclideanGeometry.angle b' a' c') := by
      nlinarith
    exact mul_left_cancel₀ hprod hmul
  exact Real.injOn_cos
    ⟨EuclideanGeometry.angle_nonneg b a c, EuclideanGeometry.angle_le_pi b a c⟩
    ⟨EuclideanGeometry.angle_nonneg b' a' c', EuclideanGeometry.angle_le_pi b' a' c'⟩
    hcos

theorem congruentFaces_face_angle_at_dart
    (P Q : TriangulatedEuclideanPolyhedron M) (hcong : CongruentFaces P Q) (d : D) :
    EuclideanGeometry.angle
        (P.pos (M.head d)) (P.pos (M.tail d)) (P.pos (M.head (M.σ.symm d)))
      =
    EuclideanGeometry.angle
        (Q.pos (M.head d)) (Q.pos (M.tail d)) (Q.pos (M.head (M.σ.symm d))) := by
  have htail_symm : M.tail (M.σ.symm d) = M.tail d := by
    have h := M.tail_sigma (M.σ.symm d)
    simpa using h.symm
  have htail_phi2 :
      M.tail (M.φ (M.φ d)) = M.head (M.σ.symm d) :=
    Ch13SphAngle.tail_phi_phi_eq_head_sigma_symm_of_triangular_euclidean P d
  have hhead_phi :
      M.head (M.φ d) = M.head (M.σ.symm d) := by
    simpa [M.tail_phi] using htail_phi2
  have hab :
      dist (P.pos (M.head d)) (P.pos (M.tail d)) =
        dist (Q.pos (M.head d)) (Q.pos (M.tail d)) := by
    simpa [dist_eq_norm] using hcong d
  have hac :
      dist (P.pos (M.head (M.σ.symm d))) (P.pos (M.tail d)) =
        dist (Q.pos (M.head (M.σ.symm d))) (Q.pos (M.tail d)) := by
    have h := hcong (M.σ.symm d)
    simpa [dist_eq_norm, htail_symm] using h
  have hbc :
      dist (P.pos (M.head d)) (P.pos (M.head (M.σ.symm d))) =
        dist (Q.pos (M.head d)) (Q.pos (M.head (M.σ.symm d))) := by
    have h := hcong (M.φ d)
    simpa [dist_eq_norm, M.tail_phi, hhead_phi, norm_sub_rev] using h
  have hba : P.pos (M.head d) ≠ P.pos (M.tail d) := by
    exact (P.edge_nondegenerate d).symm
  have hca : P.pos (M.head (M.σ.symm d)) ≠ P.pos (M.tail d) := by
    have hnd := P.edge_nondegenerate (M.σ.symm d)
    simpa [htail_symm] using hnd.symm
  exact euclidean_angle_eq_of_three_dist_eq hab hac hbc hba hca

/-- The Euclidean dart sign used by the Cauchy marked sphere. -/
def euclideanEdgeSign (P Q : TriangulatedEuclideanPolyhedron M) : D → EdgeSign :=
  dihedralSignAtDart P Q

theorem euclideanEdgeSign_alpha
    (P Q : TriangulatedEuclideanPolyhedron M) (d : D) :
    euclideanEdgeSign P Q (M.α d) = euclideanEdgeSign P Q d := by
  unfold euclideanEdgeSign
  exact dihedralSignAtDart_alpha P Q d

/-- A canonical representative dart for a vertex. -/
def vertexDartRep (v : M.Vertex) : D :=
  Quotient.out v

theorem vertexDartRep_tail (v : M.Vertex) :
    M.tail (vertexDartRep (M := M) v) = v :=
  Quotient.out_eq v

/-- Reading a finite list through `Fin.rev` gives its reverse. -/
theorem ofFn_get_rev {α : Type*} (L : List α) :
    List.ofFn (fun i : Fin L.length => L.get (Fin.rev i)) = L.reverse := by
  apply (List.ext_get_iff).2
  constructor
  · simp
  · intro n hn₁ hn₂
    simp only [List.length_ofFn, List.length_reverse] at hn₁ hn₂
    rw [List.get_ofFn]
    rw [List.get_reverse' L ⟨n, by simpa using hn₂⟩ (by omega)]
    simp [Fin.rev]
    have hidx : L.length - (n + 1) = L.length - 1 - n := by omega
    simp [hidx]

theorem ofFn_cast {α : Type*} {n m : ℕ} (e : n = m) (f : Fin m → α) :
    List.ofFn (fun i : Fin n => f (Fin.cast e i)) = List.ofFn f := by
  subst e
  rfl

/-- The dart in the actual Euclidean vertex-star order, i.e. the reverse of the
combinatorial `σ` order used by `incidentDartOfStarIndex`. -/
def starDart (P : TriangulatedEuclideanPolyhedron M) (v : M.Vertex)
    (hdeg : 3 ≤ vDeg P v) (i : Fin (starN P v + 1)) : D :=
  incidentDartOfStarIndex P v hdeg (Fin.rev i)

theorem starDart_tail (P : TriangulatedEuclideanPolyhedron M) (v : M.Vertex)
    (hdeg : 3 ≤ vDeg P v) (i : Fin (starN P v + 1)) :
    M.tail (starDart P v hdeg i) = v := by
  unfold starDart
  exact incidentDartOfStarIndex_tail P v hdeg (Fin.rev i)

theorem starDart_eq_of_index
    (P Q : TriangulatedEuclideanPolyhedron M) (v : M.Vertex)
    (hdegP : 3 ≤ vDeg P v) (hdegQ : 3 ≤ vDeg Q v)
    {i : Fin (starN P v + 1)} {j : Fin (starN Q v + 1)}
    (hij : HEq i j) :
    starDart P v hdegP i = starDart Q v hdegQ j := by
  cases hij
  simp [starDart, incidentDartOfStarIndex, incidentDart, starIndexToDeg,
    incidentDarts, vDeg, starN]

theorem incidentDarts_mem_of_tail
    (P : TriangulatedEuclideanPolyhedron M) {v : M.Vertex} {d : D}
    (hdeg : 3 ≤ vDeg P v) (htail : M.tail d = v) :
    d ∈ incidentDarts P v := by
  unfold incidentDarts
  rw [Equiv.Perm.mem_toList_iff]
  constructor
  · exact Quotient.exact ((Quotient.out_eq v).trans htail.symm)
  · rw [← Equiv.Perm.two_le_length_toList_iff_mem_support]
    unfold vDeg incidentDarts at hdeg
    omega

theorem starDart_reverseStarIndexOfDart
    (P : TriangulatedEuclideanPolyhedron M) (v : M.Vertex)
    (hdeg : 3 ≤ vDeg P v) (d : D) (hd : d ∈ incidentDarts P v) :
    starDart P v hdeg (reverseStarIndexOfDart P v hdeg d hd) = d := by
  unfold starDart
  exact incidentDartOfStarIndex_reverseStarIndexOfDart P v hdeg d hd

theorem starDart_reverseStarIndexOfDart_add_one
    (P : TriangulatedEuclideanPolyhedron M) (v : M.Vertex)
    (hdeg : 3 ≤ vDeg P v) (d : D) (hd : d ∈ incidentDarts P v) :
    starDart P v hdeg
        (reverseStarIndexOfDart P v hdeg d hd + starOne P v hdeg) =
      M.σ.symm d := by
  unfold starDart
  exact incidentDartOfStarIndex_reverseStarIndexOfDart_add_one P v hdeg d hd

theorem starDart_reverseStarIndexOfDart_sub_one
    (P : TriangulatedEuclideanPolyhedron M) (v : M.Vertex)
    (hdeg : 3 ≤ vDeg P v) (d : D) (hd : d ∈ incidentDarts P v) :
    starDart P v hdeg
        (reverseStarIndexOfDart P v hdeg d hd - starOne P v hdeg) =
      M.σ d := by
  unfold starDart
  exact incidentDartOfStarIndex_reverseStarIndexOfDart_sub_one P v hdeg d hd

theorem starOne_eq_one
    (P : TriangulatedEuclideanPolyhedron M) (v : M.Vertex)
    (hdeg : 3 ≤ vDeg P v) :
    starOne P v hdeg = (1 : Fin (starN P v + 1)) := by
  ext
  unfold starOne starN
  simp [Nat.mod_eq_of_lt (by omega : 1 < vDeg P v - 1 + 1)]

theorem fin_cast_sub_one_starN
    (P : TriangulatedEuclideanPolyhedron M) (v : M.Vertex)
    (hdeg : 3 ≤ vDeg P v) {n : ℕ} (e : n = starN P v)
    (i : Fin (n + 1)) :
    Fin.cast (congrArg Nat.succ e) (i - 1) =
      Fin.cast (congrArg Nat.succ e) i - starOne P v hdeg := by
  subst e
  rw [starOne_eq_one P v hdeg]
  rfl

theorem fin_cast_add_one_starN
    (P : TriangulatedEuclideanPolyhedron M) (v : M.Vertex)
    (hdeg : 3 ≤ vDeg P v) {n : ℕ} (e : n = starN P v)
    (i : Fin (n + 1)) :
    Fin.cast (congrArg Nat.succ e) (i + 1) =
      Fin.cast (congrArg Nat.succ e) i + starOne P v hdeg := by
  subst e
  rw [starOne_eq_one P v hdeg]
  rfl

theorem fin_cast_zero_eq_last_add_one_starN
    (P : TriangulatedEuclideanPolyhedron M) (v : M.Vertex)
    (hdeg : 3 ≤ vDeg P v) {n : ℕ} (e : n = starN P v) :
    Fin.cast (congrArg Nat.succ e) (0 : Fin (n + 1)) =
      Fin.cast (congrArg Nat.succ e) (Fin.last n) + starOne P v hdeg := by
  subst e
  rw [starOne_eq_one P v hdeg]
  ext
  simp

theorem fin_cast_merge_starN
    {nP nQ s : ℕ} (eP : nP = s) (eQ : nQ = s) (h : nQ = nP)
    (i : Fin (nP + 1)) :
    Fin.cast (congrArg Nat.succ eP) i =
      Fin.cast (congrArg Nat.succ eQ)
        (Fin.cast (congrArg Nat.succ h.symm) i) := by
  subst eP
  subst eQ
  rfl

theorem fin_cast_merge_starN_linkQcast
    {nP nQ s : ℕ} (eP : nP = s) (eQ : nQ = s) (h : nQ = nP)
    (i : Fin (nP + 1)) :
    Fin.cast (congrArg Nat.succ eP) i =
      Fin.cast (congrArg Nat.succ eQ) (Fin.cast (by rw [h]) i) := by
  subst eP
  subst eQ
  rfl

theorem fin_cast_merge_starN_of_PQ
    {nP nQ s : ℕ} (eP : nP = s) (eQ : nQ = s) (h : nP = nQ)
    (i : Fin (nP + 1)) :
    Fin.cast (congrArg Nat.succ eP) i =
      Fin.cast (congrArg Nat.succ eQ) (Fin.cast (congrArg Nat.succ h) i) := by
  subst eP
  subst eQ
  rfl

theorem fin_cast_add {n m : ℕ} (h : n = m) (i j : Fin (n + 1)) :
    Fin.cast (congrArg Nat.succ h) (i + j) =
      Fin.cast (congrArg Nat.succ h) i + Fin.cast (congrArg Nat.succ h) j := by
  subst h
  rfl

theorem starDart_mem
    (P : TriangulatedEuclideanPolyhedron M) (v : M.Vertex)
    (hdeg : 3 ≤ vDeg P v) (i : Fin (starN P v + 1)) :
    starDart P v hdeg i ∈ incidentDarts P v := by
  unfold starDart incidentDartOfStarIndex incidentDart
  exact List.get_mem _ _

theorem reverseStarIndexOfDart_starDart
    (P : TriangulatedEuclideanPolyhedron M) (v : M.Vertex)
    (hdeg : 3 ≤ vDeg P v) (i : Fin (starN P v + 1)) :
    reverseStarIndexOfDart P v hdeg (starDart P v hdeg i)
        (starDart_mem P v hdeg i) = i := by
  unfold reverseStarIndexOfDart incidentIndexOfDart starDart incidentDartOfStarIndex
    incidentDart starIndexToDeg
  apply Fin.rev_injective
  apply Fin.ext
  have hnodup : (incidentDarts P v).Nodup := by
    unfold incidentDarts
    exact Equiv.Perm.nodup_toList M.σ (Quotient.out v)
  simp [hnodup.idxOf_getElem]

theorem starDart_add_one
    (P : TriangulatedEuclideanPolyhedron M) (v : M.Vertex)
    (hdeg : 3 ≤ vDeg P v) (i : Fin (starN P v + 1)) :
    starDart P v hdeg (i + starOne P v hdeg) =
      M.σ.symm (starDart P v hdeg i) := by
  have hidx := reverseStarIndexOfDart_starDart P v hdeg i
  calc
    starDart P v hdeg (i + starOne P v hdeg)
        = starDart P v hdeg
            (reverseStarIndexOfDart P v hdeg (starDart P v hdeg i)
                (starDart_mem P v hdeg i) + starOne P v hdeg) := by
            rw [hidx]
    _ = M.σ.symm (starDart P v hdeg i) :=
        starDart_reverseStarIndexOfDart_add_one P v hdeg
          (starDart P v hdeg i) (starDart_mem P v hdeg i)

theorem starDart_sub_one
    (P : TriangulatedEuclideanPolyhedron M) (v : M.Vertex)
    (hdeg : 3 ≤ vDeg P v) (i : Fin (starN P v + 1)) :
    starDart P v hdeg (i - starOne P v hdeg) =
      M.σ (starDart P v hdeg i) := by
  have hidx := reverseStarIndexOfDart_starDart P v hdeg i
  calc
    starDart P v hdeg (i - starOne P v hdeg)
        = starDart P v hdeg
            (reverseStarIndexOfDart P v hdeg (starDart P v hdeg i)
                (starDart_mem P v hdeg i) - starOne P v hdeg) := by
            rw [hidx]
    _ = M.σ (starDart P v hdeg i) :=
        starDart_reverseStarIndexOfDart_sub_one P v hdeg
          (starDart P v hdeg i) (starDart_mem P v hdeg i)

theorem starDart_order (P : TriangulatedEuclideanPolyhedron M) (v : M.Vertex)
    (hdeg : 3 ≤ vDeg P v) :
    (M.σ.toList (vertexDartRep (M := M) v)).reverse ~r
      List.ofFn (starDart P v hdeg) := by
  have hLen : starN P v + 1 = (incidentDarts P v).length := by
    rw [starN_add_one_eq_vDeg P v hdeg]
    rfl
  have hEq :
      List.ofFn (starDart P v hdeg) = (incidentDarts P v).reverse := by
    rw [List.ofFn_congr hLen (starDart P v hdeg)]
    rw [← ofFn_get_rev (incidentDarts P v)]
    rw [List.ofFn_inj]
    funext i
    simp [starDart, incidentDartOfStarIndex, incidentDart, starIndexToDeg, hLen]
  rw [hEq]
  change (incidentDarts P v).reverse ~r (incidentDarts P v).reverse
  exact List.IsRotated.refl _

theorem dihedralRotated_of_starDart_order
    {n : ℕ} (root : D) (edgeSign : D → EdgeSign)
    (starDart : Fin n → D) (geomDiff : Fin n → ℝ)
    (horder : (M.σ.toList root).reverse ~r List.ofFn starDart)
    (hval : ∀ i : Fin n,
      edgeSign (starDart i) = realSignToEdgeSign (geomDiff i)) :
    List.DihedralRotated ((M.σ.toList root).map edgeSign)
      ((List.ofFn geomDiff).map realSignToEdgeSign) := by
  right
  have horderSign :
      ((M.σ.toList root).reverse.map edgeSign) ~r
        ((List.ofFn starDart).map edgeSign) :=
    horder.map edgeSign
  have hleft :
      ((M.σ.toList root).map edgeSign).reverse =
        (M.σ.toList root).reverse.map edgeSign := by
    simp [List.map_reverse]
  have hright :
      (List.ofFn starDart).map edgeSign =
        (List.ofFn geomDiff).map realSignToEdgeSign := by
    apply List.ext_getElem
    · simp
    · intro k hk₁ hk₂
      simp only [List.length_map, List.length_ofFn] at hk₁ hk₂
      simp only [List.getElem_map, List.getElem_ofFn]
      exact hval ⟨k, hk₂⟩
  rw [hleft]
  exact horderSign.trans (by rw [hright])

/-- The neighbour list stored in a `VertexLinkGeometry` is the head list of the
corresponding `starDart`s. -/
theorem vertexLinkGeometry_nbr_eq_head_starDart
    (P : TriangulatedEuclideanPolyhedron M) (v : M.Vertex)
    (LG : VertexLinkGeometry P v) :
    ∃ hdeg : 3 ≤ vDeg P v, ∃ e : LG.n = starN P v,
      ∀ i : Fin (LG.n + 1),
        LG.nbr i =
          M.head (starDart P v hdeg (Fin.cast (congrArg Nat.succ e) i)) := by
  rcases LG.nbr_is_sigma with ⟨hdeg, e, h⟩
  refine ⟨hdeg, e, ?_⟩
  intro i
  simpa [starDart] using h i

/-- The `VertexStar.p` points are exactly the positions of heads of `starDart`s. -/
theorem vertexStar_p_eq_head_starDart
    (P : TriangulatedEuclideanPolyhedron M) (v : M.Vertex)
    (LG : VertexLinkGeometry P v) :
    ∃ hdeg : 3 ≤ vDeg P v, ∃ e : LG.n = starN P v,
      ∀ i : Fin ((vertexStarOfEuclidean P v LG).n + 1),
        (vertexStarOfEuclidean P v LG).p i =
          P.pos (M.head (starDart P v hdeg (Fin.cast (congrArg Nat.succ e) i))) := by
  rcases vertexLinkGeometry_nbr_eq_head_starDart P v LG with ⟨hdeg, e, h⟩
  refine ⟨hdeg, e, ?_⟩
  intro i
  unfold vertexStarOfEuclidean VertexLinkGeometry.toVertexStar
  change P.pos (LG.nbr i) =
    P.pos (M.head (starDart P v hdeg (Fin.cast (congrArg Nat.succ e) i)))
  rw [h i]

theorem vertexStarOfEuclidean_n
    (P : TriangulatedEuclideanPolyhedron M) (v : M.Vertex)
    (LG : VertexLinkGeometry P v) :
    (vertexStarOfEuclidean P v LG).n = LG.n := rfl

theorem dihedralAngleAtDart_eq_linkAngle_at_vertex
    (P : TriangulatedEuclideanPolyhedron M) (d : D) {v : M.Vertex}
    (htail : M.tail d = v) (LG : VertexLinkGeometry P v) (J : Fin (LG.n + 1))
    (hprev : LG.nbr (J - 1) = M.head (M.σ d))
    (hcenter : LG.nbr J = M.head d)
    (hnext : LG.nbr (J + 1) = M.head (M.σ.symm d)) :
    dihedralAngleAtDart P d =
      linkAngle (vertexStarOfEuclidean P v LG).vertexLink J := by
  subst v
  exact ProofsInTheBook.Ch13SphAngle.dihedralAngleAtDart_eq_linkAngle
    P d LG J hprev hcenter hnext

theorem dihedralAngleAt_starDart_eq_linkAngle
    (P : TriangulatedEuclideanPolyhedron M) (v : M.Vertex)
    (LG : VertexLinkGeometry P v) :
    ∃ hdeg : 3 ≤ vDeg P v, ∃ e : LG.n = starN P v,
      ∀ J : Fin (LG.n + 1),
        dihedralAngleAtDart P
            (starDart P v hdeg (Fin.cast (congrArg Nat.succ e) J)) =
          linkAngle (vertexStarOfEuclidean P v LG).vertexLink J := by
  rcases vertexLinkGeometry_nbr_eq_head_starDart P v LG with ⟨hdeg, e, hnbr⟩
  refine ⟨hdeg, e, ?_⟩
  intro J
  let J' : Fin (starN P v + 1) := Fin.cast (congrArg Nat.succ e) J
  let d : D := starDart P v hdeg J'
  have htail_d : M.tail d = v := by
    simpa [d] using starDart_tail P v hdeg J'
  have hcenter :
      LG.nbr J = M.head d := by
    simpa [d, J'] using hnbr J
  have hprev :
      LG.nbr (J - 1) = M.head (M.σ d) := by
    have h := hnbr (J - 1)
    rw [fin_cast_sub_one_starN P v hdeg e J] at h
    rw [starDart_sub_one P v hdeg J'] at h
    simpa [d, J'] using h
  have hnext :
      LG.nbr (J + 1) = M.head (M.σ.symm d) := by
    have h := hnbr (J + 1)
    rw [fin_cast_add_one_starN P v hdeg e J] at h
    rw [starDart_add_one P v hdeg J'] at h
    simpa [d, J'] using h
  have hlink := dihedralAngleAtDart_eq_linkAngle_at_vertex P d htail_d
    LG J hprev hcenter hnext
  simpa [d, J'] using hlink

theorem vertexStar_side_angle_eq_dart_angle
    (P : TriangulatedEuclideanPolyhedron M) (v : M.Vertex)
    (LG : VertexLinkGeometry P v) :
    ∃ hdeg : 3 ≤ vDeg P v, ∃ e : LG.n = starN P v,
      ∀ i : Fin LG.n,
        let d := starDart P v hdeg (Fin.cast (congrArg Nat.succ e) i.castSucc)
        EuclideanGeometry.angle
            ((vertexStarOfEuclidean P v LG).p i.castSucc)
            (vertexStarOfEuclidean P v LG).o
            ((vertexStarOfEuclidean P v LG).p i.succ)
          =
        EuclideanGeometry.angle
            (P.pos (M.head d)) (P.pos (M.tail d)) (P.pos (M.head (M.σ.symm d))) := by
  rcases vertexStar_p_eq_head_starDart P v LG with ⟨hdeg, e, hp⟩
  refine ⟨hdeg, e, ?_⟩
  intro i
  let J : Fin (LG.n + 1) := i.castSucc
  let J' : Fin (starN P v + 1) := Fin.cast (congrArg Nat.succ e) J
  let d : D := starDart P v hdeg J'
  have hsucc :
      Fin.cast (congrArg Nat.succ e) i.succ = J' + starOne P v hdeg := by
    simpa [J, J'] using fin_cast_add_one_starN P v hdeg e J
  have hp0 := hp i.castSucc
  have hp1 := hp i.succ
  rw [hsucc] at hp1
  rw [starDart_add_one P v hdeg J'] at hp1
  have htail : M.tail d = v := by
    simpa [d] using starDart_tail P v hdeg J'
  have htail' :
      M.tail (starDart P v hdeg (Fin.cast (congrArg Nat.succ e) i.castSucc)) = v := by
    simpa [d, J, J'] using htail
  rw [hp0, hp1]
  dsimp [d, J']
  unfold vertexStarOfEuclidean VertexLinkGeometry.toVertexStar
  change EuclideanGeometry.angle
      (P.pos (M.head (starDart P v hdeg (Fin.cast (congrArg Nat.succ e) i.castSucc))))
      (P.pos v)
      (P.pos (M.head (M.σ.symm
        (starDart P v hdeg (Fin.cast (congrArg Nat.succ e) i.castSucc))))) =
    EuclideanGeometry.angle
      (P.pos (M.head (starDart P v hdeg (Fin.cast (congrArg Nat.succ e) i.castSucc))))
      (P.pos (M.tail (starDart P v hdeg (Fin.cast (congrArg Nat.succ e) i.castSucc))))
      (P.pos (M.head (M.σ.symm
        (starDart P v hdeg (Fin.cast (congrArg Nat.succ e) i.castSucc)))))
  rw [htail']

theorem vertexLinkGeometry_n_eq
    (P Q : TriangulatedEuclideanPolyhedron M)
    (LGP : ∀ v : M.Vertex, VertexLinkGeometry P v)
    (LGQ : ∀ v : M.Vertex, VertexLinkGeometry Q v)
    (v : M.Vertex) :
    (LGQ v).n = (LGP v).n := by
  rcases (LGP v).nbr_is_sigma with ⟨hdegP, eP, _⟩
  rcases (LGQ v).nbr_is_sigma with ⟨hdegQ, eQ, _⟩
  have hstar : starN P v = starN Q v := by
    rfl
  calc
    (LGQ v).n = starN Q v := eQ
    _ = starN P v := hstar.symm
    _ = (LGP v).n := eP.symm

theorem linkAngle_reindex {n m : ℕ} (h : n = m) (A : Fin (m + 1) → S2)
    (i : Fin (n + 1)) :
    linkAngle (fun j : Fin (n + 1) => A (Fin.cast (by rw [h]) j)) i =
      linkAngle A (Fin.cast (by rw [h]) i) := by
  subst h
  simp

theorem sideLen_reindex {n m : ℕ} (h : n = m) (A : Fin (m + 1) → S2)
    (i : Fin n) :
    sideLen (fun j : Fin (n + 1) => A (Fin.cast (by rw [h]) j)) i =
      sideLen A (Fin.cast (by rw [h]) i) := by
  subst h
  simp [sideLen]

theorem vertexStar_sDist_vertexLink_eq_angle
    (S : VertexStar) (i j : Fin (S.n + 1)) :
    sDist (S.vertexLink i) (S.vertexLink j) =
      EuclideanGeometry.angle (S.p i) S.o (S.p j) := by
  rw [ProofsInTheBook.SphericalArm.sDist_eq_angle]
  rw [VertexStar.vertexLink_apply, VertexStar.vertexLink_apply]
  rw [VertexStar.edgeDir_coe, VertexStar.edgeDir_coe]
  rw [InnerProductGeometry.angle_smul_left_of_pos _ _ (S.inv_norm_pos _),
      InnerProductGeometry.angle_smul_right_of_pos _ _ (S.inv_norm_pos _)]
  rw [EuclideanGeometry.angle]
  rfl

theorem euclidean_sides_eq
    (P Q : TriangulatedEuclideanPolyhedron M)
    (LGP : ∀ v : M.Vertex, VertexLinkGeometry P v)
    (LGQ : ∀ v : M.Vertex, VertexLinkGeometry Q v)
    (hcong : CongruentFaces P Q) :
    ∀ (v : M.Vertex) (i : Fin (vertexStarOfEuclidean P v (LGP v)).n),
      sideLen (vertexStarOfEuclidean P v (LGP v)).vertexLink i =
        sideLen (linkQcast M
          (fun w => vertexStarOfEuclidean P w (LGP w))
          (fun w => vertexStarOfEuclidean Q w (LGQ w))
          (fun w => vertexLinkGeometry_n_eq P Q LGP LGQ w) v) i := by
  intro v i
  let S := vertexStarOfEuclidean P v (LGP v)
  let T := vertexStarOfEuclidean Q v (LGQ v)
  let hnn := vertexLinkGeometry_n_eq P Q LGP LGQ v
  let hPQ : S.n = T.n := by
    change (LGP v).n = (LGQ v).n
    rw [hnn]
  have hside := sideLen_vertexLink_eq_of_faceAngle_eq S T hnn ?_ i
  · have hcast :
        sideLen (linkQcast M
          (fun w => vertexStarOfEuclidean P w (LGP w))
          (fun w => vertexStarOfEuclidean Q w (LGQ w))
          (fun w => vertexLinkGeometry_n_eq P Q LGP LGQ w) v) i =
        sideLen T.vertexLink (i.cast hnn.symm) := by
      dsimp [S, T]
      unfold linkQcast
      exact sideLen_reindex
        (by
          change (LGP v).n = (LGQ v).n
          rw [hnn])
        (vertexStarOfEuclidean Q v (LGQ v)).edgeDir i
    rw [hside]
    exact hcast.symm
  · intro j
    rcases vertexStar_side_angle_eq_dart_angle P v (LGP v) with ⟨hdegP, eP, hPangle⟩
    rcases vertexStar_side_angle_eq_dart_angle Q v (LGQ v) with ⟨hdegQ, eQ, hQangle⟩
    let jQ : Fin (LGQ v).n := j.cast hnn.symm
    let dP : D := starDart P v hdegP
      (Fin.cast (congrArg Nat.succ eP) j.castSucc)
    let dQ : D := starDart Q v hdegQ
      (Fin.cast (congrArg Nat.succ eQ) jQ.castSucc)
    have hidx :
        Fin.cast (congrArg Nat.succ eP) j.castSucc =
          Fin.cast (congrArg Nat.succ eQ) jQ.castSucc := by
      dsimp [jQ]
      exact fin_cast_merge_starN_of_PQ eP eQ
        (by
          change (LGP v).n = (LGQ v).n
          rw [hnn]) j.castSucc
    have hd : dP = dQ := by
      dsimp [dP, dQ]
      exact starDart_eq_of_index P Q v hdegP hdegQ (heq_of_eq hidx)
    have hPj := hPangle j
    have hQj := hQangle jQ
    dsimp [S, T] at *
    calc
      EuclideanGeometry.angle ((vertexStarOfEuclidean P v (LGP v)).p j.castSucc)
          (vertexStarOfEuclidean P v (LGP v)).o
          ((vertexStarOfEuclidean P v (LGP v)).p j.succ)
          =
        EuclideanGeometry.angle (P.pos (M.head dP)) (P.pos (M.tail dP))
          (P.pos (M.head (M.σ.symm dP))) := hPj
      _ =
        EuclideanGeometry.angle (Q.pos (M.head dP)) (Q.pos (M.tail dP))
          (Q.pos (M.head (M.σ.symm dP))) :=
            congruentFaces_face_angle_at_dart P Q hcong dP
      _ =
        EuclideanGeometry.angle (Q.pos (M.head dQ)) (Q.pos (M.tail dQ))
          (Q.pos (M.head (M.σ.symm dQ))) := by rw [hd]
      _ =
        EuclideanGeometry.angle ((vertexStarOfEuclidean Q v (LGQ v)).p jQ.castSucc)
          (vertexStarOfEuclidean Q v (LGQ v)).o
          ((vertexStarOfEuclidean Q v (LGQ v)).p jQ.succ) := hQj.symm

theorem euclidean_close_eq
    (P Q : TriangulatedEuclideanPolyhedron M)
    (LGP : ∀ v : M.Vertex, VertexLinkGeometry P v)
    (LGQ : ∀ v : M.Vertex, VertexLinkGeometry Q v)
    (hcong : CongruentFaces P Q) :
    ∀ (v : M.Vertex),
      sDist ((vertexStarOfEuclidean P v (LGP v)).vertexLink 0)
          ((vertexStarOfEuclidean P v (LGP v)).vertexLink
            (Fin.last (vertexStarOfEuclidean P v (LGP v)).n))
        =
      sDist ((linkQcast M
          (fun w => vertexStarOfEuclidean P w (LGP w))
          (fun w => vertexStarOfEuclidean Q w (LGQ w))
          (fun w => vertexLinkGeometry_n_eq P Q LGP LGQ w) v) 0)
        ((linkQcast M
          (fun w => vertexStarOfEuclidean P w (LGP w))
          (fun w => vertexStarOfEuclidean Q w (LGQ w))
          (fun w => vertexLinkGeometry_n_eq P Q LGP LGQ w) v)
            (Fin.last (vertexStarOfEuclidean P v (LGP v)).n)) := by
  intro v
  let S := vertexStarOfEuclidean P v (LGP v)
  let T := vertexStarOfEuclidean Q v (LGQ v)
  let hnn := vertexLinkGeometry_n_eq P Q LGP LGQ v
  let hPQ : S.n = T.n := by
    change (LGP v).n = (LGQ v).n
    rw [hnn]
  rcases vertexStar_p_eq_head_starDart P v (LGP v) with ⟨hdegP, eP, hpP⟩
  rcases vertexStar_p_eq_head_starDart Q v (LGQ v) with ⟨hdegQ, eQ, hpQ⟩
  let lastP : Fin ((LGP v).n + 1) := Fin.last (LGP v).n
  let lastQ : Fin ((LGQ v).n + 1) := Fin.last (LGQ v).n
  let dP : D := starDart P v hdegP (Fin.cast (congrArg Nat.succ eP) lastP)
  let dQ : D := starDart Q v hdegQ (Fin.cast (congrArg Nat.succ eQ) lastQ)
  have hidx_last :
      Fin.cast (congrArg Nat.succ eP) lastP =
        Fin.cast (congrArg Nat.succ eQ) lastQ := by
    dsimp [lastP, lastQ]
    apply Fin.ext
    simp [eP, eQ, starN, vDeg, incidentDarts]
  have hd : dP = dQ := by
    dsimp [dP, dQ]
    exact starDart_eq_of_index P Q v hdegP hdegQ (heq_of_eq hidx_last)
  have hwrapP :
      starDart P v hdegP (Fin.cast (congrArg Nat.succ eP) (0 : Fin ((LGP v).n + 1))) =
        M.σ.symm dP := by
    have hwrap := fin_cast_zero_eq_last_add_one_starN P v hdegP eP
    rw [hwrap]
    dsimp [dP, lastP]
    exact starDart_add_one P v hdegP (Fin.cast (congrArg Nat.succ eP) (Fin.last (LGP v).n))
  have hwrapQ :
      starDart Q v hdegQ (Fin.cast (congrArg Nat.succ eQ) (0 : Fin ((LGQ v).n + 1))) =
        M.σ.symm dQ := by
    have hwrap := fin_cast_zero_eq_last_add_one_starN Q v hdegQ eQ
    rw [hwrap]
    dsimp [dQ, lastQ]
    exact starDart_add_one Q v hdegQ (Fin.cast (congrArg Nat.succ eQ) (Fin.last (LGQ v).n))
  have hpP0 := hpP (0 : Fin ((LGP v).n + 1))
  have hpPL := hpP lastP
  have hpQ0 := hpQ (0 : Fin ((LGQ v).n + 1))
  have hpQL := hpQ lastQ
  rw [hwrapP] at hpP0
  rw [hwrapQ] at hpQ0
  have htailP : M.tail dP = v := by
    simpa [dP] using starDart_tail P v hdegP (Fin.cast (congrArg Nat.succ eP) lastP)
  have htailQ : M.tail dQ = v := by
    simpa [dQ] using starDart_tail Q v hdegQ (Fin.cast (congrArg Nat.succ eQ) lastQ)
  have hcloseCast :
      sDist ((linkQcast M
          (fun w => vertexStarOfEuclidean P w (LGP w))
          (fun w => vertexStarOfEuclidean Q w (LGQ w))
          (fun w => vertexLinkGeometry_n_eq P Q LGP LGQ w) v) 0)
        ((linkQcast M
          (fun w => vertexStarOfEuclidean P w (LGP w))
          (fun w => vertexStarOfEuclidean Q w (LGQ w))
          (fun w => vertexLinkGeometry_n_eq P Q LGP LGQ w) v)
            (Fin.last (vertexStarOfEuclidean P v (LGP v)).n))
        =
      sDist (T.vertexLink 0) (T.vertexLink (Fin.last T.n)) := by
    dsimp [T]
    have h0 :
        Fin.cast (congrArg Nat.succ (by
          change (vertexStarOfEuclidean P v (LGP v)).n =
            (vertexStarOfEuclidean Q v (LGQ v)).n
          change (LGP v).n = (LGQ v).n
          rw [vertexLinkGeometry_n_eq P Q LGP LGQ v]))
          (0 : Fin ((vertexStarOfEuclidean P v (LGP v)).n + 1))
          =
        (0 : Fin ((vertexStarOfEuclidean Q v (LGQ v)).n + 1)) := by
      ext
      simp
    have hlast :
        Fin.cast (congrArg Nat.succ (by
          change (vertexStarOfEuclidean P v (LGP v)).n =
            (vertexStarOfEuclidean Q v (LGQ v)).n
          change (LGP v).n = (LGQ v).n
          rw [vertexLinkGeometry_n_eq P Q LGP LGQ v]))
          (Fin.last (vertexStarOfEuclidean P v (LGP v)).n)
          =
        Fin.last (vertexStarOfEuclidean Q v (LGQ v)).n := by
      ext
      change (vertexStarOfEuclidean P v (LGP v)).n =
        (vertexStarOfEuclidean Q v (LGQ v)).n
      change (LGP v).n = (LGQ v).n
      rw [vertexLinkGeometry_n_eq P Q LGP LGQ v]
    rw [hlast]
  have hPclose :
      EuclideanGeometry.angle ((vertexStarOfEuclidean P v (LGP v)).p 0)
          (vertexStarOfEuclidean P v (LGP v)).o
          ((vertexStarOfEuclidean P v (LGP v)).p
            (Fin.last (vertexStarOfEuclidean P v (LGP v)).n)) =
        EuclideanGeometry.angle (P.pos (M.head (M.σ.symm dP))) (P.pos (M.tail dP))
          (P.pos (M.head dP)) := by
    unfold vertexStarOfEuclidean VertexLinkGeometry.toVertexStar at hpP0 hpPL ⊢
    change EuclideanGeometry.angle (P.pos ((LGP v).nbr 0)) (P.pos v)
        (P.pos ((LGP v).nbr (Fin.last (LGP v).n))) =
      EuclideanGeometry.angle (P.pos (M.head (M.σ.symm dP))) (P.pos (M.tail dP))
        (P.pos (M.head dP))
    have hpP0' : P.pos ((LGP v).nbr 0) = P.pos (M.head (M.σ.symm dP)) := by
      simpa using hpP0
    have hpPL' : P.pos ((LGP v).nbr (Fin.last (LGP v).n)) = P.pos (M.head dP) := by
      simpa [lastP, dP] using hpPL
    rw [hpP0', hpPL', htailP]
  have hQclose :
      EuclideanGeometry.angle ((vertexStarOfEuclidean Q v (LGQ v)).p 0)
          (vertexStarOfEuclidean Q v (LGQ v)).o
          ((vertexStarOfEuclidean Q v (LGQ v)).p
            (Fin.last (vertexStarOfEuclidean Q v (LGQ v)).n)) =
        EuclideanGeometry.angle (Q.pos (M.head (M.σ.symm dQ))) (Q.pos (M.tail dQ))
          (Q.pos (M.head dQ)) := by
    unfold vertexStarOfEuclidean VertexLinkGeometry.toVertexStar at hpQ0 hpQL ⊢
    change EuclideanGeometry.angle (Q.pos ((LGQ v).nbr 0)) (Q.pos v)
        (Q.pos ((LGQ v).nbr (Fin.last (LGQ v).n))) =
      EuclideanGeometry.angle (Q.pos (M.head (M.σ.symm dQ))) (Q.pos (M.tail dQ))
        (Q.pos (M.head dQ))
    have hpQ0' : Q.pos ((LGQ v).nbr 0) = Q.pos (M.head (M.σ.symm dQ)) := by
      simpa using hpQ0
    have hpQL' : Q.pos ((LGQ v).nbr (Fin.last (LGQ v).n)) = Q.pos (M.head dQ) := by
      simpa [lastQ, dQ] using hpQL
    rw [hpQ0', hpQL', htailQ]
  calc
    sDist (S.vertexLink 0) (S.vertexLink (Fin.last S.n))
        = EuclideanGeometry.angle (S.p 0) S.o (S.p (Fin.last S.n)) :=
            vertexStar_sDist_vertexLink_eq_angle S 0 (Fin.last S.n)
    _ = EuclideanGeometry.angle (P.pos (M.head (M.σ.symm dP))) (P.pos (M.tail dP))
          (P.pos (M.head dP)) := by
            dsimp [S]
            exact hPclose
    _ = EuclideanGeometry.angle (P.pos (M.head dP)) (P.pos (M.tail dP))
          (P.pos (M.head (M.σ.symm dP))) := by
            rw [EuclideanGeometry.angle_comm]
    _ = EuclideanGeometry.angle (Q.pos (M.head dP)) (Q.pos (M.tail dP))
          (Q.pos (M.head (M.σ.symm dP))) :=
            congruentFaces_face_angle_at_dart P Q hcong dP
    _ = EuclideanGeometry.angle (Q.pos (M.head (M.σ.symm dQ))) (Q.pos (M.tail dQ))
          (Q.pos (M.head dQ)) := by
            rw [hd, EuclideanGeometry.angle_comm]
    _ = EuclideanGeometry.angle (T.p 0) T.o (T.p (Fin.last T.n)) := by
            dsimp [T]
            exact hQclose.symm
    _ = sDist (T.vertexLink 0) (T.vertexLink (Fin.last T.n)) := by
            rw [vertexStar_sDist_vertexLink_eq_angle T 0 (Fin.last T.n)]
    _ = sDist ((linkQcast M
          (fun w => vertexStarOfEuclidean P w (LGP w))
          (fun w => vertexStarOfEuclidean Q w (LGQ w))
          (fun w => vertexLinkGeometry_n_eq P Q LGP LGQ w) v) 0)
        ((linkQcast M
          (fun w => vertexStarOfEuclidean P w (LGP w))
          (fun w => vertexStarOfEuclidean Q w (LGQ w))
          (fun w => vertexLinkGeometry_n_eq P Q LGP LGQ w) v)
            (Fin.last (vertexStarOfEuclidean P v (LGP v)).n)) := hcloseCast.symm

theorem euclidean_linkOrder_at_root
    (P Q : TriangulatedEuclideanPolyhedron M)
    (LGP : ∀ v : M.Vertex, VertexLinkGeometry P v)
    (LGQ : ∀ v : M.Vertex, VertexLinkGeometry Q v)
    (v : M.Vertex) (root : D) (hroot : M.tail root = v) :
      List.DihedralRotated
        ((M.σ.toList root).map (euclideanEdgeSign P Q))
        ((List.ofFn
          (linkDiff (vertexStarOfEuclidean P v (LGP v)).vertexLink
            (linkQcast M
              (fun w => vertexStarOfEuclidean P w (LGP w))
              (fun w => vertexStarOfEuclidean Q w (LGQ w))
              (fun w => vertexLinkGeometry_n_eq P Q LGP LGQ w) v))).map realSignToEdgeSign) := by
  rcases dihedralAngleAt_starDart_eq_linkAngle P v (LGP v) with ⟨hdegP, eP, hP⟩
  rcases dihedralAngleAt_starDart_eq_linkAngle Q v (LGQ v) with ⟨hdegQ, eQ, hQ⟩
  let hnn := vertexLinkGeometry_n_eq P Q LGP LGQ v
  let hPQ : (LGP v).n = (LGQ v).n := by rw [hnn]
  let starP := fun i : Fin ((LGP v).n + 1) =>
    starDart P v hdegP (Fin.cast (congrArg Nat.succ eP) i)
  let geomDiff := linkDiff (vertexStarOfEuclidean P v (LGP v)).vertexLink
    (linkQcast M
      (fun w => vertexStarOfEuclidean P w (LGP w))
      (fun w => vertexStarOfEuclidean Q w (LGQ w))
      (fun w => vertexLinkGeometry_n_eq P Q LGP LGQ w) v)
  have horder :
      (M.σ.toList root).reverse ~r List.ofFn starP := by
    have h := starDart_order P v hdegP
    have hsc : M.σ.SameCycle (vertexDartRep (M := M) v) root :=
      Quotient.exact ((vertexDartRep_tail (M := M) v).trans hroot.symm)
    have hrot :
        (M.σ.toList root).reverse ~r
          (M.σ.toList (vertexDartRep (M := M) v)).reverse :=
      (hsc.toList_isRotated.reverse).symm
    have hofn :
        List.ofFn starP = List.ofFn (starDart P v hdegP) := by
      dsimp [starP]
      rw [ofFn_cast (congrArg Nat.succ eP) (starDart P v hdegP)]
    rw [hofn]
    exact hrot.trans h
  have hval :
      ∀ i : Fin ((LGP v).n + 1),
        euclideanEdgeSign P Q (starP i) = realSignToEdgeSign (geomDiff i) := by
    intro i
    have hidx :
        Fin.cast (congrArg Nat.succ eP) i =
          Fin.cast (congrArg Nat.succ eQ)
            (Fin.cast (congrArg Nat.succ hPQ) i) :=
      fin_cast_merge_starN_of_PQ eP eQ hPQ i
    have hPi := hP i
    let iQ : Fin ((LGQ v).n + 1) := Fin.cast (congrArg Nat.succ hPQ) i
    have hQi := hQ iQ
    have hstarQ :
        starP i =
          starDart Q v hdegQ (Fin.cast (congrArg Nat.succ eQ) iQ) := by
      dsimp [starP]
      exact starDart_eq_of_index P Q v hdegP hdegQ (heq_of_eq hidx)
    unfold euclideanEdgeSign dihedralSignAtDart
    rw [hPi]
    rw [hstarQ, hQi]
    have hgeom :
        geomDiff i =
          linkAngle (vertexStarOfEuclidean Q v (LGQ v)).vertexLink iQ -
            linkAngle (vertexStarOfEuclidean P v (LGP v)).vertexLink i := by
      dsimp [geomDiff, linkDiff]
      unfold linkQcast
      dsimp [iQ, hPQ]
      exact congrArg
        (fun x => x - linkAngle (vertexStarOfEuclidean P v (LGP v)).vertexLink i)
        (linkAngle_reindex
          (by
            change (LGP v).n = (LGQ v).n
            exact hPQ)
          (vertexStarOfEuclidean Q v (LGQ v)).edgeDir i)
    rw [hgeom]
  exact dihedralRotated_of_starDart_order (M := M)
    root (euclideanEdgeSign P Q) starP geomDiff horder hval

theorem euclidean_linkOrder
    (P Q : TriangulatedEuclideanPolyhedron M)
    (LGP : ∀ v : M.Vertex, VertexLinkGeometry P v)
    (LGQ : ∀ v : M.Vertex, VertexLinkGeometry Q v) :
    ∀ (v : M.Vertex),
      List.DihedralRotated
        ((M.σ.toList (vertexDartRep v)).map (euclideanEdgeSign P Q))
        ((List.ofFn
          (linkDiff (vertexStarOfEuclidean P v (LGP v)).vertexLink
            (linkQcast M
              (fun w => vertexStarOfEuclidean P w (LGP w))
              (fun w => vertexStarOfEuclidean Q w (LGQ w))
              (fun w => vertexLinkGeometry_n_eq P Q LGP LGQ w) v))).map realSignToEdgeSign) := by
  intro v
  exact euclidean_linkOrder_at_root P Q LGP LGQ v (vertexDartRep v) (vertexDartRep_tail v)

theorem linkAngle_rotPoly {n : ℕ} (A : Fin (n + 1) → S2)
    (k i : Fin (n + 1)) :
    linkAngle (rotPoly A k) i = linkAngle A (i + k) := by
  unfold linkAngle rotPoly
  have hprev : (i - 1 : Fin (n + 1)) + k = (i + k) - 1 := by
    rw [sub_eq_add_neg, sub_eq_add_neg]
    abel
  have hnext : (i + 1 : Fin (n + 1)) + k = (i + k) + 1 := by
    rw [add_right_comm]
  rw [hprev, hnext]

theorem linkDiff_rotPoly {n : ℕ} (A B : Fin (n + 1) → S2)
    (k i : Fin (n + 1)) :
    linkDiff (rotPoly A k) (rotPoly B k) i = linkDiff A B (i + k) := by
  unfold linkDiff
  rw [linkAngle_rotPoly B k i, linkAngle_rotPoly A k i]

theorem ofFn_add_isRotated {α : Type*} {n : ℕ} (f : Fin n → α) (k : Fin n) :
    List.ofFn f ~r List.ofFn (fun i : Fin n => f (i + k)) := by
  refine ⟨k.val, ?_⟩
  apply List.ext_getElem
  · simp [List.length_rotate]
  · intro m hm₁ hm₂
    simp only [List.length_rotate, List.length_ofFn] at hm₁ hm₂
    rw [List.getElem_rotate]
    simp only [List.getElem_ofFn]
    apply congrArg f
    apply Fin.ext
    simp [Fin.val_add]

theorem dihedralRotated_trans_right {α : Type*} {l m m' : List α}
    (h : List.DihedralRotated l m) (hr : m ~r m') :
    List.DihedralRotated l m' := by
  rcases h with hrot | hrev
  · exact Or.inl (hrot.trans hr)
  · exact Or.inr (hrev.trans hr)

theorem euclideanEdgeSign_starDart_eq_linkDiff
    (P Q : TriangulatedEuclideanPolyhedron M)
    (LGP : ∀ v : M.Vertex, VertexLinkGeometry P v)
    (LGQ : ∀ v : M.Vertex, VertexLinkGeometry Q v)
    (v : M.Vertex) :
    ∃ hdeg : 3 ≤ vDeg P v, ∃ e : (LGP v).n = starN P v,
      ∀ i : Fin ((LGP v).n + 1),
        euclideanEdgeSign P Q
            (starDart P v hdeg (Fin.cast (congrArg Nat.succ e) i))
          =
        realSignToEdgeSign
          (linkDiff (vertexStarOfEuclidean P v (LGP v)).vertexLink
            (linkQcast M
              (fun w => vertexStarOfEuclidean P w (LGP w))
              (fun w => vertexStarOfEuclidean Q w (LGQ w))
              (fun w => vertexLinkGeometry_n_eq P Q LGP LGQ w) v) i) := by
  rcases dihedralAngleAt_starDart_eq_linkAngle P v (LGP v) with ⟨hdegP, eP, hP⟩
  rcases dihedralAngleAt_starDart_eq_linkAngle Q v (LGQ v) with ⟨hdegQ, eQ, hQ⟩
  refine ⟨hdegP, eP, ?_⟩
  intro i
  let hnn := vertexLinkGeometry_n_eq P Q LGP LGQ v
  let hPQ : (LGP v).n = (LGQ v).n := by rw [hnn]
  have hidx :
      Fin.cast (congrArg Nat.succ eP) i =
        Fin.cast (congrArg Nat.succ eQ)
          (Fin.cast (congrArg Nat.succ hPQ) i) :=
    fin_cast_merge_starN_of_PQ eP eQ hPQ i
  have hPi := hP i
  let iQ : Fin ((LGQ v).n + 1) := Fin.cast (congrArg Nat.succ hPQ) i
  have hQi := hQ iQ
  have hstarQ :
      starDart P v hdegP (Fin.cast (congrArg Nat.succ eP) i) =
        starDart Q v hdegQ (Fin.cast (congrArg Nat.succ eQ) iQ) := by
    exact starDart_eq_of_index P Q v hdegP hdegQ (heq_of_eq hidx)
  unfold euclideanEdgeSign dihedralSignAtDart
  rw [hPi]
  rw [hstarQ, hQi]
  have hgeom :
      linkDiff (vertexStarOfEuclidean P v (LGP v)).vertexLink
          (linkQcast M
            (fun w => vertexStarOfEuclidean P w (LGP w))
            (fun w => vertexStarOfEuclidean Q w (LGQ w))
            (fun w => vertexLinkGeometry_n_eq P Q LGP LGQ w) v) i =
        linkAngle (vertexStarOfEuclidean Q v (LGQ v)).vertexLink iQ -
          linkAngle (vertexStarOfEuclidean P v (LGP v)).vertexLink i := by
    dsimp [linkDiff]
    unfold linkQcast
    dsimp [iQ, hPQ]
    exact congrArg
      (fun x => x - linkAngle (vertexStarOfEuclidean P v (LGP v)).vertexLink i)
      (linkAngle_reindex
        (by
          change (LGP v).n = (LGQ v).n
          exact hPQ)
        (vertexStarOfEuclidean Q v (LGQ v)).edgeDir i)
  rw [hgeom]

/-- There is a nonzero edge sign in the canonical `σ`-cycle of `v`. -/
def baseActiveExists (P Q : TriangulatedEuclideanPolyhedron M) (v : M.Vertex) : Prop :=
  ∃ x, M.σ.SameCycle (vertexDartRep (M := M) v) x ∧ euclideanEdgeSign P Q x ≠ EdgeSign.zero

noncomputable def adaptiveActiveDart
    (P Q : TriangulatedEuclideanPolyhedron M) (v : M.Vertex) : D :=
  if h : baseActiveExists P Q v then h.choose else vertexDartRep (M := M) v

noncomputable def adaptiveDartRep
    (P Q : TriangulatedEuclideanPolyhedron M) (v : M.Vertex) : D :=
  if h : baseActiveExists P Q v then M.σ (M.σ h.choose) else vertexDartRep (M := M) v

theorem tail_eq_of_sigma_sameCycle {a b : D} (h : M.σ.SameCycle a b) :
    M.tail b = M.tail a := by
  change Quotient.mk (cycleSetoid M.σ) b = Quotient.mk (cycleSetoid M.σ) a
  exact Quotient.sound h.symm

theorem adaptiveActiveDart_spec
    (P Q : TriangulatedEuclideanPolyhedron M) (v : M.Vertex)
    (h : baseActiveExists P Q v) :
    M.σ.SameCycle (vertexDartRep (M := M) v) (adaptiveActiveDart P Q v) ∧
      euclideanEdgeSign P Q (adaptiveActiveDart P Q v) ≠ EdgeSign.zero := by
  unfold adaptiveActiveDart
  simpa [h] using h.choose_spec

theorem adaptiveActiveDart_tail
    (P Q : TriangulatedEuclideanPolyhedron M) (v : M.Vertex) :
    M.tail (adaptiveActiveDart P Q v) = v := by
  by_cases h : baseActiveExists P Q v
  · have hs := (adaptiveActiveDart_spec P Q v h).1
    rw [tail_eq_of_sigma_sameCycle hs, vertexDartRep_tail]
  · simp [adaptiveActiveDart, h, vertexDartRep_tail]

theorem adaptiveDartRep_tail
    (P Q : TriangulatedEuclideanPolyhedron M) (v : M.Vertex) :
    M.tail (adaptiveDartRep P Q v) = v := by
  by_cases h : baseActiveExists P Q v
  · unfold adaptiveDartRep
    simp [h]
    have htail : M.tail h.choose = v := by
      have hs : M.σ.SameCycle (vertexDartRep (M := M) v) h.choose := h.choose_spec.1
      rw [tail_eq_of_sigma_sameCycle hs, vertexDartRep_tail]
    exact htail
  · simp [adaptiveDartRep, h, vertexDartRep_tail]

noncomputable def signDartHdeg
    (P Q : TriangulatedEuclideanPolyhedron M)
    (LGP : ∀ v : M.Vertex, VertexLinkGeometry P v)
    (LGQ : ∀ v : M.Vertex, VertexLinkGeometry Q v)
    (v : M.Vertex) : 3 ≤ vDeg P v :=
  (euclideanEdgeSign_starDart_eq_linkDiff P Q LGP LGQ v).choose

noncomputable def signDartE
    (P Q : TriangulatedEuclideanPolyhedron M)
    (LGP : ∀ v : M.Vertex, VertexLinkGeometry P v)
    (LGQ : ∀ v : M.Vertex, VertexLinkGeometry Q v)
    (v : M.Vertex) :
    (LGP v).n = starN P v :=
  ((euclideanEdgeSign_starDart_eq_linkDiff P Q LGP LGQ v).choose_spec).choose

theorem signDart_value
    (P Q : TriangulatedEuclideanPolyhedron M)
    (LGP : ∀ v : M.Vertex, VertexLinkGeometry P v)
    (LGQ : ∀ v : M.Vertex, VertexLinkGeometry Q v)
    (v : M.Vertex) :
    ∀ i : Fin ((LGP v).n + 1),
      euclideanEdgeSign P Q
          (starDart P v (signDartHdeg P Q LGP LGQ v)
            (Fin.cast (congrArg Nat.succ (signDartE P Q LGP LGQ v)) i))
        =
      realSignToEdgeSign
        (linkDiff (vertexStarOfEuclidean P v (LGP v)).vertexLink
          (linkQcast M
            (fun w => vertexStarOfEuclidean P w (LGP w))
            (fun w => vertexStarOfEuclidean Q w (LGQ w))
            (fun w => vertexLinkGeometry_n_eq P Q LGP LGQ w) v) i) :=
  ((euclideanEdgeSign_starDart_eq_linkDiff P Q LGP LGQ v).choose_spec).choose_spec

noncomputable def adaptiveOffset
    (P Q : TriangulatedEuclideanPolyhedron M)
    (LGP : ∀ v : M.Vertex, VertexLinkGeometry P v)
    (LGQ : ∀ v : M.Vertex, VertexLinkGeometry Q v)
    (v : M.Vertex) :
    Fin ((LGP v).n + 1) :=
  let hdeg := signDartHdeg P Q LGP LGQ v
  let e := signDartE P Q LGP LGQ v
  let x := adaptiveActiveDart P Q v
  let hx : x ∈ incidentDarts P v :=
    incidentDarts_mem_of_tail P hdeg (adaptiveActiveDart_tail P Q v)
  Fin.cast (congrArg Nat.succ e.symm)
    (reverseStarIndexOfDart P v hdeg x hx) - 1

theorem interiorActive_of_link_index_one {n : ℕ} (A B : Fin (n + 1) → S2)
    (hn : 2 ≤ n)
    (hneq :
      realSignToEdgeSign
        (linkDiff A B ⟨1, by omega⟩) ≠ EdgeSign.zero) :
    ∃ i : Fin (n - 1), jointAngle A i ≠ jointAngle B i := by
  let i : Fin (n - 1) := ⟨0, by omega⟩
  refine ⟨i, ?_⟩
  have hdiff : linkDiff A B ⟨1, by omega⟩ ≠ 0 := by
    intro h0
    exact hneq ((realSignToEdgeSign_eq_zero_iff _).2 h0)
  have hidx :
      (⟨1, by omega⟩ : Fin (n + 1)) =
        (⟨i.val + 1, by have := i.isLt; omega⟩ : Fin (n + 1)) := by
    ext
    simp [i]
  have hJD : jointDiff A B i ≠ 0 := by
    have h := hdiff
    rw [hidx, linkDiff_interior A B i] at h
    exact h
  unfold jointDiff at hJD
  intro heq
  apply hJD
  rw [heq]
  ring

/-- A concrete, non-circular two-arc cut for a full cyclic link-difference sequence.

The non-wrapping arc is the opening arc (`A ≤ B`, strictly somewhere), and the wrapping arc is the
closing arc (`B ≤ A`).  This is the honest residual needed by the abstract two-arc assembler. -/
structure TwoArcCut {n : ℕ} (d : Fin (n + 1) → ℝ) where
  tIdx : ℕ
  sIdx : ℕ
  hts : tIdx < sIdx
  hsn : sIdx ≤ n
  hm1 : 2 ≤ sIdx - tIdx
  hm2 : 2 ≤ wrapLen n sIdx tIdx
  nonwrap_nonneg :
    ∀ i : Fin (sIdx - tIdx - 1),
      0 ≤ d ⟨tIdx + i.val + 1, by have := i.isLt; omega⟩
  nonwrap_pos :
    ∃ i : Fin (sIdx - tIdx - 1),
      0 < d ⟨tIdx + i.val + 1, by have := i.isLt; omega⟩
  wrap_nonpos :
    ∀ i : Fin (wrapLen n sIdx tIdx - 1),
      d ((⟨i.val + 1, by
            have := i.isLt
            unfold wrapLen at this
            omega⟩ : Fin (n + 1)) + ⟨sIdx, by omega⟩) ≤ 0

lemma twoArcCut_mono1 {n : ℕ} (A B : Fin (n + 1) → S2)
    (cut : TwoArcCut (linkDiff A B)) :
    ∀ i : Fin (cut.sIdx - cut.tIdx - 1),
      jointAngle (subArc A cut.tIdx cut.sIdx cut.hts cut.hsn) i
        ≤ jointAngle (subArc B cut.tIdx cut.sIdx cut.hts cut.hsn) i := by
  intro i
  let j : Fin (n - 1) := ⟨cut.tIdx + i.val, by
    have hi := i.isLt
    have hsn := cut.hsn
    omega⟩
  have hidx :
      (⟨cut.tIdx + i.val + 1, by
        have hi := i.isLt
        have hsn := cut.hsn
        omega⟩ : Fin (n + 1))
        =
      (⟨j.val + 1, by have := j.isLt; omega⟩ : Fin (n + 1)) := by
    ext
    simp [j]
  have hld : 0 ≤ jointDiff A B j := by
    have h := cut.nonwrap_nonneg i
    rw [hidx, linkDiff_interior] at h
    exact h
  rw [subArc_jointAngle, subArc_jointAngle]
  unfold jointDiff at hld
  linarith

lemma twoArcCut_strict1 {n : ℕ} (A B : Fin (n + 1) → S2)
    (cut : TwoArcCut (linkDiff A B)) :
    ∃ i : Fin (cut.sIdx - cut.tIdx - 1),
      jointAngle (subArc A cut.tIdx cut.sIdx cut.hts cut.hsn) i
        < jointAngle (subArc B cut.tIdx cut.sIdx cut.hts cut.hsn) i := by
  obtain ⟨i, hi⟩ := cut.nonwrap_pos
  refine ⟨i, ?_⟩
  let j : Fin (n - 1) := ⟨cut.tIdx + i.val, by
    have hi' := i.isLt
    have hsn := cut.hsn
    omega⟩
  have hidx :
      (⟨cut.tIdx + i.val + 1, by
        have hi' := i.isLt
        have hsn := cut.hsn
        omega⟩ : Fin (n + 1))
        =
      (⟨j.val + 1, by have := j.isLt; omega⟩ : Fin (n + 1)) := by
    ext
    simp [j]
  have hld : 0 < jointDiff A B j := by
    rw [hidx, linkDiff_interior] at hi
    exact hi
  rw [subArc_jointAngle, subArc_jointAngle]
  unfold jointDiff at hld
  linarith

lemma linkDiff_wrap_joint {n : ℕ} (A B : Fin (n + 1) → S2)
    {t s : ℕ} (hts : t < s) (hsn : s ≤ n)
    (i : Fin (wrapLen n s t - 1)) :
    linkDiff A B
      ((⟨i.val + 1, by
          have := i.isLt
          unfold wrapLen at this
          omega⟩ : Fin (n + 1)) + ⟨s, by omega⟩)
      =
    jointAngle (subArcWrap B t s hts hsn) i
      -
    jointAngle (subArcWrap A t s hts hsn) i := by
  let k : Fin (n + 1) :=
    (⟨i.val + 1, by
      have := i.isLt
      unfold wrapLen at this
      omega⟩ : Fin (n + 1)) + ⟨s, by omega⟩
  have hkprev :
      k - 1 =
        (⟨i.val, by
          have := i.isLt
          unfold wrapLen at this
          omega⟩ : Fin (n + 1)) + ⟨s, by omega⟩ := by
    apply Fin.ext
    rw [Fin.sub_def, Fin.val_one', Nat.mod_eq_of_lt (show 1 < n + 1 by omega)]
    simp only [k]
    rw [Fin.val_add, Fin.val_add]
    simp only [Fin.val_mk]
    show (n + 1 - 1 + ((i.val + 1 + s) % (n + 1))) % (n + 1) =
      (i.val + s) % (n + 1)
    have hstep :
        (n + 1 - 1 + ((i.val + 1 + s) % (n + 1))) % (n + 1) =
          (n + 1 - 1 + (i.val + 1 + s)) % (n + 1) := by
      have h := (Nat.add_mod (n + 1 - 1) (i.val + 1 + s) (n + 1)).symm
      have h0 : (n + 1 - 1) % (n + 1) = n + 1 - 1 := by
        exact Nat.mod_eq_of_lt (show n + 1 - 1 < n + 1 by omega)
      simpa [h0] using h
    rw [hstep]
    have hsum : n + 1 - 1 + (i.val + 1 + s) = i.val + s + (n + 1) := by omega
    rw [hsum, Nat.add_mod_right]
  have hkcur :
      k =
        (⟨i.val + 1, by
          have := i.isLt
          unfold wrapLen at this
          omega⟩ : Fin (n + 1)) + ⟨s, by omega⟩ := rfl
  have hknext :
      k + 1 =
        (⟨i.val + 2, by
          have := i.isLt
          unfold wrapLen at this
          omega⟩ : Fin (n + 1)) + ⟨s, by omega⟩ := by
    apply Fin.ext
    simp only [k]
    rw [Fin.val_add, Fin.val_add, Fin.val_add]
    simp only [Fin.val_mk, Fin.val_one']
    rw [Nat.mod_eq_of_lt (show 1 < n + 1 by omega)]
    show (((i.val + 1 + s) % (n + 1) + 1) % (n + 1)) =
      (i.val + 2 + s) % (n + 1)
    have hstep :
        (((i.val + 1 + s) % (n + 1) + 1) % (n + 1)) =
          (i.val + 1 + s + 1) % (n + 1) := by
      have h := (Nat.add_mod (i.val + 1 + s) 1 (n + 1)).symm
      have h1 : 1 % (n + 1) = 1 := Nat.mod_eq_of_lt (show 1 < n + 1 by omega)
      simpa [h1, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using h
    rw [hstep]
    congr 1
    omega
  change linkDiff A B k =
    jointAngle (subArcWrap B t s hts hsn) i
      -
    jointAngle (subArcWrap A t s hts hsn) i
  unfold linkDiff
  rw [subArcWrap_jointAngle, subArcWrap_jointAngle]
  rw [rotPoly_jointAngle, rotPoly_jointAngle]
  unfold linkAngle
  rw [hkprev, hkcur, hknext]

/-- Original indices where a real cyclic sequence is nonzero. -/
noncomputable def nzIdx {m : ℕ} (d : Fin m → ℝ) : List (Fin m) :=
  (List.finRange m).filter (fun i => decide (d i ≠ 0))

/-- Original nonzero indices paired with their sign (`true` means positive). -/
noncomputable def nzSignedIdx {m : ℕ} (d : Fin m → ℝ) : List (Fin m × Bool) :=
  (nzIdx d).map (fun i => (i, decide (0 < d i)))

theorem nzSignedIdx_map_snd {m : ℕ} (d : Fin m → ℝ) :
    (nzSignedIdx d).map Prod.snd = nzSigns d := by
  simp [nzSignedIdx, nzIdx, nzSigns]

theorem mem_nzIdx {m : ℕ} (d : Fin m → ℝ) (i : Fin m) :
    i ∈ nzIdx d ↔ d i ≠ 0 := by
  simp [nzIdx]

private theorem finRange_pairwise_val (m : ℕ) :
    (List.finRange m).Pairwise (fun x y : Fin m => x.val < y.val) := by
  rw [List.pairwise_iff_get]
  intro i j hij
  rw [List.get_finRange, List.get_finRange]
  simp
  exact hij

private theorem nzIdx_pairwise_val {m : ℕ} (d : Fin m → ℝ) :
    (nzIdx d).Pairwise (fun x y : Fin m => x.val < y.val) := by
  exact (finRange_pairwise_val m).filter _

theorem mem_nzSignedIdx {m : ℕ} (d : Fin m → ℝ) (x : Fin m × Bool) :
    x ∈ nzSignedIdx d ↔ x.1 ∈ nzIdx d ∧ x.2 = decide (0 < d x.1) := by
  constructor
  · intro hx
    simp only [nzSignedIdx, List.mem_map] at hx
    rcases hx with ⟨i, hi, rfl⟩
    exact ⟨hi, rfl⟩
  · rintro ⟨hi, hsign⟩
    simp only [nzSignedIdx, List.mem_map]
    refine ⟨x.1, hi, ?_⟩
    ext <;> simp [hsign]

private def signOf {n : ℕ} (d : Fin (n + 1) → ℝ) (i : Fin (n + 1)) : Bool :=
  decide (0 < d i)

private def predVal {n : ℕ} (i : Fin (n + 1)) : ℕ :=
  if i.val = 0 then n else i.val - 1

private def succVal {n : ℕ} (i : Fin (n + 1)) : ℕ :=
  if i.val = n then 0 else i.val + 1

private def cval (N start x : ℕ) : ℕ :=
  if start ≤ x then x - start else N - start + x

private lemma cval_same_branch_lt
    {N start x y : ℕ} (hsx : start ≤ x) (hsy : start ≤ y) (hxy : x < y) :
    cval N start x < cval N start y := by
  unfold cval
  simp [hsx, hsy]
  omega

private lemma cval_wrap_branch_lt
    {N start x y : ℕ} (hsx : ¬ start ≤ x) (hsy : ¬ start ≤ y) (hxy : x < y) :
    cval N start x < cval N start y := by
  unfold cval
  simp [hsx, hsy]
  omega

private lemma cval_cross_branch_lt
    {N start x y : ℕ} (hstartN : start < N) (hxN : x < N) (hyN : y < N)
    (hsx : start ≤ x) (hsy : ¬ start ≤ y) :
    cval N start x < cval N start y := by
  unfold cval
  simp [hsx, hsy]
  omega

private lemma cval_lt_succ
    {n start x : ℕ} (hstart : start < n + 1) (hx : x < n + 1) :
    cval (n + 1) start x < n + 1 := by
  unfold cval
  split_ifs <;> omega

namespace ListCyclicOrder

variable {N : ℕ}

private lemma getElem_mem_drop
    {l : List (Fin N)} {j : ℕ} (hj : j < l.length) :
    l[j] ∈ l.drop j := by
  rw [List.drop_eq_getElem_cons hj]
  exact List.mem_cons_self

private lemma getElem_mem_take_succ
    {l : List (Fin N)} {j : ℕ} (hj : j < l.length) :
    l[j] ∈ l.take (j + 1) := by
  rw [← List.take_append_getElem hj]
  exact List.mem_append_right _ (by simp)

private lemma getElem_val_le_of_mem_drop
    {l : List (Fin N)}
    (hpair : l.Pairwise (fun a b : Fin N => a.val < b.val))
    {j : ℕ} (hj : j < l.length)
    {a : Fin N} (ha : a ∈ l.drop j) :
    l[j].val ≤ a.val := by
  have hdrop : l.drop j = l[j] :: l.drop (j + 1) :=
    List.drop_eq_getElem_cons hj
  rw [hdrop] at ha
  simp only [List.mem_cons] at ha
  rcases ha with ha | ha
  · subst a
    exact le_rfl
  · have hpivot : l[j] ∈ l.take (j + 1) :=
      getElem_mem_take_succ hj
    have hlt : l[j].val < a.val :=
      hpair.rel_of_mem_take_of_mem_drop hpivot ha
    exact le_of_lt hlt

private lemma val_lt_getElem_val_of_mem_take
    {l : List (Fin N)}
    (hpair : l.Pairwise (fun a b : Fin N => a.val < b.val))
    {j : ℕ} (hj : j < l.length)
    {a : Fin N} (ha : a ∈ l.take j) :
    a.val < l[j].val := by
  have hpivot : l[j] ∈ l.drop j :=
    getElem_mem_drop hj
  exact hpair.rel_of_mem_take_of_mem_drop ha hpivot

theorem pairwise_cval_drop_append_take
    {l : List (Fin N)}
    (hpair : l.Pairwise (fun a b : Fin N => a.val < b.val))
    {j : ℕ} (hj : j < l.length) :
    (l.drop j ++ l.take j).Pairwise
      (fun a b : Fin N =>
        cval N l[j].val a.val < cval N l[j].val b.val) := by
  rw [List.pairwise_append]
  constructor
  · refine (List.Pairwise.drop (i := j) hpair).imp_of_mem ?_
    intro a b ha hb hab
    have hsa : l[j].val ≤ a.val :=
      getElem_val_le_of_mem_drop hpair hj ha
    have hsb : l[j].val ≤ b.val :=
      getElem_val_le_of_mem_drop hpair hj hb
    unfold cval
    simp [hsa, hsb]
    omega
  constructor
  · refine (List.Pairwise.take (i := j) hpair).imp_of_mem ?_
    intro a b ha hb hab
    have has : a.val < l[j].val :=
      val_lt_getElem_val_of_mem_take hpair hj ha
    have hbs : b.val < l[j].val :=
      val_lt_getElem_val_of_mem_take hpair hj hb
    have hna : ¬ l[j].val ≤ a.val := by omega
    have hnb : ¬ l[j].val ≤ b.val := by omega
    unfold cval
    simp [hna, hnb]
    omega
  · intro a ha b hb
    have hsa : l[j].val ≤ a.val :=
      getElem_val_le_of_mem_drop hpair hj ha
    have hbs : b.val < l[j].val :=
      val_lt_getElem_val_of_mem_take hpair hj hb
    have hnb : ¬ l[j].val ≤ b.val := by omega
    unfold cval
    simp [hsa, hnb]
    omega

private lemma head_drop_append_take_eq_getElem
    {l : List (Fin N)}
    {j : ℕ} (hj : j < l.length)
    (hne : l.drop j ++ l.take j ≠ []) :
    (l.drop j ++ l.take j).head hne = l[j] := by
  rw [List.head_eq_getElem hne]
  have hdropLen : 0 < (l.drop j).length := by
    rw [List.length_drop]
    omega
  calc
    (l.drop j ++ l.take j)[0]'(by
        rw [List.length_append]
        omega) = (l.drop j)[0]'hdropLen :=
      List.getElem_append_left (as := l.drop j) (bs := l.take j) (i := 0) hdropLen
    _ = l[j + 0]'(by omega) := List.getElem_drop
    _ = l[j] := by simp

theorem pairwise_cval_drop_append_take_head
    {l : List (Fin N)}
    (hpair : l.Pairwise (fun a b : Fin N => a.val < b.val))
    {j : ℕ} (hj : j < l.length)
    (hne : l.drop j ++ l.take j ≠ []) :
    (l.drop j ++ l.take j).Pairwise
      (fun a b : Fin N =>
        cval N ((l.drop j ++ l.take j).head hne).val a.val
          <
        cval N ((l.drop j ++ l.take j).head hne).val b.val) := by
  have hhead :
      (l.drop j ++ l.take j).head hne = l[j] :=
    head_drop_append_take_eq_getElem hj hne
  simpa [hhead] using
    pairwise_cval_drop_append_take (N := N) (l := l) hpair hj

theorem pairwise_cval_of_eq_drop_append_take
    {l r : List (Fin N)}
    (hpair : l.Pairwise (fun a b : Fin N => a.val < b.val))
    {j : ℕ} (hj : j < l.length)
    (hrot : r = l.drop j ++ l.take j)
    (hne : r ≠ []) :
    r.Pairwise
      (fun a b : Fin N =>
        cval N (r.head hne).val a.val
          <
        cval N (r.head hne).val b.val) := by
  subst r
  exact pairwise_cval_drop_append_take_head (N := N) (l := l) hpair hj hne

end ListCyclicOrder

theorem nzIdx_rotate_pairwise_cval_of_rotate_eq
    {n : ℕ} (d : Fin (n + 1) → ℝ)
    (k j : ℕ)
    (hj : j < (nzIdx d).length)
    (hrot :
      (nzIdx d).rotate k =
        (nzIdx d).drop j ++ (nzIdx d).take j)
    (hne : (nzIdx d).rotate k ≠ []) :
    ((nzIdx d).rotate k).Pairwise
      (fun a b : Fin (n + 1) =>
        cval (n + 1) (((nzIdx d).rotate k).head hne).val a.val
          <
        cval (n + 1) (((nzIdx d).rotate k).head hne).val b.val) := by
  exact
    ListCyclicOrder.pairwise_cval_of_eq_drop_append_take
      (N := n + 1)
      (l := nzIdx d)
      (r := (nzIdx d).rotate k)
      (hpair := nzIdx_pairwise_val d)
      (j := j)
      hj
      hrot
      hne

theorem nzIdx_rotate_pairwise_cval
    {n : ℕ} (d : Fin (n + 1) → ℝ)
    (k : ℕ)
    (hne : (nzIdx d).rotate k ≠ []) :
    ((nzIdx d).rotate k).Pairwise
      (fun a b : Fin (n + 1) =>
        cval (n + 1) (((nzIdx d).rotate k).head hne).val a.val
          <
        cval (n + 1) (((nzIdx d).rotate k).head hne).val b.val) := by
  classical
  let l : List (Fin (n + 1)) := nzIdx d
  have hlen_pos : 0 < l.length := by
    by_contra h
    have hlen0 : l.length = 0 := by omega
    have hl : l = [] := List.eq_nil_of_length_eq_zero hlen0
    apply hne
    simp [l] at hl
    simp [hl]
  let j : ℕ := k % l.length
  have hj : j < l.length := Nat.mod_lt k hlen_pos
  have hrot :
      (nzIdx d).rotate k =
        (nzIdx d).drop j ++ (nzIdx d).take j := by
    simpa [l, j] using (List.rotate_eq_drop_append_take_mod (l := nzIdx d) (n := k))
  exact nzIdx_rotate_pairwise_cval_of_rotate_eq (d := d) k j
    (by simpa [l] using hj) hrot hne

theorem nzIdx_rotate_pairwise_cval_get_zero
    {n : ℕ} (d : Fin (n + 1) → ℝ)
    (k : ℕ)
    (hlen : 0 < ((nzIdx d).rotate k).length) :
    ((nzIdx d).rotate k).Pairwise
      (fun a b : Fin (n + 1) =>
        cval (n + 1)
            (((nzIdx d).rotate k).get ⟨0, hlen⟩).val
            a.val
          <
        cval (n + 1)
            (((nzIdx d).rotate k).get ⟨0, hlen⟩).val
            b.val) := by
  classical
  have hne : (nzIdx d).rotate k ≠ [] := List.ne_nil_of_length_pos hlen
  have hhead :
      (((nzIdx d).rotate k).head hne)
        =
      ((nzIdx d).rotate k).get ⟨0, hlen⟩ := by
    rw [List.head_eq_getElem hne]
    simp [List.get_eq_getElem]
  simpa [hhead] using nzIdx_rotate_pairwise_cval (d := d) k hne

private def cdist (N l r : ℕ) : ℕ :=
  if l ≤ r then r - l else N - l + r

private def cycOpen (N l r x : ℕ) : Prop :=
  if h : l < r then
    l < x ∧ x < r
  else
    r < l ∧ (l < x ∨ x < r)

private lemma cycOpen_pred_self_last_of_cval
    {n : ℕ} (first last : Fin (n + 1))
    (hpos : 0 < cval (n + 1) first.val last.val)
    (hlt : cval (n + 1) first.val last.val < n) :
    cycOpen (n + 1) (predVal first) last.val first.val := by
  have hfirst : first.val < n + 1 := first.isLt
  have hlast : last.val < n + 1 := last.isLt
  unfold cycOpen predVal
  unfold cval at hpos hlt
  split_ifs at hpos hlt ⊢ <;> omega

private lemma cycOpen_last_pred_of_cval
    {n : ℕ} (first last x : Fin (n + 1))
    (hlo : cval (n + 1) first.val last.val < cval (n + 1) first.val x.val)
    (hxp : cval (n + 1) first.val x.val < n) :
    cycOpen (n + 1) last.val (predVal first) x.val := by
  have hfirst : first.val < n + 1 := first.isLt
  have hlast : last.val < n + 1 := last.isLt
  have hx : x.val < n + 1 := x.isLt
  unfold cycOpen predVal
  unfold cval at hlo hxp
  split_ifs at hlo hxp ⊢ <;> omega

private lemma predVal_le {n : ℕ} (i : Fin (n + 1)) :
    predVal i ≤ n := by
  unfold predVal
  split_ifs <;> omega

private lemma succVal_le {n : ℕ} (i : Fin (n + 1)) :
    succVal i ≤ n := by
  unfold succVal
  split_ifs <;> omega

private lemma cdist_of_lt {N l r : ℕ} (h : l < r) :
    cdist N l r = r - l := by
  unfold cdist
  simp [le_of_lt h]

private lemma cdist_of_gt {N l r : ℕ} (h : r < l) :
    cdist N l r = N - l + r := by
  unfold cdist
  have hle : ¬ l ≤ r := by omega
  simp [hle]

private lemma two_le_cdist_of_cycOpen
    {N l r x : ℕ} (hxN : x < N) (hlN : l < N) (hrN : r < N)
    (h : cycOpen N l r x) :
    2 ≤ cdist N l r := by
  unfold cycOpen at h
  unfold cdist
  by_cases hlr : l < r
  · simp [hlr, le_of_lt hlr] at h ⊢
    omega
  · simp [hlr] at h
    have hrl : r < l := h.1
    have hnle : ¬ l ≤ r := by omega
    simp [hnle]
    rcases h.2 with hx | hx <;> omega

private lemma pred_succ_singleton_lengths
    {n : ℕ} (hn : 3 ≤ n) (x : Fin (n + 1)) :
    cdist (n + 1) (predVal x) (succVal x) = 2 ∧
    cdist (n + 1) (succVal x) (predVal x) = n - 1 := by
  unfold predVal succVal cdist
  have hx : x.val ≤ n := by omega
  split_ifs with h0 hnlast hle₁ hle₂ hle₃ hle₄ <;> omega

private lemma singleton_forward_arc_eq
    {n : ℕ} (hn : 3 ≤ n) (x : Fin (n + 1))
    {y : Fin (n + 1)}
    (hy : cycOpen (n + 1) (predVal x) (succVal x) y.val) :
    y = x := by
  apply Fin.ext
  unfold cycOpen predVal succVal at hy
  split_ifs at hy <;> omega

private lemma singleton_reverse_arc_ne
    {n : ℕ} (hn : 3 ≤ n) (x : Fin (n + 1))
    {y : Fin (n + 1)}
    (hy : cycOpen (n + 1) (succVal x) (predVal x) y.val) :
    y ≠ x := by
  intro h
  subst h
  unfold cycOpen predVal succVal at hy
  split_ifs at hy <;> omega

private lemma pos_of_sign_true
    {n : ℕ} {d : Fin (n + 1) → ℝ} {i : Fin (n + 1)}
    (h : signOf d i = true) :
    0 < d i := by
  simpa [signOf] using h

private lemma neg_of_sign_false
    {n : ℕ} {d : Fin (n + 1) → ℝ} {i : Fin (n + 1)}
    (h0 : d i ≠ 0) (h : signOf d i = false) :
    d i < 0 := by
  have hnpos : ¬ 0 < d i := by
    simpa [signOf] using h
  have hle : d i ≤ 0 := le_of_not_gt hnpos
  exact lt_of_le_of_ne hle h0

private def nonwrapIdx
    {n t s : ℕ} (hsn : s ≤ n)
    (i : Fin (s - t - 1)) : Fin (n + 1) :=
  ⟨t + i.val + 1, by
    have hi := i.isLt
    omega⟩

private def wrapIdx
    {n t s : ℕ} (hts : t < s) (hsn : s ≤ n)
    (i : Fin (wrapLen n s t - 1)) : Fin (n + 1) :=
  ((⟨i.val + 1, by
      have hi := i.isLt
      unfold wrapLen at hi
      omega⟩ : Fin (n + 1)) + ⟨s, by omega⟩)

private lemma nonwrapIdx_zero_eq_pred
    {n r : ℕ} (first : Fin (n + 1)) (hr : r ≤ n)
    (hlt : predVal first < r)
    (h0 : 0 < r - predVal first - 1) :
    nonwrapIdx (n := n) (t := predVal first) (s := r) hr
        ⟨0, h0⟩ = first := by
  apply Fin.ext
  unfold nonwrapIdx
  by_cases hz : first.val = 0
  · have hpred : predVal first = n := by simp [predVal, hz]
    have hbad : False := by
      have hlt' : n < r := by simpa [hpred] using hlt
      omega
    exact False.elim hbad
  · have hpred : predVal first = first.val - 1 := by simp [predVal, hz]
    simp [hpred]
    omega

private lemma wrapIdx_zero_eq_pred
    {n r : ℕ} (first : Fin (n + 1)) (hrlt : r < predVal first)
    (hl : predVal first ≤ n)
    (h0 : 0 < wrapLen n (predVal first) r - 1) :
    wrapIdx (n := n) (t := r) (s := predVal first) hrlt hl
        ⟨0, h0⟩ = first := by
  apply Fin.ext
  unfold wrapIdx
  simp [Fin.val_add]
  by_cases hz : first.val = 0
  · have hpred : predVal first = n := by simp [predVal, hz]
    simp [hpred, hz, show 1 + n = n + 1 by omega, Nat.mod_self]
  · have hpred : predVal first = first.val - 1 := by simp [predVal, hz]
    have hsum : 1 + (first.val - 1) = first.val := by omega
    have hmod : (1 + (first.val - 1)) % (n + 1) = first.val := by
      rw [hsum, Nat.mod_eq_of_lt first.isLt]
    simp [hpred, hmod]

private lemma nonwrapIdx_mem_cycOpen
    {n t s : ℕ} (hts : t < s) (hsn : s ≤ n)
    (i : Fin (s - t - 1)) :
    cycOpen (n + 1) t s (nonwrapIdx hsn i).val := by
  unfold nonwrapIdx cycOpen
  simp [hts]
  have hi := i.isLt
  omega

private lemma wrapIdx_mem_cycOpen
    {n t s : ℕ} (hts : t < s) (hsn : s ≤ n)
    (i : Fin (wrapLen n s t - 1)) :
    cycOpen (n + 1) s t (wrapIdx hts hsn i).val := by
  unfold wrapIdx cycOpen wrapLen
  have hi := i.isLt
  have hi' : i.val + 1 + s < n + 1 + t := by
    unfold wrapLen at hi
    omega
  simp [Fin.val_add]
  have hmod :
      ((i.val + 1) + s) % (n + 1) =
        if (i.val + 1) + s < n + 1
        then (i.val + 1) + s
        else (i.val + 1) + s - (n + 1) := by
    by_cases h : (i.val + 1) + s < n + 1
    · simp [h, Nat.mod_eq_of_lt h]
    · have hge : n + 1 ≤ (i.val + 1) + s := by omega
      have hsublt : (i.val + 1 + s) - (n + 1) < n + 1 := by
        omega
      rw [Nat.mod_eq_sub_mod hge]
      rw [Nat.mod_eq_of_lt]
      · simp [h]
      · exact hsublt
  rw [hmod]
  have hsnot : ¬ s < t := by omega
  by_cases hsmall : (i.val + 1) + s < n + 1
  · simp [hsmall, hsnot, hts]
  · simp [hsmall, hsnot, hts]
    omega

private lemma wrapLen_eq_cdist_of_lt
    {n t s : ℕ} (hts : t < s) (_hsn : s ≤ n) :
    wrapLen n s t = cdist (n + 1) s t := by
  unfold wrapLen cdist
  have hnle : ¬ s ≤ t := by omega
  simp [hnle]

lemma twoArcCut_mono2 {n : ℕ} (A B : Fin (n + 1) → S2)
    (cut : TwoArcCut (linkDiff A B)) :
    ∀ i : Fin (wrapLen n cut.sIdx cut.tIdx - 1),
      jointAngle (subArcWrap B cut.tIdx cut.sIdx cut.hts cut.hsn) i
        ≤ jointAngle (subArcWrap A cut.tIdx cut.sIdx cut.hts cut.hsn) i := by
  intro i
  have h := cut.wrap_nonpos i
  rw [linkDiff_wrap_joint A B cut.hts cut.hsn i] at h
  linarith

/-- Mirror orientation for a concrete two-arc cut: the wrapping arc is the opening arc
(`A ≤ B`, strictly somewhere), and the non-wrapping arc is the closing arc (`B ≤ A`). -/
structure TwoArcCutWrapOpens {n : ℕ} (d : Fin (n + 1) → ℝ) where
  tIdx : ℕ
  sIdx : ℕ
  hts : tIdx < sIdx
  hsn : sIdx ≤ n
  hm1 : 2 ≤ sIdx - tIdx
  hm2 : 2 ≤ wrapLen n sIdx tIdx
  nonwrap_nonpos :
    ∀ i : Fin (sIdx - tIdx - 1),
      d ⟨tIdx + i.val + 1, by have := i.isLt; omega⟩ ≤ 0
  wrap_nonneg :
    ∀ i : Fin (wrapLen n sIdx tIdx - 1),
      0 ≤ d ((⟨i.val + 1, by
            have := i.isLt
            unfold wrapLen at this
            omega⟩ : Fin (n + 1)) + ⟨sIdx, by omega⟩)
  wrap_pos :
    ∃ i : Fin (wrapLen n sIdx tIdx - 1),
      0 < d ((⟨i.val + 1, by
            have := i.isLt
            unfold wrapLen at this
            omega⟩ : Fin (n + 1)) + ⟨sIdx, by omega⟩)

lemma twoArcCutWrap_mono1 {n : ℕ} (A B : Fin (n + 1) → S2)
    (cut : TwoArcCutWrapOpens (linkDiff A B)) :
    ∀ i : Fin (wrapLen n cut.sIdx cut.tIdx - 1),
      jointAngle (subArcWrap A cut.tIdx cut.sIdx cut.hts cut.hsn) i
        ≤ jointAngle (subArcWrap B cut.tIdx cut.sIdx cut.hts cut.hsn) i := by
  intro i
  have h := cut.wrap_nonneg i
  rw [linkDiff_wrap_joint A B cut.hts cut.hsn i] at h
  linarith

lemma twoArcCutWrap_strict1 {n : ℕ} (A B : Fin (n + 1) → S2)
    (cut : TwoArcCutWrapOpens (linkDiff A B)) :
    ∃ i : Fin (wrapLen n cut.sIdx cut.tIdx - 1),
      jointAngle (subArcWrap A cut.tIdx cut.sIdx cut.hts cut.hsn) i
        < jointAngle (subArcWrap B cut.tIdx cut.sIdx cut.hts cut.hsn) i := by
  obtain ⟨i, hi⟩ := cut.wrap_pos
  refine ⟨i, ?_⟩
  rw [linkDiff_wrap_joint A B cut.hts cut.hsn i] at hi
  linarith

lemma twoArcCutWrap_mono2 {n : ℕ} (A B : Fin (n + 1) → S2)
    (cut : TwoArcCutWrapOpens (linkDiff A B)) :
    ∀ i : Fin (cut.sIdx - cut.tIdx - 1),
      jointAngle (subArc B cut.tIdx cut.sIdx cut.hts cut.hsn) i
        ≤ jointAngle (subArc A cut.tIdx cut.sIdx cut.hts cut.hsn) i := by
  intro i
  let j : Fin (n - 1) := ⟨cut.tIdx + i.val, by
    have hi := i.isLt
    have hsn := cut.hsn
    omega⟩
  have hidx :
      (⟨cut.tIdx + i.val + 1, by
        have hi := i.isLt
        have hsn := cut.hsn
        omega⟩ : Fin (n + 1))
        =
      (⟨j.val + 1, by have := j.isLt; omega⟩ : Fin (n + 1)) := by
    ext
    simp [j]
  have hld : jointDiff A B j ≤ 0 := by
    have h := cut.nonwrap_nonpos i
    rw [hidx, linkDiff_interior] at h
    exact h
  rw [subArc_jointAngle, subArc_jointAngle]
  unfold jointDiff at hld
  linarith

/-- Mirror assembler for the case where the wrapped arc is the opening arc. -/
noncomputable def twoArcSplitData_of_indices_wrapOpens {n : ℕ} (hn : 1 ≤ n)
    (A B : Fin (n + 1) → S2)
    (hA : StrictConvexSphArm A) (hB : StrictConvexSphArm B)
    (hsides : ∀ i : Fin n, sideLen A i = sideLen B i)
    (hclose : sDist (A 0) (A (Fin.last n)) = sDist (B 0) (B (Fin.last n)))
    (t s : ℕ) (hts : t < s) (hsn : s ≤ n)
    (hm1 : 2 ≤ s - t) (hm2 : 2 ≤ wrapLen n s t)
    -- the wrap arc opens (`A ≤ B` joints), strictly somewhere; the non-wrap arc closes (`B ≤ A`).
    (hmono1 : ∀ i : Fin (wrapLen n s t - 1),
        jointAngle (subArcWrap A t s hts hsn) i ≤ jointAngle (subArcWrap B t s hts hsn) i)
    (hstrict1 : ∃ i : Fin (wrapLen n s t - 1),
        jointAngle (subArcWrap A t s hts hsn) i < jointAngle (subArcWrap B t s hts hsn) i)
    (hmono2 : ∀ i : Fin (s - t - 1),
        jointAngle (subArc B t s hts hsn) i ≤ jointAngle (subArc A t s hts hsn) i) :
    TwoArcSplitData A B where
  m₁ := wrapLen n s t
  m₂ := s - t
  hm₁ := hm2
  hm₂ := hm1
  Arc1 := subArcWrap A t s hts hsn
  Brc1 := subArcWrap B t s hts hsn
  Arc2 := subArc A t s hts hsn
  Brc2 := subArc B t s hts hsn
  harc1A := subArcWrap_strictConvexArm A hA t s hts hsn hm2
  harc1B := subArcWrap_strictConvexArm B hB t s hts hsn hm2
  harc2A := subArc_strictConvexArm A hA t s hts hsn hm1
  harc2B := subArc_strictConvexArm B hB t s hts hsn hm1
  hsides1 := by
    intro i
    rw [subArcWrap_sideLen, subArcWrap_sideLen]
    exact rotPoly_sideLen_eq hn A B hsides hclose ⟨s, by omega⟩ ⟨i.val, by
      have := i.isLt; unfold wrapLen at this; omega⟩
  hsides2 := by
    intro i
    rw [subArc_sideLen, subArc_sideLen]
    exact hsides ⟨t + i.val, by have := i.isLt; omega⟩
  hshareA := by
    rw [subArcWrap_endpt, subArc_endpt]
  hshareB := by
    rw [subArcWrap_endpt, subArc_endpt]
  hmono1 := hmono1
  hstrict1 := hstrict1
  hmono2 := hmono2

noncomputable def twoArcSplitData_of_wrapCut {n : ℕ} (hn : 1 ≤ n)
    (A B : Fin (n + 1) → S2)
    (hA : StrictConvexSphArm A) (hB : StrictConvexSphArm B)
    (hsides : ∀ i : Fin n, sideLen A i = sideLen B i)
    (hclose : sDist (A 0) (A (Fin.last n)) = sDist (B 0) (B (Fin.last n)))
    (cut : TwoArcCutWrapOpens (linkDiff A B)) :
    TwoArcSplitData A B :=
  twoArcSplitData_of_indices_wrapOpens hn A B hA hB hsides hclose
    cut.tIdx cut.sIdx cut.hts cut.hsn cut.hm1 cut.hm2
    (twoArcCutWrap_mono1 A B cut)
    (twoArcCutWrap_strict1 A B cut)
    (twoArcCutWrap_mono2 A B cut)

/-- The ambient parameters of `TwoArcSplitData` are only bookkeeping; the data fields themselves
carry the four actual sub-arms. -/
noncomputable def twoArcSplitData_reparam {n : ℕ}
    {A B A' B' : Fin (n + 1) → S2} (D : TwoArcSplitData A B) :
    TwoArcSplitData A' B' where
  m₁ := D.m₁
  m₂ := D.m₂
  hm₁ := D.hm₁
  hm₂ := D.hm₂
  Arc1 := D.Arc1
  Brc1 := D.Brc1
  Arc2 := D.Arc2
  Brc2 := D.Brc2
  harc1A := D.harc1A
  harc1B := D.harc1B
  harc2A := D.harc2A
  harc2B := D.harc2B
  hsides1 := D.hsides1
  hsides2 := D.hsides2
  hshareA := D.hshareA
  hshareB := D.hshareB
  hmono1 := D.hmono1
  hstrict1 := D.hstrict1
  hmono2 := D.hmono2

theorem linkDiff_swap {n : ℕ} (A B : Fin (n + 1) → S2) (i : Fin (n + 1)) :
    linkDiff B A i = - linkDiff A B i := by
  unfold linkDiff
  ring

/-- Orientation-complete sign-definite cut: the non-wrapping arc is nonnegative, the wrapping arc is
nonpositive, and the strict witness may lie on either arc. -/
structure TwoArcCutPlusMinus {n : ℕ} (d : Fin (n + 1) → ℝ) where
  tIdx : ℕ
  sIdx : ℕ
  hts : tIdx < sIdx
  hsn : sIdx ≤ n
  hm1 : 2 ≤ sIdx - tIdx
  hm2 : 2 ≤ wrapLen n sIdx tIdx
  nonwrap_nonneg :
    ∀ i : Fin (sIdx - tIdx - 1),
      0 ≤ d ⟨tIdx + i.val + 1, by have := i.isLt; omega⟩
  wrap_nonpos :
    ∀ i : Fin (wrapLen n sIdx tIdx - 1),
      d ((⟨i.val + 1, by
            have := i.isLt
            unfold wrapLen at this
            omega⟩ : Fin (n + 1)) + ⟨sIdx, by omega⟩) ≤ 0
  strictOnNonwrap : Bool
  strict_nonwrap :
    strictOnNonwrap = true →
      ∃ i : Fin (sIdx - tIdx - 1),
        0 < d ⟨tIdx + i.val + 1, by have := i.isLt; omega⟩
  strict_wrap :
    strictOnNonwrap = false →
      ∃ i : Fin (wrapLen n sIdx tIdx - 1),
        d ((⟨i.val + 1, by
              have := i.isLt
              unfold wrapLen at this
              omega⟩ : Fin (n + 1)) + ⟨sIdx, by omega⟩) < 0

noncomputable def twoArcSplitData_of_plusMinusCut {n : ℕ} (hn : 1 ≤ n)
    (A B : Fin (n + 1) → S2)
    (hA : StrictConvexSphArm A) (hB : StrictConvexSphArm B)
    (hsides : ∀ i : Fin n, sideLen A i = sideLen B i)
    (hclose : sDist (A 0) (A (Fin.last n)) = sDist (B 0) (B (Fin.last n)))
    (cut : TwoArcCutPlusMinus (linkDiff A B)) :
    TwoArcSplitData A B := by
  cases hstrict : cut.strictOnNonwrap
  · have hneg := cut.strict_wrap hstrict
    refine twoArcSplitData_reparam
      (twoArcSplitData_of_wrapCut hn B A hB hA (fun i => (hsides i).symm) hclose.symm ?_)
    exact
      { tIdx := cut.tIdx
        sIdx := cut.sIdx
        hts := cut.hts
        hsn := cut.hsn
        hm1 := cut.hm1
        hm2 := cut.hm2
        nonwrap_nonpos := by
          intro i
          rw [linkDiff_swap]
          have h := cut.nonwrap_nonneg i
          linarith
        wrap_nonneg := by
          intro i
          rw [linkDiff_swap]
          have h := cut.wrap_nonpos i
          linarith
        wrap_pos := by
          rcases hneg with ⟨i, hi⟩
          refine ⟨i, ?_⟩
          rw [linkDiff_swap]
          linarith }
  · have hpos := cut.strict_nonwrap hstrict
    exact twoArcSplitData_of_indices hn A B hA hB hsides hclose
      cut.tIdx cut.sIdx cut.hts cut.hsn cut.hm1 cut.hm2
      (twoArcCut_mono1 A B
        { tIdx := cut.tIdx
          sIdx := cut.sIdx
          hts := cut.hts
          hsn := cut.hsn
          hm1 := cut.hm1
          hm2 := cut.hm2
          nonwrap_nonneg := cut.nonwrap_nonneg
          nonwrap_pos := hpos
          wrap_nonpos := cut.wrap_nonpos })
      (twoArcCut_strict1 A B
        { tIdx := cut.tIdx
          sIdx := cut.sIdx
          hts := cut.hts
          hsn := cut.hsn
          hm1 := cut.hm1
          hm2 := cut.hm2
          nonwrap_nonneg := cut.nonwrap_nonneg
          nonwrap_pos := hpos
          wrap_nonpos := cut.wrap_nonpos })
      (twoArcCut_mono2 A B
        { tIdx := cut.tIdx
          sIdx := cut.sIdx
          hts := cut.hts
          hsn := cut.hsn
          hm1 := cut.hm1
          hm2 := cut.hm2
          nonwrap_nonneg := cut.nonwrap_nonneg
          nonwrap_pos := hpos
          wrap_nonpos := cut.wrap_nonpos })

/-- Mirror sign-definite cut: the non-wrapping arc is nonpositive and the wrapping arc is
nonnegative, and the strict witness may lie on either arc. -/
structure TwoArcCutMinusPlus {n : ℕ} (d : Fin (n + 1) → ℝ) where
  tIdx : ℕ
  sIdx : ℕ
  hts : tIdx < sIdx
  hsn : sIdx ≤ n
  hm1 : 2 ≤ sIdx - tIdx
  hm2 : 2 ≤ wrapLen n sIdx tIdx
  nonwrap_nonpos :
    ∀ i : Fin (sIdx - tIdx - 1),
      d ⟨tIdx + i.val + 1, by have := i.isLt; omega⟩ ≤ 0
  wrap_nonneg :
    ∀ i : Fin (wrapLen n sIdx tIdx - 1),
      0 ≤ d ((⟨i.val + 1, by
            have := i.isLt
            unfold wrapLen at this
            omega⟩ : Fin (n + 1)) + ⟨sIdx, by omega⟩)
  strictOnWrap : Bool
  strict_nonwrap :
    strictOnWrap = false →
      ∃ i : Fin (sIdx - tIdx - 1),
        d ⟨tIdx + i.val + 1, by have := i.isLt; omega⟩ < 0
  strict_wrap :
    strictOnWrap = true →
      ∃ i : Fin (wrapLen n sIdx tIdx - 1),
        0 < d ((⟨i.val + 1, by
              have := i.isLt
              unfold wrapLen at this
              omega⟩ : Fin (n + 1)) + ⟨sIdx, by omega⟩)

noncomputable def twoArcSplitData_of_minusPlusCut {n : ℕ} (hn : 1 ≤ n)
    (A B : Fin (n + 1) → S2)
    (hA : StrictConvexSphArm A) (hB : StrictConvexSphArm B)
    (hsides : ∀ i : Fin n, sideLen A i = sideLen B i)
    (hclose : sDist (A 0) (A (Fin.last n)) = sDist (B 0) (B (Fin.last n)))
    (cut : TwoArcCutMinusPlus (linkDiff A B)) :
    TwoArcSplitData A B := by
  cases hstrict : cut.strictOnWrap
  · have hneg := cut.strict_nonwrap hstrict
    refine twoArcSplitData_reparam
      (twoArcSplitData_of_plusMinusCut hn B A hB hA (fun i => (hsides i).symm) hclose.symm ?_)
    exact
      { tIdx := cut.tIdx
        sIdx := cut.sIdx
        hts := cut.hts
        hsn := cut.hsn
        hm1 := cut.hm1
        hm2 := cut.hm2
        nonwrap_nonneg := by
          intro i
          rw [linkDiff_swap]
          have h := cut.nonwrap_nonpos i
          linarith
        wrap_nonpos := by
          intro i
          rw [linkDiff_swap]
          have h := cut.wrap_nonneg i
          linarith
        strictOnNonwrap := true
        strict_nonwrap := by
          intro _
          rcases hneg with ⟨i, hi⟩
          refine ⟨i, ?_⟩
          rw [linkDiff_swap]
          linarith
        strict_wrap := by
          intro hfalse
          simp at hfalse }
  · have hpos := cut.strict_wrap hstrict
    exact twoArcSplitData_of_wrapCut hn A B hA hB hsides hclose
      { tIdx := cut.tIdx
        sIdx := cut.sIdx
        hts := cut.hts
        hsn := cut.hsn
        hm1 := cut.hm1
        hm2 := cut.hm2
        nonwrap_nonpos := cut.nonwrap_nonpos
        wrap_nonneg := cut.wrap_nonneg
        wrap_pos := hpos }

/-- Orientation-complete cut, as data rather than a `Prop` disjunction, so it can dispatch to
`TwoArcSplitData`. -/
inductive OrientedTwoArcCut {n : ℕ} (d : Fin (n + 1) → ℝ) where
  | plusMinus (cut : TwoArcCutPlusMinus d)
  | minusPlus (cut : TwoArcCutMinusPlus d)

noncomputable def twoArcSplitData_of_orientedCut {n : ℕ} (hn : 1 ≤ n)
    (A B : Fin (n + 1) → S2)
    (hA : StrictConvexSphArm A) (hB : StrictConvexSphArm B)
    (hsides : ∀ i : Fin n, sideLen A i = sideLen B i)
    (hclose : sDist (A 0) (A (Fin.last n)) = sDist (B 0) (B (Fin.last n)))
    (cut : OrientedTwoArcCut (linkDiff A B)) :
    TwoArcSplitData A B := by
  cases cut with
  | plusMinus cut => exact twoArcSplitData_of_plusMinusCut hn A B hA hB hsides hclose cut
  | minusPlus cut => exact twoArcSplitData_of_minusPlusCut hn A B hA hB hsides hclose cut

/-- At a triangular link (`n = 2`) the two nondegenerate complementary sub-arms required by
`TwoArcCut` cannot both exist. -/
theorem no_twoArcCut_triangle (d : Fin (2 + 1) → ℝ) : TwoArcCut d → False := by
  intro cut
  have hm1 := cut.hm1
  have hm2 := cut.hm2
  have hts := cut.hts
  have hsn := cut.hsn
  unfold wrapLen at hm2
  omega

/-- At a triangular link (`n = 2`) the mirrored two nondegenerate complementary sub-arms also cannot
both exist. -/
theorem no_twoArcCutWrapOpens_triangle (d : Fin (2 + 1) → ℝ) :
    TwoArcCutWrapOpens d → False := by
  intro cut
  have hm1 := cut.hm1
  have hm2 := cut.hm2
  have hts := cut.hts
  have hsn := cut.hsn
  unfold wrapLen at hm2
  omega

theorem triangle_linkAngle_eq_of_sides
    (A B : Fin (2 + 1) → S2)
    (hA : StrictConvexSphArm A) (hB : StrictConvexSphArm B)
    (hsides : ∀ i : Fin 2, sideLen A i = sideLen B i)
    (hclose : sDist (A 0) (A (Fin.last 2)) = sDist (B 0) (B (Fin.last 2))) :
    ∀ i : Fin (2 + 1), linkAngle A i = linkAngle B i := by
  intro i
  have hAedge := hA.closed_convex.edge_short
  have hBedge := hB.closed_convex.edge_short
  fin_cases i
  · change linkAngle A (0 : Fin (2 + 1)) = linkAngle B (0 : Fin (2 + 1))
    rw [linkAngle_zero, linkAngle_zero]
    refine sphAngle_eq_of_three_sDist_eq
      (hAedge (Fin.last 2)) (hAedge 0)
      (hBedge (Fin.last 2)) (hBedge 0) ?_ ?_ ?_
    · have h := hsides (⟨1, by omega⟩ : Fin 2)
      simpa [sideLen, sDist_comm] using h
    · simpa [sDist_comm] using hclose
    · simpa [sideLen] using hsides (⟨0, by omega⟩ : Fin 2)
  · rw [linkAngle_interior A (⟨0, by omega⟩ : Fin (2 - 1)),
      linkAngle_interior B (⟨0, by omega⟩ : Fin (2 - 1))]
    unfold jointAngle
    refine sphAngle_eq_of_three_sDist_eq
      (hAedge 0) (hAedge 1)
      (hBedge 0) (hBedge 1) ?_ ?_ ?_
    · simpa using hclose
    · simpa [sideLen] using hsides (⟨0, by omega⟩ : Fin 2)
    · simpa [sideLen] using hsides (⟨1, by omega⟩ : Fin 2)
  · change linkAngle A (Fin.last 2) = linkAngle B (Fin.last 2)
    rw [linkAngle_last, linkAngle_last]
    refine sphAngle_eq_of_three_sDist_eq
      (hAedge 1) (hAedge (Fin.last 2))
      (hBedge 1) (hBedge (Fin.last 2)) ?_ ?_ ?_
    · calc
        sDist (A 1) (A 0)
            = sDist (A 0) (A 1) := sDist_comm _ _
        _ = sDist (B 0) (B 1) := by
          simpa [sideLen] using hsides (⟨0, by omega⟩ : Fin 2)
        _ = sDist (B 1) (B 0) := (sDist_comm _ _).symm
    · simpa [sideLen] using hsides (⟨1, by omega⟩ : Fin 2)
    · simpa [sDist_comm] using hclose

theorem signChangesFull_ne_two_triangle
    (A B : Fin (2 + 1) → S2)
    (hA : StrictConvexSphArm A) (hB : StrictConvexSphArm B)
    (hsides : ∀ i : Fin 2, sideLen A i = sideLen B i)
    (hclose : sDist (A 0) (A (Fin.last 2)) = sDist (B 0) (B (Fin.last 2))) :
    signChangesFull A B ≠ 2 := by
  intro h2
  have hlink := triangle_linkAngle_eq_of_sides A B hA hB hsides hclose
  have hzero : signChangesFull A B = 0 := by
    unfold signChangesFull
    have hdiff : linkDiff A B = fun _ => (0 : ℝ) := by
      funext i
      unfold linkDiff
      rw [hlink i]
      ring
    rw [hdiff]
    simp [nzSigns, cyclicFlips]
  omega

/-- A cyclic Boolean list consists of exactly two nonempty sign blocks, up to rotation. -/
def BoolTwoBlocks (L : List Bool) : Prop :=
  ∃ trueBlock falseBlock : List Bool,
    trueBlock ≠ [] ∧
      falseBlock ≠ [] ∧
      (∀ x ∈ trueBlock, x = true) ∧
      (∀ x ∈ falseBlock, x = false) ∧
      trueBlock ++ falseBlock ~r L

private theorem bool_eq_not_of_ne {a b : Bool} (h : a ≠ b) : b = !a := by
  cases a <;> cases b <;> simp at h ⊢

private theorem bool_eq_of_ne_ne {a b c : Bool} (hab : a ≠ b) (hac : c ≠ a) : c = b := by
  cases a <;> cases b <;> cases c <;> simp at hab hac ⊢

private theorem flips_eq_one_open_blocks :
    ∀ (a b : Bool) (l : List Bool), a ≠ b →
      flips ((a :: l) ++ [b]) = 1 →
      ∃ pre post : List Bool,
        l = pre ++ post ∧
          (∀ x ∈ pre, x = a) ∧
          (∀ x ∈ post, x = b)
  | a, b, [], hab, _ => by
      refine ⟨[], [], by simp, ?_, ?_⟩ <;> simp
  | a, b, c :: xs, hab, hflip => by
      by_cases hca : c = a
      · subst c
        have hrest : flips ((a :: xs) ++ [b]) = 1 := by
          simpa [flips, hab] using hflip
        obtain ⟨pre, post, hxs, hpre, hpost⟩ :=
          flips_eq_one_open_blocks a b xs hab hrest
        refine ⟨a :: pre, post, ?_, ?_, hpost⟩
        · rw [hxs]
          simp [List.cons_append]
        · intro x hx
          simp only [List.mem_cons] at hx
          rcases hx with rfl | hx
          · rfl
          · exact hpre x hx
      · have hcb : c = b := bool_eq_of_ne_ne hab hca
        have hrest : flips ((c :: xs) ++ [b]) = 0 := by
          rw [show flips ((a :: c :: xs) ++ [b]) =
              (if a ≠ c then 1 else 0) + flips ((c :: xs) ++ [b]) by rfl] at hflip
          have hac : a ≠ c := by exact fun h => hca h.symm
          have hsum : 1 + flips ((c :: xs) ++ [b]) = 1 := by
            simpa [hac] using hflip
          omega
        refine ⟨[], c :: xs, by simp, by simp, ?_⟩
        intro x hx
        have hall := (flips_eq_zero_iff_all_eq ((c :: xs) ++ [b])).mp hrest
        have hx' : x ∈ (c :: xs) ++ [b] := List.mem_append_left _ hx
        have hb' : b ∈ (c :: xs) ++ [b] := List.mem_append_right _ (by simp)
        exact hall x hx' b hb'

private theorem flips_eq_two_closed_blocks :
    ∀ (a : Bool) (l : List Bool),
      flips ((a :: l) ++ [a]) = 2 →
      ∃ pre mid post : List Bool,
        l = pre ++ mid ++ post ∧
          mid ≠ [] ∧
          (∀ x ∈ pre, x = a) ∧
          (∀ x ∈ mid, x = !a) ∧
          (∀ x ∈ post, x = a)
  | a, [], hflip => by
      simp [flips] at hflip
  | a, c :: xs, hflip => by
      by_cases hca : c = a
      · subst c
        have hrest : flips ((a :: xs) ++ [a]) = 2 := by
          simpa [flips] using hflip
        obtain ⟨pre, mid, post, hxs, hmidne, hpre, hmid, hpost⟩ :=
          flips_eq_two_closed_blocks a xs hrest
        refine ⟨a :: pre, mid, post, ?_, hmidne, ?_, hmid, hpost⟩
        · rw [hxs]
          simp [List.cons_append, List.append_assoc]
        · intro x hx
          simp only [List.mem_cons] at hx
          rcases hx with rfl | hx
          · rfl
          · exact hpre x hx
      · have hac : a ≠ c := fun h => hca h.symm
        have hrest : flips ((c :: xs) ++ [a]) = 1 := by
          rw [show flips ((a :: c :: xs) ++ [a]) =
              (if a ≠ c then 1 else 0) + flips ((c :: xs) ++ [a]) by rfl] at hflip
          have hsum : 1 + flips ((c :: xs) ++ [a]) = 2 := by
            simpa [hac] using hflip
          omega
        obtain ⟨midTail, post, hxs, hmidTail, hpost⟩ :=
          flips_eq_one_open_blocks c a xs hca hrest
        have hcnot : c = !a := bool_eq_not_of_ne hac
        refine ⟨[], c :: midTail, post, ?_, by simp, by simp, ?_, hpost⟩
        · rw [hxs]
          simp [List.cons_append, List.append_assoc]
        · intro x hx
          simp only [List.mem_cons] at hx
          rcases hx with rfl | hx
          · exact hcnot
          · rw [← hcnot]
            exact hmidTail x hx

/-- If a cyclic Boolean list has exactly two flips, then up to rotation it is one nonempty
`true` block followed by one nonempty `false` block. -/
theorem cyclicFlips_two_blocks (L : List Bool) (h : cyclicFlips L = 2) :
    BoolTwoBlocks L := by
  cases L with
  | nil =>
      simp [cyclicFlips] at h
  | cons a l =>
      have hclosed : flips ((a :: l) ++ [a]) = 2 := by
        simpa [cyclicFlips] using h
      obtain ⟨pre, mid, post, hl, hmidne, hpre, hmid, hpost⟩ :=
        flips_eq_two_closed_blocks a l hclosed
      have hL : a :: l = (a :: pre) ++ mid ++ post := by
        rw [hl]
        simp [List.cons_append, List.append_assoc]
      by_cases ha : a = true
      · subst a
        refine ⟨post ++ (true :: pre), mid, by simp, hmidne, ?_, ?_, ?_⟩
        · intro x hx
          rcases List.mem_append.mp hx with hx | hx
          · exact hpost x hx
          · simp only [List.mem_cons] at hx
            rcases hx with rfl | hx
            · rfl
            · exact hpre x hx
        · intro x hx
          simpa using hmid x hx
        · rw [hL]
          simpa [List.cons_append, List.append_assoc] using
            (List.isRotated_append (l := (true :: pre) ++ mid) (l' := post)).symm
      · have ha' : a = false := by cases a <;> simp at ha ⊢
        subst a
        refine ⟨mid, post ++ (false :: pre), hmidne, by simp, ?_, ?_, ?_⟩
        · intro x hx
          simpa using hmid x hx
        · intro x hx
          rcases List.mem_append.mp hx with hx | hx
          · exact hpost x hx
          · simp only [List.mem_cons] at hx
            rcases hx with rfl | hx
            · rfl
            · exact hpre x hx
        · rw [hL]
          simpa [List.cons_append, List.append_assoc] using
            (List.isRotated_append (l := (false :: pre)) (l' := mid ++ post)).symm

private theorem list_eq_replicate_of_forall_eq {α : Type*} (a : α) :
    ∀ l : List α, (∀ x ∈ l, x = a) → l = List.replicate l.length a := by
  intro l h
  exact (List.eq_replicate_length (a := a) (l := l)).2 h

theorem cyclicFlips_two_replicate_blocks (L : List Bool) (h : cyclicFlips L = 2) :
    ∃ k a b : ℕ,
      1 ≤ a ∧ 1 ≤ b ∧
        L.rotate k = List.replicate a true ++ List.replicate b false := by
  rcases cyclicFlips_two_blocks L h with
    ⟨trueBlock, falseBlock, htrue_ne, hfalse_ne, htrue, hfalse, hrot⟩
  have htf : L ~r trueBlock ++ falseBlock := List.isRotated_comm.mp hrot
  rcases (List.isRotated_iff_mod.mp htf) with ⟨k, _hk, hk⟩
  refine ⟨k, trueBlock.length, falseBlock.length, ?_, ?_, ?_⟩
  · cases trueBlock with
    | nil => simp at htrue_ne
    | cons _ _ => simp
  · cases falseBlock with
    | nil => simp at hfalse_ne
    | cons _ _ => simp
  · calc
      L.rotate k = trueBlock ++ falseBlock := hk
      _ = List.replicate trueBlock.length true ++ List.replicate falseBlock.length false := by
        have htb := list_eq_replicate_of_forall_eq true trueBlock htrue
        have hfb := list_eq_replicate_of_forall_eq false falseBlock hfalse
        rw [htb, hfb]
        simp

private lemma cval_lt_of_cycOpen_pred_last
    {n : ℕ} {first last j : Fin (n + 1)}
    (hj :
      cycOpen (n + 1) (predVal first) last.val j.val) :
    cval (n + 1) first.val j.val
      <
    cval (n + 1) first.val last.val := by
  unfold cycOpen predVal at hj
  unfold cval
  split_ifs at hj ⊢ <;> omega

private lemma cval_last_lt_of_cycOpen_last_pred
    {n : ℕ} {first last j : Fin (n + 1)}
    (hj :
      cycOpen (n + 1) last.val (predVal first) j.val) :
    cval (n + 1) first.val last.val
      <
    cval (n + 1) first.val j.val := by
  unfold cycOpen predVal at hj
  unfold cval
  split_ifs at hj ⊢ <;> omega

private theorem exists_get_of_mem {α : Type*} {xs : List α} {x : α}
    (hx : x ∈ xs) :
    ∃ q : Fin xs.length, xs.get q = x := by
  exact List.get_of_mem hx

private theorem pairwise_rel_get {α : Type*} {R : α → α → Prop} {l : List α}
    (hpair : l.Pairwise R) {i j : Fin l.length} (hij : i.val < j.val) :
    R (l.get i) (l.get j) := by
  exact (List.pairwise_iff_get.mp hpair) i j hij

structure RotTwoBlockCert {n : ℕ} (d : Fin (n + 1) → ℝ)
    (σ : Bool) where
  k : ℕ
  a : ℕ
  b : ℕ
  ha : 1 ≤ a
  hb : 1 ≤ b
  hrot :
    (nzSigns d).rotate k =
      List.replicate a σ ++ List.replicate b (!σ)

namespace RotTwoBlockCert

variable {n : ℕ} {d : Fin (n + 1) → ℝ} {σ : Bool}
variable (R : RotTwoBlockCert d σ)

private abbrev rIdx : List (Fin (n + 1)) :=
  (nzIdx d).rotate R.k

private lemma rIdx_length :
    R.rIdx.length = R.a + R.b := by
  have h := congrArg List.length R.hrot
  simpa [rIdx, nzIdx, nzSigns, signOf, List.length_rotate] using h

private lemma rIdx_ne_nil : R.rIdx ≠ [] := by
  have hlen := R.rIdx_length
  intro hnil
  have : R.rIdx.length = 0 := by simp [hnil]
  have ha := R.ha
  have hb := R.hb
  omega

private def getR (q : ℕ) (hq : q < R.a + R.b) : Fin (n + 1) :=
  R.rIdx.get ⟨q, by
    rw [R.rIdx_length]
    exact hq⟩

private lemma zero_lt_ab : 0 < R.a + R.b := by
  have ha := R.ha
  have hb := R.hb
  omega

private lemma sign_getR_left {q : ℕ} (hq : q < R.a) :
    signOf d (R.getR q (by omega)) = σ := by
  have hmap :
      R.rIdx.map (signOf d) =
        (nzSigns d).rotate R.k := by
    rw [← nzSignedIdx_map_snd d]
    simp [rIdx, nzSignedIdx, signOf, List.map_rotate]
  have hmain :
      R.rIdx.map (signOf d) =
        List.replicate R.a σ ++ List.replicate R.b (!σ) := by
    rw [hmap, R.hrot]
  have hqIdx : q < R.rIdx.length := by
    rw [R.rIdx_length]
    omega
  have hqMap : q < (R.rIdx.map (signOf d)).length := by
    simpa using hqIdx
  have hqRep : q < (List.replicate R.a σ ++ List.replicate R.b (!σ)).length := by
    simp
    omega
  calc
    signOf d (R.getR q (by omega))
        = (R.rIdx.map (signOf d))[q]'hqMap := by
          rw [List.getElem_map]
          simp [getR]
    _ = (List.replicate R.a σ ++ List.replicate R.b (!σ))[q]'(by
          simpa [hmain] using hqMap) :=
          List.getElem_of_eq hmain hqMap
    _ = σ := by
          rw [List.getElem_append_left (as := List.replicate R.a σ)
            (bs := List.replicate R.b (!σ)) (i := q) (by simpa using hq)]
          rw [List.getElem_replicate]

private lemma sign_getR_right {q : ℕ} (hq₁ : R.a ≤ q) (hq₂ : q < R.a + R.b) :
    signOf d (R.getR q hq₂) = !σ := by
  have hmap :
      R.rIdx.map (signOf d) =
        (nzSigns d).rotate R.k := by
    rw [← nzSignedIdx_map_snd d]
    simp [rIdx, nzSignedIdx, signOf, List.map_rotate]
  have hmain :
      R.rIdx.map (signOf d) =
        List.replicate R.a σ ++ List.replicate R.b (!σ) := by
    rw [hmap, R.hrot]
  have hqIdx : q < R.rIdx.length := by
    rw [R.rIdx_length]
    exact hq₂
  have hqMap : q < (R.rIdx.map (signOf d)).length := by
    simpa using hqIdx
  have hqRep : q < (List.replicate R.a σ ++ List.replicate R.b (!σ)).length := by
    simp
    exact hq₂
  calc
    signOf d (R.getR q hq₂)
        = (R.rIdx.map (signOf d))[q]'hqMap := by
          rw [List.getElem_map]
          simp [getR]
    _ = (List.replicate R.a σ ++ List.replicate R.b (!σ))[q]'(by
          simpa [hmain] using hqMap) :=
          List.getElem_of_eq hmain hqMap
    _ = !σ := by
          rw [List.getElem_append_right (as := List.replicate R.a σ)
            (bs := List.replicate R.b (!σ)) (i := q) (by simpa using hq₁)]
          rw [List.getElem_replicate]

private lemma rIdx_pairwise_from_first :
    R.rIdx.Pairwise
      (fun x y =>
        cval (n + 1) (R.getR 0 R.zero_lt_ab).val x.val
          <
        cval (n + 1) (R.getR 0 R.zero_lt_ab).val y.val) := by
  have hlen : 0 < R.rIdx.length := by
    rw [R.rIdx_length]
    have ha := R.ha
    have hb := R.hb
    omega
  simpa [rIdx, getR, R.rIdx_length, R.zero_lt_ab] using
    nzIdx_rotate_pairwise_cval_get_zero (d := d) (k := R.k) hlen

private lemma sign_firstBlock_of_in_dropLast_arc
    (ha2 : 2 ≤ R.a) (hb1 : 1 ≤ R.b)
    {j : Fin (n + 1)}
    (hj0 : d j ≠ 0)
    (hjArc :
      cycOpen (n + 1)
        (predVal (R.getR 0 R.zero_lt_ab))
        (R.getR (R.a - 1) (by omega)).val
        j.val) :
    signOf d j = σ := by
  have hjmem0 : j ∈ nzIdx d :=
    (mem_nzIdx (d := d) j).2 hj0
  have hjmem : j ∈ R.rIdx := by
    simpa [rIdx] using
      (List.mem_rotate (l := nzIdx d) (a := j) (n := R.k)).2 hjmem0
  obtain ⟨q, hqget⟩ := exists_get_of_mem hjmem
  have hArcShift :
      cval (n + 1) (R.getR 0 R.zero_lt_ab).val j.val
        <
      cval (n + 1) (R.getR 0 R.zero_lt_ab).val
        (R.getR (R.a - 1) (by omega)).val := by
    simpa using
      cval_lt_of_cycOpen_pred_last
        (n := n)
        (first := R.getR 0 R.zero_lt_ab)
        (last := R.getR (R.a - 1) (by omega))
        (j := j)
        hjArc
  have hq_lt_a : q.val < R.a := by
    by_contra hqa
    have hqa' : R.a ≤ q.val := by omega
    have hlt_index : (R.a - 1 : ℕ) < q.val := by omega
    have hpair := pairwise_rel_get R.rIdx_pairwise_from_first
      (i := ⟨R.a - 1, by
        rw [R.rIdx_length]
        omega⟩)
      (j := q)
      hlt_index
    rw [← hqget] at hArcShift
    exact not_lt_of_ge (le_of_lt hArcShift) hpair
  rw [← hqget]
  simpa [getR] using R.sign_getR_left hq_lt_a

private lemma sign_secondBlock_of_in_complement_arc
    (ha2 : 2 ≤ R.a) (hb2 : 2 ≤ R.b)
    {j : Fin (n + 1)}
    (hj0 : d j ≠ 0)
    (hjArc :
      cycOpen (n + 1)
        (R.getR (R.a - 1) (by omega)).val
        (predVal (R.getR 0 R.zero_lt_ab))
        j.val) :
    signOf d j = !σ := by
  have hjmem0 : j ∈ nzIdx d :=
    (mem_nzIdx (d := d) j).2 hj0
  have hjmem : j ∈ R.rIdx := by
    simpa [rIdx] using
      (List.mem_rotate (l := nzIdx d) (a := j) (n := R.k)).2 hjmem0
  obtain ⟨q, hqget⟩ := exists_get_of_mem hjmem
  have hcompShift :
      cval (n + 1) (R.getR 0 R.zero_lt_ab).val
        (R.getR (R.a - 1) (by omega)).val
        <
      cval (n + 1) (R.getR 0 R.zero_lt_ab).val j.val := by
    simpa using
      cval_last_lt_of_cycOpen_last_pred
        (n := n)
        (first := R.getR 0 R.zero_lt_ab)
        (last := R.getR (R.a - 1) (by omega))
        (j := j)
        hjArc
  have hq_ge_a : R.a ≤ q.val := by
    by_contra hqa
    have hq_lt_a : q.val < R.a := by omega
    have hq_le_last : q.val ≤ R.a - 1 := by omega
    have hshift_le :
        cval (n + 1) (R.getR 0 R.zero_lt_ab).val j.val
          ≤
        cval (n + 1) (R.getR 0 R.zero_lt_ab).val
          (R.getR (R.a - 1) (by omega)).val := by
      rcases lt_or_eq_of_le hq_le_last with hlt | heq
      · have hpair := pairwise_rel_get R.rIdx_pairwise_from_first
          (i := q)
          (j := ⟨R.a - 1, by
            rw [R.rIdx_length]
            omega⟩)
          hlt
        rw [hqget] at hpair
        exact le_of_lt hpair
      · have : j = R.getR (R.a - 1) (by omega) := by
          rw [← hqget]
          apply congrArg R.rIdx.get
          apply Fin.ext
          exact heq
        simp [this]
    exact not_lt_of_ge hshift_le hcompShift
  rw [← hqget]
  exact R.sign_getR_right hq_ge_a (by
    simpa [R.rIdx_length] using q.isLt)

private lemma eq_singleton_firstBlock_of_sign
    (ha1 : R.a = 1)
    {j : Fin (n + 1)}
    (hj0 : d j ≠ 0)
    (hsgn : signOf d j = σ) :
    j = R.getR 0 R.zero_lt_ab := by
  have hjmem0 : j ∈ nzIdx d :=
    (mem_nzIdx (d := d) j).2 hj0
  have hjmem : j ∈ R.rIdx := by
    simpa [rIdx] using
      (List.mem_rotate (l := nzIdx d) (a := j) (n := R.k)).2 hjmem0
  obtain ⟨q, hqget⟩ := exists_get_of_mem hjmem
  have hq_lt_one : q.val < 1 := by
    by_contra hq
    have hqa : R.a ≤ q.val := by
      have ha1' := ha1
      omega
    have hright := R.sign_getR_right
      (q := q.val) hqa (by
        simpa [R.rIdx_length] using q.isLt)
    have hgetEq : R.getR q.val (by simpa [R.rIdx_length] using q.isLt) = j := by
      simpa [getR] using hqget
    rw [hgetEq] at hright
    have hbad : σ = !σ := hsgn.symm.trans hright
    cases σ <;> simp at hbad
  apply Fin.ext
  have hq0 : q.val = 0 := by omega
  have : q = ⟨0, by
      rw [R.rIdx_length]
      omega⟩ := Fin.ext hq0
  rw [← hqget, this]
  rfl

private lemma eq_singleton_secondBlock_of_sign
    (hb1 : R.b = 1)
    {j : Fin (n + 1)}
    (hj0 : d j ≠ 0)
    (hsgn : signOf d j = !σ) :
    j = R.getR R.a (by omega) := by
  have hjmem0 : j ∈ nzIdx d :=
    (mem_nzIdx (d := d) j).2 hj0
  have hjmem : j ∈ R.rIdx := by
    simpa [rIdx] using
      (List.mem_rotate (l := nzIdx d) (a := j) (n := R.k)).2 hjmem0
  obtain ⟨q, hqget⟩ := exists_get_of_mem hjmem
  have hq_ge_a : R.a ≤ q.val := by
    by_contra hq
    have hleft := R.sign_getR_left
      (q := q.val) (by
        have hq' := hq
        omega)
    have hgetEq : R.getR q.val (by omega) = j := by
      simpa [getR] using hqget
    rw [hgetEq] at hleft
    have hbad : σ = !σ := hleft.symm.trans hsgn
    cases σ <;> simp at hbad
  have hq_eq_a : q.val = R.a := by
    have hq_lt : q.val < R.a + R.b := by
      simpa [R.rIdx_length] using q.isLt
    omega
  apply Fin.ext
  have : q = ⟨R.a, by
      rw [R.rIdx_length]
      omega⟩ := Fin.ext hq_eq_a
  rw [← hqget, this]
  rfl

end RotTwoBlockCert

private lemma first_mem_dropLast_arc
    {n : ℕ} {d : Fin (n + 1) → ℝ} {σ : Bool} {R : RotTwoBlockCert d σ}
    (ha2 : 2 ≤ R.a) (hb1 : 1 ≤ R.b) :
    cycOpen (n + 1)
      (predVal (R.getR 0 R.zero_lt_ab))
      (R.getR (R.a - 1) (by omega)).val
      (R.getR 0 R.zero_lt_ab).val := by
  have ha := R.ha
  have hb := R.hb
  have hpair := pairwise_rel_get R.rIdx_pairwise_from_first
    (i := ⟨R.a - 1, by
      rw [R.rIdx_length]
      omega⟩)
    (j := ⟨R.a, by
      rw [R.rIdx_length]
      omega⟩)
    (by
      show R.a - 1 < R.a
      omega)
  have hfirstLast := pairwise_rel_get R.rIdx_pairwise_from_first
    (i := ⟨0, by
      rw [R.rIdx_length]
      omega⟩)
    (j := ⟨R.a - 1, by
      rw [R.rIdx_length]
      omega⟩)
    (by
      show 0 < R.a - 1
      omega)
  have hpos :
      0 < cval (n + 1) (R.getR 0 R.zero_lt_ab).val
          (R.getR (R.a - 1) (by omega)).val := by
    simpa [RotTwoBlockCert.getR, cval] using hfirstLast
  have hpair' :
      cval (n + 1) (R.getR 0 R.zero_lt_ab).val
          (R.getR (R.a - 1) (by omega)).val <
        cval (n + 1) (R.getR 0 R.zero_lt_ab).val
          (R.getR R.a (by omega)).val := by
    simpa [RotTwoBlockCert.getR] using hpair
  have hoppN :
      cval (n + 1) (R.getR 0 R.zero_lt_ab).val
          (R.getR R.a (by omega)).val < n + 1 :=
    cval_lt_succ (R.getR 0 R.zero_lt_ab).isLt (R.getR R.a (by omega)).isLt
  have hlt :
      cval (n + 1) (R.getR 0 R.zero_lt_ab).val
          (R.getR (R.a - 1) (by omega)).val < n := by
    omega
  exact cycOpen_pred_self_last_of_cval
    (R.getR 0 R.zero_lt_ab) (R.getR (R.a - 1) (by omega)) hpos hlt

private lemma first_secondBlock_mem_complement_arc
    {n : ℕ} {d : Fin (n + 1) → ℝ} {σ : Bool} {R : RotTwoBlockCert d σ}
    (ha2 : 2 ≤ R.a) (hb2 : 2 ≤ R.b) :
    cycOpen (n + 1)
      (R.getR (R.a - 1) (by omega)).val
      (predVal (R.getR 0 R.zero_lt_ab))
      (R.getR R.a (by omega)).val := by
  have ha := R.ha
  have hb := R.hb
  have hlast_lt_firstOpp := pairwise_rel_get R.rIdx_pairwise_from_first
    (i := ⟨R.a - 1, by
      rw [R.rIdx_length]
      omega⟩)
    (j := ⟨R.a, by
      rw [R.rIdx_length]
      omega⟩)
    (by
      show R.a - 1 < R.a
      omega)
  have hfirstOpp_lt_lastOpp := pairwise_rel_get R.rIdx_pairwise_from_first
    (i := ⟨R.a, by
      rw [R.rIdx_length]
      omega⟩)
    (j := ⟨R.a + 1, by
      rw [R.rIdx_length]
      omega⟩)
    (by
      show R.a < R.a + 1
      omega)
  have hfirstLast := pairwise_rel_get R.rIdx_pairwise_from_first
    (i := ⟨0, by
      rw [R.rIdx_length]
      omega⟩)
    (j := ⟨R.a - 1, by
      rw [R.rIdx_length]
      omega⟩)
    (by
      show 0 < R.a - 1
      omega)
  have hlastOppN :
      cval (n + 1) (R.getR 0 R.zero_lt_ab).val
          (R.getR (R.a + 1) (by omega)).val < n + 1 :=
    cval_lt_succ (R.getR 0 R.zero_lt_ab).isLt (R.getR (R.a + 1) (by omega)).isLt
  have hlast_firstOpp' :
      cval (n + 1) (R.getR 0 R.zero_lt_ab).val
          (R.getR (R.a - 1) (by omega)).val <
        cval (n + 1) (R.getR 0 R.zero_lt_ab).val
          (R.getR R.a (by omega)).val := by
    simpa [RotTwoBlockCert.getR] using hlast_lt_firstOpp
  have hfirstOpp_lastOpp' :
      cval (n + 1) (R.getR 0 R.zero_lt_ab).val
          (R.getR R.a (by omega)).val <
        cval (n + 1) (R.getR 0 R.zero_lt_ab).val
          (R.getR (R.a + 1) (by omega)).val := by
    simpa [RotTwoBlockCert.getR] using hfirstOpp_lt_lastOpp
  have hxp :
      cval (n + 1) (R.getR 0 R.zero_lt_ab).val
          (R.getR R.a (by omega)).val < n := by
    omega
  exact cycOpen_last_pred_of_cval
    (R.getR 0 R.zero_lt_ab)
    (R.getR (R.a - 1) (by omega))
    (R.getR R.a (by omega))
    hlast_firstOpp' hxp

private def emitPosFromArc
    {n : ℕ} (d : Fin (n + 1) → ℝ)
    (l r : ℕ) (hl : l ≤ n) (hr : r ≤ n)
    (hLen : 2 ≤ cdist (n + 1) l r)
    (hComp : 2 ≤ cdist (n + 1) r l)
    (hpos :
      ∀ j : Fin (n + 1),
        cycOpen (n + 1) l r j.val → 0 ≤ d j)
    (hstrictNonwrap :
      ∀ hlt : l < r,
        ∃ i : Fin (r - l - 1),
          0 < d (nonwrapIdx (n := n) (t := l) (s := r) hr i))
    (hstrictWrap :
      ∀ hgt : r < l,
        ∃ i : Fin (wrapLen n l r - 1),
          0 < d (wrapIdx (n := n) (t := r) (s := l) hgt hl i))
    (hneg :
      ∀ j : Fin (n + 1),
        cycOpen (n + 1) r l j.val → d j ≤ 0) :
    OrientedTwoArcCut d := by
  by_cases hlr : l < r
  · exact OrientedTwoArcCut.plusMinus
      (
      { tIdx := l
        sIdx := r
        hts := hlr
        hsn := hr
        hm1 := by simpa [cdist_of_lt hlr] using hLen
        hm2 := by
          have := hComp
          rw [cdist_of_gt hlr] at this
          simpa [wrapLen] using this
        nonwrap_nonneg := by
          intro i
          exact hpos _ (nonwrapIdx_mem_cycOpen hlr hr i)
        wrap_nonpos := by
          intro i
          exact hneg _ (wrapIdx_mem_cycOpen hlr hr i)
        strictOnNonwrap := true
        strict_nonwrap := by
          intro _
          exact hstrictNonwrap hlr
        strict_wrap := by
          intro hfalse
          simp at hfalse } : TwoArcCutPlusMinus d)
  · by_cases hrl : r < l
    · exact OrientedTwoArcCut.minusPlus (
      { tIdx := r
        sIdx := l
        hts := hrl
        hsn := hl
        hm1 := by simpa [cdist_of_lt hrl] using hComp
        hm2 := by
          have := hLen
          rw [cdist_of_gt hrl] at this
          simpa [wrapLen] using this
        nonwrap_nonpos := by
          intro i
          exact hneg _ (nonwrapIdx_mem_cycOpen hrl hl i)
        wrap_nonneg := by
          intro i
          exact hpos _ (wrapIdx_mem_cycOpen hrl hl i)
        strictOnWrap := true
        strict_nonwrap := by
          intro hfalse
          simp at hfalse
        strict_wrap := by
          intro _
          exact hstrictWrap hrl } : TwoArcCutMinusPlus d)
    · have heq : l = r := by omega
      subst r
      simp [cdist] at hLen

private def emitNegFromArc
    {n : ℕ} (d : Fin (n + 1) → ℝ)
    (l r : ℕ) (hl : l ≤ n) (hr : r ≤ n)
    (hLen : 2 ≤ cdist (n + 1) l r)
    (hComp : 2 ≤ cdist (n + 1) r l)
    (hneg :
      ∀ j : Fin (n + 1),
        cycOpen (n + 1) l r j.val → d j ≤ 0)
    (hstrictNonwrap :
      ∀ hlt : l < r,
        ∃ i : Fin (r - l - 1),
          d (nonwrapIdx (n := n) (t := l) (s := r) hr i) < 0)
    (hstrictWrap :
      ∀ hgt : r < l,
        ∃ i : Fin (wrapLen n l r - 1),
          d (wrapIdx (n := n) (t := r) (s := l) hgt hl i) < 0)
    (hpos :
      ∀ j : Fin (n + 1),
        cycOpen (n + 1) r l j.val → 0 ≤ d j) :
    OrientedTwoArcCut d := by
  by_cases hlr : l < r
  · exact OrientedTwoArcCut.minusPlus
      (
      { tIdx := l
        sIdx := r
        hts := hlr
        hsn := hr
        hm1 := by simpa [cdist_of_lt hlr] using hLen
        hm2 := by
          have := hComp
          rw [cdist_of_gt hlr] at this
          simpa [wrapLen] using this
        nonwrap_nonpos := by
          intro i
          exact hneg _ (nonwrapIdx_mem_cycOpen hlr hr i)
        wrap_nonneg := by
          intro i
          exact hpos _ (wrapIdx_mem_cycOpen hlr hr i)
        strictOnWrap := false
        strict_nonwrap := by
          intro _
          exact hstrictNonwrap hlr
        strict_wrap := by
          intro htrue
          simp at htrue } : TwoArcCutMinusPlus d)
  · by_cases hrl : r < l
    · exact OrientedTwoArcCut.plusMinus (
      { tIdx := r
        sIdx := l
        hts := hrl
        hsn := hl
        hm1 := by simpa [cdist_of_lt hrl] using hComp
        hm2 := by
          have := hLen
          rw [cdist_of_gt hrl] at this
          simpa [wrapLen] using this
        nonwrap_nonneg := by
          intro i
          exact hpos _ (nonwrapIdx_mem_cycOpen hrl hl i)
        wrap_nonpos := by
          intro i
          exact hneg _ (wrapIdx_mem_cycOpen hrl hl i)
        strictOnNonwrap := false
        strict_nonwrap := by
          intro htrue
          simp at htrue
        strict_wrap := by
          intro _
          exact hstrictWrap hrl } : TwoArcCutPlusMinus d)
    · have heq : l = r := by omega
      subst r
      simp [cdist] at hLen

private def cut_singleton_pos
    {n : ℕ} (d : Fin (n + 1) → ℝ) (hn : 3 ≤ n)
    (x : Fin (n + 1))
    (hxpos : 0 < d x)
    (honly :
      ∀ j : Fin (n + 1), d j ≠ 0 → signOf d j = true → j = x) :
    OrientedTwoArcCut d := by
  let l := predVal x
  let r := succVal x
  have hl : l ≤ n := predVal_le x
  have hr : r ≤ n := succVal_le x
  have hLens := pred_succ_singleton_lengths hn x
  have hLen : 2 ≤ cdist (n + 1) l r := by
    simpa [l, r, hLens.1] using (show 2 ≤ 2 by omega)
  have hComp : 2 ≤ cdist (n + 1) r l := by
    have hn' : 2 ≤ n - 1 := by omega
    simpa [l, r, hLens.2] using hn'
  refine emitPosFromArc d l r hl hr hLen hComp ?hpos ?hstrictNW ?hstrictW ?hneg
  · intro j hjArc
    have hj : j = x := singleton_forward_arc_eq hn x hjArc
    rw [hj]
    exact le_of_lt hxpos
  · intro hlt
    let i0 : Fin (r - l - 1) := ⟨0, by
      have hcd := hLen
      rw [cdist_of_lt hlt] at hcd
      omega⟩
    refine ⟨i0, ?_⟩
    have hidx :
        nonwrapIdx (n := n) (t := l) (s := r) hr i0 = x := by
      exact singleton_forward_arc_eq hn x
        (by simpa [l, r] using nonwrapIdx_mem_cycOpen hlt hr i0)
    simpa [hidx] using hxpos
  · intro hgt
    let i0 : Fin (wrapLen n l r - 1) := ⟨0, by
      have hcd := hLen
      rw [cdist_of_gt hgt] at hcd
      unfold wrapLen
      omega⟩
    refine ⟨i0, ?_⟩
    have hidx :
        wrapIdx (n := n) (t := r) (s := l) hgt hl i0 = x := by
      exact singleton_forward_arc_eq hn x
        (by simpa [l, r] using wrapIdx_mem_cycOpen hgt hl i0)
    simpa [hidx] using hxpos
  · intro j hjArc
    by_cases hj0 : d j = 0
    · simp [hj0]
    · by_cases hsgn : signOf d j = true
      · have hEq := honly j hj0 hsgn
        have hne := singleton_reverse_arc_ne hn x hjArc
        exact False.elim (hne hEq)
      · have hfalse : signOf d j = false := by
          cases h : signOf d j <;> simp [h] at hsgn ⊢
        exact le_of_lt (neg_of_sign_false hj0 hfalse)

private def cut_singleton_neg
    {n : ℕ} (d : Fin (n + 1) → ℝ) (hn : 3 ≤ n)
    (x : Fin (n + 1))
    (hxneg : d x < 0)
    (honly :
      ∀ j : Fin (n + 1), d j ≠ 0 → signOf d j = false → j = x) :
    OrientedTwoArcCut d := by
  let l := predVal x
  let r := succVal x
  have hl : l ≤ n := predVal_le x
  have hr : r ≤ n := succVal_le x
  have hLens := pred_succ_singleton_lengths hn x
  have hLen : 2 ≤ cdist (n + 1) l r := by
    simpa [l, r, hLens.1] using (show 2 ≤ 2 by omega)
  have hComp : 2 ≤ cdist (n + 1) r l := by
    have hn' : 2 ≤ n - 1 := by omega
    simpa [l, r, hLens.2] using hn'
  refine emitNegFromArc d l r hl hr hLen hComp ?hneg ?hstrictNW ?hstrictW ?hpos
  · intro j hjArc
    have hj : j = x := singleton_forward_arc_eq hn x hjArc
    rw [hj]
    exact le_of_lt hxneg
  · intro hlt
    let i0 : Fin (r - l - 1) := ⟨0, by
      have hcd := hLen
      rw [cdist_of_lt hlt] at hcd
      omega⟩
    refine ⟨i0, ?_⟩
    have hidx :
        nonwrapIdx (n := n) (t := l) (s := r) hr i0 = x := by
      exact singleton_forward_arc_eq hn x
        (by simpa [l, r] using nonwrapIdx_mem_cycOpen hlt hr i0)
    simpa [hidx] using hxneg
  · intro hgt
    let i0 : Fin (wrapLen n l r - 1) := ⟨0, by
      have hcd := hLen
      rw [cdist_of_gt hgt] at hcd
      unfold wrapLen
      omega⟩
    refine ⟨i0, ?_⟩
    have hidx :
        wrapIdx (n := n) (t := r) (s := l) hgt hl i0 = x := by
      exact singleton_forward_arc_eq hn x
        (by simpa [l, r] using wrapIdx_mem_cycOpen hgt hl i0)
    simpa [hidx] using hxneg
  · intro j hjArc
    by_cases hj0 : d j = 0
    · simp [hj0]
    · by_cases hsgn : signOf d j = false
      · have hEq := honly j hj0 hsgn
        have hne := singleton_reverse_arc_ne hn x hjArc
        exact False.elim (hne hEq)
      · have htrue : signOf d j = true := by
          cases h : signOf d j <;> simp [h] at hsgn ⊢
        exact le_of_lt (pos_of_sign_true htrue)

private def cut_firstBlock_dropLast
    {n : ℕ} {d : Fin (n + 1) → ℝ} {σ : Bool}
    (hn : 3 ≤ n) (R : RotTwoBlockCert d σ)
    (ha2 : 2 ≤ R.a) (hb2 : 2 ≤ R.b) :
    OrientedTwoArcCut d := by
  let first := R.getR 0 R.zero_lt_ab
  let last := R.getR (R.a - 1) (by omega)
  let l := predVal first
  let r := last.val
  have hl : l ≤ n := predVal_le first
  have hr : r ≤ n := Nat.le_of_lt_succ last.isLt
  have hfirstArc : cycOpen (n + 1) l r first.val := by
    simpa [first, last, l, r] using first_mem_dropLast_arc (R := R) ha2 (by omega)
  have hfirstOppArc : cycOpen (n + 1) r l (R.getR R.a (by omega)).val := by
    simpa [first, last, l, r] using first_secondBlock_mem_complement_arc (R := R) ha2 hb2
  have hLen : 2 ≤ cdist (n + 1) l r :=
    two_le_cdist_of_cycOpen first.isLt (by omega) (by omega) hfirstArc
  have hComp : 2 ≤ cdist (n + 1) r l :=
    two_le_cdist_of_cycOpen (R.getR R.a (by omega)).isLt (by omega) (by omega) hfirstOppArc
  have hfirstSign : signOf d first = σ := by
    simpa [first] using R.sign_getR_left (q := 0) (by omega)
  by_cases hσ : σ = true
  · have hfirstPos : 0 < d first := pos_of_sign_true (by simpa [hσ] using hfirstSign)
    refine emitPosFromArc d l r hl hr hLen hComp ?_ ?_ ?_ ?_
    · intro j hjArc
      by_cases hj0 : d j = 0
      · simp [hj0]
      · have hs := R.sign_firstBlock_of_in_dropLast_arc ha2 (by omega) hj0
          (by simpa [first, last, l, r] using hjArc)
        exact le_of_lt (pos_of_sign_true (by simpa [hσ] using hs))
    · intro hlt
      let i0 : Fin (r - l - 1) := ⟨0, by
        have hcd := hLen
        rw [cdist_of_lt hlt] at hcd
        omega⟩
      refine ⟨i0, ?_⟩
      have hidx : nonwrapIdx (n := n) (t := l) (s := r) hr i0 = first := by
        have h0idx : 0 < r - predVal first - 1 := by
          have hcd := hLen
          rw [cdist_of_lt hlt] at hcd
          simp [l] at hcd
          omega
        simpa [first, l, r, i0] using
          nonwrapIdx_zero_eq_pred first hr (by simpa [l, r] using hlt) h0idx
      simpa [hidx] using hfirstPos
    · intro hgt
      let i0 : Fin (wrapLen n l r - 1) := ⟨0, by
        have hcd := hLen
        rw [cdist_of_gt hgt] at hcd
        unfold wrapLen
        omega⟩
      refine ⟨i0, ?_⟩
      have hidx : wrapIdx (n := n) (t := r) (s := l) hgt hl i0 = first := by
        have h0idx : 0 < wrapLen n (predVal first) r - 1 := by
          have hcd := hLen
          rw [cdist_of_gt hgt] at hcd
          simp [l] at hcd
          unfold wrapLen
          omega
        simpa [first, l, r, i0] using
          wrapIdx_zero_eq_pred first (by simpa [l, r] using hgt) hl h0idx
      simpa [hidx] using hfirstPos
    · intro j hjArc
      by_cases hj0 : d j = 0
      · simp [hj0]
      · have hs := R.sign_secondBlock_of_in_complement_arc ha2 hb2 hj0
          (by simpa [first, last, l, r] using hjArc)
        exact le_of_lt (neg_of_sign_false hj0 (by simpa [hσ] using hs))
  · have hσfalse : σ = false := by cases σ <;> simp at hσ ⊢
    have hfirstNeg : d first < 0 := by
      have hfalse : signOf d first = false := by simpa [hσfalse] using hfirstSign
      have h0 : d first ≠ 0 := by
        have hmemRot : first ∈ R.rIdx := by
          exact List.get_mem R.rIdx ⟨0, by rw [R.rIdx_length]; omega⟩
        have hmem : first ∈ nzIdx d := by
          simpa [first, RotTwoBlockCert.rIdx] using
            (List.mem_rotate (l := nzIdx d) (a := first) (n := R.k)).1 hmemRot
        exact (mem_nzIdx (d := d) first).1 hmem
      exact neg_of_sign_false h0 hfalse
    refine emitNegFromArc d l r hl hr hLen hComp ?_ ?_ ?_ ?_
    · intro j hjArc
      by_cases hj0 : d j = 0
      · simp [hj0]
      · have hs := R.sign_firstBlock_of_in_dropLast_arc ha2 (by omega) hj0
          (by simpa [first, last, l, r] using hjArc)
        exact le_of_lt (neg_of_sign_false hj0 (by simpa [hσfalse] using hs))
    · intro hlt
      let i0 : Fin (r - l - 1) := ⟨0, by
        have hcd := hLen
        rw [cdist_of_lt hlt] at hcd
        omega⟩
      refine ⟨i0, ?_⟩
      have hidx : nonwrapIdx (n := n) (t := l) (s := r) hr i0 = first := by
        have h0idx : 0 < r - predVal first - 1 := by
          have hcd := hLen
          rw [cdist_of_lt hlt] at hcd
          simp [l] at hcd
          omega
        simpa [first, l, r, i0] using
          nonwrapIdx_zero_eq_pred first hr (by simpa [l, r] using hlt) h0idx
      simpa [hidx] using hfirstNeg
    · intro hgt
      let i0 : Fin (wrapLen n l r - 1) := ⟨0, by
        have hcd := hLen
        rw [cdist_of_gt hgt] at hcd
        unfold wrapLen
        omega⟩
      refine ⟨i0, ?_⟩
      have hidx : wrapIdx (n := n) (t := r) (s := l) hgt hl i0 = first := by
        have h0idx : 0 < wrapLen n (predVal first) r - 1 := by
          have hcd := hLen
          rw [cdist_of_gt hgt] at hcd
          simp [l] at hcd
          unfold wrapLen
          omega
        simpa [first, l, r, i0] using
          wrapIdx_zero_eq_pred first (by simpa [l, r] using hgt) hl h0idx
      simpa [hidx] using hfirstNeg
    · intro j hjArc
      by_cases hj0 : d j = 0
      · simp [hj0]
      · have hs := R.sign_secondBlock_of_in_complement_arc ha2 hb2 hj0
          (by simpa [first, last, l, r] using hjArc)
        exact le_of_lt (pos_of_sign_true (by simpa [hσfalse] using hs))

private def cut_of_rot_two_block
    {n : ℕ} {d : Fin (n + 1) → ℝ} {σ : Bool}
    (hn : 3 ≤ n) (R : RotTwoBlockCert d σ) :
    OrientedTwoArcCut d := by
  by_cases ha1 : R.a = 1
  · let x := R.getR 0 R.zero_lt_ab
    have hxsign : signOf d x = σ := by simpa [x] using R.sign_getR_left (q := 0) (by omega)
    cases hσ : σ
    · have hxneg : d x < 0 := by
        have hxfalse : signOf d x = false := by simpa [hσ] using hxsign
        have hx0 : d x ≠ 0 := by
          have hxmemRot : x ∈ R.rIdx := by
            exact List.get_mem R.rIdx ⟨0, by rw [R.rIdx_length]; omega⟩
          have hxmem : x ∈ nzIdx d := by
            simpa [RotTwoBlockCert.rIdx] using
              (List.mem_rotate (l := nzIdx d) (a := x) (n := R.k)).1 hxmemRot
          exact (mem_nzIdx (d := d) x).1 hxmem
        exact neg_of_sign_false hx0 hxfalse
      exact cut_singleton_neg d hn x hxneg (fun j hj0 hsgn =>
        R.eq_singleton_firstBlock_of_sign ha1 hj0 (by simpa [hσ] using hsgn))
    · have hxpos : 0 < d x := pos_of_sign_true (by simpa [hσ] using hxsign)
      exact cut_singleton_pos d hn x hxpos (fun j hj0 hsgn =>
        R.eq_singleton_firstBlock_of_sign ha1 hj0 (by simpa [hσ] using hsgn))
  · by_cases hb1 : R.b = 1
    · let x := R.getR R.a (by omega)
      have hxsign : signOf d x = !σ := by
        simpa [x] using R.sign_getR_right (q := R.a) (by omega) (by omega)
      cases hσ : σ
      · have hxpos : 0 < d x := pos_of_sign_true (by simpa [hσ] using hxsign)
        exact cut_singleton_pos d hn x hxpos (fun j hj0 hsgn =>
          R.eq_singleton_secondBlock_of_sign hb1 hj0 (by simpa [hσ] using hsgn))
      · have hxneg : d x < 0 := by
          have hxfalse : signOf d x = false := by simpa [hσ] using hxsign
          have hx0 : d x ≠ 0 := by
            have hxmemRot : x ∈ R.rIdx := by
              exact List.get_mem R.rIdx ⟨R.a, by rw [R.rIdx_length]; omega⟩
            have hxmem : x ∈ nzIdx d := by
              simpa [RotTwoBlockCert.rIdx] using
                (List.mem_rotate (l := nzIdx d) (a := x) (n := R.k)).1 hxmemRot
            exact (mem_nzIdx (d := d) x).1 hxmem
          exact neg_of_sign_false hx0 hxfalse
        exact cut_singleton_neg d hn x hxneg (fun j hj0 hsgn =>
          R.eq_singleton_secondBlock_of_sign hb1 hj0 (by simpa [hσ] using hsgn))
    · have ha2 : 2 ≤ R.a := by
        have ha := R.ha
        omega
      have hb2 : 2 ≤ R.b := by
        have hb := R.hb
        omega
      exact cut_firstBlock_dropLast hn R ha2 hb2

noncomputable def oriented_cut_of_cyclicFlips_nzSigns_eq_two
    {n : ℕ} (d : Fin (n + 1) → ℝ)
    (hn : 3 ≤ n)
    (h2 : cyclicFlips (nzSigns d) = 2) :
    OrientedTwoArcCut d := by
  classical
  let ex0 := cyclicFlips_two_replicate_blocks (nzSigns d) h2
  let k := Classical.choose ex0
  let ex1 := Classical.choose_spec ex0
  let a := Classical.choose ex1
  let ex2 := Classical.choose_spec ex1
  let b := Classical.choose ex2
  let ex3 := Classical.choose_spec ex2
  have ha : 1 ≤ a := ex3.1
  have hb : 1 ≤ b := ex3.2.1
  have hrot : (nzSigns d).rotate k =
      List.replicate a true ++ List.replicate b false := ex3.2.2
  exact cut_of_rot_two_block hn
    ({ k := k
       a := a
       b := b
       ha := ha
       hb := hb
       hrot := by simpa using hrot } : RotTwoBlockCert d true)

noncomputable def orientedCutData_of_signChangesFull
    {n : ℕ} (hn : 2 ≤ n) (A B : Fin (n + 1) → S2)
    (hA : StrictConvexSphArm A) (hB : StrictConvexSphArm B)
    (hsides : ∀ i : Fin n, sideLen A i = sideLen B i)
    (hclose : sDist (A 0) (A (Fin.last n)) = sDist (B 0) (B (Fin.last n)))
    (h2 : signChangesFull A B = 2) :
    OrientedTwoArcCut (linkDiff A B) := by
  classical
  by_cases hn2 : n = 2
  · subst n
    exfalso
    exact signChangesFull_ne_two_triangle A B hA hB hsides hclose h2
  · have hn3 : 3 ≤ n := by omega
    exact oriented_cut_of_cyclicFlips_nzSigns_eq_two (linkDiff A B) hn3
      (by simpa [signChangesFull] using h2)

noncomputable def twoArcSplitData_of_cut {n : ℕ} (hn : 1 ≤ n) (A B : Fin (n + 1) → S2)
    (hA : StrictConvexSphArm A) (hB : StrictConvexSphArm B)
    (hsides : ∀ i : Fin n, sideLen A i = sideLen B i)
    (hclose : sDist (A 0) (A (Fin.last n)) = sDist (B 0) (B (Fin.last n)))
    (cut : TwoArcCut (linkDiff A B)) :
    TwoArcSplitData A B :=
  twoArcSplitData_of_indices hn A B hA hB hsides hclose
    cut.tIdx cut.sIdx cut.hts cut.hsn cut.hm1 cut.hm2
    (twoArcCut_mono1 A B cut)
    (twoArcCut_strict1 A B cut)
    (twoArcCut_mono2 A B cut)

/-- Route-B two-arc input: the realization carries only the sign-definite cut certificate. -/
structure EuclideanTwoArcCutData
    (P Q : TriangulatedEuclideanPolyhedron M)
    (LGP : ∀ v : M.Vertex, VertexLinkGeometry P v)
    (LGQ : ∀ v : M.Vertex, VertexLinkGeometry Q v) where
  twoArcCutData : ∀ (v : M.Vertex),
    signChangesFull (vertexStarOfEuclidean P v (LGP v)).vertexLink
        (linkQcast M
          (fun w => vertexStarOfEuclidean P w (LGP w))
          (fun w => vertexStarOfEuclidean Q w (LGQ w))
          (fun w => vertexLinkGeometry_n_eq P Q LGP LGQ w) v) = 2 →
      OrientedTwoArcCut
        (linkDiff (vertexStarOfEuclidean P v (LGP v)).vertexLink
          (linkQcast M
            (fun w => vertexStarOfEuclidean P w (LGP w))
            (fun w => vertexStarOfEuclidean Q w (LGQ w))
            (fun w => vertexLinkGeometry_n_eq P Q LGP LGQ w) v))

noncomputable def euclidean_twoArc_of_cutData
    (P Q : TriangulatedEuclideanPolyhedron M)
    (LGP : ∀ v : M.Vertex, VertexLinkGeometry P v)
    (LGQ : ∀ v : M.Vertex, VertexLinkGeometry Q v)
    (hsides : ∀ (v : M.Vertex) (i : Fin (vertexStarOfEuclidean P v (LGP v)).n),
      sideLen (vertexStarOfEuclidean P v (LGP v)).vertexLink i =
        sideLen (linkQcast M
          (fun w => vertexStarOfEuclidean P w (LGP w))
          (fun w => vertexStarOfEuclidean Q w (LGQ w))
          (fun w => vertexLinkGeometry_n_eq P Q LGP LGQ w) v) i)
    (hclose : ∀ (v : M.Vertex),
      sDist ((vertexStarOfEuclidean P v (LGP v)).vertexLink 0)
          ((vertexStarOfEuclidean P v (LGP v)).vertexLink
            (Fin.last (vertexStarOfEuclidean P v (LGP v)).n))
        =
      sDist ((linkQcast M
          (fun w => vertexStarOfEuclidean P w (LGP w))
          (fun w => vertexStarOfEuclidean Q w (LGQ w))
          (fun w => vertexLinkGeometry_n_eq P Q LGP LGQ w) v) 0)
        ((linkQcast M
          (fun w => vertexStarOfEuclidean P w (LGP w))
          (fun w => vertexStarOfEuclidean Q w (LGQ w))
          (fun w => vertexLinkGeometry_n_eq P Q LGP LGQ w) v)
            (Fin.last (vertexStarOfEuclidean P v (LGP v)).n)))
    (C : EuclideanTwoArcCutData P Q LGP LGQ) :
    ∀ (v : M.Vertex),
      signChangesFull (vertexStarOfEuclidean P v (LGP v)).vertexLink
          (linkQcast M
            (fun w => vertexStarOfEuclidean P w (LGP w))
            (fun w => vertexStarOfEuclidean Q w (LGQ w))
            (fun w => vertexLinkGeometry_n_eq P Q LGP LGQ w) v) = 2 →
        TwoArcSplitData (vertexStarOfEuclidean P v (LGP v)).vertexLink
          (linkQcast M
            (fun w => vertexStarOfEuclidean P w (LGP w))
            (fun w => vertexStarOfEuclidean Q w (LGQ w))
            (fun w => vertexLinkGeometry_n_eq P Q LGP LGQ w) v) := by
  intro v h2
  let S := vertexStarOfEuclidean P v (LGP v)
  let T :=
    linkQcast M
      (fun w => vertexStarOfEuclidean P w (LGP w))
      (fun w => vertexStarOfEuclidean Q w (LGQ w))
      (fun w => vertexLinkGeometry_n_eq P Q LGP LGQ w) v
  have hn : 1 ≤ S.n := by
    have := S.hn
    omega
  exact twoArcSplitData_of_orientedCut hn S.vertexLink T S.vertexLink_strictArm
    (linkQcast_strictArm M
      (fun w => vertexStarOfEuclidean P w (LGP w))
      (fun w => vertexStarOfEuclidean Q w (LGQ w))
      (fun w => vertexLinkGeometry_n_eq P Q LGP LGQ w) v)
    (hsides v) (hclose v) (C.twoArcCutData v h2)

abbrev rotatedStarP
    (P : TriangulatedEuclideanPolyhedron M)
    (LGP : ∀ v : M.Vertex, VertexLinkGeometry P v)
    (offset : ∀ v : M.Vertex, Fin ((LGP v).n + 1))
    (v : M.Vertex) : VertexStar :=
  (vertexStarOfEuclidean P v (LGP v)).rotate (offset v)

abbrev rotatedStarQ
    (P Q : TriangulatedEuclideanPolyhedron M)
    (LGP : ∀ v : M.Vertex, VertexLinkGeometry P v)
    (LGQ : ∀ v : M.Vertex, VertexLinkGeometry Q v)
    (offset : ∀ v : M.Vertex, Fin ((LGP v).n + 1))
    (v : M.Vertex) : VertexStar :=
  (vertexStarOfEuclidean Q v (LGQ v)).rotate
    (Fin.cast
      (congrArg Nat.succ
        (vertexLinkGeometry_n_eq P Q LGP LGQ v).symm)
      (offset v))

abbrev fixedLinkQcast
    (P Q : TriangulatedEuclideanPolyhedron M)
    (LGP : ∀ v : M.Vertex, VertexLinkGeometry P v)
    (LGQ : ∀ v : M.Vertex, VertexLinkGeometry Q v)
    (v : M.Vertex) : Fin ((LGP v).n + 1) → S2 :=
  fun i => (vertexStarOfEuclidean Q v (LGQ v)).vertexLink
    (Fin.cast
      (congrArg Nat.succ (vertexLinkGeometry_n_eq P Q LGP LGQ v).symm) i)

abbrev rotatedHnn
    (P Q : TriangulatedEuclideanPolyhedron M)
    (LGP : ∀ v : M.Vertex, VertexLinkGeometry P v)
    (LGQ : ∀ v : M.Vertex, VertexLinkGeometry Q v)
    (offset : ∀ v : M.Vertex, Fin ((LGP v).n + 1)) :
    ∀ v : M.Vertex,
      (rotatedStarQ P Q LGP LGQ offset v).n = (rotatedStarP P LGP offset v).n :=
  fun v => by
    unfold rotatedStarP rotatedStarQ VertexStar.rotate
    change (LGQ v).n = (LGP v).n
    exact vertexLinkGeometry_n_eq P Q LGP LGQ v

theorem rotatedStarP_n
    (P : TriangulatedEuclideanPolyhedron M)
    (LGP : ∀ v : M.Vertex, VertexLinkGeometry P v)
    (offset : ∀ v : M.Vertex, Fin ((LGP v).n + 1))
    (v : M.Vertex) :
    (rotatedStarP P LGP offset v).n = (LGP v).n := by
  unfold rotatedStarP VertexStar.rotate
  rfl

theorem linkQcast_rotated_eq
    (P Q : TriangulatedEuclideanPolyhedron M)
    (LGP : ∀ v : M.Vertex, VertexLinkGeometry P v)
    (LGQ : ∀ v : M.Vertex, VertexLinkGeometry Q v)
    (offset : ∀ v : M.Vertex, Fin ((LGP v).n + 1))
    (v : M.Vertex) :
    (fun i : Fin ((LGP v).n + 1) =>
      (linkQcast M
        (rotatedStarP P LGP offset)
        (rotatedStarQ P Q LGP LGQ offset)
        (rotatedHnn P Q LGP LGQ offset) v)
        (Fin.cast (congrArg Nat.succ (rotatedStarP_n P LGP offset v).symm) i))
      =
    rotPoly (n := (LGP v).n)
      (fixedLinkQcast P Q LGP LGQ v)
      (offset v) := by
  unfold rotatedStarP VertexStar.rotate
  funext i
  let i0 : Fin ((LGP v).n + 1) := i
  let hQP := vertexLinkGeometry_n_eq P Q LGP LGQ v
  let hPQ : (LGP v).n = (LGQ v).n := hQP.symm
  let offQ : Fin ((LGQ v).n + 1) := Fin.cast (congrArg Nat.succ hPQ) (offset v)
  unfold linkQcast rotatedStarQ rotPoly
  change ((vertexStarOfEuclidean Q v (LGQ v)).rotate offQ).vertexLink
      (Fin.cast (congrArg Nat.succ hPQ) i0)
    =
    (vertexStarOfEuclidean Q v (LGQ v)).vertexLink
      (Fin.cast (congrArg Nat.succ hPQ) (i0 + offset v))
  rw [VertexStar.vertexLink_rotate]
  unfold rotPoly
  apply congrArg (vertexStarOfEuclidean Q v (LGQ v)).vertexLink
  dsimp [offQ]
  exact (fin_cast_add hPQ i0 (offset v)).symm

theorem rotated_sides_eq
    (P Q : TriangulatedEuclideanPolyhedron M)
    (LGP : ∀ v : M.Vertex, VertexLinkGeometry P v)
    (LGQ : ∀ v : M.Vertex, VertexLinkGeometry Q v)
    (offset : ∀ v : M.Vertex, Fin ((LGP v).n + 1))
    (hcong : CongruentFaces P Q) :
    ∀ (v : M.Vertex) (i : Fin ((rotatedStarP P LGP offset v).n)),
      sideLen (rotatedStarP P LGP offset v).vertexLink i =
        sideLen (linkQcast M
          (rotatedStarP P LGP offset)
          (rotatedStarQ P Q LGP LGQ offset)
          (rotatedHnn P Q LGP LGQ offset) v) i := by
  intro v i
  let A := (vertexStarOfEuclidean P v (LGP v)).vertexLink
  let B := fixedLinkQcast P Q LGP LGQ v
  have hsides0 := euclidean_sides_eq P Q LGP LGQ hcong v
  have hclose0 := euclidean_close_eq P Q LGP LGQ hcong v
  have hsides : ∀ i : Fin (LGP v).n, sideLen A i = sideLen B i := by
    intro i
    simpa [A, B] using hsides0 i
  have hclose : sDist (A 0) (A (Fin.last (LGP v).n)) =
      sDist (B 0) (B (Fin.last (LGP v).n)) := by
    simpa [A, B] using hclose0
  have hn : 1 ≤ (LGP v).n := by
    have := (LGP v).hn
    omega
  change sideLen (rotatedStarP P LGP offset v).vertexLink i =
    sideLen
      (fun j : Fin ((LGP v).n + 1) =>
        (linkQcast M
          (rotatedStarP P LGP offset)
          (rotatedStarQ P Q LGP LGQ offset)
          (rotatedHnn P Q LGP LGQ offset) v)
          (Fin.cast (congrArg Nat.succ (rotatedStarP_n P LGP offset v).symm) j)) i
  rw [linkQcast_rotated_eq P Q LGP LGQ offset v]
  unfold rotatedStarP
  rw [VertexStar.vertexLink_rotate]
  exact rotPoly_sideLen_eq hn A B hsides hclose (offset v) i

theorem rotPoly_close_eq {n : ℕ} (hn : 1 ≤ n) (A B : Fin (n + 1) → S2)
    (hsides : ∀ i : Fin n, sideLen A i = sideLen B i)
    (hclose : sDist (A 0) (A (Fin.last n)) = sDist (B 0) (B (Fin.last n)))
    (k : Fin (n + 1)) :
    sDist ((rotPoly A k) 0) ((rotPoly A k) (Fin.last n)) =
      sDist ((rotPoly B k) 0) ((rotPoly B k) (Fin.last n)) := by
  let j : Fin (n + 1) := (Fin.last n) + k
  have hnext : j + 1 = (0 : Fin (n + 1)) + k := by
    have h := congrArg (fun x : Fin (n + 1) => x + k) (Fin.last_add_one n)
    simpa [j, add_assoc, add_comm, add_left_comm] using h
  have hcyc := all_cyclic_edges_eq hn A B hsides hclose j
  unfold rotPoly
  rw [← hnext]
  rw [sDist_comm (A (j + 1)) (A j)]
  rw [sDist_comm (B (j + 1)) (B j)]
  exact hcyc

theorem rotated_close_eq
    (P Q : TriangulatedEuclideanPolyhedron M)
    (LGP : ∀ v : M.Vertex, VertexLinkGeometry P v)
    (LGQ : ∀ v : M.Vertex, VertexLinkGeometry Q v)
    (offset : ∀ v : M.Vertex, Fin ((LGP v).n + 1))
    (hcong : CongruentFaces P Q) :
    ∀ (v : M.Vertex),
      sDist ((rotatedStarP P LGP offset v).vertexLink 0)
          ((rotatedStarP P LGP offset v).vertexLink
            (Fin.last (rotatedStarP P LGP offset v).n))
        =
      sDist ((linkQcast M
          (rotatedStarP P LGP offset)
          (rotatedStarQ P Q LGP LGQ offset)
          (rotatedHnn P Q LGP LGQ offset) v) 0)
        ((linkQcast M
          (rotatedStarP P LGP offset)
          (rotatedStarQ P Q LGP LGQ offset)
          (rotatedHnn P Q LGP LGQ offset) v)
            (Fin.last (rotatedStarP P LGP offset v).n)) := by
  intro v
  let A := (vertexStarOfEuclidean P v (LGP v)).vertexLink
  let B := fixedLinkQcast P Q LGP LGQ v
  have hsides0 := euclidean_sides_eq P Q LGP LGQ hcong v
  have hclose0 := euclidean_close_eq P Q LGP LGQ hcong v
  have hsides : ∀ i : Fin (LGP v).n, sideLen A i = sideLen B i := by
    intro i
    simpa [A, B] using hsides0 i
  have hclose : sDist (A 0) (A (Fin.last (LGP v).n)) =
      sDist (B 0) (B (Fin.last (LGP v).n)) := by
    simpa [A, B] using hclose0
  have hn : 1 ≤ (LGP v).n := by
    have := (LGP v).hn
    omega
  change sDist ((rotatedStarP P LGP offset v).vertexLink 0)
      ((rotatedStarP P LGP offset v).vertexLink (Fin.last (rotatedStarP P LGP offset v).n))
    =
    sDist
      ((fun j : Fin ((LGP v).n + 1) =>
        (linkQcast M
          (rotatedStarP P LGP offset)
          (rotatedStarQ P Q LGP LGQ offset)
          (rotatedHnn P Q LGP LGQ offset) v)
          (Fin.cast (congrArg Nat.succ (rotatedStarP_n P LGP offset v).symm) j)) 0)
      ((fun j : Fin ((LGP v).n + 1) =>
        (linkQcast M
          (rotatedStarP P LGP offset)
          (rotatedStarQ P Q LGP LGQ offset)
          (rotatedHnn P Q LGP LGQ offset) v)
          (Fin.cast (congrArg Nat.succ (rotatedStarP_n P LGP offset v).symm) j))
        (Fin.last (LGP v).n))
  rw [linkQcast_rotated_eq P Q LGP LGQ offset v]
  unfold rotatedStarP
  rw [VertexStar.vertexLink_rotate]
  exact rotPoly_close_eq hn A B hsides hclose (offset v)

theorem rotated_linkOrder
    (P Q : TriangulatedEuclideanPolyhedron M)
    (LGP : ∀ v : M.Vertex, VertexLinkGeometry P v)
    (LGQ : ∀ v : M.Vertex, VertexLinkGeometry Q v)
    (offset : ∀ v : M.Vertex, Fin ((LGP v).n + 1))
    (dartRep : M.Vertex → D)
    (hdart : ∀ v : M.Vertex, M.tail (dartRep v) = v) :
    ∀ (v : M.Vertex),
      List.DihedralRotated
        ((M.σ.toList (dartRep v)).map (euclideanEdgeSign P Q))
        ((List.ofFn
          (linkDiff (rotatedStarP P LGP offset v).vertexLink
            (linkQcast M
              (rotatedStarP P LGP offset)
              (rotatedStarQ P Q LGP LGQ offset)
              (rotatedHnn P Q LGP LGQ offset) v))).map realSignToEdgeSign) := by
  intro v
  let A := (vertexStarOfEuclidean P v (LGP v)).vertexLink
  let B := fixedLinkQcast P Q LGP LGQ v
  let fixedDiff := linkDiff A B
  let rotatedDiff :=
    linkDiff (rotatedStarP P LGP offset v).vertexLink
      (linkQcast M
        (rotatedStarP P LGP offset)
        (rotatedStarQ P Q LGP LGQ offset)
        (rotatedHnn P Q LGP LGQ offset) v)
  have hfixed := euclidean_linkOrder_at_root P Q LGP LGQ v (dartRep v) (hdart v)
  have hdiff :
      ∀ i : Fin ((LGP v).n + 1), rotatedDiff i = fixedDiff (i + offset v) := by
    intro i
    dsimp [rotatedDiff, fixedDiff, A, B]
    change linkDiff (rotatedStarP P LGP offset v).vertexLink
        (fun j : Fin ((LGP v).n + 1) =>
          (linkQcast M
            (rotatedStarP P LGP offset)
            (rotatedStarQ P Q LGP LGQ offset)
            (rotatedHnn P Q LGP LGQ offset) v)
            (Fin.cast (congrArg Nat.succ (rotatedStarP_n P LGP offset v).symm) j))
        i =
      fixedDiff (i + offset v)
    rw [linkQcast_rotated_eq P Q LGP LGQ offset v]
    unfold rotatedStarP
    rw [VertexStar.vertexLink_rotate]
    exact linkDiff_rotPoly A B (offset v) i
  have hrot :
      ((List.ofFn fixedDiff).map realSignToEdgeSign) ~r
        ((List.ofFn rotatedDiff).map realSignToEdgeSign) := by
    have hshift :
        List.ofFn fixedDiff ~r List.ofFn (fun i : Fin ((LGP v).n + 1) => fixedDiff (i + offset v)) :=
      ofFn_add_isRotated fixedDiff (offset v)
    have hmap := hshift.map realSignToEdgeSign
    have heq :
        List.ofFn (fun i : Fin ((LGP v).n + 1) => fixedDiff (i + offset v)) =
          List.ofFn rotatedDiff := by
      exact (List.ofFn_inj).2 (funext fun i => (hdiff i).symm)
    rw [heq] at hmap
    exact hmap
  exact dihedralRotated_trans_right hfixed hrot

theorem adaptive_activeIndexOne
    (P Q : TriangulatedEuclideanPolyhedron M)
    (LGP : ∀ v : M.Vertex, VertexLinkGeometry P v)
    (LGQ : ∀ v : M.Vertex, VertexLinkGeometry Q v)
    (v : M.Vertex) :
    ActiveVertex M (euclideanEdgeSign P Q) (adaptiveDartRep P Q v) →
      realSignToEdgeSign
        (linkDiff (rotatedStarP P LGP (adaptiveOffset P Q LGP LGQ) v).vertexLink
          (linkQcast M
            (rotatedStarP P LGP (adaptiveOffset P Q LGP LGQ))
            (rotatedStarQ P Q LGP LGQ (adaptiveOffset P Q LGP LGQ))
            (fun w => vertexLinkGeometry_n_eq P Q LGP LGQ w) v)
          ⟨1, by
            have := (rotatedStarP P LGP (adaptiveOffset P Q LGP LGQ) v).hn
            omega⟩) ≠ EdgeSign.zero := by
  intro hact
  have hbase : baseActiveExists P Q v := by
    by_contra hnone
    apply hnone
    rcases hact with ⟨y, hy, hyne⟩
    refine ⟨y, ?_, hyne⟩
    simpa [adaptiveDartRep, hnone] using hy
  let x : D := adaptiveActiveDart P Q v
  have hxspec := adaptiveActiveDart_spec P Q v hbase
  have hxnonzero : euclideanEdgeSign P Q x ≠ EdgeSign.zero := hxspec.2
  let hdeg := signDartHdeg P Q LGP LGQ v
  let e := signDartE P Q LGP LGQ v
  have hxtail : M.tail x = v := by
    simpa [x] using adaptiveActiveDart_tail P Q v
  let hxmem : x ∈ incidentDarts P v := incidentDarts_mem_of_tail P hdeg hxtail
  let Jstar : Fin (starN P v + 1) := reverseStarIndexOfDart P v hdeg x hxmem
  let J : Fin ((LGP v).n + 1) := Fin.cast (congrArg Nat.succ e.symm) Jstar
  have hcastJ : Fin.cast (congrArg Nat.succ e) J = Jstar := by
    subst e
    rfl
  have hstar : starDart P v hdeg (Fin.cast (congrArg Nat.succ e) J) = x := by
    rw [hcastJ]
    exact starDart_reverseStarIndexOfDart P v hdeg x hxmem
  have hval := signDart_value P Q LGP LGQ v J
  have hneqJ :
      realSignToEdgeSign
        (linkDiff (vertexStarOfEuclidean P v (LGP v)).vertexLink
          (linkQcast M
            (fun w => vertexStarOfEuclidean P w (LGP w))
            (fun w => vertexStarOfEuclidean Q w (LGQ w))
            (fun w => vertexLinkGeometry_n_eq P Q LGP LGQ w) v) J) ≠ EdgeSign.zero := by
    intro hz
    have hxsign :
        euclideanEdgeSign P Q x =
          realSignToEdgeSign
            (linkDiff (vertexStarOfEuclidean P v (LGP v)).vertexLink
              (linkQcast M
                (fun w => vertexStarOfEuclidean P w (LGP w))
                (fun w => vertexStarOfEuclidean Q w (LGQ w))
                (fun w => vertexLinkGeometry_n_eq P Q LGP LGQ w) v) J) := by
      simpa [hstar] using hval
    apply hxnonzero
    rw [hxsign, hz]
  let one : Fin ((LGP v).n + 1) := ⟨1, by have := (LGP v).hn; omega⟩
  have hoff :
      adaptiveOffset P Q LGP LGQ v = J - 1 := by
    unfold adaptiveOffset
    change
      (let hdeg := signDartHdeg P Q LGP LGQ v
       let e := signDartE P Q LGP LGQ v
       let x := adaptiveActiveDart P Q v
       let hx : x ∈ incidentDarts P v :=
         incidentDarts_mem_of_tail P hdeg (adaptiveActiveDart_tail P Q v)
       Fin.cast (congrArg Nat.succ e.symm)
         (reverseStarIndexOfDart P v hdeg x hx) - 1) = J - 1
    rfl
  have honeJ0 : one + (J - 1) = J := by
    apply Fin.ext
    rw [Fin.val_add, Fin.sub_def, Fin.val_one']
    simp only [one, Fin.val_mk]
    rw [Nat.mod_eq_of_lt (show 1 < (LGP v).n + 1 by have := (LGP v).hn; omega)]
    show (1 + (((LGP v).n + 1 - 1 + J.val) % ((LGP v).n + 1))) %
        ((LGP v).n + 1) = J.val
    have hstep :
        (1 + (((LGP v).n + 1 - 1 + J.val) % ((LGP v).n + 1))) %
            ((LGP v).n + 1) =
          (1 + ((LGP v).n + 1 - 1 + J.val)) % ((LGP v).n + 1) := by
      have h := (Nat.add_mod 1 ((LGP v).n + 1 - 1 + J.val) ((LGP v).n + 1)).symm
      have h1 : 1 % ((LGP v).n + 1) = 1 :=
        Nat.mod_eq_of_lt (show 1 < (LGP v).n + 1 by have := (LGP v).hn; omega)
      simpa [h1] using h
    rw [hstep]
    have hsum : 1 + ((LGP v).n + 1 - 1 + J.val) = J.val + ((LGP v).n + 1) := by
      omega
    rw [hsum, Nat.add_mod_right, Nat.mod_eq_of_lt J.isLt]
  have hrot :
      linkDiff (rotatedStarP P LGP (adaptiveOffset P Q LGP LGQ) v).vertexLink
          (linkQcast M
            (rotatedStarP P LGP (adaptiveOffset P Q LGP LGQ))
            (rotatedStarQ P Q LGP LGQ (adaptiveOffset P Q LGP LGQ))
            (fun w => vertexLinkGeometry_n_eq P Q LGP LGQ w) v)
          one
        =
      linkDiff (vertexStarOfEuclidean P v (LGP v)).vertexLink
          (linkQcast M
            (fun w => vertexStarOfEuclidean P w (LGP w))
            (fun w => vertexStarOfEuclidean Q w (LGQ w))
            (fun w => vertexLinkGeometry_n_eq P Q LGP LGQ w) v) J := by
    let offP : Fin ((LGP v).n + 1) := adaptiveOffset P Q LGP LGQ v
    have honeJ : one + offP = J := by
      dsimp [offP]
      rw [hoff]
      exact honeJ0
    have hPang :
        linkAngle (rotatedStarP P LGP (adaptiveOffset P Q LGP LGQ) v).vertexLink one =
          linkAngle (vertexStarOfEuclidean P v (LGP v)).vertexLink J := by
      unfold rotatedStarP
      rw [VertexStar.vertexLink_rotate]
      calc
        linkAngle
            (rotPoly (vertexStarOfEuclidean P v (LGP v)).vertexLink
              (adaptiveOffset P Q LGP LGQ v)) one
            = linkAngle (vertexStarOfEuclidean P v (LGP v)).vertexLink
                (one + adaptiveOffset P Q LGP LGQ v) :=
              linkAngle_rotPoly (vertexStarOfEuclidean P v (LGP v)).vertexLink
                (adaptiveOffset P Q LGP LGQ v) one
        _ = linkAngle (vertexStarOfEuclidean P v (LGP v)).vertexLink J := by rw [honeJ]
    have hQang :
        linkAngle
            (linkQcast M
              (rotatedStarP P LGP (adaptiveOffset P Q LGP LGQ))
              (rotatedStarQ P Q LGP LGQ (adaptiveOffset P Q LGP LGQ))
              (fun w => vertexLinkGeometry_n_eq P Q LGP LGQ w) v) one =
          linkAngle
            (linkQcast M
              (fun w => vertexStarOfEuclidean P w (LGP w))
              (fun w => vertexStarOfEuclidean Q w (LGQ w))
              (fun w => vertexLinkGeometry_n_eq P Q LGP LGQ w) v) J := by
      let hQP := vertexLinkGeometry_n_eq P Q LGP LGQ v
      let hPQ : (LGP v).n = (LGQ v).n := hQP.symm
      let offQ : Fin ((LGQ v).n + 1) := Fin.cast (congrArg Nat.succ hPQ) offP
      have hcast :
          Fin.cast (congrArg Nat.succ hPQ) one + offQ =
            Fin.cast (congrArg Nat.succ hPQ) J := by
        apply Fin.ext
        have hval := congrArg Fin.val honeJ
        simpa [offQ, hPQ, Fin.val_add] using hval
      unfold linkQcast rotatedStarQ
      change
        linkAngle
            (fun i =>
              ((vertexStarOfEuclidean Q v (LGQ v)).rotate offQ).vertexLink
                (Fin.cast (congrArg Nat.succ hPQ) i)) one =
          linkAngle
            (fun i =>
              (vertexStarOfEuclidean Q v (LGQ v)).vertexLink
                (Fin.cast (congrArg Nat.succ hPQ) i)) J
      calc
        linkAngle
            (fun i =>
              ((vertexStarOfEuclidean Q v (LGQ v)).rotate offQ).vertexLink
                (Fin.cast (congrArg Nat.succ hPQ) i)) one
            =
          linkAngle ((vertexStarOfEuclidean Q v (LGQ v)).rotate offQ).vertexLink
            (Fin.cast (congrArg Nat.succ hPQ) one) :=
              linkAngle_reindex hPQ
                ((vertexStarOfEuclidean Q v (LGQ v)).rotate offQ).vertexLink one
        _ =
          linkAngle (rotPoly (vertexStarOfEuclidean Q v (LGQ v)).vertexLink offQ)
            (Fin.cast (congrArg Nat.succ hPQ) one) := by
              exact congrArg
                (fun A => linkAngle A (Fin.cast (congrArg Nat.succ hPQ) one))
                (VertexStar.vertexLink_rotate (vertexStarOfEuclidean Q v (LGQ v)) offQ)
        _ =
          linkAngle (vertexStarOfEuclidean Q v (LGQ v)).vertexLink
            (Fin.cast (congrArg Nat.succ hPQ) one + offQ) :=
              linkAngle_rotPoly (vertexStarOfEuclidean Q v (LGQ v)).vertexLink offQ
                (Fin.cast (congrArg Nat.succ hPQ) one)
        _ =
          linkAngle (vertexStarOfEuclidean Q v (LGQ v)).vertexLink
            (Fin.cast (congrArg Nat.succ hPQ) J) :=
              congrArg
                (fun idx => linkAngle (vertexStarOfEuclidean Q v (LGQ v)).vertexLink idx)
                hcast
        _ =
          linkAngle
            (fun i =>
              (vertexStarOfEuclidean Q v (LGQ v)).vertexLink
                (Fin.cast (congrArg Nat.succ hPQ) i)) J :=
              (linkAngle_reindex hPQ (vertexStarOfEuclidean Q v (LGQ v)).vertexLink J).symm
    unfold linkDiff
    rw [hQang, hPang]
  intro hz
  apply hneqJ
  rw [← hrot]
  exact hz

/-- Route-B rerooted fields: stars are really rotated, and active vertices only supply
the index-one nonzero link-difference certificate. -/
structure EuclideanRerootedCutFieldData
    (P Q : TriangulatedEuclideanPolyhedron M)
    (LGP : ∀ v : M.Vertex, VertexLinkGeometry P v)
    (LGQ : ∀ v : M.Vertex, VertexLinkGeometry Q v) where
  isSphere : M.IsSphereMap
  isSimple : M.IsSimpleGraph
  offset : ∀ v : M.Vertex, Fin ((LGP v).n + 1)
  dartRep : M.Vertex → D
  dartRep_tail : ∀ v : M.Vertex, M.tail (dartRep v) = v
  sides_eq : ∀ (v : M.Vertex) (i : Fin ((rotatedStarP P LGP offset v).n)),
    sideLen (rotatedStarP P LGP offset v).vertexLink i =
      sideLen (linkQcast M
        (rotatedStarP P LGP offset)
        (rotatedStarQ P Q LGP LGQ offset)
        (fun w => vertexLinkGeometry_n_eq P Q LGP LGQ w) v) i
  close_eq : ∀ (v : M.Vertex),
    sDist ((rotatedStarP P LGP offset v).vertexLink 0)
        ((rotatedStarP P LGP offset v).vertexLink
          (Fin.last (rotatedStarP P LGP offset v).n))
      =
    sDist ((linkQcast M
        (rotatedStarP P LGP offset)
        (rotatedStarQ P Q LGP LGQ offset)
        (fun w => vertexLinkGeometry_n_eq P Q LGP LGQ w) v) 0)
      ((linkQcast M
        (rotatedStarP P LGP offset)
        (rotatedStarQ P Q LGP LGQ offset)
        (fun w => vertexLinkGeometry_n_eq P Q LGP LGQ w) v)
          (Fin.last (rotatedStarP P LGP offset v).n))
  activeIndexOne : ∀ (v : M.Vertex),
    ActiveVertex M (euclideanEdgeSign P Q) (dartRep v) →
      realSignToEdgeSign
        (linkDiff (rotatedStarP P LGP offset v).vertexLink
          (linkQcast M
            (rotatedStarP P LGP offset)
            (rotatedStarQ P Q LGP LGQ offset)
            (fun w => vertexLinkGeometry_n_eq P Q LGP LGQ w) v)
          ⟨1, by have := (rotatedStarP P LGP offset v).hn; omega⟩) ≠ EdgeSign.zero
  twoArcCutData : ∀ (v : M.Vertex),
    signChangesFull (rotatedStarP P LGP offset v).vertexLink
        (linkQcast M
          (rotatedStarP P LGP offset)
          (rotatedStarQ P Q LGP LGQ offset)
          (fun w => vertexLinkGeometry_n_eq P Q LGP LGQ w) v) = 2 →
      OrientedTwoArcCut
        (linkDiff (rotatedStarP P LGP offset v).vertexLink
          (linkQcast M
            (rotatedStarP P LGP offset)
            (rotatedStarQ P Q LGP LGQ offset)
            (fun w => vertexLinkGeometry_n_eq P Q LGP LGQ w) v))
  linkOrder : ∀ (v : M.Vertex),
    List.DihedralRotated
      ((M.σ.toList (dartRep v)).map (euclideanEdgeSign P Q))
      ((List.ofFn
        (linkDiff (rotatedStarP P LGP offset v).vertexLink
          (linkQcast M
            (rotatedStarP P LGP offset)
            (rotatedStarQ P Q LGP LGQ offset)
            (fun w => vertexLinkGeometry_n_eq P Q LGP LGQ w) v))).map realSignToEdgeSign)

/-- Adaptive rerooted fields.  Unlike `EuclideanRerootedCutFieldData`, this does not carry
`activeIndexOne`; the offset and dart representative are chosen from the edge-sign data, and
`activeIndexOne` is derived by `adaptive_activeIndexOne`. -/
structure EuclideanAdaptiveCutFieldData
    (P Q : TriangulatedEuclideanPolyhedron M)
    (LGP : ∀ v : M.Vertex, VertexLinkGeometry P v)
    (LGQ : ∀ v : M.Vertex, VertexLinkGeometry Q v) where
  isSphere : M.IsSphereMap
  isSimple : M.IsSimpleGraph
  sides_eq : ∀ (v : M.Vertex)
      (i : Fin ((rotatedStarP P LGP (adaptiveOffset P Q LGP LGQ) v).n)),
    sideLen (rotatedStarP P LGP (adaptiveOffset P Q LGP LGQ) v).vertexLink i =
      sideLen (linkQcast M
        (rotatedStarP P LGP (adaptiveOffset P Q LGP LGQ))
        (rotatedStarQ P Q LGP LGQ (adaptiveOffset P Q LGP LGQ))
        (fun w => vertexLinkGeometry_n_eq P Q LGP LGQ w) v) i
  close_eq : ∀ (v : M.Vertex),
    sDist ((rotatedStarP P LGP (adaptiveOffset P Q LGP LGQ) v).vertexLink 0)
        ((rotatedStarP P LGP (adaptiveOffset P Q LGP LGQ) v).vertexLink
          (Fin.last (rotatedStarP P LGP (adaptiveOffset P Q LGP LGQ) v).n))
      =
    sDist ((linkQcast M
        (rotatedStarP P LGP (adaptiveOffset P Q LGP LGQ))
        (rotatedStarQ P Q LGP LGQ (adaptiveOffset P Q LGP LGQ))
        (fun w => vertexLinkGeometry_n_eq P Q LGP LGQ w) v) 0)
      ((linkQcast M
        (rotatedStarP P LGP (adaptiveOffset P Q LGP LGQ))
        (rotatedStarQ P Q LGP LGQ (adaptiveOffset P Q LGP LGQ))
        (fun w => vertexLinkGeometry_n_eq P Q LGP LGQ w) v)
          (Fin.last (rotatedStarP P LGP (adaptiveOffset P Q LGP LGQ) v).n))
  twoArcCutData : ∀ (v : M.Vertex),
    signChangesFull (rotatedStarP P LGP (adaptiveOffset P Q LGP LGQ) v).vertexLink
        (linkQcast M
          (rotatedStarP P LGP (adaptiveOffset P Q LGP LGQ))
          (rotatedStarQ P Q LGP LGQ (adaptiveOffset P Q LGP LGQ))
          (fun w => vertexLinkGeometry_n_eq P Q LGP LGQ w) v) = 2 →
      OrientedTwoArcCut
        (linkDiff (rotatedStarP P LGP (adaptiveOffset P Q LGP LGQ) v).vertexLink
          (linkQcast M
            (rotatedStarP P LGP (adaptiveOffset P Q LGP LGQ))
            (rotatedStarQ P Q LGP LGQ (adaptiveOffset P Q LGP LGQ))
            (fun w => vertexLinkGeometry_n_eq P Q LGP LGQ w) v))
  linkOrder : ∀ (v : M.Vertex),
    List.DihedralRotated
      ((M.σ.toList (adaptiveDartRep P Q v)).map (euclideanEdgeSign P Q))
      ((List.ofFn
        (linkDiff (rotatedStarP P LGP (adaptiveOffset P Q LGP LGQ) v).vertexLink
          (linkQcast M
            (rotatedStarP P LGP (adaptiveOffset P Q LGP LGQ))
            (rotatedStarQ P Q LGP LGQ (adaptiveOffset P Q LGP LGQ))
            (fun w => vertexLinkGeometry_n_eq P Q LGP LGQ w) v))).map realSignToEdgeSign)

noncomputable def euclideanAdaptiveCutFieldData_of_congruent
    (P Q : ConvexEuclideanPolyhedron M)
    (hcong : CongruentFaces P.toTri Q.toTri) :
    EuclideanAdaptiveCutFieldData P.toTri Q.toTri
      (fun v => P.linkGeomAt v) (fun v => Q.linkGeomAt v) where
  isSphere := P.sphere
  isSimple := P.isSimple
  sides_eq :=
    rotated_sides_eq P.toTri Q.toTri
      (fun v => P.linkGeomAt v) (fun v => Q.linkGeomAt v)
      (adaptiveOffset P.toTri Q.toTri
        (fun v => P.linkGeomAt v) (fun v => Q.linkGeomAt v))
      hcong
  close_eq :=
    rotated_close_eq P.toTri Q.toTri
      (fun v => P.linkGeomAt v) (fun v => Q.linkGeomAt v)
      (adaptiveOffset P.toTri Q.toTri
        (fun v => P.linkGeomAt v) (fun v => Q.linkGeomAt v))
      hcong
  twoArcCutData := by
    intro v h2
    exact orientedCutData_of_signChangesFull
      (rotatedStarP P.toTri (fun w => P.linkGeomAt w)
        (adaptiveOffset P.toTri Q.toTri
          (fun w => P.linkGeomAt w) (fun w => Q.linkGeomAt w)) v).hn
      (rotatedStarP P.toTri (fun w => P.linkGeomAt w)
        (adaptiveOffset P.toTri Q.toTri
          (fun w => P.linkGeomAt w) (fun w => Q.linkGeomAt w)) v).vertexLink
      (linkQcast M
        (rotatedStarP P.toTri (fun w => P.linkGeomAt w)
          (adaptiveOffset P.toTri Q.toTri
            (fun w => P.linkGeomAt w) (fun w => Q.linkGeomAt w)))
        (rotatedStarQ P.toTri Q.toTri
          (fun w => P.linkGeomAt w) (fun w => Q.linkGeomAt w)
          (adaptiveOffset P.toTri Q.toTri
            (fun w => P.linkGeomAt w) (fun w => Q.linkGeomAt w)))
        (fun w => vertexLinkGeometry_n_eq P.toTri Q.toTri
          (fun x => P.linkGeomAt x) (fun x => Q.linkGeomAt x) w) v)
      (rotatedStarP P.toTri (fun w => P.linkGeomAt w)
        (adaptiveOffset P.toTri Q.toTri
          (fun w => P.linkGeomAt w) (fun w => Q.linkGeomAt w)) v).vertexLink_strictArm
      (linkQcast_strictArm M
        (rotatedStarP P.toTri (fun w => P.linkGeomAt w)
          (adaptiveOffset P.toTri Q.toTri
            (fun w => P.linkGeomAt w) (fun w => Q.linkGeomAt w)))
        (rotatedStarQ P.toTri Q.toTri
          (fun w => P.linkGeomAt w) (fun w => Q.linkGeomAt w)
          (adaptiveOffset P.toTri Q.toTri
            (fun w => P.linkGeomAt w) (fun w => Q.linkGeomAt w)))
        (fun w => vertexLinkGeometry_n_eq P.toTri Q.toTri
          (fun x => P.linkGeomAt x) (fun x => Q.linkGeomAt x) w) v)
      (rotated_sides_eq P.toTri Q.toTri
        (fun w => P.linkGeomAt w) (fun w => Q.linkGeomAt w)
        (adaptiveOffset P.toTri Q.toTri
          (fun w => P.linkGeomAt w) (fun w => Q.linkGeomAt w))
        hcong v)
      (rotated_close_eq P.toTri Q.toTri
        (fun w => P.linkGeomAt w) (fun w => Q.linkGeomAt w)
        (adaptiveOffset P.toTri Q.toTri
          (fun w => P.linkGeomAt w) (fun w => Q.linkGeomAt w))
        hcong v)
      h2
  linkOrder :=
    rotated_linkOrder P.toTri Q.toTri
      (fun v => P.linkGeomAt v) (fun v => Q.linkGeomAt v)
      (adaptiveOffset P.toTri Q.toTri
        (fun v => P.linkGeomAt v) (fun v => Q.linkGeomAt v))
      (adaptiveDartRep P.toTri Q.toTri)
      (adaptiveDartRep_tail P.toTri Q.toTri)

noncomputable def rerootedCutFieldData_of_adaptive
    (P Q : TriangulatedEuclideanPolyhedron M)
    (LGP : ∀ v : M.Vertex, VertexLinkGeometry P v)
    (LGQ : ∀ v : M.Vertex, VertexLinkGeometry Q v)
    (F : EuclideanAdaptiveCutFieldData P Q LGP LGQ) :
    EuclideanRerootedCutFieldData P Q LGP LGQ where
  isSphere := F.isSphere
  isSimple := F.isSimple
  offset := adaptiveOffset P Q LGP LGQ
  dartRep := adaptiveDartRep P Q
  dartRep_tail := adaptiveDartRep_tail P Q
  sides_eq := F.sides_eq
  close_eq := F.close_eq
  activeIndexOne := adaptive_activeIndexOne P Q LGP LGQ
  twoArcCutData := F.twoArcCutData
  linkOrder := F.linkOrder

noncomputable def rotated_twoArc_of_cutData
    (P Q : TriangulatedEuclideanPolyhedron M)
    (LGP : ∀ v : M.Vertex, VertexLinkGeometry P v)
    (LGQ : ∀ v : M.Vertex, VertexLinkGeometry Q v)
    (F : EuclideanRerootedCutFieldData P Q LGP LGQ) :
    ∀ (v : M.Vertex),
      signChangesFull (rotatedStarP P LGP F.offset v).vertexLink
          (linkQcast M
            (rotatedStarP P LGP F.offset)
            (rotatedStarQ P Q LGP LGQ F.offset)
            (fun w => vertexLinkGeometry_n_eq P Q LGP LGQ w) v) = 2 →
        TwoArcSplitData (rotatedStarP P LGP F.offset v).vertexLink
          (linkQcast M
            (rotatedStarP P LGP F.offset)
            (rotatedStarQ P Q LGP LGQ F.offset)
            (fun w => vertexLinkGeometry_n_eq P Q LGP LGQ w) v) := by
  intro v h2
  let S := rotatedStarP P LGP F.offset v
  let T :=
    linkQcast M
      (rotatedStarP P LGP F.offset)
      (rotatedStarQ P Q LGP LGQ F.offset)
      (fun w => vertexLinkGeometry_n_eq P Q LGP LGQ w) v
  have hn : 1 ≤ S.n := by
    have := S.hn
    omega
  exact twoArcSplitData_of_orientedCut hn S.vertexLink T S.vertexLink_strictArm
    (linkQcast_strictArm M
      (rotatedStarP P LGP F.offset)
      (rotatedStarQ P Q LGP LGQ F.offset)
      (fun w => vertexLinkGeometry_n_eq P Q LGP LGQ w) v)
    (F.sides_eq v) (F.close_eq v) (F.twoArcCutData v h2)

noncomputable def convexPolytopeRealization_of_rerooted_cutFields
    (P Q : TriangulatedEuclideanPolyhedron M)
    (LGP : ∀ v : M.Vertex, VertexLinkGeometry P v)
    (LGQ : ∀ v : M.Vertex, VertexLinkGeometry Q v)
    (F : EuclideanRerootedCutFieldData P Q LGP LGQ) :
    ConvexPolytopeRealization M where
  isSphere := F.isSphere
  triangle := P.every_face_triangle
  isSimple := F.isSimple
  starP := rotatedStarP P LGP F.offset
  starQ := rotatedStarQ P Q LGP LGQ F.offset
  hnn := fun v => vertexLinkGeometry_n_eq P Q LGP LGQ v
  edgeSign := euclideanEdgeSign P Q
  edgeSign_inv := euclideanEdgeSign_alpha P Q
  sides_eq := F.sides_eq
  close_eq := F.close_eq
  dartRep := F.dartRep
  dartRep_tail := F.dartRep_tail
  interiorActive := by
    intro v hact
    exact interiorActive_of_link_index_one
      (rotatedStarP P LGP F.offset v).vertexLink
      (linkQcast M
        (rotatedStarP P LGP F.offset)
        (rotatedStarQ P Q LGP LGQ F.offset)
        (fun w => vertexLinkGeometry_n_eq P Q LGP LGQ w) v)
      (rotatedStarP P LGP F.offset v).hn
      (F.activeIndexOne v hact)
  twoArc := rotated_twoArc_of_cutData P Q LGP LGQ F
  linkOrder := F.linkOrder

/-- Extra Euclidean-to-Cauchy field suppliers not yet derivable from `CongruentFaces` alone. -/
structure EuclideanCauchyFieldData
    (P Q : TriangulatedEuclideanPolyhedron M)
    (LGP : ∀ v : M.Vertex, VertexLinkGeometry P v)
    (LGQ : ∀ v : M.Vertex, VertexLinkGeometry Q v) where
  isSphere : M.IsSphereMap
  isSimple : M.IsSimpleGraph
  sides_eq : ∀ (v : M.Vertex) (i : Fin (vertexStarOfEuclidean P v (LGP v)).n),
    sideLen (vertexStarOfEuclidean P v (LGP v)).vertexLink i =
      sideLen (linkQcast M
        (fun w => vertexStarOfEuclidean P w (LGP w))
        (fun w => vertexStarOfEuclidean Q w (LGQ w))
        (fun w => vertexLinkGeometry_n_eq P Q LGP LGQ w) v) i
  close_eq : ∀ (v : M.Vertex),
    sDist ((vertexStarOfEuclidean P v (LGP v)).vertexLink 0)
        ((vertexStarOfEuclidean P v (LGP v)).vertexLink
          (Fin.last (vertexStarOfEuclidean P v (LGP v)).n))
      =
    sDist ((linkQcast M
        (fun w => vertexStarOfEuclidean P w (LGP w))
        (fun w => vertexStarOfEuclidean Q w (LGQ w))
        (fun w => vertexLinkGeometry_n_eq P Q LGP LGQ w) v) 0)
      ((linkQcast M
        (fun w => vertexStarOfEuclidean P w (LGP w))
        (fun w => vertexStarOfEuclidean Q w (LGQ w))
        (fun w => vertexLinkGeometry_n_eq P Q LGP LGQ w) v)
          (Fin.last (vertexStarOfEuclidean P v (LGP v)).n))
  interiorActive : ∀ (v : M.Vertex),
    ActiveVertex M (euclideanEdgeSign P Q) (vertexDartRep v) →
      ∃ i : Fin ((vertexStarOfEuclidean P v (LGP v)).n - 1),
        jointAngle (vertexStarOfEuclidean P v (LGP v)).vertexLink i ≠
          jointAngle (linkQcast M
            (fun w => vertexStarOfEuclidean P w (LGP w))
            (fun w => vertexStarOfEuclidean Q w (LGQ w))
            (fun w => vertexLinkGeometry_n_eq P Q LGP LGQ w) v) i
  twoArc : ∀ (v : M.Vertex),
    signChangesFull (vertexStarOfEuclidean P v (LGP v)).vertexLink
        (linkQcast M
          (fun w => vertexStarOfEuclidean P w (LGP w))
          (fun w => vertexStarOfEuclidean Q w (LGQ w))
          (fun w => vertexLinkGeometry_n_eq P Q LGP LGQ w) v) = 2 →
      TwoArcSplitData (vertexStarOfEuclidean P v (LGP v)).vertexLink
        (linkQcast M
          (fun w => vertexStarOfEuclidean P w (LGP w))
          (fun w => vertexStarOfEuclidean Q w (LGQ w))
          (fun w => vertexLinkGeometry_n_eq P Q LGP LGQ w) v)
  linkOrder : ∀ (v : M.Vertex),
    List.DihedralRotated
      ((M.σ.toList (vertexDartRep v)).map (euclideanEdgeSign P Q))
      ((List.ofFn
        (linkDiff (vertexStarOfEuclidean P v (LGP v)).vertexLink
          (linkQcast M
            (fun w => vertexStarOfEuclidean P w (LGP w))
            (fun w => vertexStarOfEuclidean Q w (LGQ w))
            (fun w => vertexLinkGeometry_n_eq P Q LGP LGQ w) v))).map realSignToEdgeSign)

/-- Route-B Euclidean-to-Cauchy suppliers: carry `TwoArcCut`, derive `TwoArcSplitData`. -/
structure EuclideanCauchyCutFieldData
    (P Q : TriangulatedEuclideanPolyhedron M)
    (LGP : ∀ v : M.Vertex, VertexLinkGeometry P v)
    (LGQ : ∀ v : M.Vertex, VertexLinkGeometry Q v) where
  isSphere : M.IsSphereMap
  isSimple : M.IsSimpleGraph
  sides_eq : ∀ (v : M.Vertex) (i : Fin (vertexStarOfEuclidean P v (LGP v)).n),
    sideLen (vertexStarOfEuclidean P v (LGP v)).vertexLink i =
      sideLen (linkQcast M
        (fun w => vertexStarOfEuclidean P w (LGP w))
        (fun w => vertexStarOfEuclidean Q w (LGQ w))
        (fun w => vertexLinkGeometry_n_eq P Q LGP LGQ w) v) i
  close_eq : ∀ (v : M.Vertex),
    sDist ((vertexStarOfEuclidean P v (LGP v)).vertexLink 0)
        ((vertexStarOfEuclidean P v (LGP v)).vertexLink
          (Fin.last (vertexStarOfEuclidean P v (LGP v)).n))
      =
    sDist ((linkQcast M
        (fun w => vertexStarOfEuclidean P w (LGP w))
        (fun w => vertexStarOfEuclidean Q w (LGQ w))
        (fun w => vertexLinkGeometry_n_eq P Q LGP LGQ w) v) 0)
      ((linkQcast M
        (fun w => vertexStarOfEuclidean P w (LGP w))
        (fun w => vertexStarOfEuclidean Q w (LGQ w))
        (fun w => vertexLinkGeometry_n_eq P Q LGP LGQ w) v)
          (Fin.last (vertexStarOfEuclidean P v (LGP v)).n))
  interiorActive : ∀ (v : M.Vertex),
    ActiveVertex M (euclideanEdgeSign P Q) (vertexDartRep v) →
      ∃ i : Fin ((vertexStarOfEuclidean P v (LGP v)).n - 1),
        jointAngle (vertexStarOfEuclidean P v (LGP v)).vertexLink i ≠
          jointAngle (linkQcast M
            (fun w => vertexStarOfEuclidean P w (LGP w))
            (fun w => vertexStarOfEuclidean Q w (LGQ w))
            (fun w => vertexLinkGeometry_n_eq P Q LGP LGQ w) v) i
  twoArcCut : EuclideanTwoArcCutData P Q LGP LGQ
  linkOrder : ∀ (v : M.Vertex),
    List.DihedralRotated
      ((M.σ.toList (vertexDartRep v)).map (euclideanEdgeSign P Q))
      ((List.ofFn
        (linkDiff (vertexStarOfEuclidean P v (LGP v)).vertexLink
          (linkQcast M
            (fun w => vertexStarOfEuclidean P w (LGP w))
            (fun w => vertexStarOfEuclidean Q w (LGQ w))
            (fun w => vertexLinkGeometry_n_eq P Q LGP LGQ w) v))).map realSignToEdgeSign)

noncomputable def euclideanFieldData_of_cutFieldData
    (P Q : TriangulatedEuclideanPolyhedron M)
    (LGP : ∀ v : M.Vertex, VertexLinkGeometry P v)
    (LGQ : ∀ v : M.Vertex, VertexLinkGeometry Q v)
    (F : EuclideanCauchyCutFieldData P Q LGP LGQ) :
    EuclideanCauchyFieldData P Q LGP LGQ where
  isSphere := F.isSphere
  isSimple := F.isSimple
  sides_eq := F.sides_eq
  close_eq := F.close_eq
  interiorActive := F.interiorActive
  twoArc := euclidean_twoArc_of_cutData P Q LGP LGQ F.sides_eq F.close_eq F.twoArcCut
  linkOrder := F.linkOrder

/-- Assemble the abstract Cauchy realization interface from Euclidean local field suppliers. -/
def convexPolytopeRealization_of_euclidean_fields
    (P Q : TriangulatedEuclideanPolyhedron M)
    (LGP : ∀ v : M.Vertex, VertexLinkGeometry P v)
    (LGQ : ∀ v : M.Vertex, VertexLinkGeometry Q v)
    (F : EuclideanCauchyFieldData P Q LGP LGQ) :
    ConvexPolytopeRealization M where
  isSphere := F.isSphere
  triangle := P.every_face_triangle
  isSimple := F.isSimple
  starP := fun v => vertexStarOfEuclidean P v (LGP v)
  starQ := fun v => vertexStarOfEuclidean Q v (LGQ v)
  hnn := fun v => vertexLinkGeometry_n_eq P Q LGP LGQ v
  edgeSign := euclideanEdgeSign P Q
  edgeSign_inv := euclideanEdgeSign_alpha P Q
  sides_eq := F.sides_eq
  close_eq := F.close_eq
  dartRep := vertexDartRep
  dartRep_tail := vertexDartRep_tail
  interiorActive := F.interiorActive
  twoArc := F.twoArc
  linkOrder := F.linkOrder

/-- The 3D Cauchy conclusion once the remaining honest Euclidean field suppliers are available. -/
theorem chapter13_euclidean_of_fields
    (P Q : TriangulatedEuclideanPolyhedron M)
    (LGP : ∀ v : M.Vertex, VertexLinkGeometry P v)
    (LGQ : ∀ v : M.Vertex, VertexLinkGeometry Q v)
    (F : EuclideanCauchyFieldData P Q LGP LGQ)
    (v : M.Vertex) (i : Fin ((vertexStarOfEuclidean P v (LGP v)).n - 1)) :
    (vertexStarOfEuclidean P v (LGP v)).dihedral i =
      (vertexStarOfEuclidean Q v (LGQ v)).dihedral
        (Fin.cast (by
          unfold vertexStarOfEuclidean VertexLinkGeometry.toVertexStar
          change (LGP v).n - 1 = (LGQ v).n - 1
          rw [← vertexLinkGeometry_n_eq P Q LGP LGQ v]) i) := by
  simpa [convexPolytopeRealization_of_euclidean_fields, vertexStarOfEuclidean,
    VertexLinkGeometry.toVertexStar] using
    (convexPolytopeRealization_of_euclidean_fields P Q LGP LGQ F).realization_rigid v i

/-- Assemble the abstract Cauchy realization interface from convex Euclidean polyhedra
once the remaining per-field Euclidean producers are supplied. -/
def convexPolytopeRealization_of_convexEuclidean_fields
    (P Q : ConvexEuclideanPolyhedron M)
    (F : EuclideanCauchyFieldData P.toTri Q.toTri
      (fun v => P.linkGeomAt v) (fun v => Q.linkGeomAt v)) :
    ConvexPolytopeRealization M :=
  convexPolytopeRealization_of_euclidean_fields P.toTri Q.toTri
    (fun v => P.linkGeomAt v) (fun v => Q.linkGeomAt v)
    { F with
      isSphere := P.sphere
      isSimple := P.isSimple }

/-- The Euclidean Cauchy conclusion for convex Euclidean polyhedra, conditional
only on the remaining honest field producers. -/
theorem chapter13_euclidean_of_convexEuclidean_fields
    (P Q : ConvexEuclideanPolyhedron M)
    (F : EuclideanCauchyFieldData P.toTri Q.toTri
      (fun v => P.linkGeomAt v) (fun v => Q.linkGeomAt v))
    (v : M.Vertex) (i : Fin ((P.vertexStar v).n - 1)) :
    (P.vertexStar v).dihedral i =
      (Q.vertexStar v).dihedral
        (Fin.cast (by
          change (P.linkGeomAt v).n - 1 = (Q.linkGeomAt v).n - 1
          exact congrArg (fun n => n - 1)
            (vertexLinkGeometry_n_eq P.toTri Q.toTri
              (fun w => P.linkGeomAt w) (fun w => Q.linkGeomAt w) v).symm) i) := by
  simpa [ConvexEuclideanPolyhedron.vertexStar,
    convexPolytopeRealization_of_convexEuclidean_fields,
    ConvexEuclideanPolyhedron.linkGeomAt] using
    (convexPolytopeRealization_of_convexEuclidean_fields P Q F).realization_rigid v i

def convexPolytopeRealization_of_convexEuclidean_cutFields
    (P Q : ConvexEuclideanPolyhedron M)
    (F : EuclideanCauchyCutFieldData P.toTri Q.toTri
      (fun v => P.linkGeomAt v) (fun v => Q.linkGeomAt v)) :
    ConvexPolytopeRealization M :=
  convexPolytopeRealization_of_convexEuclidean_fields P Q
    (euclideanFieldData_of_cutFieldData P.toTri Q.toTri
      (fun v => P.linkGeomAt v) (fun v => Q.linkGeomAt v)
      { F with
        isSphere := P.sphere
        isSimple := P.isSimple })

theorem chapter13_euclidean_of_convexEuclidean_cutFields
    (P Q : ConvexEuclideanPolyhedron M)
    (F : EuclideanCauchyCutFieldData P.toTri Q.toTri
      (fun v => P.linkGeomAt v) (fun v => Q.linkGeomAt v))
    (v : M.Vertex) (i : Fin ((P.vertexStar v).n - 1)) :
    (P.vertexStar v).dihedral i =
      (Q.vertexStar v).dihedral
        (Fin.cast (by
          change (P.linkGeomAt v).n - 1 = (Q.linkGeomAt v).n - 1
          exact congrArg (fun n => n - 1)
            (vertexLinkGeometry_n_eq P.toTri Q.toTri
              (fun w => P.linkGeomAt w) (fun w => Q.linkGeomAt w) v).symm) i) := by
  simpa [convexPolytopeRealization_of_convexEuclidean_cutFields] using
    (convexPolytopeRealization_of_convexEuclidean_cutFields P Q F).realization_rigid v i

theorem chapter13_euclidean_of_rerooted_cutFields
    (P Q : TriangulatedEuclideanPolyhedron M)
    (LGP : ∀ v : M.Vertex, VertexLinkGeometry P v)
    (LGQ : ∀ v : M.Vertex, VertexLinkGeometry Q v)
    (F : EuclideanRerootedCutFieldData P Q LGP LGQ)
    (v : M.Vertex) (i : Fin ((rotatedStarP P LGP F.offset v).n - 1)) :
    (rotatedStarP P LGP F.offset v).dihedral i =
      (rotatedStarQ P Q LGP LGQ F.offset v).dihedral
        (Fin.cast (by
          change (LGP v).n - 1 = (LGQ v).n - 1
          exact congrArg (fun n => n - 1)
            (vertexLinkGeometry_n_eq P Q LGP LGQ v).symm) i) := by
  simpa [convexPolytopeRealization_of_rerooted_cutFields] using
    (convexPolytopeRealization_of_rerooted_cutFields P Q LGP LGQ F).realization_rigid v i

def convexPolytopeRealization_of_adaptive_cutFields
    (P Q : TriangulatedEuclideanPolyhedron M)
    (LGP : ∀ v : M.Vertex, VertexLinkGeometry P v)
    (LGQ : ∀ v : M.Vertex, VertexLinkGeometry Q v)
    (F : EuclideanAdaptiveCutFieldData P Q LGP LGQ) :
    ConvexPolytopeRealization M :=
  convexPolytopeRealization_of_rerooted_cutFields P Q LGP LGQ
    (rerootedCutFieldData_of_adaptive P Q LGP LGQ F)

theorem chapter13_euclidean_of_adaptive_cutFields
    (P Q : TriangulatedEuclideanPolyhedron M)
    (LGP : ∀ v : M.Vertex, VertexLinkGeometry P v)
    (LGQ : ∀ v : M.Vertex, VertexLinkGeometry Q v)
    (F : EuclideanAdaptiveCutFieldData P Q LGP LGQ)
    (v : M.Vertex)
    (i : Fin ((rotatedStarP P LGP (adaptiveOffset P Q LGP LGQ) v).n - 1)) :
    (rotatedStarP P LGP (adaptiveOffset P Q LGP LGQ) v).dihedral i =
      (rotatedStarQ P Q LGP LGQ (adaptiveOffset P Q LGP LGQ) v).dihedral
        (Fin.cast (by
          change (LGP v).n - 1 = (LGQ v).n - 1
          exact congrArg (fun n => n - 1)
            (vertexLinkGeometry_n_eq P Q LGP LGQ v).symm) i) := by
  simpa [convexPolytopeRealization_of_adaptive_cutFields,
    rerootedCutFieldData_of_adaptive] using
    (convexPolytopeRealization_of_adaptive_cutFields P Q LGP LGQ F).realization_rigid v i

def convexPolytopeRealization_of_convexEuclidean
    (P Q : ConvexEuclideanPolyhedron M)
    (hcong : CongruentFaces P.toTri Q.toTri) :
    ConvexPolytopeRealization M :=
  convexPolytopeRealization_of_adaptive_cutFields P.toTri Q.toTri
    (fun v => P.linkGeomAt v) (fun v => Q.linkGeomAt v)
    (euclideanAdaptiveCutFieldData_of_congruent P Q hcong)

theorem chapter13_euclidean
    (P Q : ConvexEuclideanPolyhedron M)
    (hcong : CongruentFaces P.toTri Q.toTri)
    (v : M.Vertex)
    (i : Fin ((rotatedStarP P.toTri (fun w => P.linkGeomAt w)
      (adaptiveOffset P.toTri Q.toTri (fun w => P.linkGeomAt w) (fun w => Q.linkGeomAt w)) v).n - 1)) :
    (rotatedStarP P.toTri (fun w => P.linkGeomAt w)
        (adaptiveOffset P.toTri Q.toTri (fun w => P.linkGeomAt w) (fun w => Q.linkGeomAt w)) v).dihedral i =
      (rotatedStarQ P.toTri Q.toTri (fun w => P.linkGeomAt w) (fun w => Q.linkGeomAt w)
        (adaptiveOffset P.toTri Q.toTri (fun w => P.linkGeomAt w) (fun w => Q.linkGeomAt w)) v).dihedral
        (Fin.cast (by
          change (P.linkGeomAt v).n - 1 = (Q.linkGeomAt v).n - 1
          exact congrArg (fun n => n - 1)
            (vertexLinkGeometry_n_eq P.toTri Q.toTri
              (fun w => P.linkGeomAt w) (fun w => Q.linkGeomAt w) v).symm) i) := by
  simpa [convexPolytopeRealization_of_convexEuclidean] using
    (convexPolytopeRealization_of_convexEuclidean P Q hcong).realization_rigid v i

/--
**Chapter 13 — Cauchy's rigidity theorem (canonical headline).**

Two congruent-faced `ℝ³` convex triangulated polyhedra have equal dihedral
angles at every vertex.  Non-vacuous:
`chapter13_cauchy_rigidity_tetra` actually instantiates this theorem for the
regular tetrahedron.  The carried geometric residual is the convex-link
certificate in `ConvexEuclideanPolyhedron`; the two-arc cut formerly carried as
an external supplier is derived here from the sign-counting theorem.
-/
theorem chapter13_cauchy_rigidity
    (P Q : ConvexEuclideanPolyhedron M)
    (hcong : CongruentFaces P.toTri Q.toTri)
    (v : M.Vertex)
    (i : Fin ((rotatedStarP P.toTri (fun w => P.linkGeomAt w)
      (adaptiveOffset P.toTri Q.toTri (fun w => P.linkGeomAt w) (fun w => Q.linkGeomAt w)) v).n - 1)) :
    (rotatedStarP P.toTri (fun w => P.linkGeomAt w)
        (adaptiveOffset P.toTri Q.toTri (fun w => P.linkGeomAt w) (fun w => Q.linkGeomAt w)) v).dihedral i =
      (rotatedStarQ P.toTri Q.toTri (fun w => P.linkGeomAt w) (fun w => Q.linkGeomAt w)
        (adaptiveOffset P.toTri Q.toTri (fun w => P.linkGeomAt w) (fun w => Q.linkGeomAt w)) v).dihedral
        (Fin.cast (by
          change (P.linkGeomAt v).n - 1 = (Q.linkGeomAt v).n - 1
          exact congrArg (fun n => n - 1)
            (vertexLinkGeometry_n_eq P.toTri Q.toTri
              (fun w => P.linkGeomAt w) (fun w => Q.linkGeomAt w) v).symm) i) :=
  chapter13_euclidean P Q hcong v i

theorem CongruentFaces.refl (P : TriangulatedEuclideanPolyhedron M) :
    CongruentFaces P P := by
  intro d
  rfl

theorem signChangesFull_self_local {n : ℕ} (A : Fin (n + 1) → S2) :
    signChangesFull A A = 0 := by
  unfold signChangesFull
  have hdiff : linkDiff A A = fun _ => (0 : ℝ) := by
    funext i
    unfold linkDiff
    ring
  rw [hdiff]
  simp [nzSigns, cyclicFlips]

abbrev tetraAdaptiveOffset (v : tetraMap.Vertex) :
    Fin ((tetraConvexEuclideanPolyhedron.linkGeomAt v).n + 1) :=
  adaptiveOffset tetraConvexEuclideanPolyhedron.toTri tetraConvexEuclideanPolyhedron.toTri
    (fun w => tetraConvexEuclideanPolyhedron.linkGeomAt w)
    (fun w => tetraConvexEuclideanPolyhedron.linkGeomAt w) v

abbrev tetraRotatedStarP (v : tetraMap.Vertex) : VertexStar :=
  rotatedStarP tetraConvexEuclideanPolyhedron.toTri
    (fun w => tetraConvexEuclideanPolyhedron.linkGeomAt w)
    tetraAdaptiveOffset v

abbrev tetraRotatedStarQ (v : tetraMap.Vertex) : VertexStar :=
  rotatedStarQ tetraConvexEuclideanPolyhedron.toTri tetraConvexEuclideanPolyhedron.toTri
    (fun w => tetraConvexEuclideanPolyhedron.linkGeomAt w)
    (fun w => tetraConvexEuclideanPolyhedron.linkGeomAt w)
    tetraAdaptiveOffset v

theorem tetra_rotated_linkQcast_self (v : tetraMap.Vertex) :
    linkQcast tetraMap tetraRotatedStarP tetraRotatedStarQ
        (fun w => vertexLinkGeometry_n_eq tetraConvexEuclideanPolyhedron.toTri
          tetraConvexEuclideanPolyhedron.toTri
          (fun x => tetraConvexEuclideanPolyhedron.linkGeomAt x)
          (fun x => tetraConvexEuclideanPolyhedron.linkGeomAt x) w) v
      =
    (tetraRotatedStarP v).vertexLink := by
  funext i
  unfold linkQcast tetraRotatedStarP tetraRotatedStarQ rotatedStarP rotatedStarQ
  rw [VertexStar.vertexLink_rotate, VertexStar.vertexLink_rotate]
  unfold rotPoly
  apply congrArg (vertexStarOfEuclidean tetraConvexEuclideanPolyhedron.toTri v
    (tetraConvexEuclideanPolyhedron.linkGeomAt v)).vertexLink
  apply Fin.ext
  simp [Fin.val_add]

theorem chapter13_euclidean_tetra
    (v : tetraMap.Vertex)
    (i : Fin ((tetraConvexEuclideanPolyhedron.vertexStar v).n - 1)) :
    (tetraConvexEuclideanPolyhedron.vertexStar v).dihedral i =
      (tetraConvexEuclideanPolyhedron.vertexStar v).dihedral
        (Fin.cast (by rfl) i) := by
  rfl

theorem chapter13_euclidean_tetra_genuine
    (v : tetraMap.Vertex)
    (i : Fin ((tetraRotatedStarP v).n - 1)) :
    (tetraRotatedStarP v).dihedral i =
      (tetraRotatedStarQ v).dihedral
        (Fin.cast (by
          change (tetraConvexEuclideanPolyhedron.linkGeomAt v).n - 1 =
            (tetraConvexEuclideanPolyhedron.linkGeomAt v).n - 1
          rfl) i) := by
  exact chapter13_euclidean tetraConvexEuclideanPolyhedron tetraConvexEuclideanPolyhedron
    (CongruentFaces.refl tetraConvexEuclideanPolyhedron.toTri) v i

theorem chapter13_cauchy_rigidity_tetra
    (v : tetraMap.Vertex)
    (i : Fin ((tetraRotatedStarP v).n - 1)) :
    (tetraRotatedStarP v).dihedral i =
      (tetraRotatedStarQ v).dihedral
        (Fin.cast (by
          change (tetraConvexEuclideanPolyhedron.linkGeomAt v).n - 1 =
            (tetraConvexEuclideanPolyhedron.linkGeomAt v).n - 1
          rfl) i) :=
  chapter13_euclidean_tetra_genuine v i

#print axioms ProofsInTheBook.Ch13Cauchy3D.CongruentFaces
#print axioms ProofsInTheBook.Ch13Cauchy3D.euclideanEdgeSign_alpha
#print axioms ProofsInTheBook.Ch13VertexStar.VertexStar.rotate
#print axioms ProofsInTheBook.Ch13VertexStar.VertexStar.vertexLink_rotate
#print axioms ProofsInTheBook.Ch13Cauchy3D.interiorActive_of_link_index_one
#print axioms ProofsInTheBook.Ch13Cauchy3D.adaptive_activeIndexOne
#print axioms ProofsInTheBook.Ch13Cauchy3D.twoArcSplitData_of_cut
#print axioms ProofsInTheBook.Ch13Cauchy3D.euclideanFieldData_of_cutFieldData
#print axioms ProofsInTheBook.Ch13Cauchy3D.rerootedCutFieldData_of_adaptive
#print axioms ProofsInTheBook.Ch13Cauchy3D.convexPolytopeRealization_of_adaptive_cutFields
#print axioms ProofsInTheBook.Ch13Cauchy3D.chapter13_euclidean_of_adaptive_cutFields
#print axioms ProofsInTheBook.Ch13Cauchy3D.convexPolytopeRealization_of_convexEuclidean
#print axioms ProofsInTheBook.Ch13Cauchy3D.chapter13_euclidean
#print axioms ProofsInTheBook.Ch13Cauchy3D.chapter13_cauchy_rigidity
#print axioms ProofsInTheBook.Ch13Cauchy3D.chapter13_euclidean_tetra
#print axioms ProofsInTheBook.Ch13Cauchy3D.chapter13_euclidean_tetra_genuine
#print axioms ProofsInTheBook.Ch13Cauchy3D.chapter13_cauchy_rigidity_tetra
#print axioms ProofsInTheBook.Ch13Cauchy3D.convexPolytopeRealization_of_rerooted_cutFields
#print axioms ProofsInTheBook.Ch13Cauchy3D.chapter13_euclidean_of_rerooted_cutFields
#print axioms ProofsInTheBook.Ch13Cauchy3D.convexPolytopeRealization_of_euclidean_fields
#print axioms ProofsInTheBook.Ch13Cauchy3D.chapter13_euclidean_of_fields
#print axioms ProofsInTheBook.Ch13Cauchy3D.tetraConvexEuclideanPolyhedron
#print axioms ProofsInTheBook.Ch13Cauchy3D.convexPolytopeRealization_of_convexEuclidean_fields
#print axioms ProofsInTheBook.Ch13Cauchy3D.chapter13_euclidean_of_convexEuclidean_fields
#print axioms ProofsInTheBook.Ch13Cauchy3D.convexPolytopeRealization_of_convexEuclidean_cutFields
#print axioms ProofsInTheBook.Ch13Cauchy3D.chapter13_euclidean_of_convexEuclidean_cutFields

end ProofsInTheBook.Ch13Cauchy3D
