import Mathlib

/-!
# Chapter 9: Hilbert's third problem

From "Proofs from THE BOOK":

**Hilbert's third problem**: A regular tetrahedron cannot be cut into finitely
many polyhedral pieces and reassembled into a cube (scissors congruence fails).

The book proves this via the **Dehn invariant**: for a polyhedron P,
  D(P) = ∑_{edges e} length(e) ⊗ θ(e) ∈ ℝ ⊗_ℤ (ℝ/πℚ)
where θ(e) is the dihedral angle at edge e. Scissors-congruent polyhedra
have equal Dehn invariants. The cube has D = 0, while the regular
tetrahedron has D ≠ 0 (since arccos(1/3) is irrational over π).

Formalization status: this file closes the algebraic obstruction layer.  It
defines finite Dehn-invariant sums, the angle quotient by rational multiples
of `π`, proves that cube-like right angles vanish in that quotient, proves
`Real.arccos (1 / 3)` is not a rational multiple of `π`, and packages the
final contradiction as `chapter09` / `hilbert_third_problem` once the cube
and tetrahedron Dehn values are supplied.

Gap to the full book theorem: Mathlib does not currently provide the required
three-dimensional scissors-congruence geometry.  A complete proof still needs
a robust Euclidean polyhedron type with faces, edges, lengths, and dihedral
angles; concrete cube and regular tetrahedron models; a geometric Dehn
invariant for those polyhedra; additivity under actual finite dissections and
rigid reassembly; and the nonzero tensor-sum computation for the regular
tetrahedron's six equal edge contributions.
-/

namespace ProofsInTheBook.Chapter09

open scoped BigOperators TensorProduct
open Polynomial Chebyshev

/-!
### Dehn invariant

The key algebraic invariant. Its construction requires:
1. The tensor product ℝ ⊗[ℤ] (ℝ / πℚ)
2. Showing D is additive under dissection
3. Computing D for specific polyhedra

This is a deep geometric result requiring substantial infrastructure
beyond current Mathlib coverage.
-/

/-!
### Current Mathlib geometry coverage

The local Mathlib checkout has the raw Euclidean tools needed for coordinate
calculations in `EuclideanSpace ℝ (Fin 3)`: finite-dimensional inner product
spaces, `Affine.Simplex`, equilateral simplex lemmas, convex hulls/convex sets,
orthogonal projection, signed distance to affine subspaces, and unoriented
angles.  It does not currently expose a bundled three-dimensional polyhedron
API with faces, edges, incidence, dihedral angles, geometric Dehn invariant, or
finite scissors dissections/reassemblies.  The coordinate lemmas below are
therefore deliberately local: they verify the regular tetrahedron model and the
`1 / 3` dihedral cosine calculation, but they are not yet connected to a
global polyhedron/dissection type.
-/

/-- Algebraic target for a Dehn invariant with an abstract angle quotient. -/
abbrev DehnTarget (Angle : Type*) [AddCommGroup Angle] [Module ℤ Angle] :=
  TensorProduct ℤ ℝ Angle

/-- Rational-vector-space target for the classical Dehn invariant. -/
abbrev DehnQTarget (Angle : Type*) [AddCommGroup Angle] [Module ℚ Angle] :=
  TensorProduct ℚ ℝ Angle

/-- Integer multiples of `π`, used as a first algebraic angle quotient. -/
noncomputable def piZSubmodule : Submodule ℤ ℝ :=
  Submodule.span ℤ ({Real.pi} : Set ℝ)

/-- Real angles modulo integer multiples of `π`. -/
abbrev AngleModPiZ :=
  ℝ ⧸ piZSubmodule

/-- Concrete algebraic target `ℝ ⊗[ℤ] (ℝ / πℤ)`. -/
abbrev DehnPiTarget :=
  DehnTarget AngleModPiZ

noncomputable def angleClass (x : ℝ) : AngleModPiZ :=
  Submodule.Quotient.mk x

@[simp]
theorem angleClass_pi : angleClass Real.pi = 0 := by
  exact (Submodule.Quotient.mk_eq_zero piZSubmodule).mpr (Submodule.subset_span (by simp))

/-! ### Rational multiples of `π` quotient (Tier 2 building block)

The Dehn-invariant proof of Hilbert's third problem requires the *rational*
multiples of `π` to be quotiented out, not just integer multiples.  E.g., the
cube's dihedral angle `π/2` is *not* an integer multiple of `π` but *is* a
rational multiple, so it must vanish in the angle target.  The integer
submodule `piZSubmodule` is too coarse — we need `piQSubmodule := ℚ • π`.
-/

/-- Rational multiples of `π`. -/
noncomputable def piQSubmodule : Submodule ℚ ℝ :=
  Submodule.span ℚ ({Real.pi} : Set ℝ)

/-- Real angles modulo rational multiples of `π`. -/
abbrev AngleModPiQ : Type :=
  ℝ ⧸ piQSubmodule

/-- Concrete rational target `ℝ ⊗[ℚ] (ℝ / πℚ)`. -/
abbrev DehnPiQTarget :=
  DehnQTarget AngleModPiQ

/-- The `ℝ ⧸ πℚ` projection. -/
noncomputable def angleClassQ (x : ℝ) : AngleModPiQ :=
  Submodule.Quotient.mk x

@[simp]
theorem angleClassQ_pi : angleClassQ Real.pi = 0 := by
  exact (Submodule.Quotient.mk_eq_zero piQSubmodule).mpr (Submodule.subset_span (by simp))

/-- Any rational multiple of `π` vanishes in the `πℚ` quotient. -/
theorem angleClassQ_rat_mul_pi (q : ℚ) : angleClassQ ((q : ℝ) * Real.pi) = 0 := by
  refine (Submodule.Quotient.mk_eq_zero piQSubmodule).mpr ?_
  rw [show ((q : ℝ) * Real.pi) = q • Real.pi from by
    rw [Rat.smul_def]]
  exact Submodule.smul_mem _ q (Submodule.subset_span (by simp))

/-- The cube's dihedral angle `π/2` is rational over `π`, so it vanishes. -/
@[simp]
theorem angleClassQ_pi_div_two : angleClassQ (Real.pi / 2) = 0 := by
  have h : Real.pi / 2 = ((1/2 : ℚ) : ℝ) * Real.pi := by push_cast; ring
  rw [h, angleClassQ_rat_mul_pi]

/-- Any divisor `π / n` with `0 < n` vanishes in the πℚ quotient. -/
theorem angleClassQ_pi_div (n : ℕ) (_hn : 0 < n) : angleClassQ (Real.pi / n) = 0 := by
  have h : Real.pi / n = ((1/n : ℚ) : ℝ) * Real.pi := by
    push_cast
    rw [div_mul_eq_mul_div, one_mul]
  rw [h, angleClassQ_rat_mul_pi]

/-- Any integer multiple of `π` vanishes in the πℚ quotient
(special case of `angleClassQ_rat_mul_pi` for integer `q`). -/
theorem angleClassQ_int_mul_pi (n : ℤ) :
    angleClassQ ((n : ℝ) * Real.pi) = 0 := by
  have h : (n : ℝ) * Real.pi = ((n : ℚ) : ℝ) * Real.pi := by push_cast; ring
  rw [h, angleClassQ_rat_mul_pi]

/-- `angleClassQ` is additive. -/
@[simp]
theorem angleClassQ_add (x y : ℝ) :
    angleClassQ (x + y) = angleClassQ x + angleClassQ y := rfl

/-- `angleClassQ` of zero is zero. -/
@[simp]
theorem angleClassQ_zero : angleClassQ 0 = 0 := rfl

/-- `angleClassQ` of a negation is the negation in the quotient. -/
@[simp]
theorem angleClassQ_neg (x : ℝ) : angleClassQ (-x) = -(angleClassQ x) := rfl

/-- `angleClassQ` commutes with finite sums. -/
theorem angleClassQ_sum {I : Type*} (s : Finset I) (angle : I → ℝ) :
    angleClassQ (∑ i ∈ s, angle i) = ∑ i ∈ s, angleClassQ (angle i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih => simp [Finset.sum_insert, ha, ih]

/--
If the raw angles around an internal dissection edge add to a rational multiple
of `π`, their classes vanish in `ℝ / πℚ`.
-/
theorem angleClassQ_sum_eq_zero_of_sum_rat_mul_pi {I : Type*}
    (s : Finset I) (angle : I → ℝ) {q : ℚ}
    (h : (∑ i ∈ s, angle i) = (q : ℝ) * Real.pi) :
    (∑ i ∈ s, angleClassQ (angle i)) = 0 := by
  rw [← angleClassQ_sum, h, angleClassQ_rat_mul_pi]

/-- `angleClassQ x = 0` iff `x` is a rational multiple of `π`. -/
theorem angleClassQ_eq_zero_iff (x : ℝ) :
    angleClassQ x = 0 ↔ ∃ q : ℚ, x = (q : ℝ) * Real.pi := by
  rw [angleClassQ, Submodule.Quotient.mk_eq_zero, piQSubmodule,
      Submodule.mem_span_singleton]
  constructor
  · rintro ⟨q, hq⟩; exact ⟨q, by rw [← hq, Rat.smul_def]⟩
  · rintro ⟨q, hq⟩; exact ⟨q, by rw [hq, Rat.smul_def]⟩

/-- `angleClassQ` of a difference of two rational multiples of `π` is zero. -/
theorem angleClassQ_sub_rat_mul_pi (q r : ℚ) :
    angleClassQ ((q : ℝ) * Real.pi - (r : ℝ) * Real.pi) = 0 := by
  rw [show (q : ℝ) * Real.pi - (r : ℝ) * Real.pi = ((q - r : ℚ) : ℝ) * Real.pi from by
    push_cast; ring]
  exact angleClassQ_rat_mul_pi (q - r)

-- (`angleClassQ_arccos_one_third_ne_zero` defined below, after
-- `arccos_one_third_irrational_over_pi`.)

/-- The contribution of one edge: length tensor angle. -/
def dehnEdge {Angle : Type*} [AddCommGroup Angle] [Module ℤ Angle]
    (length : ℝ) (angle : Angle) : DehnTarget Angle :=
  TensorProduct.tmul ℤ length angle

/-- One edge contribution in the classical rational tensor target. -/
noncomputable def dehnEdgeQ {Angle : Type*} [AddCommGroup Angle] [Module ℚ Angle]
    (length : ℝ) (angle : Angle) : DehnQTarget Angle :=
  TensorProduct.tmul ℚ length angle

@[simp]
theorem dehnEdge_zero_length {Angle : Type*} [AddCommGroup Angle] [Module ℤ Angle]
    (angle : Angle) : dehnEdge 0 angle = 0 := by
  simp [dehnEdge]

@[simp]
theorem dehnEdge_zero_angle {Angle : Type*} [AddCommGroup Angle] [Module ℤ Angle]
    (length : ℝ) : dehnEdge length (0 : Angle) = 0 := by
  simp [dehnEdge]

theorem dehnEdge_add_length {Angle : Type*} [AddCommGroup Angle] [Module ℤ Angle]
    (length₁ length₂ : ℝ) (angle : Angle) :
    dehnEdge (length₁ + length₂) angle =
      dehnEdge length₁ angle + dehnEdge length₂ angle := by
  simp [dehnEdge, TensorProduct.add_tmul]

theorem dehnEdge_add_angle {Angle : Type*} [AddCommGroup Angle] [Module ℤ Angle]
    (length : ℝ) (angle₁ angle₂ : Angle) :
    dehnEdge length (angle₁ + angle₂) =
      dehnEdge length angle₁ + dehnEdge length angle₂ := by
  simp [dehnEdge, TensorProduct.tmul_add]

/-- Splitting one geometric edge into finitely many angle pieces is additive. -/
theorem dehnEdge_angle_sum {I Angle : Type*} [AddCommGroup Angle] [Module ℤ Angle]
    (s : Finset I) (length : ℝ) (angle : I → Angle) :
    dehnEdge length (∑ i ∈ s, angle i) =
      ∑ i ∈ s, dehnEdge length (angle i) := by
  simp [dehnEdge, TensorProduct.tmul_sum]

/-- Rational-target version of `dehnEdge_angle_sum`. -/
theorem dehnEdgeQ_angle_sum {I Angle : Type*} [AddCommGroup Angle] [Module ℚ Angle]
    (s : Finset I) (length : ℝ) (angle : I → Angle) :
    dehnEdgeQ length (∑ i ∈ s, angle i) =
      ∑ i ∈ s, dehnEdgeQ length (angle i) := by
  simp [dehnEdgeQ, TensorProduct.tmul_sum]

/--
The algebraic cancellation used for an internal edge of a dissection: if the
incident angles add to a rational multiple of `π`, the total edge contribution
is zero in the angle quotient.
-/
theorem dehnEdge_angleClassQ_sum_eq_zero_of_sum_rat_mul_pi {I : Type*}
    (s : Finset I) (length : ℝ) (angle : I → ℝ) {q : ℚ}
    (h : (∑ i ∈ s, angle i) = (q : ℝ) * Real.pi) :
    (∑ i ∈ s, dehnEdge length (angleClassQ (angle i))) = 0 := by
  rw [← dehnEdge_angle_sum, angleClassQ_sum_eq_zero_of_sum_rat_mul_pi s angle h]
  simp

/--
Rational-target version of the algebraic cancellation used for an internal edge
of a dissection.
-/
theorem dehnEdgeQ_angleClassQ_sum_eq_zero_of_sum_rat_mul_pi {I : Type*}
    (s : Finset I) (length : ℝ) (angle : I → ℝ) {q : ℚ}
    (h : (∑ i ∈ s, angle i) = (q : ℝ) * Real.pi) :
    (∑ i ∈ s, dehnEdgeQ length (angleClassQ (angle i))) = 0 := by
  rw [← dehnEdgeQ_angle_sum, angleClassQ_sum_eq_zero_of_sum_rat_mul_pi s angle h]
  simp [dehnEdgeQ]

/-- Finite edge-sum model for the Dehn invariant. -/
def dehnInvariant {Edge Angle : Type*} [AddCommGroup Angle] [Module ℤ Angle]
    (edges : Finset Edge) (length : Edge → ℝ) (angle : Edge → Angle) :
    DehnTarget Angle :=
  ∑ e ∈ edges, dehnEdge (length e) (angle e)

/-- Finite edge-sum model in the rational tensor target. -/
noncomputable def dehnInvariantQ {Edge Angle : Type*} [AddCommGroup Angle] [Module ℚ Angle]
    (edges : Finset Edge) (length : Edge → ℝ) (angle : Edge → Angle) :
    DehnQTarget Angle :=
  ∑ e ∈ edges, dehnEdgeQ (length e) (angle e)

@[simp]
theorem dehnInvariantQ_empty {Edge Angle : Type*} [AddCommGroup Angle] [Module ℚ Angle]
    (length : Edge → ℝ) (angle : Edge → Angle) :
    dehnInvariantQ (∅ : Finset Edge) length angle = 0 := by
  simp [dehnInvariantQ]

@[simp]
theorem dehnInvariant_empty {Edge Angle : Type*} [AddCommGroup Angle] [Module ℤ Angle]
    (length : Edge → ℝ) (angle : Edge → Angle) :
    dehnInvariant (∅ : Finset Edge) length angle = 0 := by
  simp [dehnInvariant]

theorem dehnInvariant_insert {Edge Angle : Type*} [DecidableEq Edge]
    [AddCommGroup Angle] [Module ℤ Angle] {edges : Finset Edge} {e : Edge}
    (he : e ∉ edges) (length : Edge → ℝ) (angle : Edge → Angle) :
    dehnInvariant (insert e edges) length angle =
      dehnEdge (length e) (angle e) + dehnInvariant edges length angle := by
  simp [dehnInvariant, he]

theorem dehnInvariant_union_of_disjoint {Edge Angle : Type*} [DecidableEq Edge]
    [AddCommGroup Angle] [Module ℤ Angle] {left right : Finset Edge}
    (hdisj : Disjoint left right) (length : Edge → ℝ) (angle : Edge → Angle) :
    dehnInvariant (left ∪ right) length angle =
      dehnInvariant left length angle + dehnInvariant right length angle := by
  simp [dehnInvariant, Finset.sum_union hdisj]

theorem dehnInvariant_biUnion_of_pairwiseDisjoint {Piece Edge Angle : Type*}
    [DecidableEq Edge] [AddCommGroup Angle] [Module ℤ Angle]
    {pieces : Finset Piece} {edges : Piece → Finset Edge}
    (hdisj : Set.PairwiseDisjoint (↑pieces) edges)
    (length : Edge → ℝ) (angle : Edge → Angle) :
    dehnInvariant (pieces.biUnion edges) length angle =
      ∑ p ∈ pieces, dehnInvariant (edges p) length angle := by
  simp [dehnInvariant, Finset.sum_biUnion hdisj]

theorem dehnInvariantQ_union_of_disjoint {Edge Angle : Type*} [DecidableEq Edge]
    [AddCommGroup Angle] [Module ℚ Angle] {left right : Finset Edge}
    (hdisj : Disjoint left right) (length : Edge → ℝ) (angle : Edge → Angle) :
    dehnInvariantQ (left ∪ right) length angle =
      dehnInvariantQ left length angle + dehnInvariantQ right length angle := by
  simp [dehnInvariantQ, Finset.sum_union hdisj]

theorem dehnInvariantQ_biUnion_of_pairwiseDisjoint {Piece Edge Angle : Type*}
    [DecidableEq Edge] [AddCommGroup Angle] [Module ℚ Angle]
    {pieces : Finset Piece} {edges : Piece → Finset Edge}
    (hdisj : Set.PairwiseDisjoint (↑pieces) edges)
    (length : Edge → ℝ) (angle : Edge → Angle) :
    dehnInvariantQ (pieces.biUnion edges) length angle =
      ∑ p ∈ pieces, dehnInvariantQ (edges p) length angle := by
  simp [dehnInvariantQ, Finset.sum_biUnion hdisj]

/-- If every edge has the same angle, the invariant is one tensor with total length. -/
theorem dehnInvariant_const_angle {Edge Angle : Type*}
    [AddCommGroup Angle] [Module ℤ Angle]
    (edges : Finset Edge) (length : Edge → ℝ) (angle : Angle) :
    dehnInvariant edges length (fun _ => angle) =
      dehnEdge (∑ e ∈ edges, length e) angle := by
  simp [dehnInvariant, dehnEdge, TensorProduct.sum_tmul]

/-- If every edge has the same length and angle, only the edge count remains. -/
theorem dehnInvariant_const_length_angle {Edge Angle : Type*}
    [AddCommGroup Angle] [Module ℤ Angle]
    (edges : Finset Edge) (length : ℝ) (angle : Angle) :
    dehnInvariant edges (fun _ => length) (fun _ => angle) =
      dehnEdge ((edges.card : ℝ) * length) angle := by
  rw [dehnInvariant_const_angle]
  congr 1
  simp [nsmul_eq_mul]

/-- Rational-target version of `dehnInvariant_const_angle`. -/
theorem dehnInvariantQ_const_angle {Edge Angle : Type*}
    [AddCommGroup Angle] [Module ℚ Angle]
    (edges : Finset Edge) (length : Edge → ℝ) (angle : Angle) :
    dehnInvariantQ edges length (fun _ => angle) =
      dehnEdgeQ (∑ e ∈ edges, length e) angle := by
  simp [dehnInvariantQ, dehnEdgeQ, TensorProduct.sum_tmul]

/-- Rational-target version of `dehnInvariant_const_length_angle`. -/
theorem dehnInvariantQ_const_length_angle {Edge Angle : Type*}
    [AddCommGroup Angle] [Module ℚ Angle]
    (edges : Finset Edge) (length : ℝ) (angle : Angle) :
    dehnInvariantQ edges (fun _ => length) (fun _ => angle) =
      dehnEdgeQ ((edges.card : ℝ) * length) angle := by
  rw [dehnInvariantQ_const_angle]
  congr 1
  simp [nsmul_eq_mul]

theorem dehnInvariantQ_six_equal_edges {Angle : Type*}
    [AddCommGroup Angle] [Module ℚ Angle] (length : ℝ) (angle : Angle) :
    dehnInvariantQ (Finset.univ : Finset (Fin 6)) (fun _ => length) (fun _ => angle) =
      dehnEdgeQ (6 * length) angle := by
  rw [dehnInvariantQ_const_length_angle]
  norm_num

theorem dehnInvariantQ_eq_zero_of_angles_zero {Edge Angle : Type*}
    [AddCommGroup Angle] [Module ℚ Angle]
    (edges : Finset Edge) (length : Edge → ℝ) (angle : Edge → Angle)
    (hangle : ∀ e ∈ edges, angle e = 0) :
    dehnInvariantQ edges length angle = 0 := by
  unfold dehnInvariantQ
  apply Finset.sum_eq_zero
  intro e he
  unfold dehnEdgeQ
  rw [hangle e he, TensorProduct.tmul_zero]

/--
Algebraic skeleton for the geometric additivity proof: after grouping all
piece-edge contributions by an internal geometric edge, the whole internal
part vanishes if each grouped angle sum is a rational multiple of `π`.
-/
theorem internalDehnContributionQ_eq_zero {InternalEdge Incident : Type*}
    (internalEdges : Finset InternalEdge) (incident : InternalEdge → Finset Incident)
    (length : InternalEdge → ℝ) (angle : InternalEdge → Incident → ℝ)
    (q : InternalEdge → ℚ)
    (hangle : ∀ e ∈ internalEdges,
      (∑ i ∈ incident e, angle e i) = (q e : ℝ) * Real.pi) :
    (∑ e ∈ internalEdges, ∑ i ∈ incident e,
      dehnEdgeQ (length e) (angleClassQ (angle e i))) = 0 := by
  apply Finset.sum_eq_zero
  intro e he
  exact dehnEdgeQ_angleClassQ_sum_eq_zero_of_sum_rat_mul_pi (incident e) (length e)
    (angle e) (hangle e he)

/--
Boundary plus grouped internal contributions reduces to the boundary part.
The geometric work still needed is to supply the `incident` relation and the
angle-sum hypotheses from an actual polyhedral dissection.
-/
theorem boundary_add_internalDehnContributionQ {InternalEdge Incident : Type*}
    (boundary : DehnPiQTarget) (internalEdges : Finset InternalEdge)
    (incident : InternalEdge → Finset Incident) (length : InternalEdge → ℝ)
    (angle : InternalEdge → Incident → ℝ) (q : InternalEdge → ℚ)
    (hangle : ∀ e ∈ internalEdges,
      (∑ i ∈ incident e, angle e i) = (q e : ℝ) * Real.pi) :
    boundary + (∑ e ∈ internalEdges, ∑ i ∈ incident e,
      dehnEdgeQ (length e) (angleClassQ (angle e i))) = boundary := by
  rw [internalDehnContributionQ_eq_zero internalEdges incident length angle q hangle, add_zero]

/--
Algebraic interface for the geometric additivity step.  A future polyhedron
formalization should construct this from an actual finite dissection by
separating boundary edges from internal edges and proving the internal
angle-sum equations.
-/
structure DehnAdditivitySkeletonQ (Piece InternalEdge Incident : Type*) where
  pieces : Finset Piece
  pieceDehn : Piece → DehnPiQTarget
  boundaryDehn : DehnPiQTarget
  internalEdges : Finset InternalEdge
  incident : InternalEdge → Finset Incident
  internalLength : InternalEdge → ℝ
  internalAngle : InternalEdge → Incident → ℝ
  internalAngleMultiple : InternalEdge → ℚ
  piece_sum_eq_boundary_add_internal :
    (∑ p ∈ pieces, pieceDehn p) =
      boundaryDehn + ∑ e ∈ internalEdges, ∑ i ∈ incident e,
        dehnEdgeQ (internalLength e) (angleClassQ (internalAngle e i))
  internal_angle_sum : ∀ e ∈ internalEdges,
    (∑ i ∈ incident e, internalAngle e i) =
      (internalAngleMultiple e : ℝ) * Real.pi

theorem DehnAdditivitySkeletonQ.piece_sum_eq_boundary
    {Piece InternalEdge Incident : Type*}
    (cert : DehnAdditivitySkeletonQ Piece InternalEdge Incident) :
    (∑ p ∈ cert.pieces, cert.pieceDehn p) = cert.boundaryDehn := by
  calc
    (∑ p ∈ cert.pieces, cert.pieceDehn p) =
        cert.boundaryDehn + ∑ e ∈ cert.internalEdges, ∑ i ∈ cert.incident e,
          dehnEdgeQ (cert.internalLength e) (angleClassQ (cert.internalAngle e i)) :=
      cert.piece_sum_eq_boundary_add_internal
    _ = cert.boundaryDehn :=
      boundary_add_internalDehnContributionQ cert.boundaryDehn cert.internalEdges cert.incident
        cert.internalLength cert.internalAngle cert.internalAngleMultiple cert.internal_angle_sum

/--
If two boundary polyhedra decompose into the same finite pieces, and both
geometric additivity skeletons have been supplied, then their boundary Dehn
invariants agree.
-/
theorem boundaryDehn_eq_of_same_piece_additivitySkeletonQ
    {Piece Internal₁ Incident₁ Internal₂ Incident₂ : Type*}
    (left : DehnAdditivitySkeletonQ Piece Internal₁ Incident₁)
    (right : DehnAdditivitySkeletonQ Piece Internal₂ Incident₂)
    (hpieces : left.pieces = right.pieces)
    (hpiece : ∀ p ∈ left.pieces, left.pieceDehn p = right.pieceDehn p) :
    left.boundaryDehn = right.boundaryDehn := by
  calc
    left.boundaryDehn = ∑ p ∈ left.pieces, left.pieceDehn p :=
      left.piece_sum_eq_boundary.symm
    _ = ∑ p ∈ left.pieces, right.pieceDehn p := Finset.sum_congr rfl hpiece
    _ = ∑ p ∈ right.pieces, right.pieceDehn p := by rw [hpieces]
    _ = right.boundaryDehn := right.piece_sum_eq_boundary

/--
Algebraic skeleton for rigid reassembly invariance: a bijection of edge sets
that preserves lengths and angle classes preserves the rational Dehn invariant.
-/
theorem dehnInvariantQ_univ_eq_of_edge_equiv {Edge₁ Edge₂ Angle : Type*}
    [Fintype Edge₁] [Fintype Edge₂] [AddCommGroup Angle] [Module ℚ Angle]
    (e : Edge₁ ≃ Edge₂) (length₁ : Edge₁ → ℝ) (length₂ : Edge₂ → ℝ)
    (angle₁ : Edge₁ → Angle) (angle₂ : Edge₂ → Angle)
    (hlength : ∀ x, length₁ x = length₂ (e x))
    (hangle : ∀ x, angle₁ x = angle₂ (e x)) :
    dehnInvariantQ (Finset.univ : Finset Edge₁) length₁ angle₁ =
      dehnInvariantQ (Finset.univ : Finset Edge₂) length₂ angle₂ := by
  unfold dehnInvariantQ
  exact Fintype.sum_equiv e _ _ (fun x => by simp [hlength x, hangle x])

/-- If every edge angle vanishes in the angle target, the Dehn invariant is zero.
This is the cube case: all dihedral angles are `π/2`, which is a rational
multiple of `π` and therefore zero in `AngleModPiQ`. -/
theorem dehnInvariant_eq_zero_of_angles_zero {Edge Angle : Type*}
    [AddCommGroup Angle] [Module ℤ Angle]
    (edges : Finset Edge) (length : Edge → ℝ) (angle : Edge → Angle)
    (hangle : ∀ e ∈ edges, angle e = 0) :
    dehnInvariant edges length angle = 0 := by
  unfold dehnInvariant
  apply Finset.sum_eq_zero
  intro e he
  unfold dehnEdge
  rw [hangle e he, TensorProduct.tmul_zero]

/-- The cube's Dehn invariant in `DehnPiTarget` is zero: every cube dihedral
angle equals `π/2`, which is a rational multiple of `π` and therefore vanishes
under `angleClassQ`. -/
theorem dehnInvariant_cube_eq_zero {Edge : Type*} (edges : Finset Edge)
    (length : Edge → ℝ) :
    dehnInvariant edges length (fun _ => angleClassQ (Real.pi / 2)) = 0 := by
  apply dehnInvariant_eq_zero_of_angles_zero
  intro _ _
  exact angleClassQ_pi_div_two

/-- Rational-target cube Dehn invariant: all edge angles are right angles. -/
theorem dehnInvariantQ_cube_eq_zero {Edge : Type*} (edges : Finset Edge)
    (length : Edge → ℝ) :
    dehnInvariantQ edges length (fun _ => angleClassQ (Real.pi / 2)) = 0 := by
  apply dehnInvariantQ_eq_zero_of_angles_zero
  intro _ _
  exact angleClassQ_pi_div_two

/-- Additivity of an abstract Dehn invariant over finitely many pieces. -/
theorem dehnInvariant_additive_over_dissection {Piece A : Type*} [AddCommMonoid A]
    (pieces : Finset Piece) (dehn : Piece → A) :
    (∑ p ∈ pieces, dehn p) = ∑ p ∈ pieces, dehn p := rfl

/--
If two dissections have matching piecewise Dehn contributions, their total
Dehn invariants agree.
-/
theorem dehnInvariant_eq_of_same_piece_multiset {Piece A : Type*} [AddCommMonoid A]
    (pieces : Finset Piece) (dehn₁ dehn₂ : Piece → A)
    (h : ∀ p ∈ pieces, dehn₁ p = dehn₂ p) :
    (∑ p ∈ pieces, dehn₁ p) = ∑ p ∈ pieces, dehn₂ p := by
  exact Finset.sum_congr rfl h

structure DehnScissorsCertificate (Piece A : Type*) [AddCommMonoid A] (left right : A) where
  pieces : Finset Piece
  leftDehn : Piece → A
  rightDehn : Piece → A
  left_eq : left = ∑ p ∈ pieces, leftDehn p
  right_eq : right = ∑ p ∈ pieces, rightDehn p
  piece_eq : ∀ p ∈ pieces, leftDehn p = rightDehn p

theorem dehn_eq_of_scissors_certificate {Piece A : Type*} [AddCommMonoid A]
    {left right : A} (cert : DehnScissorsCertificate Piece A left right) : left = right := by
  calc
    left = ∑ p ∈ cert.pieces, cert.leftDehn p := cert.left_eq
    _ = ∑ p ∈ cert.pieces, cert.rightDehn p :=
      dehnInvariant_eq_of_same_piece_multiset cert.pieces cert.leftDehn cert.rightDehn cert.piece_eq
    _ = right := cert.right_eq.symm

theorem no_scissors_certificate_of_dehn_ne {Piece A : Type*} [AddCommMonoid A]
    {left right : A} (hleft : left = 0) (hright : right ≠ 0) :
    ¬ Nonempty (DehnScissorsCertificate Piece A left right) := by
  rintro ⟨cert⟩
  exact hright ((dehn_eq_of_scissors_certificate cert).symm.trans hleft)

/--
The final invariant obstruction in Hilbert's third problem: an object with
zero Dehn invariant cannot be scissors-congruent to one with nonzero Dehn
invariant.
-/
theorem impossible_scissors_congruence_of_dehn_ne {A : Type*} [AddCommMonoid A]
    {cube tetra : A} (hcube : cube = 0) (htetra : tetra ≠ 0) : cube ≠ tetra := by
  intro h
  exact htetra (h.symm.trans hcube)

/-! ### Concrete cube and regular tetrahedron coordinate models -/

abbrev Euclidean3 :=
  EuclideanSpace ℝ (Fin 3)

/-- Outward face normals of the cube centered at the origin. -/
noncomputable def cubeFaceNormal : Fin 6 → Euclidean3 :=
  ![!₂[(1 : ℝ), 0, 0], !₂[-1, 0, 0], !₂[0, 1, 0], !₂[0, -1, 0],
    !₂[0, 0, 1], !₂[0, 0, -1]]

/-- The coordinate axis perpendicular to each cube face. -/
def cubeFaceAxis : Fin 6 → Fin 3 :=
  ![⟨0, by decide⟩, ⟨0, by decide⟩, ⟨1, by decide⟩, ⟨1, by decide⟩,
    ⟨2, by decide⟩, ⟨2, by decide⟩]

/--
The standard regular tetrahedron centered at the origin.  Its vertices are the
four sign vectors with an even number of negative signs.
-/
noncomputable def regularTetrahedronVertex : Fin 4 → Euclidean3 :=
  ![!₂[(1 : ℝ), 1, 1], !₂[(1 : ℝ), -1, -1], !₂[-1, 1, -1], !₂[-1, -1, 1]]

/-- Coordinate dot product in `EuclideanSpace ℝ (Fin 3)`, written explicitly for computation. -/
def dot3 (u v : Euclidean3) : ℝ :=
  u ⟨0, by decide⟩ * v ⟨0, by decide⟩ +
  u ⟨1, by decide⟩ * v ⟨1, by decide⟩ +
  u ⟨2, by decide⟩ * v ⟨2, by decide⟩

noncomputable def cubeFaceNormalCosine (i j : Fin 6) : ℝ :=
  dot3 (cubeFaceNormal i) (cubeFaceNormal j)

theorem cubeFaceNormal_dot_self (i : Fin 6) :
    dot3 (cubeFaceNormal i) (cubeFaceNormal i) = 1 := by
  fin_cases i <;> simp [dot3, cubeFaceNormal]

theorem cubeFaceNormalCosine_of_axis_ne {i j : Fin 6}
    (haxis : cubeFaceAxis i ≠ cubeFaceAxis j) :
    cubeFaceNormalCosine i j = 0 := by
  fin_cases i <;> fin_cases j <;>
    simp [cubeFaceNormalCosine, cubeFaceAxis, dot3, cubeFaceNormal] at haxis ⊢

theorem cube_rightAngle_has_faceNormal_cosine {i j : Fin 6}
    (haxis : cubeFaceAxis i ≠ cubeFaceAxis j) :
    Real.cos (Real.pi / 2) = cubeFaceNormalCosine i j := by
  rw [Real.cos_pi_div_two, cubeFaceNormalCosine_of_axis_ne haxis]

/--
Edges of the coordinate cube, represented as intersections of two adjacent
faces.  The condition `cubeFaceAxis i ≠ cubeFaceAxis j` excludes opposite
parallel face pairs, leaving the twelve actual cube edges.
-/
abbrev CubeEdge :=
  {p : Fin 6 × Fin 6 // p.1 < p.2 ∧ cubeFaceAxis p.1 ≠ cubeFaceAxis p.2}

theorem cubeEdge_card : Fintype.card CubeEdge = 12 := by
  native_decide

theorem cubeEdge_univ_card :
    (Finset.univ : Finset CubeEdge).card = 12 := by
  native_decide

noncomputable def cubeEdgeLength (_e : CubeEdge) : ℝ :=
  2

noncomputable def cubeEdgeDihedralAngle (_e : CubeEdge) : ℝ :=
  Real.pi / 2

theorem cubeEdgeDihedralAngle_faceNormal_cosine (e : CubeEdge) :
    Real.cos (cubeEdgeDihedralAngle e) =
      cubeFaceNormalCosine e.1.1 e.1.2 := by
  rw [cubeEdgeDihedralAngle, cube_rightAngle_has_faceNormal_cosine e.2.2]

/-- Concrete cube Dehn invariant in the rational angle target. -/
theorem cube_dehnInvariantQ_edges_eq_zero :
    dehnInvariantQ (Finset.univ : Finset CubeEdge)
        cubeEdgeLength
        (fun e => angleClassQ (cubeEdgeDihedralAngle e)) = 0 := by
  apply dehnInvariantQ_eq_zero_of_angles_zero
  intro e _he
  simp [cubeEdgeDihedralAngle]

/-- Coordinate squared distance in `EuclideanSpace ℝ (Fin 3)`, written explicitly for computation. -/
def coordinateDistSq3 (u v : Euclidean3) : ℝ :=
  (u ⟨0, by decide⟩ - v ⟨0, by decide⟩) ^ 2 +
  (u ⟨1, by decide⟩ - v ⟨1, by decide⟩) ^ 2 +
  (u ⟨2, by decide⟩ - v ⟨2, by decide⟩) ^ 2

theorem euclidean3_dist_sq_eq_coordinateDistSq3 (u v : Euclidean3) :
    dist u v ^ 2 = coordinateDistSq3 u v := by
  rw [EuclideanSpace.dist_sq_eq]
  simp [coordinateDistSq3, Fin.sum_univ_three, dist_eq_norm]

theorem regularTetrahedronVertex_dot_self (i : Fin 4) :
    dot3 (regularTetrahedronVertex i) (regularTetrahedronVertex i) = 3 := by
  fin_cases i <;> simp [dot3, regularTetrahedronVertex] <;> norm_num

theorem regularTetrahedronVertex_dot_of_ne {i j : Fin 4} (hij : i ≠ j) :
    dot3 (regularTetrahedronVertex i) (regularTetrahedronVertex j) = -1 := by
  fin_cases i <;> fin_cases j <;>
    simp [dot3, regularTetrahedronVertex] at hij ⊢

theorem regularTetrahedronVertex_coordinateDistSq_of_ne {i j : Fin 4} (hij : i ≠ j) :
    coordinateDistSq3 (regularTetrahedronVertex i) (regularTetrahedronVertex j) = 8 := by
  fin_cases i <;> fin_cases j <;>
    simp [coordinateDistSq3, regularTetrahedronVertex] at hij ⊢ <;> norm_num

/-- All six edges in the coordinate tetrahedron have squared length `8`. -/
theorem regularTetrahedronVertex_dist_sq_of_ne {i j : Fin 4} (hij : i ≠ j) :
    dist (regularTetrahedronVertex i) (regularTetrahedronVertex j) ^ 2 = 8 := by
  rw [euclidean3_dist_sq_eq_coordinateDistSq3]
  exact regularTetrahedronVertex_coordinateDistSq_of_ne hij

theorem regularTetrahedronVertex_affineIndependent :
    AffineIndependent ℝ regularTetrahedronVertex := by
  rw [affineIndependent_iff_of_fintype]
  intro w hsum hvec i
  rw [Finset.weightedVSub_eq_linear_combination Finset.univ hsum] at hvec
  have h0 := congrArg (fun v : Euclidean3 => v ⟨0, by decide⟩) hvec
  have h1 := congrArg (fun v : Euclidean3 => v ⟨1, by decide⟩) hvec
  have h2 := congrArg (fun v : Euclidean3 => v ⟨2, by decide⟩) hvec
  simp [regularTetrahedronVertex, Fin.sum_univ_four] at hsum h0 h1 h2
  fin_cases i <;> simp <;> linarith

/-- The coordinate regular tetrahedron as a bundled Mathlib affine simplex. -/
noncomputable def regularTetrahedronSimplex : Affine.Simplex ℝ Euclidean3 3 where
  points := regularTetrahedronVertex
  independent := regularTetrahedronVertex_affineIndependent

theorem regularTetrahedronSimplex_equilateral :
    regularTetrahedronSimplex.Equilateral := by
  refine ⟨Real.sqrt 8, ?_⟩
  intro i j hij
  change dist (regularTetrahedronVertex i) (regularTetrahedronVertex j) = Real.sqrt 8
  rw [← sq_eq_sq₀ dist_nonneg (Real.sqrt_nonneg 8)]
  rw [regularTetrahedronVertex_dist_sq_of_ne hij, Real.sq_sqrt]
  norm_num

/-- Edges of the concrete regular tetrahedron, represented once as ordered pairs `i < j`. -/
abbrev RegularTetrahedronEdge :=
  {p : Fin 4 × Fin 4 // p.1 < p.2}

theorem regularTetrahedronEdge_card : Fintype.card RegularTetrahedronEdge = 6 := by
  native_decide

theorem regularTetrahedronEdge_univ_card :
    (Finset.univ : Finset RegularTetrahedronEdge).card = 6 := by
  native_decide

noncomputable def regularTetrahedronEdgeLength (e : RegularTetrahedronEdge) : ℝ :=
  dist (regularTetrahedronVertex e.1.1) (regularTetrahedronVertex e.1.2)

theorem regularTetrahedronEdgeLength_eq_sqrt8 (e : RegularTetrahedronEdge) :
    regularTetrahedronEdgeLength e = Real.sqrt 8 := by
  rw [regularTetrahedronEdgeLength]
  rw [← sq_eq_sq₀ dist_nonneg (Real.sqrt_nonneg 8)]
  rw [regularTetrahedronVertex_dist_sq_of_ne e.2.ne, Real.sq_sqrt]
  norm_num

theorem regularTetrahedron_dehnInvariantQ_edges_eq :
    dehnInvariantQ (Finset.univ : Finset RegularTetrahedronEdge)
        regularTetrahedronEdgeLength
        (fun _ => angleClassQ (Real.arccos (1 / 3))) =
      dehnEdgeQ (6 * Real.sqrt 8) (angleClassQ (Real.arccos (1 / 3))) := by
  simpa [dehnInvariantQ, regularTetrahedronEdgeLength_eq_sqrt8,
    regularTetrahedronEdge_univ_card] using
    (dehnInvariantQ_const_length_angle
      (edges := (Finset.univ : Finset RegularTetrahedronEdge))
      (length := Real.sqrt 8)
      (angle := angleClassQ (Real.arccos (1 / 3))))

/--
The vector from the origin to a vertex is orthogonal to every edge of the
opposite face.  This is the coordinate fact behind using these vertex vectors
as face normals for the regular tetrahedron.
-/
theorem regularTetrahedronVertex_orthogonal_to_opposite_face_edge
    {i j k : Fin 4} (hji : j ≠ i) (hki : k ≠ i) :
    dot3 (regularTetrahedronVertex i)
      (regularTetrahedronVertex j - regularTetrahedronVertex k) = 0 := by
  fin_cases i <;> fin_cases j <;> fin_cases k <;>
    simp [dot3, regularTetrahedronVertex] at hji hki ⊢

/--
The face opposite vertex `i` has normal parallel to `regularTetrahedronVertex i`.
Since all these normals have squared length `3`, this quotient is the cosine
between the two face normals.
-/
noncomputable def regularTetrahedronFaceNormalCosine (i j : Fin 4) : ℝ :=
  dot3 (regularTetrahedronVertex i) (regularTetrahedronVertex j) / 3

theorem regularTetrahedronFaceNormalCosine_of_ne {i j : Fin 4} (hij : i ≠ j) :
    regularTetrahedronFaceNormalCosine i j = -1 / 3 := by
  rw [regularTetrahedronFaceNormalCosine, regularTetrahedronVertex_dot_of_ne hij]

/--
For adjacent faces of the regular tetrahedron, the cosine of the interior
dihedral angle is the negative of the cosine between outward normals.
-/
theorem regularTetrahedron_dihedralCosine_of_ne {i j : Fin 4} (hij : i ≠ j) :
    -regularTetrahedronFaceNormalCosine i j = 1 / 3 := by
  rw [regularTetrahedronFaceNormalCosine_of_ne hij]
  norm_num

theorem regularTetrahedron_arccos_one_third_has_dihedral_cosine {i j : Fin 4}
    (hij : i ≠ j) :
    Real.cos (Real.arccos (1 / 3)) = -regularTetrahedronFaceNormalCosine i j := by
  rw [Real.cos_arccos, regularTetrahedron_dihedralCosine_of_ne hij] <;> norm_num

/--
The dihedral angle determined by the two outward face normals opposite
vertices `i` and `j`.
-/
noncomputable def regularTetrahedronDihedralAngle (i j : Fin 4) : ℝ :=
  Real.arccos (-regularTetrahedronFaceNormalCosine i j)

theorem regularTetrahedronDihedralAngle_of_ne {i j : Fin 4} (hij : i ≠ j) :
    regularTetrahedronDihedralAngle i j = Real.arccos (1 / 3) := by
  rw [regularTetrahedronDihedralAngle, regularTetrahedron_dihedralCosine_of_ne hij]

/--
The regular tetrahedron has nonzero Dehn invariant because its dihedral
angle `arccos(1/3)` is irrational over `π`. This is the book's key
number-theoretic computation.
-/
def a : ℕ → ℤ
  | 0 => 1
  | 1 => 1
  | (q + 2) => 2 * a (q + 1) - 9 * a q

lemma a_zmod_3 (q : ℕ) : (a q : ZMod 3) = 1 ∨ (a q : ZMod 3) = 2 := by
  induction' q using Nat.strong_induction_on with q ih
  rcases q with _ | q
  · left; rfl
  rcases q with _ | q
  · left; rfl
  · have h1 := ih (q + 1) (by omega)
    have eq : (a (q + 2) : ZMod 3) = 2 * (a (q + 1) : ZMod 3) := by
      have h_a : a (q + 2) = 2 * a (q + 1) - 9 * a q := rfl
      rw [h_a]
      push_cast
      have : (9 : ZMod 3) = 0 := rfl
      rw [this, zero_mul, sub_zero]
    rcases h1 with h | h
    · right; rw [eq, h]; rfl
    · left; rw [eq, h]; rfl

lemma a_eq_T (q : ℕ) :
    (a q : ℝ) = (3 : ℝ)^q * (T ℝ (q : ℤ)).eval (1/3) := by
  induction q using Nat.strong_induction_on with
  | _ q ih =>
    match q with
    | 0 =>
      simp [a, T_zero, eval_one]
    | 1 =>
      simp [a, T_one, eval_X]
    | q + 2 =>
      have ih_q  : (a q : ℝ) = (3 : ℝ)^q * (T ℝ (q : ℤ)).eval (1/3) := ih q (by omega)
      have ih_q1 : (a (q+1) : ℝ) = (3 : ℝ)^(q+1) * (T ℝ ((q+1 : ℕ) : ℤ)).eval (1/3) :=
        ih (q+1) (by omega)
      have hcast : ((q + 2 : ℕ) : ℤ) = (q : ℤ) + 2 := by push_cast; rfl
      have hT :
          (T ℝ ((q + 2 : ℕ) : ℤ)).eval (1/3 : ℝ) =
            2 * (1/3) * (T ℝ ((q : ℤ) + 1)).eval (1/3) -
              (T ℝ ((q : ℕ) : ℤ)).eval (1/3) := by
        rw [hcast, T_add_two]
        simp [eval_sub, eval_mul, eval_X]
      have ha_rec : (a (q + 2) : ℝ) = 2 * (a (q + 1) : ℝ) - 9 * (a q : ℝ) := by
        have : a (q + 2) = 2 * a (q + 1) - 9 * a q := rfl
        rw [this]
        push_cast
        rfl
      have hcast_norm : ((q + 1 : ℕ) : ℤ) = (q : ℤ) + 1 := by push_cast; rfl
      rw [hcast_norm] at ih_q1
      rw [ha_rec, hT, ih_q, ih_q1]
      have h3 : (3 : ℝ)^(q+2) = (3 : ℝ)^q * 9 := by rw [pow_add]; norm_num
      have h31 : (3 : ℝ)^(q+1) = (3 : ℝ)^q * 3 := by rw [pow_add]; norm_num
      rw [h3, h31]
      ring

theorem arccos_one_third_irrational_over_pi (q : ℚ) :
    Real.arccos (1/3) ≠ q * Real.pi := by
  intro h
  rcases eq_or_ne q 0 with hq | hq
  · rw [hq] at h
    simp at h
    revert h
    norm_num
  have hden_pos : (0 : ℝ) < q.den := by exact_mod_cast q.pos
  have h_int : (q.den : ℝ) * Real.arccos (1/3) = (q.num : ℝ) * Real.pi := by
    have hq_eq : (q : ℝ) = (q.num : ℝ) / (q.den : ℝ) := by rw [Rat.cast_def]
    rw [h, hq_eq]
    field_simp
  have h_cos_lhs :
      Real.cos ((q.den : ℝ) * Real.arccos (1/3)) =
        (T ℝ (q.den : ℤ)).eval (1/3) := by
    have hcos_arccos : Real.cos (Real.arccos (1/3)) = 1/3 := by
      rw [Real.cos_arccos] <;> norm_num
    have h_symm := (T_real_cos (Real.arccos (1/3)) (q.den : ℤ)).symm
    have h_cast : ((q.den : ℤ) : ℝ) = (q.den : ℝ) := by push_cast; rfl
    rw [h_cast] at h_symm
    rw [hcos_arccos] at h_symm
    exact h_symm
  
  have h_cos_eq : Real.cos ((q.den : ℝ) * Real.arccos (1/3)) =
                  Real.cos ((q.num : ℝ) * Real.pi) := by rw [h_int]
  
  have h_sin : Real.sin ((q.num : ℝ) * Real.pi) = 0 := by
    have : (q.num : ℝ) * Real.pi = (q.num : ℤ) * Real.pi := by rfl
    rw [this, Real.sin_int_mul_pi]
  have h_cos_sq : Real.cos ((q.num : ℝ) * Real.pi) ^ 2 = 1 := by
    have := Real.cos_sq_add_sin_sq ((q.num : ℝ) * Real.pi)
    rw [h_sin] at this
    linarith
  have h4 : Real.cos ((q.num : ℝ) * Real.pi) = 1 ∨ Real.cos ((q.num : ℝ) * Real.pi) = -1 := sq_eq_one_iff.mp h_cos_sq

  have h_T_eval : (T ℝ (q.den : ℤ)).eval (1/3) = 1 ∨ (T ℝ (q.den : ℤ)).eval (1/3) = -1 := by
    rcases h4 with h4 | h4
    · left; rw [← h_cos_lhs, h_cos_eq, h4]
    · right; rw [← h_cos_lhs, h_cos_eq, h4]

  have h_a_eq : (a q.den : ℝ) = (3 : ℝ)^q.den ∨ (a q.den : ℝ) = -(3 : ℝ)^q.den := by
    have eq := a_eq_T q.den
    rcases h_T_eval with ht | ht
    · left; rw [eq, ht, mul_one]
    · right; rw [eq, ht]; ring
  
  have h_a_eq_int : (a q.den : ℤ) = (3 : ℤ)^q.den ∨ (a q.den : ℤ) = -(3 : ℤ)^q.den := by
    rcases h_a_eq with ha | ha
    · left; exact_mod_cast ha
    · right; exact_mod_cast ha

  have h_den_pos : 1 ≤ q.den := q.pos
  have h_a_zmod : (a q.den : ZMod 3) = 0 := by
    have h_pow : (3 : ZMod 3)^q.den = 0 := by
      obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero (ne_of_gt h_den_pos)
      rw [hk]
      have h3 : (3 : ZMod 3) = 0 := rfl
      rw [h3]
      exact zero_pow (by omega)
    rcases h_a_eq_int with ha | ha
    · have : ((a q.den : ℤ) : ZMod 3) = (3 : ZMod 3)^q.den := by
        rw [ha]
        exact Int.cast_pow 3 q.den
      rw [this, h_pow]
    · have : ((a q.den : ℤ) : ZMod 3) = -(3 : ZMod 3)^q.den := by
        rw [ha]
        have h_pow_cast : (((3 : ℤ)^q.den : ℤ) : ZMod 3) = (3 : ZMod 3)^q.den := Int.cast_pow 3 q.den
        rw [Int.cast_neg, h_pow_cast]
      rw [this, h_pow, neg_zero]
      
  rcases a_zmod_3 q.den with h1 | h2
  · rw [h_a_zmod] at h1; revert h1; decide
  · rw [h_a_zmod] at h2; revert h2; decide


/-- `arccos(1/3)` is *not* a rational multiple of `π`, hence is nonzero in the
`πℚ` quotient — this is the tetrahedron's nontrivial Dehn-edge contribution. -/
theorem angleClassQ_arccos_one_third_ne_zero :
    angleClassQ (Real.arccos (1/3)) ≠ 0 := by
  intro h
  rw [angleClassQ, Submodule.Quotient.mk_eq_zero] at h
  rw [piQSubmodule, Submodule.mem_span_singleton] at h
  obtain ⟨q, hq⟩ := h
  rw [Rat.smul_def] at hq
  exact arccos_one_third_irrational_over_pi q hq.symm

theorem angleClassQ_regularTetrahedronDihedralAngle_ne_zero {i j : Fin 4} (hij : i ≠ j) :
    angleClassQ (regularTetrahedronDihedralAngle i j) ≠ 0 := by
  rw [regularTetrahedronDihedralAngle_of_ne hij]
  exact angleClassQ_arccos_one_third_ne_zero

/--
Pure tensors over a field are nonzero when both factors are nonzero.  This is
the algebraic fact needed to turn the tetrahedron's nonzero angle class into a
nonzero rational Dehn invariant.
-/
theorem tensor_tmul_ne_zero_of_ne_zero {K M N : Type*} [Field K]
    [AddCommGroup M] [Module K M] [AddCommGroup N] [Module K N]
    {m : M} {n : N} (hm : m ≠ 0) (hn : n ≠ 0) :
    (m ⊗ₜ[K] n : TensorProduct K M N) ≠ 0 := by
  classical
  let s : Set N := {n}
  have hs : LinearIndepOn K id s := by
    rw [linearIndepOn_singleton_iff]
    exact hn
  let b : Module.Basis (hs.extend (Set.subset_univ s)) K N := Module.Basis.extend hs
  have hn_mem : n ∈ hs.extend (Set.subset_univ s) :=
    hs.subset_extend (Set.subset_univ s) (by simp [s])
  let i : hs.extend (Set.subset_univ s) := ⟨n, hn_mem⟩
  have hb_i : b i = n := by
    change (Module.Basis.extend hs) i = (i : N)
    exact Module.Basis.extend_apply_self hs i
  intro hzero
  have hcoeff : (TensorProduct.equivFinsuppOfBasisRight b) (m ⊗ₜ[K] n) i = 0 := by
    rw [hzero]
    simp
  rw [TensorProduct.equivFinsuppOfBasisRight_apply_tmul_apply] at hcoeff
  have hrepr : b.repr n i = 1 := by
    rw [← hb_i, Module.Basis.repr_self]
    simp
  rw [hrepr, one_smul] at hcoeff
  exact hm hcoeff

theorem dehnEdgeQ_ne_zero_of_ne_zero {Angle : Type*}
    [AddCommGroup Angle] [Module ℚ Angle] {length : ℝ} {angle : Angle}
    (hlength : length ≠ 0) (hangle : angle ≠ 0) :
    dehnEdgeQ length angle ≠ 0 := by
  exact tensor_tmul_ne_zero_of_ne_zero hlength hangle

/--
In the rational tensor target, the six equal edges of a regular tetrahedron
give a nonzero Dehn sum as soon as the common edge length is nonzero.
-/
theorem regularTetrahedron_six_edge_dehnQ_ne_zero {edgeLength : ℝ}
    (hedgeLength : edgeLength ≠ 0) :
    dehnInvariantQ (Finset.univ : Finset (Fin 6)) (fun _ => edgeLength)
        (fun _ => angleClassQ (Real.arccos (1 / 3))) ≠ 0 := by
  rw [dehnInvariantQ_six_equal_edges]
  exact dehnEdgeQ_ne_zero_of_ne_zero
    (mul_ne_zero (by norm_num : (6 : ℝ) ≠ 0) hedgeLength)
    angleClassQ_arccos_one_third_ne_zero

/--
The regular tetrahedron's concrete six-edge Dehn invariant is nonzero in
`ℝ ⊗[ℚ] (ℝ / πℚ)`.
-/
theorem regularTetrahedron_dehnInvariantQ_edges_ne_zero :
    dehnInvariantQ (Finset.univ : Finset RegularTetrahedronEdge)
        regularTetrahedronEdgeLength
        (fun _ => angleClassQ (Real.arccos (1 / 3))) ≠ 0 := by
  rw [regularTetrahedron_dehnInvariantQ_edges_eq]
  exact dehnEdgeQ_ne_zero_of_ne_zero
    (mul_ne_zero (by norm_num : (6 : ℝ) ≠ 0)
      (ne_of_gt (Real.sqrt_pos_of_pos (by norm_num : (0 : ℝ) < 8))))
    angleClassQ_arccos_one_third_ne_zero

/--
The abstract rational Dehn sums for a right-angled cube and a regular
tetrahedron are different.  This still does not assert geometric scissors
congruence, because the polyhedron/dissection layer is not available.
-/
theorem cube_not_regularTetrahedron_abstract_dehnQ {cubeEdgeLength tetraEdgeLength : ℝ}
    (htetraEdgeLength : tetraEdgeLength ≠ 0) :
    dehnInvariantQ (Finset.univ : Finset (Fin 12)) (fun _ => cubeEdgeLength)
        (fun _ => angleClassQ (Real.pi / 2)) ≠
      dehnInvariantQ (Finset.univ : Finset (Fin 6)) (fun _ => tetraEdgeLength)
        (fun _ => angleClassQ (Real.arccos (1 / 3))) := by
  exact impossible_scissors_congruence_of_dehn_ne
    (dehnInvariantQ_cube_eq_zero (Finset.univ : Finset (Fin 12)) (fun _ => cubeEdgeLength))
    (regularTetrahedron_six_edge_dehnQ_ne_zero htetraEdgeLength)

/--
The right-angled 12-edge cube Dehn sum differs from the concrete regular
tetrahedron edge Dehn sum.
-/
theorem cube_not_regularTetrahedron_concrete_dehnQ {cubeEdgeLength : ℝ} :
    dehnInvariantQ (Finset.univ : Finset (Fin 12)) (fun _ => cubeEdgeLength)
        (fun _ => angleClassQ (Real.pi / 2)) ≠
      dehnInvariantQ (Finset.univ : Finset RegularTetrahedronEdge)
        regularTetrahedronEdgeLength
        (fun _ => angleClassQ (Real.arccos (1 / 3))) := by
  exact impossible_scissors_congruence_of_dehn_ne
    (dehnInvariantQ_cube_eq_zero (Finset.univ : Finset (Fin 12)) (fun _ => cubeEdgeLength))
    regularTetrahedron_dehnInvariantQ_edges_ne_zero

/--
The concrete cube edge model and the concrete regular tetrahedron edge model
have different rational Dehn invariants.
-/
theorem cube_not_regularTetrahedron_concrete_geometry_dehnQ :
    dehnInvariantQ (Finset.univ : Finset CubeEdge)
        cubeEdgeLength
        (fun e => angleClassQ (cubeEdgeDihedralAngle e)) ≠
      dehnInvariantQ (Finset.univ : Finset RegularTetrahedronEdge)
        regularTetrahedronEdgeLength
        (fun _ => angleClassQ (Real.arccos (1 / 3))) := by
  exact impossible_scissors_congruence_of_dehn_ne
    cube_dehnInvariantQ_edges_eq_zero
    regularTetrahedron_dehnInvariantQ_edges_ne_zero

/--
Hilbert's third problem: a regular tetrahedron cannot be cut into finitely
many polyhedral pieces and reassembled into a cube. The book's proof:
1. The cube has Dehn invariant 0 (dihedral angles are π/2, which is 0 mod π)
2. The tetrahedron has nonzero Dehn invariant (arccos(1/3) is irrational over π)
3. Scissors-congruent polyhedra have equal Dehn invariants
4. Therefore the cube and tetrahedron are not scissors-congruent
-/
theorem hilbert_third_problem
    (cubeDehn tetraDehn : DehnPiTarget)
    (hcube : cubeDehn = 0)
    (htetra : tetraDehn ≠ 0) :
    cubeDehn ≠ tetraDehn :=
  impossible_scissors_congruence_of_dehn_ne hcube htetra

theorem chapter09 {A : Type*} [AddCommMonoid A] {cube tetra : A}
    (hcube : cube = 0) (htetra : tetra ≠ 0) : cube ≠ tetra :=
  impossible_scissors_congruence_of_dehn_ne hcube htetra

end ProofsInTheBook.Chapter09
